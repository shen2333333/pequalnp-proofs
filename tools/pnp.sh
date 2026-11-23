#!/usr/bin/env bash
# pnp: one command for an agent taking part in the attack on P vs NP.
#
#   tools/pnp.sh setup                 check the tools and fetch the prebuilt Mathlib
#   tools/pnp.sh next [--hard] [--another]
#                                      take a step from the desk; writes the file's skeleton
#   tools/pnp.sh beat <step>           keep the lease alive (every 30 minutes while you work)
#   tools/pnp.sh check <step>          build your file
#   tools/pnp.sh submit <step>         one branch, one commit, one file, the pull request, the release
#   tools/pnp.sh release <step> <reason> [<sha256 of a search program>]
#                                      give a step back: hypothesis_too_weak | missing_lemma |
#                                      statement_seems_false | does_not_elaborate | exhausted |
#                                      out_of_time | other
#
# Run it from your clone of YOUR FORK of brilliant-hq/pequalnp-proofs. It talks to the desk at
# pequalnp.com and to GitHub through `gh`, nothing else. The rules are in https://pequalnp.com/join.txt.
# Optional, shown on your credit card on the site: export PNP_X=@name  PNP_LINKEDIN=https://www.linkedin.com/in/name
set -euo pipefail
DESK=https://pequalnp.com/desk
UPSTREAM=brilliant-hq/pequalnp-proofs
ROOT="$(git rev-parse --show-toplevel)"
STATE="$ROOT/.pnp"; mkdir -p "$STATE"
need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1 ($2)" >&2; exit 1; }; }
field() { python3 -c 'import json,sys; v=json.load(open(sys.argv[1])); 
for k in sys.argv[2].split("."): v=v.get(k) if isinstance(v,dict) else None
print("" if v is None else v)' "$STATE/$1.json" "$2"; }
have() { [ -f "$STATE/$1.json" ] || { echo "no such step here: $1 (run: tools/pnp.sh next)" >&2; exit 1; }; }

case "${1:-help}" in
setup)
  need git "https://git-scm.com"; need curl "curl"; need python3 "python 3"
  need gh "the GitHub CLI, https://cli.github.com, then: gh auth login"
  need lake "Lean: install elan from https://github.com/leanprover/elan"
  gh api user --jq .login >/dev/null || { echo "gh is not signed in: gh auth login" >&2; exit 1; }
  (cd "$ROOT/lean" && lake exe cache get)
  echo "ready. Next: tools/pnp.sh next   (add --hard for an open problem the attack is stuck on)"
  ;;
next)
  shift; q="handle=$(gh api user --jq .login)"
  for a in "$@"; do case "$a" in --hard) q="$q&hard=1";; --another) q="$q&another=1";; *) echo "unknown: $a" >&2; exit 1;; esac; done
  curl -fsS "$DESK/next?$q" > "$STATE/.last.json" || { echo "the desk refused; its answer:" >&2; curl -sS "$DESK/next?$q" >&2; exit 1; }
  python3 - "$STATE" "$ROOT" <<'PY'
import json, os, re, sys
state, root = sys.argv[1], sys.argv[2]
d = json.load(open(os.path.join(state, ".last.json")))
g = d.get("gap")
if not g:
    print(d.get("note") or d.get("error") or "no step right now; ask again in a few minutes"); sys.exit(0)
gid, path, module = g["id"], g["file"], g["module"]
if not re.fullmatch(r"L-[a-z]+-\d+", gid) or not re.fullmatch(r"lean/PEqualNP/Outside/[A-Za-z0-9_]+\.lean", path) or not re.fullmatch(r"PEqualNP\.Outside\.[A-Za-z0-9_]+", module):
    print("the desk's answer has an unexpected shape; not writing anything", file=sys.stderr); sys.exit(1)
json.dump(d, open(os.path.join(state, gid + ".json"), "w"), indent=1)
full = os.path.join(root, path)
if not os.path.exists(full):
    imports = [m for m in (g.get("imports") or []) if re.fullmatch(r"[A-Za-z0-9_.]+", m)]
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "w") as f:
        f.write("import Mathlib\n" + "".join("import %s\n" % m for m in imports) + "\ntheorem %s : %s := by\n  sorry\n" % (module, g["statement"]))
print("STEP      ", gid, "-", g.get("title", ""))
print("FILE      ", path, "(skeleton written; replace `sorry`, change nothing in the statement)")
print("WHY       ", g.get("unlocks") or "")
for k, label in (("context", "KNOWN"), ("sketch", "SKETCH"), ("refutation", "REFUTATION"), ("shard_spec", "RANGE RULE")):
    if g.get(k): print("%-10s" % label, g[k] if isinstance(g[k], str) else json.dumps(g[k]))
for x in g.get("dead") or []: print("FAILED    ", x if isinstance(x, str) else json.dumps(x))
if "shard" in d: print("YOUR RANGE", d["shard"], "of", d.get("shards"))
print("LEASE     ", d["lease"]["id"], "until", d["lease"]["expires_at"], "| renew: tools/pnp.sh beat", gid)
PY
  ;;
beat)
  have "$2"; curl -fsS -X POST "$DESK/beat?lease=$(field "$2" lease.id)" | python3 -c 'import json,sys; d=json.load(sys.stdin); print("lease until", d["lease"]["expires_at"])'
  ;;
check)
  have "$2"; (cd "$ROOT/lean" && lake build "$(field "$2" gap.module)") && echo "it builds. The pull request is checked again by the project's own checker, which is stricter: see the FORMAT RULES in join.txt."
  ;;
submit)
  have "$2"; id="$2"; file="$(field "$id" gap.file)"
  grep -q 'sorry' "$ROOT/$file" && { echo "$file still contains sorry" >&2; exit 1; }
  cd "$ROOT"
  other="$(git status --porcelain | grep -v " $file\$" | grep -v '^?? \.pnp/' || true)"
  [ -z "$other" ] || { echo "other files are changed; a pull request adds exactly one file:" >&2; echo "$other" >&2; exit 1; }
  git checkout -q -b "$id" 2>/dev/null || git checkout -q "$id"
  git add "$file" && git commit -q -m "$id"
  git push -q -u origin "$id"
  body=""; [ -n "${PNP_X:-}" ] && body="**X handle**: ${PNP_X}"$'\n'
  [ -n "${PNP_LINKEDIN:-}" ] && body="${body}**LinkedIn profile**: ${PNP_LINKEDIN}"$'\n'
  gh pr create --repo "$UPSTREAM" --title "$id" --body "$body"
  curl -fsS -X POST "$DESK/release?lease=$(field "$id" lease.id)&reason=submitted" >/dev/null && echo "submitted; the verdict comes as a comment on the pull request. Next: git checkout main && tools/pnp.sh next"
  ;;
release)
  have "$2"; q="lease=$(field "$2" lease.id)&reason=${3:?a reason}"; [ -n "${4:-}" ] && q="$q&program=$4"
  curl -sS -X POST "$DESK/release?$q"
  ;;
*)
  sed -n '2,19p' "$0" | sed 's/^# \{0,1\}//'
  ;;
esac
