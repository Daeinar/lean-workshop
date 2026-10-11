#!/usr/bin/env bash
# The mechanical part of the checklist in README.md.
#
# Normally run through make: `make` builds and records the statement files,
# `make check` / `make check-model` / `make check-rust` run the checks.
#
#   ./check.sh snapshot        record the statement files as they are now
#   ./check.sh                 check everything
#   ./check.sh model           check exercise 1 only
#   ./check.sh rust            check exercises 2 to 4 only
#
# Checks:
#   1. The given files match .given.sha256, and the statement files match the snapshot.
#   2. `lake build` succeeds with no `sorry` left in the proof files.
#   3. The exercise theorems use only the allowed axioms.
set -u
cd "$(dirname "$0")"

STATEMENTS="exercises/Model/Statements.lean exercises/FastcryptoMerkle/Statements.lean"
ALLOWED='propext\|Classical.choice\|Quot.sound\|Aeneas.Std.core.fmt.Formatter'
SNAP=.snapshot

if [ "${1:-}" = "snapshot" ]; then
  for f in $STATEMENTS; do mkdir -p "$SNAP/$(dirname "$f")"; cp "$f" "$SNAP/$f"; done
  echo "snapshot taken of: $STATEMENTS"
  exit 0
fi

part="${1:-model rust}"
status=0
in_part() {
  case "$1" in
    exercises/Model*) case "$part" in *model*) return 0;; esac;;
    *) case "$part" in *rust*) return 0;; esac;;
  esac
  return 1
}

echo "== 1. given files and statements unchanged"
if shasum -a 256 -c --quiet .given.sha256 >/dev/null 2>&1; then
  echo "ok: given files unchanged"
else
  echo "FAIL: a given file was modified:"
  shasum -a 256 -c .given.sha256 2>/dev/null | grep -v ": OK$"
  status=1
fi
for f in $STATEMENTS; do
  in_part "$f" || continue
  if [ -f "$SNAP/$f" ]; then
    if cmp -s "$f" "$SNAP/$f"; then
      echo "ok: $f matches the snapshot"
    else
      echo "FAIL: $f differs from the version recorded by the last 'make':"
      diff "$SNAP/$f" "$f" | head -20
      status=1
    fi
  else
    echo "no snapshot of $f (run 'make' once after writing the statement, before prompting the LLM)."
    echo "    Compare the statements below with what you wrote:"
    case "$f" in
      exercises/Model*) mod=Model.Statements; names="Model.CompletenessStatement";;
      *) mod=FastcryptoMerkle.Statements
         names="FastcryptoMerkle.Exercises.EmptyRootStatement FastcryptoMerkle.Exercises.OutOfBoundsStatement FastcryptoMerkle.Exercises.RoundtripStatement";;
    esac
    for n in $names; do
      printf 'import %s\n#print %s\n' "$mod" "$n" | lake env lean --stdin 2>&1 | grep -v "^info:.*Except" | sed 's/^/    /'
    done
  fi
done

echo "== 2. build"
build_log=$(lake build 2>&1)
if [ $? -ne 0 ]; then
  echo "FAIL: lake build failed"; echo "$build_log" | grep -i "error" | head -20; status=1
else
  echo "ok: build succeeded"
  for f in exercises/Model/Statements.lean exercises/Model/Proof.lean \
           exercises/FastcryptoMerkle/Statements.lean exercises/FastcryptoMerkle/Proofs.lean; do
    in_part "$f" || continue
    if echo "$build_log" | grep -q "$f.*sorry"; then
      echo "FAIL: $f still contains sorry"; status=1
    fi
  done
fi

echo "== 3. axioms"
check_axioms() {  # $1 = module to import, $2 = theorem name
  ax=$(printf 'import %s\n#print axioms %s\n' "$1" "$2" | lake env lean --stdin 2>&1 | tr '\n' ' ' \
       | grep -o "'[^']*' \(depends on axioms: \[[^]]*\]\|does not depend on any axioms\)")
  echo "$ax"
  if echo "$ax" | grep -q "does not depend"; then return; fi
  if echo "$ax" | sed 's/.*\[\(.*\)\].*/\1/' | tr ',' '\n' | sed 's/ //g' | grep -vqx "$ALLOWED"; then
    echo "FAIL ($2): disallowed axiom (sorryAx = sorry left; Lean.ofReduceBool = native_decide; other = axiom added)"
    status=1
  fi
}
case "$part" in *model*) check_axioms Model.Proof Model.completeness;; esac
case "$part" in *rust*)
  for t in empty_root out_of_bounds roundtrip; do
    check_axioms FastcryptoMerkle.Proofs FastcryptoMerkle.Exercises.$t
  done;;
esac

echo "== now do items 4 and 5 of the checklist in README.md by hand"
exit $status
