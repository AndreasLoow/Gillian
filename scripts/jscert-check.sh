#!/usr/bin/env bash
# Local regression gate for the JSCert memory-model refactoring of Gillian-JS.
#
# Runs, in order:
#   1. dune build @all
#   2. the AWS Encryption SDK case study (Gillian-JS/Examples/Amazon)
#   3. the two AWS bug variants, each of which must fail *for its documented
#      reason* (see Gillian-JS/Examples/Amazon/README.md)
#   4. the JaVerT verification examples and Cosette symbolic tests
#
# Prints one PASS/FAIL/KNOWN line per check and exits non-zero if any check
# fails. KNOWN marks a failure caused by a known upstream bug; it does not fail
# the gate.
# Logs are kept in $JSCERT_CHECK_LOGS (default: _build/jscert-check).
#
# Usage: scripts/jscert-check.sh [--quick]
#   --quick  only run the build and the AWS case study

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

QUICK=0
[[ "${1:-}" == "--quick" ]] && QUICK=1

LOGS=${JSCERT_CHECK_LOGS:-$ROOT/_build/jscert-check}
GJS=$ROOT/_build/install/default/bin/gillian-js
FAILED=0

report() { # name status detail
  printf '%-5s %-40s %s\n' "$2" "$1" "$3"
  [[ "$2" == PASS || "$2" == KNOWN ]] || FAILED=1
}

# z3 >= 5 is required: older versions (e.g. Ubuntu's 4.8.12) crash mid-run.
z3v=$(z3 --version 2>/dev/null | sed -n 's/^Z3 version \([0-9]*\).*/\1/p')
if [[ -z "$z3v" || "$z3v" -lt 5 ]]; then
  echo "ABORT: z3 >= 5 required (found: $(z3 --version 2>/dev/null || echo none))" >&2
  exit 2
fi

rm -rf "$LOGS"
mkdir -p "$LOGS"

# 1. Build
if dune build @all > "$LOGS/build.log" 2>&1; then
  report build PASS ""
else
  report build FAIL "see $LOGS/build.log"
  exit 1
fi

# 2. AWS case study
AMAZON=$ROOT/Gillian-JS/Examples/Amazon
cd "$AMAZON"
start=$SECONDS
"$GJS" verify deserialize_factory.js --no-lemma-proof -l disabled > "$LOGS/aws.log" 2>&1
rc=$?
secs=$((SECONDS - start))
if [[ $rc -eq 0 ]] && grep -q "All specs succeeded" "$LOGS/aws.log"; then
  report aws PASS "$(grep -o 'All specs succeeded.*' "$LOGS/aws.log" | head -1) (wall ${secs}s)"
else
  report aws FAIL "rc=$rc, see $LOGS/aws.log"
fi

if [[ $QUICK -eq 1 ]]; then exit $FAILED; fi

# 3. AWS bug variants. Each must fail, and must fail for the documented reason:
# decodeEncryptionContext is the only failing spec, and its failure is the
# expected one.
bug_variant() { # name expected-failure-message [known-issue-if-verified]
  local name=$1 expected=$2 known=${3:-} dir="$LOGS/bug-$1"
  mkdir -p "$dir"
  cp -r "$AMAZON/bugs/$name/." "$dir/"
  (cd "$dir" && "$GJS" verify deserialize_factory.js --no-lemma-proof -l disabled > out.log 2>&1)
  local rc=$?
  local failing
  failing=$(sed -n 's/^Verifying one spec of procedure \([A-Za-z_]*\)\.\.\. .* Failure$/\1/p' "$dir/out.log" | sort -u | tr '\n' ' ')
  if [[ $rc -eq 0 && -n "$known" ]]; then
    report "aws-bug-$name" KNOWN "verifies: $known"
  elif [[ $rc -eq 0 ]]; then
    report "aws-bug-$name" FAIL "unexpectedly verified"
  elif [[ "$failing" == "decodeEncryptionContext " ]] \
       && grep -q "^1\. $expected" "$dir/out.log" && ! grep -q "^2\. " "$dir/out.log"; then
    report "aws-bug-$name" PASS "decodeEncryptionContext: $expected"
  else
    report "aws-bug-$name" FAIL "failing: ${failing:-none}; see $dir/out.log"
  fi
}
# pp: the duplicate-key check throws (prototype poisoning).
# Known upstream bug since #391: the throwing path leaves a loop, and putting
# the loop's frame back fails ("FRAMING ON RESULTED IN 0 STATES"), so the path
# is dropped and the variant verifies. See the fix-produce-matching PR.
bug_variant pp "Terminated with flag error instead of normal" \
  "upstream frame-vanishing bug (#391), path dropped"
# frozen: the returned empty encryption context is still extensible.
bug_variant frozen "Couldn't satisfy postcondition"

# 4. JaVerT and Cosette, run from a scratch copy of the examples.
ENV=$LOGS/environment
mkdir -p "$ENV"
cp -r "$ROOT/Gillian-JS/Examples" "$ENV/"
cd "$ENV"
for f in BST PriQ SLL DLL Sort ExprEval IDGen KVMap annotated/SLL; do
  log="$LOGS/javert-${f//\//_}.log"
  "$GJS" verify "Examples/JaVerT/$f.js" -l disabled --no-lemma-proof > "$log" 2>&1
  rc=$?
  if [[ $rc -eq 0 ]] && grep -q "All specs succeeded" "$log"; then
    report "javert/$f" PASS ""
  else
    report "javert/$f" FAIL "rc=$rc, see $log"
  fi
done

for f in BST/bst_find_1 BST/bst_find_min_1 BST/bst_insert_1 BST/bst_remove_1 \
         DLL/dll ExprEval/exprEval_3 ExprEval/exprEval_4 ExprEval/exprEval_5 \
         ExprEval/exprEval_6 ExprEval/exprEval_7 IDGen/IdGen KVMap/kv_map_1 \
         KVMap/kv_map_2 PriQ/pri_q_1 PriQ/pri_q_2 SLL/sll Sort/sort_1 Sort/sort_2 \
         ../simple_example ../check_div_by_zero; do
  log="$LOGS/cosette-${f//\//_}.log"
  "$GJS" wpst "Examples/Cosette/CaseStudies/$f.js" -l disabled > "$log" 2>&1
  rc=$?
  if [[ $rc -eq 0 ]] && grep -q "Success!" "$log"; then
    report "cosette/${f#../}" PASS ""
  else
    report "cosette/${f#../}" FAIL "rc=$rc, see $log"
  fi
done

echo
if [[ $FAILED -eq 0 ]]; then echo "jscert-check: ALL PASS"; else echo "jscert-check: FAILURES"; fi
exit $FAILED
