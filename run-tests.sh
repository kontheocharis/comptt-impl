#!/bin/bash

IMPL=$(stack exec which comptt)

PASS=0
FAIL=0

echo "Running tests with implementation: $IMPL"
for f in test/bad/*.er; do
    output=$(cat "$f" | $IMPL nf 2>&1)
    exitcode=$?
    expect=$(sed -n 's/^-- expect: //p' "$f")
    if echo "$output" | grep -q "CallStack"; then
        echo "PANIC: $f"
        ((FAIL++))
    elif [ $exitcode -eq 0 ]; then
        echo "FAIL (should reject): $f"
        ((FAIL++))
    elif [ -n "$expect" ] && ! echo "$output" | grep -qF "$expect"; then
        echo "FAIL (wrong error message): $f"
        echo "  expected: $expect"
        echo "$output" | tail -3
        ((FAIL++))
    else
        echo "PASS (rejected): $f"
        ((PASS++))
    fi
done

for f in test/good/*.er; do
    output=$((cat "$f" | $IMPL nf 2>&1) && (cat "$f" | $IMPL ex 2>&1))
    exitcode=$?
    if echo "$output" | grep -q "CallStack"; then
        echo "PANIC: $f"
        ((FAIL++))
    elif [ $exitcode -eq 0 ]; then
        echo "PASS (accepted): $f"
        ((PASS++))
    else
        echo "FAIL (should accept): $f"
        echo "$output"
        ((FAIL++))
    fi
done

echo ""
echo "Results: $PASS passed, $FAIL failed"

[ $FAIL -eq 0 ]
