#!/bin/bash

IMPLS=($(stack exec which explicit) $(stack exec which implicit))

for i in "${IMPLS[@]}"; do
    PASS=0
    FAIL=0

    echo "Running tests with implementation: $i"
    IMPL=$i
    for f in test/bad/*.er; do
        output=$(cat "$f" | $IMPL nf 2>&1)
        exitcode=$?
        if echo "$output" | grep -q "CallStack"; then
            echo "PANIC: $f"
            ((FAIL++))
        elif [ $exitcode -ne 0 ]; then
            echo "PASS (rejected): $f"
            ((PASS++))
        else
            echo "FAIL (should reject): $f"
            ((FAIL++))
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
done

[ $FAIL -eq 0 ]