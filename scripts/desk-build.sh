#!/usr/bin/env bash
# Desk tooling (not published): build the given targets one at a time, logging errors and sorry warnings.
cd /c/GitHub_Files/Claude-Repos/finite-quantum-designs-lean
for m in "$@"; do
  echo "=== $m $(date +%T)"
  lake build "$m" > .last-build.out 2>&1; st=$?
  grep -i "error\|warning: declaration uses 'sorry'\|sorry" .last-build.out | grep -v "^trace" | head -30
  echo "exit $st $(date +%T)"
done
echo "DONE $(date +%T)"
