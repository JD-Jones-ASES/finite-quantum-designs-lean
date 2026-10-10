#!/usr/bin/env bash
# Desk tooling (not published). Cut one worktree per lane under C:/GitHub_Files/Claude-Repos/wt/fqd-<lane> on
# branch desk/<lane>, link .lake/packages to the main repo's packages by a junction (made from PowerShell, never
# mklink from Bash), and copy .lake/build so the lane's first build is a replay. Usage: bash scripts/make-worktrees.sh lane1 lane2 ...
set -e
ROOT=/c/GitHub_Files/Claude-Repos/finite-quantum-designs-lean
WT=/c/GitHub_Files/Claude-Repos/wt
mkdir -p "$WT"
cd "$ROOT"
for lane in "$@"; do
  dir="$WT/fqd-$lane"
  if [ -e "$dir" ]; then echo "exists: $dir"; continue; fi
  git branch -f "desk/$lane" main >/dev/null 2>&1 || git branch "desk/$lane"
  git worktree add -q "$dir" "desk/$lane"
  mkdir -p "$dir/.lake"
  powershell.exe -NoProfile -Command "New-Item -ItemType Junction -Path 'C:\\GitHub_Files\\Claude-Repos\\wt\\fqd-$lane\\.lake\\packages' -Target 'C:\\GitHub_Files\\Claude-Repos\\finite-quantum-designs-lean\\.lake\\packages' | Out-Null"
  cp -r "$ROOT/.lake/build" "$dir/.lake/build"
  echo "worktree: $dir (desk/$lane)"
done
