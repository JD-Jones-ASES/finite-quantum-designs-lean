module

import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A module file importing `Solution` (not `Challenge.lean`). Walks every constant of the environment
whose name begins with `QuantumDesigns.`, `_private.QuantumDesigns.` or `_private.Solution.` (the public declarations of
this development; the private auxiliaries that Lean generates are not enumerated under the module
system, but `collectAxioms` reaches every private constant a public proof refers to, including a
private `axiom`), and collects the axioms each depends on. Anything outside `propext`,
`Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`. The audit
also fails if it matched fewer constants than the floor below (so a renamed namespace cannot make it
pass vacuously) or if any of the compared theorems is missing from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "QuantumDesigns." || label.startsWith "_private.QuantumDesigns." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 200 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 200"
  for n in [`QuantumDesigns.hasMUBs_le, `QuantumDesigns.hasMUBs_one_dim,
      `QuantumDesigns.hasMUBs_of_le, `QuantumDesigns.hasMUBs_mul,
      `QuantumDesigns.hasMUBs_of_forall_primePow, `QuantumDesigns.hasMUBs_three,
      `QuantumDesigns.quadSum_normSq, `QuantumDesigns.hasCompleteMUBs_of_odd_char,
      `QuantumDesigns.isMaxMUBCount_odd_prime_pow, `QuantumDesigns.hasCompleteMUBs_two_pow,
      `QuantumDesigns.isMaxMUBCount_two_pow, `QuantumDesigns.isMaxMUBCount_prime_pow,
      `QuantumDesigns.hasCompleteMUBs_iff_isMaxMUBCount, `QuantumDesigns.isMaxMUBCount_two,
      `QuantumDesigns.isMaxMUBCount_four, `QuantumDesigns.isMaxMUBCount_eight,
      `QuantumDesigns.gerzon_bound, `QuantumDesigns.gerzon_sharp,
      `QuantumDesigns.gerzon_equality, `QuantumDesigns.gerzon_frame,
      `QuantumDesigns.isSICFamily_frame, `QuantumDesigns.hasSICPOVM_iff_equiangular,
      `QuantumDesigns.card_le_of_sicOverlapSq, `QuantumDesigns.hasSICPOVM_two,
      `QuantumDesigns.hasSICPOVM_three, `QuantumDesigns.hasSICPOVM_eight] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
