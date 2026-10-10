# Verification

All twenty-six statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
definition and statement checks, the standard-library replay of every construction, the metadata check, the
module-resolution check, the elaboration check and Palomar's core-notation audit of the statements pass;
`python scripts/verify.py` runs them all and ends with `VERIFY: PASS`. The checks below were last run on the tree of the
final commit (the counts are printed by verify.py); a build log is evidence for that tree only. Theorems are numbered
as in `comparator.json`, which is also their order in Challenge.lean. `comparator.json` lists no `definition_names`: a
name there is a definition hole whose value the Solution supplies; the fourteen definitions here are fully specified in
the Challenge (formal-conjectures' own, restated), so the comparator checks the Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `hasMUBs_le` — for d ≥ 2, HasMUBs d m → m ≤ d + 1 | QuantumDesigns/Bound.lean |
| 2 | `hasMUBs_one_dim` — HasMUBs 1 m for every m (the hypothesis d ≥ 2 is sharp) | QuantumDesigns/Bound.lean |
| 3 | `hasMUBs_of_le` — restriction to a subfamily | QuantumDesigns/Bound.lean |
| 4 | `hasMUBs_mul` — the tensor bound HasMUBs m k → HasMUBs n k → HasMUBs (m n) k | QuantumDesigns/Tensor.lean |
| 5 | `hasMUBs_of_forall_primePow` — HasMUBs d k when k ≤ q + 1 for every exact prime-power divisor q of d | QuantumDesigns/Tensor.lean |
| 6 | `hasMUBs_three` — HasMUBs d 3 for d ≥ 2 | QuantumDesigns/Tensor.lean |
| 7 | `quadSum_normSq` — ‖Σ_x ψ(c x² + e x)‖² = \|F\| for c ≠ 0, odd characteristic | QuantumDesigns/OddField.lean |
| 8 | `hasCompleteMUBs_of_odd_char` — q + 1 mutually unbiased bases of ℂ^q for an odd-characteristic field of size q | QuantumDesigns/OddField.lean |
| 9 | `isMaxMUBCount_odd_prime_pow` — μ(pᵏ) = pᵏ + 1 for odd p | QuantumDesigns/Main.lean |
| 10 | `hasCompleteMUBs_two_pow` — 2ⁿ + 1 mutually unbiased bases of ℂ^{2ⁿ}, n ≥ 1 | QuantumDesigns/TwoPow.lean |
| 11 | `isMaxMUBCount_two_pow` — μ(2ⁿ) = 2ⁿ + 1 | QuantumDesigns/Main.lean |
| 12 | `isMaxMUBCount_prime_pow` — μ(pᵏ) = pᵏ + 1 for every prime power | QuantumDesigns/Main.lean |
| 13 | `hasCompleteMUBs_iff_isMaxMUBCount` — for d ≥ 2, HasCompleteMUBs d ↔ IsMaxMUBCount d (d + 1) | QuantumDesigns/Main.lean |
| 14 | `isMaxMUBCount_two` — μ(2) = 3 | QuantumDesigns/Main.lean |
| 15 | `isMaxMUBCount_four` — μ(4) = 5 | QuantumDesigns/Main.lean |
| 16 | `isMaxMUBCount_eight` — μ(8) = 9 | QuantumDesigns/Main.lean |
| 17 | `gerzon_bound` — N unit vectors with the same squared overlap c ≠ 1 have N ≤ d² | QuantumDesigns/Gerzon.lean |
| 18 | `gerzon_sharp` — with c = 1 the family may be any length (d ≥ 1) | QuantumDesigns/Gerzon.lean |
| 19 | `gerzon_equality` — for d ≥ 2, d² such vectors have c = 1/(d + 1) | QuantumDesigns/Gerzon.lean |
| 20 | `gerzon_frame` — and resolve the identity, Σ_i (1/d)\|φ_i⟩⟨φ_i\| = 1 | QuantumDesigns/Gerzon.lean |
| 21 | `isSICFamily_frame` — every SIC family is a POVM | QuantumDesigns/Gerzon.lean |
| 22 | `hasSICPOVM_iff_equiangular` — for d ≥ 2, HasSICPOVM d ↔ d² equiangular unit vectors exist | QuantumDesigns/Gerzon.lean |
| 23 | `card_le_of_sicOverlapSq` — a family at the SIC angle has at most d² members | QuantumDesigns/Gerzon.lean |
| 24 | `hasSICPOVM_two` — the tetrahedron | QuantumDesigns/SIC.lean |
| 25 | `hasSICPOVM_three` — the Hesse configuration | QuantumDesigns/SIC.lean |
| 26 | `hasSICPOVM_eight` — Hoggar's 64 lines | QuantumDesigns/SIC.lean |

`QuantumDesigns/Small.lean` holds the explicit complete sets in dimensions 2, 4 and 8 (`hasMUBs_two_three`,
`hasMUBs_four_five`, `hasMUBs_eight_nine`, kernel-checked tables in `QuantumDesigns/SmallTables.lean`), used by 14–16;
`QuantumDesigns/Chirp.lean` proves `hasMUBs_three_chirp`, a second, field-free proof of 6 (the Fourier and chirped
Fourier bases); `QuantumDesigns/PrimePow.lean` assembles 8 and 10 into `hasCompleteMUBs_prime_pow_internal`.

## Checks

- **Pins:** `lean-toolchain` is `leanprover/lean4:v4.35.0-rc2`; `lake-manifest.json` pins Mathlib to
  `065356127b1dc0016f66b7283ce0ce2c4055aa55` (tag `v4.35.0-rc2`); `lake update` is never run.
- **Source guard** (`scripts/check-source.py`): no `sorry`, `native_decide`, `axiom`, `unsafe`, `partial`,
  `implemented_by`, `extern`, `mutual`, `opaque`, kernel-bypass options.
- **Definitions** (`scripts/check_definitions.py`): the definition blocks of Challenge.lean and QuantumDesigns/Defs.lean
  agree character for character, with the same import; the elaboration check prints each with `pp.all` from both
  modules and compares.
- **Statements** (`scripts/check_statements.py`): every theorem header of Challenge.lean appears verbatim in
  Solution.lean, which does not import Challenge.
- **Replay** (`scripts/check_designs.py`, standard library, exact arithmetic): the odd-characteristic bases for
  q ≤ 27, the ℤ/4 bases for 2ⁿ ≤ 16 with every difference of Gram matrices nonsingular, Hoggar's 64 vectors (4096
  ordered pairs) with the frame identity, the tetrahedron and the Hesse configuration; `VERDICT: PASS`.
- **Build and axioms:** `lake build` of every target; `Test/Axioms.lean` walks every constant of the project and every
  compared theorem and fails on any axiom beyond `propext`, `Classical.choice`, `Quot.sound`.
- **Module resolution** (`scripts/check_module_resolution.py`): `Challenge` and `Solution` resolve to this repository's
  files first in Lake's source path.
- **Core-notation audit** (`scripts/core_notation_audit.lean`, Palomar's): the 26 theorems and 14 definitions print
  with Mathlib's definitions as opaque axioms (40 rows).
