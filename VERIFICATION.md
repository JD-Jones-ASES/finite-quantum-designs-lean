# Verification

All sixty statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
definition and statement checks, the standard-library replay of the constructions behind the compared statements, the metadata check, the
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
| 7 | `quadSum_normSq` — ‖Σ_x ψ(c x² + e x)‖² = \|F\| for c ≠ 0, ψ ≠ 1, odd characteristic | QuantumDesigns/OddField.lean |
| 8 | `hasCompleteMUBs_of_odd_char` — q + 1 mutually unbiased bases of ℂ^q for an odd-characteristic field of size q | QuantumDesigns/OddField.lean |
| 9 | `isMaxMUBCount_odd_prime_pow` — μ(pᵏ) = pᵏ + 1 for odd p, k ≥ 1 | QuantumDesigns/Main.lean |
| 10 | `hasCompleteMUBs_two_pow` — 2ⁿ + 1 mutually unbiased bases of ℂ^{2ⁿ}, n ≥ 1 | QuantumDesigns/TwoPow.lean |
| 11 | `isMaxMUBCount_two_pow` — μ(2ⁿ) = 2ⁿ + 1, n ≥ 1 | QuantumDesigns/Main.lean |
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
| 22 | `hasSICPOVM_iff_equiangular` — for d ≥ 2, HasSICPOVM d ↔ d² unit vectors with one squared overlap c ≠ 1 exist | QuantumDesigns/Gerzon.lean |
| 23 | `card_le_of_sicOverlapSq` — a family at the SIC angle has at most d² members | QuantumDesigns/Gerzon.lean |
| 24 | `hasSICPOVM_two` — the tetrahedron | QuantumDesigns/SIC.lean |
| 25 | `hasSICPOVM_three` — the Hesse configuration | QuantumDesigns/SIC.lean |
| 26 | `hasSICPOVM_eight` — Hoggar's 64 lines | QuantumDesigns/SIC.lean |
| 27 | `hasCompleteMUBs_of_hasMUBs_self` — Weiner's gap: HasMUBs d d → HasCompleteMUBs d, for every d | QuantumDesigns/GapMain.lean |
| 28 | `exists_isMUBFamily_extension` — the extension form: d mutually unbiased bases B of ℂ^d extend to d + 1 bases C with C (r + 1) = B r | QuantumDesigns/GapMain.lean |
| 29 | `hasCompleteMUBs_of_le_hasMUBs` — for d ≤ k, HasMUBs d k → HasCompleteMUBs d | QuantumDesigns/GapMain.lean |
| 30 | `isMaxMUBCount_ne_self` — for d ≥ 2, ¬ IsMaxMUBCount d d | QuantumDesigns/GapMain.lean |
| 31 | `isMaxMUBCount_dichotomy` — for d ≥ 2, IsMaxMUBCount d k → k = d + 1 ∨ k < d | QuantumDesigns/GapMain.lean |
| 32 | `hasMUBs_two` — HasMUBs d 2 for every d | QuantumDesigns/Count.lean |
| 33 | `hasMUBs_prime_pow_iff` — for p prime and k ≥ 1, HasMUBs (pᵏ) m ↔ m ≤ pᵏ + 1 | QuantumDesigns/Count.lean |
| 34 | `isMaxMUBCount_unique` — IsMaxMUBCount d k → IsMaxMUBCount d l → k = l | QuantumDesigns/Count.lean |
| 35 | `exists_isMaxMUBCount` — for d ≥ 2, IsMaxMUBCount d k for some k | QuantumDesigns/Count.lean |
| 36 | `not_exists_isMaxMUBCount_one` — no k has IsMaxMUBCount 1 k | QuantumDesigns/Count.lean |
| 37 | `isMaxMUBCount_bounds` — for d ≥ 2, IsMaxMUBCount d k → 3 ≤ k ≤ d + 1 | QuantumDesigns/Count.lean |
| 38 | `mutuallyUnbiasedBases_dim6_bounds` — HasMUBs 6 3, and HasMUBs 6 m → m ≤ 7 (formal-conjectures' statement) | QuantumDesigns/Count.lean |
| 39 | `not_isMaxMUBCount_six_six` — ¬ IsMaxMUBCount 6 6 | QuantumDesigns/GapMain.lean |
| 40 | `mub_reconstruction` — d + 1 mutually unbiased bases: X = Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1 for every matrix X | QuantumDesigns/Reconstruct.lean |
| 41 | `sic_reconstruction` — a SIC family: X = Σ_i ((d + 1) Tr(X P_i) − Tr X)/d · P_i for every matrix X | QuantumDesigns/Reconstruct.lean |
| 42 | `welch_bound` — N unit vectors have Σ_{i,j} \|⟨φ_i, φ_j⟩\|² ≥ N²/d | QuantumDesigns/Welch.lean |
| 43 | `welch_bound_of_constantOverlap` — N ≥ 2 unit vectors with one squared overlap c have c ≥ (N − d)/(d(N − 1)) | QuantumDesigns/Welch.lean |
| 44 | `welch_card_bound` — N unit vectors with every pairwise squared overlap at most α, α d < 1, have N (1 − α d) ≤ d (1 − α) | QuantumDesigns/Welch.lean |
| 45 | `card_le_of_overlapSq_le_sic` — N unit vectors with every pairwise squared overlap at most 1/(d + 1) have N ≤ d² | QuantumDesigns/Welch.lean |
| 46 | `hasSICPOVM_four` — the Weyl–Heisenberg orbit of Appleby's fiducial | QuantumDesigns/SIC4.lean |
| 47 | `mub_second_moment` — for all X, Y, Σ_{s,l} Tr(X P_{s,l}) Tr(Y P_{s,l}) = Tr(XY) + Tr X Tr Y (a complete set is a 2-design) | QuantumDesigns/Tomography.lean |
| 48 | `sic_second_moment` — (d + 1) Σ_i Tr(X P_i) Tr(Y P_i) = d (Tr(XY) + Tr X Tr Y) (a SIC family is a 2-design) | QuantumDesigns/Tomography.lean |
| 49 | `mub_hilbert_schmidt` — Σ_{s,l} \|Tr(X P_{s,l})\|² = ‖X‖²_HS + \|Tr X\|² | QuantumDesigns/Tomography.lean |
| 50 | `sic_hilbert_schmidt` — d(d + 1) Σ_i \|Tr(X P_i)/d\|² = ‖X‖²_HS + \|Tr X\|² | QuantumDesigns/Tomography.lean |
| 51 | `mub_tomography_distance` — for Tr X = Tr Y, Σ_{s,l} \|Tr(X P_{s,l}) − Tr(Y P_{s,l})\|² = ‖X − Y‖²_HS | QuantumDesigns/Tomography.lean |
| 52 | `sic_tomography_distance` — for Tr X = Tr Y, d(d + 1) Σ_i \|(Tr(X P_i) − Tr(Y P_i))/d\|² = ‖X − Y‖²_HS | QuantumDesigns/Tomography.lean |
| 53 | `mub_tomography_purity` — for Hermitian ρ with Tr ρ = 1, Σ_{s,l} \|Tr(ρ P_{s,l})\|² = Tr(ρ²) + 1 | QuantumDesigns/Tomography.lean |
| 54 | `sic_tomography_purity` — for Hermitian ρ with Tr ρ = 1, d(d + 1) Σ_i \|Tr(ρ P_i)/d\|² = Tr(ρ²) + 1 | QuantumDesigns/Tomography.lean |
| 55 | `welch_deficit` — Σ_{i,j} \|⟨φ_i, φ_j⟩\|² − N²/d = ‖S − (N/d)·1‖²_HS for S = Σ_i \|φ_i⟩⟨φ_i\| | QuantumDesigns/WelchEquality.lean |
| 56 | `welch_equality_iff_tight` — equality in Welch's bound iff S = (N/d)·1 | QuantumDesigns/WelchEquality.lean |
| 57 | `welch_relative_equality` — at N (1 − α d) = d (1 − α), every pairwise squared overlap is α and S = (N/d)·1 | QuantumDesigns/WelchEquality.lean |
| 58 | `isSICFamily_of_overlapSq_le` — d² unit vectors with every pairwise squared overlap at most 1/(d + 1) are a SIC family | QuantumDesigns/WelchEquality.lean |
| 59 | `hasSICPOVM_iff_overlapSq_le` — HasSICPOVM d iff d² unit vectors with every pairwise squared overlap at most 1/(d + 1) exist | QuantumDesigns/WelchEquality.lean |
| 60 | `frame_defect_le_of_overlapSq_le` — for d ≥ 1, d² unit vectors with pairwise squared overlaps at most 1/(d + 1) + ε have ‖S/d − 1‖²_HS ≤ (d² − 1) ε | QuantumDesigns/WelchEquality.lean |

`QuantumDesigns/Small.lean` holds the explicit complete sets in dimensions 2, 4 and 8 (`hasMUBs_two_three`,
`hasMUBs_four_five`, `hasMUBs_eight_nine`, kernel-checked tables in `QuantumDesigns/SmallTables.lean`), used by 14–16;
`QuantumDesigns/Chirp.lean` proves `hasMUBs_three_chirp`, a second, field-free proof of 6 (the Fourier and chirped
Fourier bases); `QuantumDesigns/PrimePow.lean` assembles 8 and 10 into `hasCompleteMUBs_prime_pow_internal`.
`QuantumDesigns/GapCore.lean`, `GapPhi.lean`, `GapKraus.lean`, `GapDFT.lean`, `GapSchwarz.lean` and `GapDiag.lean` hold
the steps of 27 and 28 (PROOF.md §10); `QuantumDesigns/SIC4Tables.lean` holds the kernel-checked index arithmetic of 46;
`QuantumDesigns/Tomography.lean` derives 47–54 from the reconstruction formulas (§15) and `QuantumDesigns/WelchEquality.lean`
55–60 from Welch's deficit (§16).

## Checks

- **Pins:** `lean-toolchain` is `leanprover/lean4:v4.35.0-rc2`; `lake-manifest.json` pins Mathlib to
  `065356127b1dc0016f66b7283ce0ce2c4055aa55` (tag `v4.35.0-rc2`); `lake update` is never run.
- **Source guard** (`scripts/check-source.py`): no `sorry`, `native_decide`, `axiom`, `unsafe`, `partial`,
  `implemented_by`, `extern`, `mutual`, `opaque`, kernel-bypass options.
- **Definitions** (`scripts/check_definitions.py`): the definition blocks of Challenge.lean and QuantumDesigns/Defs.lean
  agree character for character, with the same import; the elaboration check prints each with `pp.all` from both
  modules and compares.
- **Statements** (`scripts/check_statements.py`): every theorem header of Challenge.lean appears verbatim in
  Solution.lean, which does not import Challenge; Solution.lean, comparator.json and the list in Test/Axioms.lean are
  generated from Challenge.lean by `scripts/gen_solution.py`.
- **Replay** (`scripts/check_designs.py`, standard library, exact arithmetic): the odd-characteristic bases for
  q ∈ {3, 5, 7, 9, 11, 13, 25, 27}, the ℤ/4 bases for 2ⁿ ≤ 16 with every difference of Gram matrices nonsingular, Hoggar's 64 vectors (4096
  ordered pairs) with the frame identity, the tetrahedron, the Hesse configuration, and Appleby's dimension-4 fiducial
  as printed (eq. (149)) with its sixteen translates, in the ring ℚ[c, q, i] (all 16 norms and 120 pairs; a float
  check outside the verdict); `VERDICT: PASS`.
- **Build and axioms:** `lake build` of every target; `Test/Axioms.lean` walks every constant of the project and every
  compared theorem and fails on any axiom beyond `propext`, `Classical.choice`, `Quot.sound` (518 project constants, no other axiom).
- **Module resolution** (`scripts/check_module_resolution.py`): `Challenge` and `Solution` resolve to this repository's
  files first in Lake's source path.
- **Core-notation audit** (`scripts/core_notation_audit.lean`, Palomar's): the 60 theorems and 14 definitions print
  with Mathlib's definitions as opaque axioms (74 rows).
- **Abbreviated run:** `--skip-build` leaves out the four Lean steps, lists them, and ends with
  `VERIFY (source/replay only)`; it does not check the proofs.
