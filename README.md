# Finite quantum designs: mutually unbiased bases in every prime-power dimension, Weiner's gap, reconstruction from complete sets and SIC families, the Welch and Gerzon bounds, and SIC-POVMs in dimensions 2, 3, 4 and 8

Two structures of finite-dimensional quantum information, in the vocabulary of the formal-conjectures repository
(google-deepmind/formal-conjectures, Open Quantum Problems 13 and 23; Apache-2.0, restated character for character,
see [NOTICE](NOTICE)). A basis of `ℂ^d` is a unitary matrix whose columns are the basis vectors; two bases `U`, `V` are
*mutually unbiased* when every entry of `U†V` has squared norm `1/d`; `HasMUBs d k` says `k` pairwise unbiased bases
exist, `IsMaxMUBCount d k` that `k` is the largest such number. A SIC family in `ℂ^d` is `d²` unit vectors with
pairwise squared overlap `1/(d + 1)`; `HasSICPOVM d` says one exists (Zauner's conjecture: for every `d`).

[Challenge.lean](Challenge.lean) restates the fourteen definitions and states forty-six theorems;
[Solution.lean](Solution.lean) proves them, kernel-only; the table in [VERIFICATION.md](VERIFICATION.md) names each:

- **the bound:** for `d ≥ 2`, `HasMUBs d m → m ≤ d + 1` (Wootters–Fields 1989; Bandyopadhyay–Boykin–Roychowdhury–Vatan
  2002, Theorem 3.5: the identity and the `m(d − 1)` traceless combinations of the projectors are pairwise orthogonal in
  the `d²`-dimensional matrix space); the hypothesis is sharp: in dimension `1` every two bases are unbiased;
- **restriction and the tensor bound:** `HasMUBs m k → HasMUBs n k → HasMUBs (mn) k` (Klappenecker–Rötteler 2004,
  Lemma 3; XC0R's `hasMUBs_mul`, adapted), and its corollary over the factorization: `HasMUBs d k` whenever `k ≤ q + 1`
  for every exact prime-power divisor `q` of `d`; hence `HasMUBs d 3` for every `d ≥ 2` (also proved directly, by the
  Fourier basis and a chirped Fourier basis, in `QuantumDesigns/Chirp.lean`);
- **complete sets in every prime-power dimension:** for a finite field `F` of odd characteristic and size `q`, the
  standard basis and the `q` bases with entries `ψ(a x² + b x)/√q` (`ψ` a nontrivial additive character; `a` the basis,
  `b` the column, `x` the row) are `q + 1` mutually unbiased bases (Wootters–Fields 1989; Klappenecker–Rötteler 2004,
  Theorem 2), through the identity `‖Σ_x ψ(c x² + e x)‖² = q` for `c ≠ 0` (Weyl differencing; no Gauss sums); for
  `q = 2ⁿ`, the bases with entries `i^{xᵀS_a x}(−1)^{b·x}/√q` (`x`, `b` and `S_a` lifted to `{0, 1}`), `S_a` the Gram matrix of the trace form
  `(x, y) ↦ Tr(a x y)` of `𝔽_{2ⁿ}` (equivalent to the Galois-ring bases of Klappenecker–Rötteler Theorem 3); so
  `IsMaxMUBCount (pᵏ) (pᵏ + 1)` for every prime power, and `HasCompleteMUBs d ↔ IsMaxMUBCount d (d + 1)` for
  `d ≥ 2`; `μ(2) = 3`, `μ(4) = 5`, `μ(8) = 9` also by explicit kernel-checked tables;
- **Weiner's gap:** any `d` mutually unbiased bases of `ℂ^d` extend, by one more basis, to a complete set, the given
  bases keeping their places (Weiner 2013, Corollary 3.4), so `HasMUBs d d → HasCompleteMUBs d`, for every `d`; by the
  paper's route with its operator-algebra steps written out: Weiner's projection onto the matrices with a constant
  diagonal in every basis has a Kraus form (his Lemma 3.2), the Kadison–Schwarz defect of a Kraus map is a sum of
  squares, so the flat fixed points commute with the Kraus operators, and a common eigenbasis of the commuting family
  is the missing basis; hence `k ≥ d` bases complete to `d + 1`, and for `d ≥ 2` the maximal number `μ(d)` is never
  `d`: it is `d + 1` or below `d` (the paper's dichotomy); `μ(6) ≠ 6`;
- **the maximal number:** for `d ≥ 2`, `μ(d)` exists, is unique and lies in `[3, d + 1]`; dimension `1` has none; two
  bases exist in every dimension; for a prime power `q`, `HasMUBs q m ↔ m ≤ q + 1`; formal-conjectures'
  `mutuallyUnbiasedBases_dim6_bounds` (`3 ≤ μ(6) ≤ 7`, left with `sorry` there) is proved verbatim;
- **Gerzon's bound over `ℂ`:** `N` unit vectors of `ℂ^d` with the same squared overlap `c ≠ 1` on every pair have
  `N ≤ d²` (the absolute bound of Delsarte–Goethals–Seidel 1975, not read, as stated in Roy's thesis, Corollary 3.3.2; the complex form of Gerzon's real bound); sharp: with
  `c = 1` the family may be any length (`d ≥ 1`);
- **the equality case:** for `d ≥ 2`, `d²` such vectors have `c = 1/(d + 1)` and resolve the identity,
  `Σ_i (1/d)|φ_i⟩⟨φ_i| = 1`; so every SIC family is a POVM (Renes–Blume-Kohout–Scott–Caves 2004, §II), `HasSICPOVM d`
  holds iff `ℂ^d` has `d²` unit vectors with one squared overlap `c ≠ 1`, and a family at the SIC angle has at most `d²`
  members;
- **Welch's bound:** `N` unit vectors of `ℂ^d` have `Σ_{i,j} |⟨φ_i, φ_j⟩|² ≥ N²/d` (Cauchy–Schwarz for the identity and
  the frame operator); so `N ≥ 2` of them with one squared overlap `c` have `c ≥ (N − d)/(d(N − 1))`; with every squared
  overlap at most `α` and `α d < 1`, `N (1 − α d) ≤ d (1 − α)`; and at most `d²` have every squared overlap at most
  `1/(d + 1)` (Welch 1974, closed access and not read, as stated by Datta–Howard–Cochran, eq. (2) with `k = 1`, and by
  Mixon–Needham–Shonkwiler–Villar, Proposition 1; the double sum is the frame potential of Benedetto–Fickus 2003);
- **reconstruction:** with `P` the rank-one projectors, a complete set of `d + 1` mutually unbiased bases determines
  every matrix, `X = Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1`, and so does a SIC family,
  `X = Σ_i ((d + 1) Tr(X P_i) − Tr X)/d · P_i` (the coefficients as printed in Scott 2006, eq. (9); the informational
  completeness of SICs is Renes et al. 2004, §II; the MUB formula goes back to Ivanović 1981 and Wootters–Fields 1989,
  not read here);
- **SIC-POVMs in dimensions 2, 3 and 8:** the tetrahedron and the Hesse configuration (formal-conjectures' witness
  families, whose `hasSICPOVM_two` and `hasSICPOVM_three` are left with `sorry` there), and Hoggar's 64 lines: the orbit
  of `(−1 + 2i, 1, 1, 1, 1, 1, 1, 1)/√12` under the three-qubit Pauli group (Jedwab–Wiebe 2015, Example 4; equivalent to
  Hoggar's lines), kernel-checked over all ordered pairs;
- **the SIC-POVM in dimension 4:** the sixteen Weyl–Heisenberg translates of Appleby's exact fiducial (Appleby 2005, §8,
  eq. (149), which credits Zauner 1999 and Renes et al. 2004),
  `ψ = √((5 − √5)/40) (2 cos(π/8), i(e^{−iπ/8} + √(2 + √5) e^{iπ/8}), 2i sin(π/8), i(e^{−iπ/8} − √(2 + √5) e^{iπ/8}))`;
  covariance reduces the 240 overlaps to fifteen, proved by exact trigonometric and radical identities (only the index
  arithmetic is kernel-checked).

Not claimed: anything about dimension six beyond `3 ≤ μ(6) ≤ 7` and `μ(6) ≠ 6`; SICs in dimensions 5–7; any first
formalization. In dimension six openai/math goes further, in its own vocabulary: its `N6_le_five` (`μ(6) ≤ 5`) implies
`μ(6) ≠ 6` and `μ(6) ≤ 7`, and its `six_extend_to_seven` is the extension form of Weiner's gap at `d = 6`. The
general-`n` lemmas of its `lean/OAI/Analysis/MutuallyUnbiased/Completion` (commit `adc7f1241b`, 2026-10-06) make the same
elementary move as the route here: the Kadison–Schwarz defect of a Kraus map as squared Hilbert–Schmidt norms of
commutators (`commutator_trace_identity`, `commute_of_kraus_fixed` in `Completion/Kraus.lean`), a joint eigenbasis
(`exists_joint_projection_basis`), fixed rank-one projectors (`exists_fixed_projection_basis`). Those files were read
after the route here was pinned; this repository takes the step in formal-conjectures' vocabulary and for every `d`. The
Kadison–Schwarz inequality for completely positive and Kraus maps is in physlib, Lean-QIT and kencyke/quantum-system;
the-omega-institute/trureturing proves the injectivity of the diagonal map of a complete family (in its vocabulary of
rank-one contexts) and a density-matrix reconstruction under an assumed completeness hypothesis, and kernel-checks the
same 64 Hoggar vectors and the Hesse SIC; the dimension-2 MUB case is formal-conjectures' `mutuallyUnbiasedBases_dim2`,
the dimension-6 projector argument and the Kronecker lemma are XC0R's, and the dimension-2 and 3 SIC overlaps are in
zblore/csd-lean4.

## Verifying

Lean `v4.35.0-rc2` with Mathlib at the same tag (pinned by `lake-manifest.json`). `python scripts/verify.py` runs the
pins, the source guard, the definition and statement checks, the standard-library replay of the constructions
(`scripts/check_designs.py`), the metadata check, the build with the axiom audit (`Test/Axioms.lean` rejects any axiom
beyond `propext`, `Classical.choice`, `Quot.sound`), the module-resolution check, the `pp.all` elaboration check of the
definitions and Palomar's core-notation audit, and ends with `VERIFY: PASS`. [PROOF.md](PROOF.md) gives the proofs
with the Lean names; [DISCLOSURE.md](DISCLOSURE.md) says how the repository was made.

License: [MIT](LICENSE) for the Lean files and scripts; the fourteen definitions and the lemmas listed in [NOTICE](NOTICE)
derive from formal-conjectures under Apache-2.0 ([LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt));
`scripts/core_notation_audit.lean` is Palomar's, under its MIT licence ([LICENSES/PalomarSubmission-MIT.txt](LICENSES/PalomarSubmission-MIT.txt)).
