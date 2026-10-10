# Finite quantum designs: mutually unbiased bases and SIC-POVMs in every prime-power and small dimension

Two structures of finite-dimensional quantum information, in the vocabulary of the formal-conjectures repository
(google-deepmind/formal-conjectures, Open Quantum Problems 13 and 23; Apache-2.0, restated character for character,
see [NOTICE](NOTICE)). A basis of `ℂ^d` is a unitary matrix whose columns are the basis vectors; two bases `U`, `V` are
*mutually unbiased* when every entry of `U†V` has squared norm `1/d`; `HasMUBs d k` says `k` pairwise unbiased bases
exist, `IsMaxMUBCount d k` that `k` is the largest such number. A SIC family in `ℂ^d` is `d²` unit vectors with
pairwise squared overlap `1/(d + 1)`; `HasSICPOVM d` says one exists (Zauner's conjecture: for every `d`).

[Challenge.lean](Challenge.lean) restates the fourteen definitions and states twenty-six theorems;
[Solution.lean](Solution.lean) proves them, kernel-only; the table in [VERIFICATION.md](VERIFICATION.md) names each:

- **the bound:** for `d ≥ 2`, `HasMUBs d m → m ≤ d + 1` (Wootters–Fields 1989; Bandyopadhyay–Boykin–Roychowdhury–Vatan
  2002, Theorem 3.5: the identity and the `m(d − 1)` traceless combinations of the projectors are pairwise orthogonal in
  the `d²`-dimensional matrix space); the hypothesis is sharp: in dimension `1` every two bases are unbiased;
- **restriction and the tensor bound:** `HasMUBs m k → HasMUBs n k → HasMUBs (mn) k` (Klappenecker–Rötteler 2004,
  Lemma 3; XC0R's `hasMUBs_mul`, adapted), and its corollary over the factorization: `HasMUBs d k` whenever `k ≤ q + 1`
  for every exact prime-power divisor `q` of `d`; hence `HasMUBs d 3` for every `d ≥ 2`;
- **complete sets in every prime-power dimension:** for a finite field `F` of odd characteristic and size `q`, the
  standard basis and the `q` bases with entries `ψ(a x² + b x)/√q` (`ψ` a nontrivial additive character; `a` the basis,
  `b` the column, `x` the row) are `q + 1` mutually unbiased bases (Wootters–Fields 1989; Klappenecker–Rötteler 2004,
  Theorem 2), through the identity `‖Σ_x ψ(c x² + e x)‖² = q` for `c ≠ 0` (Weyl differencing; no Gauss sums); for
  `q = 2ⁿ`, the bases with entries `i^{xᵀS_a x}(−1)^{b·x}/√q`, `S_a` the `{0, 1}`-lifted Gram matrix of the trace form
  `(x, y) ↦ Tr(a x y)` of `𝔽_{2ⁿ}` (equivalent to the Galois-ring bases of Klappenecker–Rötteler Theorem 3); so
  `IsMaxMUBCount (pᵏ) (pᵏ + 1)` for every prime power, and `HasCompleteMUBs d ↔ IsMaxMUBCount d (d + 1)` for
  `d ≥ 2`; `μ(2) = 3`, `μ(4) = 5`, `μ(8) = 9` also by explicit kernel-checked tables;
- **Gerzon's bound over `ℂ`:** `N` unit vectors of `ℂ^d` with the same squared overlap `c ≠ 1` on every pair have
  `N ≤ d²` (the absolute bound of Delsarte–Goethals–Seidel 1975, the complex form of Gerzon's real bound); sharp: with
  `c = 1` the family may be any length;
- **the equality case:** for `d ≥ 2`, `d²` such vectors have `c = 1/(d + 1)` and resolve the identity,
  `Σ_i (1/d)|φ_i⟩⟨φ_i| = 1`; so every SIC family is a POVM (Renes–Blume-Kohout–Scott–Caves 2004, §II), `HasSICPOVM d`
  holds iff `ℂ^d` has `d²` equiangular unit vectors, and a family at the SIC angle has at most `d²` members;
- **SIC-POVMs in dimensions 2, 3 and 8:** the tetrahedron and the Hesse configuration (formal-conjectures' witness
  families, whose `hasSICPOVM_two` and `hasSICPOVM_three` are left with `sorry` there), and Hoggar's 64 lines: the orbit
  of `(−1 + 2i, 1, 1, 1, 1, 1, 1, 1)/√12` under the three-qubit Pauli group (Jedwab–Wiebe 2015, Example 4; equivalent to
  Hoggar's lines), kernel-checked over all ordered pairs.

Not claimed: anything about dimension six (the general bound gives `μ(6) ≤ 7`; openai/math holds `μ(6) ≤ 5` in Lean);
Weiner's completion gap; SICs in dimensions 4–7; any first formalization — the dimension-2 MUB case is
formal-conjectures' `mutuallyUnbiasedBases_dim2`, the dimension-6 projector argument and the Kronecker lemma are XC0R's,
the dimension-2 and 3 SIC overlaps are in zblore/csd-lean4, and the-omega-institute/trureturing kernel-checks the same
64 Hoggar vectors and the Hesse SIC in its own vocabulary.

## Verifying

Lean `v4.35.0-rc2` with Mathlib at the same tag (pinned by `lake-manifest.json`). `python scripts/verify.py` runs the
pins, the source guard, the definition and statement checks, the standard-library replay of every construction
(`scripts/check_designs.py`), the metadata check, the build with the axiom audit (`Test/Axioms.lean` rejects any axiom
beyond `propext`, `Classical.choice`, `Quot.sound`), the module-resolution check, the `pp.all` elaboration check of the
definitions and Palomar's core-notation audit, and ends with `VERIFY: PASS`. [PROOF.md](PROOF.md) gives the proofs
with the Lean names; [DISCLOSURE.md](DISCLOSURE.md) says how the repository was made.
