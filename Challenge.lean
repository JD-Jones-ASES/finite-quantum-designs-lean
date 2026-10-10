module

public import Mathlib

/-!
# Finite quantum designs: mutually unbiased bases in every prime-power dimension, Weiner's gap, reconstruction from complete sets and SIC families, the Welch and Gerzon bounds, and SIC-POVMs in dimensions 2, 3, 4 and 8

Two structures of finite-dimensional quantum information, stated in the vocabulary of the
formal-conjectures repository (google-deepmind/formal-conjectures, Apache-2.0; its Open Quantum Problems 13 and
23), whose definitions are restated here character for character (see NOTICE).

**Mutually unbiased bases.** An orthonormal basis of `ℂ^d` is a unitary matrix whose columns are the basis
vectors; two bases `U`, `V` are *unbiased* when every entry of `U†V` has squared norm `1/d`; `HasMUBs d k` says
that `k` pairwise unbiased bases exist in `ℂ^d`, `HasCompleteMUBs d` that `d + 1` do, and `IsMaxMUBCount d k` that
`k` is the largest such number (written `μ(d) = k`). This file states, and `Solution.lean` proves (kernel-only):

* the bound: for `d ≥ 2`, `HasMUBs d m → m ≤ d + 1` (the `d² − 1`-dimensional space of traceless matrices
  holds the `m(d − 1)` pairwise orthogonal traceless projector combinations; Wootters–Fields 1989;
  Bandyopadhyay–Boykin–Roychowdhury–Vatan 2002, Theorem 3.5; the argument of XC0R's formalization of the case `d = 6`); the hypothesis is sharp: in
  dimension `1` every two bases are unbiased, so `HasMUBs 1 m` for every `m`;
* restriction, the tensor bound `HasMUBs m k → HasMUBs n k → HasMUBs (m n) k` (Klappenecker–Rötteler 2004,
  Lemma 3; XC0R's `hasMUBs_mul`), and its corollary over the factorization: `HasMUBs d k` whenever `k ≤ q + 1` for
  every exact prime-power divisor `q` of `d`; hence `HasMUBs d 3` for every `d ≥ 2`;
* complete sets in every prime-power dimension: for a finite field `F` of odd characteristic and size `q`, the
  standard basis and the `q` bases with entries `ψ(a x² + b x)/√q` (`ψ` a nontrivial additive character, `a` the
  basis index, `b` the column index, `x` the row) are `q + 1` mutually unbiased bases (Wootters–Fields 1989;
  Klappenecker–Rötteler 2004, Theorem 2), through the Weyl-differencing identity `‖Σ_x ψ(c x² + e x)‖² = q` for
  `c ≠ 0`; for `q = 2ⁿ`, the bases with entries `i^{xᵀS_a x}(−1)^{b·x}/√q` (`S_a` the Gram matrix of the trace form
  `(x, y) ↦ Tr(a x y)` of `𝔽_{2ⁿ}`, lifted to `{0, 1}`; equivalent to the Galois-ring bases of Klappenecker–Rötteler
  Theorem 3, up to `a ↦ a²` and a relabelling of columns); so `IsMaxMUBCount (pᵏ) (pᵏ + 1)` for every prime power, and `HasCompleteMUBs d ↔
  IsMaxMUBCount d (d + 1)` for `d ≥ 2`; the cases `2, 4, 8` also by explicit kernel-checked tables;
* Weiner's gap: for every `d`, any `d` mutually unbiased bases of `ℂ^d` extend by one more basis to a complete set
  of `d + 1`, the given bases keeping their places, so `HasMUBs d d → HasCompleteMUBs d` (Weiner 2013, Corollary
  3.4, in its extension and its existence form; the route of its proof, the operator-algebra steps written out: the
  orthogonal projection onto the matrices with a constant diagonal in every basis of the family has a Kraus form, at
  a fixed point its Kadison–Schwarz defect is a trace-zero sum of squares of commutators, and the missing basis is a
  common eigenbasis of the Kraus operators); hence `k ≥ d` bases give a complete set, for `d ≥ 2` the maximal number is never `d` (so `μ(6) ≠ 6`),
  and Weiner's dichotomy: for `d ≥ 2` it is `d + 1` or below `d`;
* the maximal number: two bases in every dimension; `HasMUBs q m ↔ m ≤ q + 1` in every prime-power dimension `q`;
  for `d ≥ 2`, `μ(d)` exists, is unique and lies in `[3, d + 1]`; in dimension `1` there is none; and
  formal-conjectures' `mutuallyUnbiasedBases_dim6_bounds`, stated verbatim: `HasMUBs 6 3 ∧ ∀ m : ℕ, HasMUBs 6 m → m ≤ 7`;
* reconstruction: a complete set determines every matrix from its diagonals,
  `X = Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1` with `P_{s,l}` the projector onto column `l` of basis `s` (after
  Ivanović 1981 and Wootters–Fields 1989, in the form of Scott 2006, eqs. (9) and (56)).

**SIC-POVMs and equiangular lines.** A SIC family in `ℂ^d` is `d²` unit vectors with pairwise squared overlap
`1/(d + 1)`; `HasSICPOVM d` says one exists (Zauner's conjecture: for every `d`). This file states, and
`Solution.lean` proves:

* Gerzon's bound over `ℂ`: `N` unit vectors in `ℂ^d` with the same squared overlap `c ≠ 1` on every pair have
  `N ≤ d²` (the rank-one projectors are linearly independent in the `d²`-dimensional matrix space;
  Delsarte–Goethals–Seidel 1975, not read, as stated in Roy's thesis, Corollary 3.3.2; the complex form of Gerzon's unpublished bound); the hypothesis is sharp: with
  `c = 1` the family may be any length;
* the equality case: for `d ≥ 2`, `d²` unit vectors with the same overlap `c ≠ 1` have `c = 1/(d + 1)`, and
  their rank-one projectors resolve the identity, `Σ_i (1/d) |φ_i⟩⟨φ_i| = 1` (so every SIC family is a POVM, and
  `HasSICPOVM d` holds iff `ℂ^d` has `d²` equiangular unit vectors); every family at the SIC angle has at most `d²`
  members;
* `HasSICPOVM 8`: Hoggar's 64 lines (Hoggar 1981, 1998), as the orbit of `(−1 + 2i, 1, 1, 1, 1, 1, 1, 1)/√12` under
  the three-qubit Pauli group (Jedwab–Wiebe 2015, Example 4), kernel-checked; `HasSICPOVM 2` (the tetrahedron) and
  `HasSICPOVM 3` (the Hesse configuration), the witness families of formal-conjectures' file;
* `HasSICPOVM 4`: the sixteen Weyl–Heisenberg translates of Appleby's exact fiducial (Appleby 2005, §8, eq. (149),
  which credits Zauner 1999 and Renes–Blume-Kohout–Scott–Caves 2004), the squared overlaps `1/5` by exact
  trigonometric and radical identities;
* reconstruction: a SIC family determines every matrix, `X = Σ_i ((d + 1) Tr(X P_i) − Tr X)/d · P_i` with
  `P_i = |φ_i⟩⟨φ_i|` (informational completeness: Renes–Blume-Kohout–Scott–Caves 2004, §II; the coefficients: Scott
  2006, eq. (9) in the proof of Theorem 4, and Appleby–Dang–Fuchs, eq. (3));
* Welch's bound in the frame-potential form: `N` unit vectors of `ℂ^d` have `Σ_{i,j} |⟨φ_i, φ_j⟩|² ≥ N²/d` (Welch
  1974, as restated by Datta–Howard–Cochran and by Mixon–Needham–Shonkwiler–Villar; the frame potential is the
  name of Benedetto–Fickus 2003); with one squared overlap `c` on every pair of `N ≥ 2` unit vectors,
  `c ≥ (N − d)/(d(N − 1))`; with every pairwise squared overlap at most `α`, where `α d < 1`, the relative bound
  `N (1 − α d) ≤ d (1 − α)`; and at most `d²` unit vectors have every pairwise squared overlap at or below the SIC
  angle `1/(d + 1)`.

Conventions: `Matrix.unitaryGroup (Fin d) ℂ` is the group of unitary `d × d` matrices (`star U * U = 1 = U * star U`);
`‖z‖` is the complex absolute value; `EuclideanSpace ℂ (Fin d)` is `ℂ^d` with the `ℓ²` norm, a vector `ψ` having
coordinates `ψ i`; `Complex.normSq z = ‖z‖²`; `Pairwise P` means `P i j` for all `i ≠ j`; `Fintype.card F` is the
size of the finite field `F`; `ringChar F` its characteristic; `AddChar F ℂ` the additive characters of `F` into
`ℂ` (unit-valued homomorphisms from `(F, +)` to `(ℂ, ×)`); `d.factorization p` the exponent of the prime `p` in `d`;
`Matrix.vecMulVec v w` the matrix `(i, j) ↦ v i * w j`, so that `|φ⟩⟨φ|` is `Matrix.vecMulVec φ (star ∘ φ)`;
`Tr X` is `Matrix.trace X`; `|⟨φ, ψ⟩|²` is `overlapSq φ ψ`.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/- ## Mutually unbiased bases (formal-conjectures, OpenQuantumProblems/13.lean) -/

/-- A unitary matrix representing an orthonormal basis of $\mathbb{C}^d$ via its columns. -/
abbrev UMat (d : ℕ) := ↥(Matrix.unitaryGroup (Fin d) ℂ)

/-- The relative unitary between two bases. -/
def relativeUnitary {d : ℕ} (U V : UMat d) : Matrix (Fin d) (Fin d) ℂ :=
  star (U : Matrix (Fin d) (Fin d) ℂ) * (V : Matrix (Fin d) (Fin d) ℂ)

/-- Two unitary matrices represent mutually unbiased bases if every entry of the relative
unitary has squared norm $1 / d$. -/
def IsUnbiased {d : ℕ} (U V : UMat d) : Prop :=
  ∀ i j : Fin d, ‖relativeUnitary U V i j‖ ^ (2 : ℕ) = (d : ℝ)⁻¹

/-- A family of unitary matrices is a family of mutually unbiased bases if every two distinct
members are unbiased. -/
def IsMUBFamily {d k : ℕ} (B : Fin k → UMat d) : Prop :=
  Pairwise fun m n => IsUnbiased (B m) (B n)

/-- There exist $k$ mutually unbiased bases in $\mathbb{C}^d$. -/
def HasMUBs (d k : ℕ) : Prop :=
  ∃ B : Fin k → UMat d, IsMUBFamily B

/-- There exists a complete set of $d + 1$ mutually unbiased bases in $\mathbb{C}^d$. -/
def HasCompleteMUBs (d : ℕ) : Prop :=
  HasMUBs d (d + 1)

/-- $k$ is the maximal size of a family of mutually unbiased bases in dimension $d$. -/
def IsMaxMUBCount (d k : ℕ) : Prop :=
  HasMUBs d k ∧ ∀ m : ℕ, HasMUBs d m → m ≤ k

/- ## SIC-POVMs (formal-conjectures, OpenQuantumProblems/23.lean) -/

/-- A state vector in the $d$-dimensional complex Hilbert space $\mathbb{C}^d$. -/
abbrev StateVector (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {d : ℕ} (ψ : StateVector d) : Prop := ‖ψ‖ = 1

/-- The squared magnitude of the overlap between two state vectors. -/
def overlapSq {d : ℕ} (φ ψ : StateVector d) : ℝ :=
  Complex.normSq (∑ i : Fin d, star (φ i) * ψ i)

/-- A family has constant pairwise squared overlap $c$ if every two distinct members have squared overlap $c$. -/
def HasConstantOverlapSq {d N : ℕ} (c : ℝ) (Φ : Fin N → StateVector d) : Prop :=
  Pairwise fun i j => overlapSq (Φ i) (Φ j) = c

/-- The squared overlap value of a SIC family in dimension $d$. -/
def sicOverlapSq (d : ℕ) : ℝ := (d + 1 : ℝ)⁻¹

/-- A SIC family in dimension $d$ consists of $d^2$ normalized vectors in $\mathbb{C}^d$ with pairwise squared overlap $(d + 1)^{-1}$. -/
def IsSICFamily (d : ℕ) (Φ : Fin (d ^ 2) → StateVector d) : Prop :=
  (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq (sicOverlapSq d) Φ

/-- There exists a SIC-POVM in dimension $d$. -/
def HasSICPOVM (d : ℕ) : Prop :=
  ∃ Φ : Fin (d ^ 2) → StateVector d, IsSICFamily d Φ

/- ## The bound and its sharpness -/

/-- The bound: in dimension `d ≥ 2` there are at most `d + 1` mutually unbiased bases
(Bandyopadhyay–Boykin–Roychowdhury–Vatan 2002, Theorem 3.5). -/
theorem hasMUBs_le (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (h : HasMUBs d m) : m ≤ d + 1 := sorry

/-- The hypothesis `d ≥ 2` is necessary: in dimension `1` every two bases are unbiased
(`‖u‖² = 1 = 1⁻¹` for a unit `u`), so there are arbitrarily many. -/
theorem hasMUBs_one_dim (m : ℕ) : HasMUBs 1 m := sorry

/-- Restriction: a subfamily of mutually unbiased bases is one. -/
theorem hasMUBs_of_le {d k l : ℕ} (hkl : k ≤ l) (h : HasMUBs d l) : HasMUBs d k := sorry

/- ## The tensor bound -/

/-- The tensor bound (Klappenecker–Rötteler 2004, Lemma 3; XC0R's `hasMUBs_mul`): Kronecker products of
`k` unbiased bases of `ℂ^m` with `k` unbiased bases of `ℂ^n` are `k` unbiased bases of `ℂ^{mn}`. -/
theorem hasMUBs_mul {m n k : ℕ} (hm : HasMUBs m k) (hn : HasMUBs n k) : HasMUBs (m * n) k := sorry

/-- The tensor bound over the factorization (Klappenecker–Rötteler 2004, Lemma 3): if `k ≤ q + 1` for every
exact prime-power divisor `q = p ^ (d.factorization p)` of `d ≥ 1`, then `ℂ^d` has `k` mutually unbiased bases
(the complete sets of the prime-power factors, restricted to `k` bases each and tensored). -/
theorem hasMUBs_of_forall_primePow (d k : ℕ) (hd : d ≠ 0)
    (h : ∀ p ∈ d.primeFactors, k ≤ p ^ d.factorization p + 1) : HasMUBs d k := sorry

/-- Every dimension `d ≥ 2` has three mutually unbiased bases. -/
theorem hasMUBs_three (d : ℕ) (hd : 2 ≤ d) : HasMUBs d 3 := sorry

/- ## Complete sets in prime-power dimension -/

/-- The quadratic-phase sum over a finite field of odd characteristic: for a nontrivial additive character `ψ`
and `c ≠ 0`, `‖Σ_x ψ(c x² + e x)‖² = |F|` (Weyl differencing: `x = y + t`, then `Σ_y ψ(2 c t y)` vanishes
unless `t = 0`). -/
theorem quadSum_normSq (F : Type) [Field F] [Fintype F] (h2 : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (c e : F) (hc : c ≠ 0) :
    ‖∑ x : F, ψ (c * x ^ 2 + e * x)‖ ^ (2 : ℕ) = Fintype.card F := sorry

/-- A finite field `F` of odd characteristic and size `q` gives `q + 1` mutually unbiased bases of `ℂ^q`
(Wootters–Fields 1989; Klappenecker–Rötteler 2004, Theorem 2): the standard basis, and for each `a ∈ F` the
basis whose column `b` has entries `ψ(a x² + b x)/√q`, `x ∈ F`. -/
theorem hasCompleteMUBs_of_odd_char (F : Type) [Field F] [Fintype F] (h2 : ringChar F ≠ 2) :
    HasCompleteMUBs (Fintype.card F) := sorry

/-- `q + 1` is the maximal number of mutually unbiased bases in every odd prime-power dimension `q = pᵏ`. -/
theorem isMaxMUBCount_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    IsMaxMUBCount (p ^ k) (p ^ k + 1) := sorry

/-- `2ⁿ + 1` mutually unbiased bases of `ℂ^{2ⁿ}` for every `n ≥ 1`: the standard basis and, for each
`a ∈ 𝔽_{2ⁿ}`, the basis whose column `b ∈ 𝔽₂ⁿ` has entries `i^{xᵀ S_a x} (−1)^{b·x} / √2ⁿ`, `x ∈ 𝔽₂ⁿ`, where
`S_a` is the Gram matrix of the bilinear form `(x, y) ↦ Tr(a x y)` lifted to `{0, 1}` (equivalent to the Galois-ring
bases of Klappenecker–Rötteler 2004, Theorem 3, up to `a ↦ a²` and a relabelling of columns). -/
theorem hasCompleteMUBs_two_pow (n : ℕ) (hn : 1 ≤ n) : HasCompleteMUBs (2 ^ n) := sorry

/-- `2ⁿ + 1` is the maximal number of mutually unbiased bases in dimension `2ⁿ`, `n ≥ 1`. -/
theorem isMaxMUBCount_two_pow (n : ℕ) (hn : 1 ≤ n) : IsMaxMUBCount (2 ^ n) (2 ^ n + 1) := sorry

/-- `q + 1` is the maximal number of mutually unbiased bases in every prime-power dimension `q = pᵏ`, `k ≥ 1`. -/
theorem isMaxMUBCount_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    IsMaxMUBCount (p ^ k) (p ^ k + 1) := sorry

/-- For `d ≥ 2`, a complete set of `d + 1` mutually unbiased bases exists iff `d + 1` is the maximal number. -/
theorem hasCompleteMUBs_iff_isMaxMUBCount (d : ℕ) (hd : 2 ≤ d) :
    HasCompleteMUBs d ↔ IsMaxMUBCount d (d + 1) := sorry

/-- `μ(2) = 3` (formal-conjectures' `mutuallyUnbiasedBases_dim2`, re-proved here by a kernel-checked table; also the
case `n = 1` of `isMaxMUBCount_two_pow`). -/
theorem isMaxMUBCount_two : IsMaxMUBCount 2 3 := sorry

/-- `μ(4) = 5`: the standard basis and four bases of `ℂ⁴` with entries in `{±1, ±i}/2`, kernel-checked. -/
theorem isMaxMUBCount_four : IsMaxMUBCount 4 5 := sorry

/-- `μ(8) = 9`: the standard basis and eight bases of `ℂ⁸` with entries in `{±1 ± i}/4`, kernel-checked. -/
theorem isMaxMUBCount_eight : IsMaxMUBCount 8 9 := sorry

/- ## Gerzon's bound and its equality case -/

/-- Gerzon's bound over `ℂ` (Delsarte–Goethals–Seidel 1975): `N` unit vectors of `ℂ^d` whose pairwise squared
overlaps all equal `c ≠ 1` satisfy `N ≤ d²`. -/
theorem gerzon_bound {d N : ℕ} {c : ℝ} (hc : c ≠ 1) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) : N ≤ d ^ 2 := sorry

/-- The hypothesis `c ≠ 1` is necessary: for `d ≥ 1`, a unit vector repeated `N` times has every pairwise
squared overlap `1`, for every `N`. -/
theorem gerzon_sharp (d N : ℕ) (hd : 1 ≤ d) :
    ∃ Φ : Fin N → StateVector d, (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq 1 Φ := sorry

/-- The equality case: for `d ≥ 2`, `d²` unit vectors of `ℂ^d` with the same squared overlap `c ≠ 1` have
`c = 1/(d + 1)`. -/
theorem gerzon_equality {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : c ≠ 1) (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) : c = sicOverlapSq d := sorry

/-- The frame identity in the equality case: for `d ≥ 2`, `d²` unit vectors with the same squared overlap
`c ≠ 1` resolve the identity, `Σ_i (1/d) |φ_i⟩⟨φ_i| = 1`. -/
theorem gerzon_frame {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : c ≠ 1) (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    ∑ i, (d : ℂ)⁻¹ • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) = 1 := sorry

/-- Every SIC family is a POVM: its rank-one projectors, weighted by `1/d`, resolve the identity. -/
theorem isSICFamily_frame {d : ℕ} (hd : 2 ≤ d) (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ) :
    ∑ i, (d : ℂ)⁻¹ • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) = 1 := sorry

/-- For `d ≥ 2`, a SIC-POVM exists iff `ℂ^d` has `d²` unit vectors with one squared overlap `c ≠ 1` on every pair. -/
theorem hasSICPOVM_iff_equiangular (d : ℕ) (hd : 2 ≤ d) :
    HasSICPOVM d ↔ ∃ c : ℝ, c ≠ 1 ∧ ∃ Φ : Fin (d ^ 2) → StateVector d,
      (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq c Φ := sorry

/-- A family of unit vectors at the SIC angle `1/(d + 1)` has at most `d²` members: a SIC family is maximal. -/
theorem card_le_of_sicOverlapSq {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq (sicOverlapSq d) Φ) : N ≤ d ^ 2 := sorry

/- ## SIC-POVMs in dimensions 2, 3 and 8 -/

/-- The tetrahedral SIC-POVM of the qubit (formal-conjectures' `hasSICPOVM_two`, left with `sorry` there). -/
theorem hasSICPOVM_two : HasSICPOVM 2 := sorry

/-- The Hesse SIC-POVM of the qutrit (formal-conjectures' `hasSICPOVM_three`, left with `sorry` there). -/
theorem hasSICPOVM_three : HasSICPOVM 3 := sorry

/-- Hoggar's 64 lines: the orbit of `(−1 + 2i, 1, 1, 1, 1, 1, 1, 1)/√12` under the three-qubit Pauli group,
`(X^a Z^b v)(x) = (−1)^{b·(x ⊕ a)} v(x ⊕ a)` for `a, b ∈ 𝔽₂³`, is a SIC-POVM in `ℂ⁸` (Hoggar 1981, 1998;
Jedwab–Wiebe 2015, Example 4). -/
theorem hasSICPOVM_eight : HasSICPOVM 8 := sorry

/- ## Weiner's gap: `d` bases complete to `d + 1` -/

/-- Weiner's gap (Weiner 2013; the operator-algebra steps of its proof written out): `d` mutually unbiased bases of
`ℂ^d` give a complete set of `d + 1` (the existence form of Corollary 3.4). The orthogonal projection onto the
matrices with a constant diagonal in every one of the `d` bases has a Kraus form `X ↦ Σ_i K_i^* X K_i` (Weiner's
Lemma 3.2) whose operators `K_i` have constant diagonals themselves. At a fixed point `X` of the projection, such as
any `K_i` or `K_i^*`, its Kadison–Schwarz defect is the trace-zero sum `Σ_i (X K_i − K_i X)^* (X K_i − K_i X)`, so
`X` commutes with every `K_i`: the `K_i` commute with one another and with their adjoints, and the projectors of a
common eigenbasis of the `K_i` are again fixed by the projection, hence have constant diagonals, hence are unbiased
to every basis of the family. -/
theorem hasCompleteMUBs_of_hasMUBs_self (d : ℕ) (h : HasMUBs d d) : HasCompleteMUBs d := sorry

/-- Weiner's Corollary 3.4 in its extension form (Weiner 2013; the route as above): any `d` mutually unbiased bases
of `ℂ^d` extend, by one more basis, to a complete set of `d + 1`, the given bases keeping their places
(`C (r + 1) = B r`). -/
theorem exists_isMUBFamily_extension {d : ℕ} (B : Fin d → UMat d) (hB : IsMUBFamily B) :
    ∃ C : Fin (d + 1) → UMat d, IsMUBFamily C ∧ ∀ r : Fin d, C r.succ = B r := sorry

/-- `k ≥ d` mutually unbiased bases of `ℂ^d` give a complete set of `d + 1` (restrict to `d` and apply Weiner's
gap). -/
theorem hasCompleteMUBs_of_le_hasMUBs {d k : ℕ} (hk : d ≤ k) (h : HasMUBs d k) : HasCompleteMUBs d := sorry

/-- The gap (Weiner 2013, abstract: `N(d) ≠ d`): for `d ≥ 2`, `d` is never the maximal number of mutually
unbiased bases. -/
theorem isMaxMUBCount_ne_self (d : ℕ) (hd : 2 ≤ d) : ¬ IsMaxMUBCount d d := sorry

/-- Weiner's dichotomy (Weiner 2013, abstract): for `d ≥ 2` the maximal number of mutually unbiased bases is `d + 1`
or below `d`. -/
theorem isMaxMUBCount_dichotomy (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (h : IsMaxMUBCount d k) :
    k = d + 1 ∨ k < d := sorry

/- ## The maximal number: existence, uniqueness, bounds -/

/-- Two mutually unbiased bases in every dimension (e.g. the standard basis and the Fourier basis). -/
theorem hasMUBs_two (d : ℕ) : HasMUBs d 2 := sorry

/-- In a prime-power dimension `q = pᵏ`, `m` mutually unbiased bases exist iff `m ≤ q + 1`. -/
theorem hasMUBs_prime_pow_iff (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (m : ℕ) :
    HasMUBs (p ^ k) m ↔ m ≤ p ^ k + 1 := sorry

/-- The maximal number of mutually unbiased bases is unique. -/
theorem isMaxMUBCount_unique {d k l : ℕ} (hk : IsMaxMUBCount d k) (hl : IsMaxMUBCount d l) : k = l := sorry

/-- For `d ≥ 2` the maximal number exists: `μ(d)` is well defined. -/
theorem exists_isMaxMUBCount (d : ℕ) (hd : 2 ≤ d) : ∃ k, IsMaxMUBCount d k := sorry

/-- In dimension `1` there is no maximal number: every `k` is exceeded. -/
theorem not_exists_isMaxMUBCount_one : ¬ ∃ k, IsMaxMUBCount 1 k := sorry

/-- For `d ≥ 2`, the maximal number lies in `[3, d + 1]`. -/
theorem isMaxMUBCount_bounds (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (h : IsMaxMUBCount d k) :
    3 ≤ k ∧ k ≤ d + 1 := sorry

/-- formal-conjectures' `mutuallyUnbiasedBases_dim6_bounds` (left with `sorry` there, marked solved with a
`formal_proof` link to XC0R's fork at c8733543), stated verbatim: `3 ≤ μ(6) ≤ 7`, the instance `d = 6` of three
bases and the bound. -/
theorem mutuallyUnbiasedBases_dim6_bounds : HasMUBs 6 3 ∧ ∀ m : ℕ, HasMUBs 6 m → m ≤ 7 := sorry

/-- The instance `d = 6` of Weiner's gap: `μ(6) ≠ 6` (also implied by the bound of five bases formalized in
openai/math, `N6_le_five`). -/
theorem not_isMaxMUBCount_six_six : ¬ IsMaxMUBCount 6 6 := sorry

/- ## Reconstruction: complete sets and SIC families are informationally complete -/

/-- A complete set of `d + 1` mutually unbiased bases determines every matrix from its diagonals:
`X = Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1`, where `P_{s,l} = |e_{s,l}⟩⟨e_{s,l}|` is the projector onto column `l`
of basis `s` (after Ivanović 1981 and Wootters–Fields 1989, in the form of Scott 2006, eqs. (9) and (56)). -/
theorem mub_reconstruction {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    X = ∑ s, ∑ l, Matrix.trace (X * Matrix.vecMulVec (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
          (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))) •
        Matrix.vecMulVec (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
          (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l)) -
      Matrix.trace X • (1 : Matrix (Fin d) (Fin d) ℂ) := sorry

/-- A SIC family determines every matrix: `X = Σ_i ((d + 1) Tr(X P_i) − Tr X)/d · P_i` with `P_i = |φ_i⟩⟨φ_i|`
(informational completeness: Renes–Blume-Kohout–Scott–Caves 2004, §II; the coefficients: Scott 2006, eq. (9) in the
proof of Theorem 4, and Appleby–Dang–Fuchs, eq. (3)). -/
theorem sic_reconstruction {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    X = ∑ i, ((((d : ℂ) + 1) * Matrix.trace (X * Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) -
          Matrix.trace X) / (d : ℂ)) • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) := sorry

/- ## Welch's bound -/

/-- Welch's bound in the frame-potential form: `N` unit vectors of `ℂ^d` have `Σ_{i,j} |⟨φ_i, φ_j⟩|² ≥ N²/d` (Welch
1974, as restated by Datta–Howard–Cochran, eq. (2) with `k = 1`, and by Mixon–Needham–Shonkwiler–Villar,
Proposition 1; the frame potential is the name of Benedetto–Fickus 2003). -/
theorem welch_bound {d N : ℕ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i)) :
    (N : ℝ) ^ 2 / (d : ℝ) ≤ ∑ i, ∑ j, overlapSq (Φ i) (Φ j) := sorry

/-- Welch's bound for a constant overlap: `N ≥ 2` unit vectors with the same squared overlap `c` on every pair
have `c ≥ (N − d)/(d(N − 1))` (Welch 1974, as restated by Datta–Howard–Cochran, eq. (1) with `k = 1`). -/
theorem welch_bound_of_constantOverlap {d N : ℕ} {c : ℝ} (hN : 2 ≤ N) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    ((N : ℝ) - d) / ((d : ℝ) * ((N : ℝ) - 1)) ≤ c := sorry

/-- The relative bound, from Welch's inequality: `N` unit vectors with every pairwise squared overlap at most `α`,
where `α d < 1`, satisfy `N (1 − α d) ≤ d (1 − α)`. -/
theorem welch_card_bound {d N : ℕ} {α : ℝ} (hα : α * (d : ℝ) < 1) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ α) :
    (N : ℝ) * (1 - α * (d : ℝ)) ≤ (d : ℝ) * (1 - α) := sorry

/-- At most `d²` unit vectors of `ℂ^d` have every pairwise squared overlap at most `1/(d + 1)` (the relative bound
at `α = 1/(d + 1)`): a SIC family is a largest family of unit vectors at or below the SIC angle (for `d ≥ 2`,
`welch_card_bound` shows that `d²` unit vectors cannot all stay strictly below it). -/
theorem card_le_of_overlapSq_le_sic {d N : ℕ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d) : N ≤ d ^ 2 := sorry

/- ## A SIC-POVM in dimension 4 -/

/-- A SIC-POVM in dimension `4`: the sixteen vectors `(S^a T^b ψ)(x) = i^{b(x − a)} ψ(x − a)`, `a, b ∈ ℤ/4`, of
Appleby's exact fiducial
`ψ = √((5 − √5)/40) · (2 cos(π/8), i(e^{−iπ/8} + √(2 + √5) e^{iπ/8}), 2i sin(π/8), i(e^{−iπ/8} − √(2 + √5) e^{iπ/8}))`
(Appleby 2005, §8, eq. (149), which credits Zauner 1999 and Renes–Blume-Kohout–Scott–Caves 2004); the squared
overlaps `1/5` by exact trigonometric and radical identities. -/
theorem hasSICPOVM_four : HasSICPOVM 4 := sorry

end QuantumDesigns
