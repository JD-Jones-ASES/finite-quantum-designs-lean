module

public import QuantumDesigns.PrimePow
public import QuantumDesigns.Bound

/-!
# The tensor bound and the prime-power-divisor corollary

`hasMUBs_mul`: if `B : Fin k → UMat m` and `C : Fin k → UMat n` are families of mutually unbiased
bases, the Kronecker products `B r ⊗ C r`, reindexed along `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`, form `k`
mutually unbiased bases of `ℂ^{mn}`: `(B r ⊗ C r)^* (B s ⊗ C s) = (B r^* B s) ⊗ (C r^* C s)` (`Matrix.mul_kronecker_mul`,
`Matrix.conjTranspose` of a Kronecker product), so every entry of the relative unitary is a product of entries with
squared norms `1/m` and `1/n`. Unitarity: `Matrix.mul_kronecker_mul`, `Matrix.one_kronecker_one`
(`Matrix.kronecker`, `Matrix.kroneckerMap`, `Matrix.reindex` through `Matrix.reindexAlgEquiv` or
`Matrix.submatrix` with the equivalence; a reindexed unitary is unitary). XC0R's `hasMUBs_mul` is prior public Lean
for this statement (adapted; credited in NOTICE).

`hasMUBs_of_forall_primePow`: induction over the factorization (`Nat.recOnPosPrimePosCoprime`, or
`Nat.prod_primeFactors_pow_factorization`): for a prime power `q = p ^ j`, `j ≥ 1`, `HasMUBs q (q + 1)` is
`hasCompleteMUBs_prime_pow_internal` (a black box of `PrimePow.lean`) and restriction gives `HasMUBs q k` for
`k ≤ q + 1` (`hasMUBs_of_le_internal`, a black box of `Bound.lean`); for coprime `a * b` the factorizations split
(`Nat.factorization_mul_of_coprime`, `Nat.primeFactors_mul`), so the hypothesis passes to both factors and
`hasMUBs_mul_internal` finishes; the case `d = 1` is `hasMUBs_one_dim_internal`. The statement for a single prime
divisor (`HasMUBs d (q + 1)` for every `p ∣ d`) is false in general: `d = 6`, `p = 3` would give four bases in
dimension six, an open question. `hasMUBs_three_internal`: every exact prime-power divisor is `≥ 2`, so `3 ≤ q + 1`.
-/

@[expose] public section

namespace QuantumDesigns

open scoped Kronecker
open Matrix

/-- The Kronecker product of two unitary matrices, reindexed along `finProdFinEquiv` to `Fin (m * n)`; adapts
`kroneckerUMat` of XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
noncomputable def tn_kroneckerUMat {m n : ℕ} (U : UMat m) (V : UMat n) : UMat (m * n) :=
  let UV : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
    (U : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (V : Matrix (Fin n) (Fin n) ℂ)
  ⟨(reindex finProdFinEquiv finProdFinEquiv) UV, by
    rw [Matrix.mem_unitaryGroup_iff']
    have hU := (Matrix.mem_unitaryGroup_iff').mp U.2
    have hV := (Matrix.mem_unitaryGroup_iff').mp V.2
    have hUV : UVᴴ * UV = 1 := by
      show ((↑U : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (↑V : Matrix (Fin n) (Fin n) ℂ))ᴴ *
        ((↑U : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (↑V : Matrix (Fin n) (Fin n) ℂ)) = 1
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
      simp only [star_eq_conjTranspose] at hU hV
      rw [hU, hV, Matrix.one_kronecker_one]
    show ((reindex finProdFinEquiv finProdFinEquiv) UV)ᴴ *
      (reindex finProdFinEquiv finProdFinEquiv) UV = 1
    rw [Matrix.conjTranspose_reindex]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, hUV, Matrix.submatrix_one_equiv]⟩

/-- The relative unitary of two Kronecker products is the Kronecker product of the relative unitaries; adapts
`relativeUnitary_kronecker` of XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
theorem tn_relativeUnitary_kronecker {m n : ℕ}
    (U₁ U₂ : UMat m) (V₁ V₂ : UMat n) (i₁ j₁ : Fin m) (i₂ j₂ : Fin n) :
    relativeUnitary (tn_kroneckerUMat U₁ V₁) (tn_kroneckerUMat U₂ V₂)
      (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv (j₁, j₂)) =
    relativeUnitary U₁ U₂ i₁ j₁ * relativeUnitary V₁ V₂ i₂ j₂ := by
  simp only [relativeUnitary, tn_kroneckerUMat, star_eq_conjTranspose]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_apply]
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.kroneckerMap_apply]
  simp [finProdFinEquiv.symm_apply_apply]

/-- Kronecker products of unbiased pairs are unbiased; adapts `isUnbiased_kronecker` of
XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
theorem tn_isUnbiased_kronecker {m n : ℕ}
    (U₁ U₂ : UMat m) (V₁ V₂ : UMat n)
    (hU : IsUnbiased U₁ U₂) (hV : IsUnbiased V₁ V₂) :
    IsUnbiased (tn_kroneckerUMat U₁ V₁) (tn_kroneckerUMat U₂ V₂) := by
  intro i j
  have hi : i = finProdFinEquiv (finProdFinEquiv.symm i) := (finProdFinEquiv.apply_symm_apply i).symm
  have hj : j = finProdFinEquiv (finProdFinEquiv.symm j) := (finProdFinEquiv.apply_symm_apply j).symm
  rw [hi, hj, tn_relativeUnitary_kronecker, norm_mul, mul_pow, hU, hV]
  push_cast
  ring

/-- The tensor bound: `k` mutually unbiased bases in dimensions `m` and `n` give `k` in dimension `m * n`; adapts
`hasMUBs_mul` of XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
theorem hasMUBs_mul_internal {m n k : ℕ} (hm : HasMUBs m k) (hn : HasMUBs n k) : HasMUBs (m * n) k := by
  obtain ⟨B₁, hB₁⟩ := hm
  obtain ⟨B₂, hB₂⟩ := hn
  exact ⟨fun i => tn_kroneckerUMat (B₁ i) (B₂ i), fun i j hij =>
    tn_isUnbiased_kronecker _ _ _ _ (hB₁ hij) (hB₂ hij)⟩

/-- The tensor bound over the factorization: if `k ≤ q + 1` for every exact prime-power divisor `q` of `d ≥ 1`,
then `ℂ^d` has `k` mutually unbiased bases. -/
theorem hasMUBs_of_forall_primePow_internal (d k : ℕ) (hd : d ≠ 0)
    (h : ∀ p ∈ d.primeFactors, k ≤ p ^ d.factorization p + 1) : HasMUBs d k := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hd
  | one => exact hasMUBs_one_dim_internal k
  | prime_pow p j hp hj =>
    have hp' : p.Prime := hp
    have hmem : p ∈ (p ^ j).primeFactors := by
      rw [Nat.primeFactors_prime_pow (Nat.pos_iff_ne_zero.mp hj) hp']
      exact Finset.mem_singleton_self p
    have hk := h p hmem
    rw [hp'.factorization_pow, Finsupp.single_eq_same] at hk
    exact hasMUBs_of_le_internal hk (hasCompleteMUBs_prime_pow_internal p j hp' hj)
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hfac : (a * b).factorization = a.factorization + b.factorization :=
      Nat.factorization_mul ha0 hb0
    have hnd : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ b → False := fun p hp hpa hpb => by
      have h1 : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
      rw [hab] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    refine hasMUBs_mul_internal (iha ha0 ?_) (ihb hb0 ?_)
    · intro p hpm
      have hp := Nat.prime_of_mem_primeFactors hpm
      have hpa := Nat.dvd_of_mem_primeFactors hpm
      have hmem : p ∈ (a * b).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, Dvd.dvd.mul_right hpa b, Nat.mul_ne_zero ha0 hb0⟩
      have hk := h p hmem
      rw [hfac, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (fun hpb => hnd p hp hpa hpb), Nat.add_zero] at hk
      exact hk
    · intro p hpm
      have hp := Nat.prime_of_mem_primeFactors hpm
      have hpb := Nat.dvd_of_mem_primeFactors hpm
      have hmem : p ∈ (a * b).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, Dvd.dvd.mul_left hpb a, Nat.mul_ne_zero ha0 hb0⟩
      have hk := h p hmem
      rw [hfac, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (fun hpa => hnd p hp hpa hpb), Nat.zero_add] at hk
      exact hk

theorem hasMUBs_three_internal (d : ℕ) (hd : 2 ≤ d) : HasMUBs d 3 := by
  refine hasMUBs_of_forall_primePow_internal d 3 (by omega) ?_
  intro p hpm
  have hp := Nat.prime_of_mem_primeFactors hpm
  have hpd := Nat.dvd_of_mem_primeFactors hpm
  have he : 0 < d.factorization p := hp.factorization_pos_of_dvd (by omega) hpd
  have h2 : 2 ≤ p := hp.two_le
  have hle : p ≤ p ^ d.factorization p := Nat.le_self_pow (Nat.pos_iff_ne_zero.mp he) p
  omega

end QuantumDesigns
