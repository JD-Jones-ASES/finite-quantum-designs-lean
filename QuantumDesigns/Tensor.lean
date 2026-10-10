module

public import QuantumDesigns.PrimePow

/-!
# The tensor bound and the prime-power-divisor corollary

Lane **tensor**. `hasMUBs_mul`: if `B : Fin k → UMat m` and `C : Fin k → UMat n` are families of mutually unbiased
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

theorem hasMUBs_mul_internal {m n k : ℕ} (hm : HasMUBs m k) (hn : HasMUBs n k) : HasMUBs (m * n) k := sorry

/-- The tensor bound over the factorization: if `k ≤ q + 1` for every exact prime-power divisor `q` of `d ≥ 1`,
then `ℂ^d` has `k` mutually unbiased bases. -/
theorem hasMUBs_of_forall_primePow_internal (d k : ℕ) (hd : d ≠ 0)
    (h : ∀ p ∈ d.primeFactors, k ≤ p ^ d.factorization p + 1) : HasMUBs d k := sorry

theorem hasMUBs_three_internal (d : ℕ) (hd : 2 ≤ d) : HasMUBs d 3 := sorry

end QuantumDesigns
