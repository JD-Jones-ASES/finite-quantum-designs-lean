module

public import QuantumDesigns.Bound
public import QuantumDesigns.Tensor
public import QuantumDesigns.Chirp
public import QuantumDesigns.Main

/-!
# The maximal number `μ(d)`: existence, uniqueness, bounds, and the small statements

Two bases in every dimension: `d ≥ 2` restricts three (`hasMUBs_three_internal`, `hasMUBs_of_le_internal`),
`d = 1` is `hasMUBs_one_dim_internal`, `d = 0` has nothing to check. In a prime-power dimension `q`,
`HasMUBs q m ↔ m ≤ q + 1` (`isMaxMUBCount_prime_pow_internal` and restriction). The maximal number is unique (two
maxima bound each other); for `d ≥ 2` it exists (`Nat.findGreatest` below the bound `d + 1`,
`hasMUBs_le_internal`) and lies in `[3, d + 1]`; in dimension `1` there is none (`HasMUBs 1 (k + 1)`).
formal-conjectures' `mutuallyUnbiasedBases_dim6_bounds` is the instance `d = 6` of three bases and the bound.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

theorem hasMUBs_two_internal (d : ℕ) : HasMUBs d 2 := sorry

theorem hasMUBs_prime_pow_iff_internal (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (m : ℕ) :
    HasMUBs (p ^ k) m ↔ m ≤ p ^ k + 1 := sorry

theorem isMaxMUBCount_unique_internal {d k l : ℕ} (hk : IsMaxMUBCount d k) (hl : IsMaxMUBCount d l) :
    k = l := sorry

theorem exists_isMaxMUBCount_internal (d : ℕ) (hd : 2 ≤ d) : ∃ k, IsMaxMUBCount d k := sorry

theorem not_exists_isMaxMUBCount_one_internal : ¬ ∃ k, IsMaxMUBCount 1 k := sorry

theorem isMaxMUBCount_bounds_internal (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (h : IsMaxMUBCount d k) :
    3 ≤ k ∧ k ≤ d + 1 := sorry

theorem mutuallyUnbiasedBases_dim6_bounds_internal : HasMUBs 6 3 ∧ ∀ m : ℕ, HasMUBs 6 m → m ≤ 7 := sorry

end QuantumDesigns
