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

theorem hasMUBs_two_internal (d : ℕ) : HasMUBs d 2 := by
  rcases Nat.lt_or_ge d 2 with h | h
  · interval_cases d
    · exact ⟨fun _ => 1, fun _ _ _ i _ => i.elim0⟩
    · exact hasMUBs_one_dim_internal 2
  · exact hasMUBs_of_le_internal (by norm_num : 2 ≤ 3) (hasMUBs_three_internal d h)

theorem hasMUBs_prime_pow_iff_internal (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (m : ℕ) :
    HasMUBs (p ^ k) m ↔ m ≤ p ^ k + 1 :=
  ⟨fun h => (isMaxMUBCount_prime_pow_internal p k hp hk).2 m h,
    fun h => hasMUBs_of_le_internal h (isMaxMUBCount_prime_pow_internal p k hp hk).1⟩

theorem isMaxMUBCount_unique_internal {d k l : ℕ} (hk : IsMaxMUBCount d k) (hl : IsMaxMUBCount d l) :
    k = l :=
  le_antisymm (hl.2 k hk.1) (hk.2 l hl.1)

theorem exists_isMaxMUBCount_internal (d : ℕ) (hd : 2 ≤ d) : ∃ k, IsMaxMUBCount d k := by
  classical
  refine ⟨Nat.findGreatest (fun m => HasMUBs d m) (d + 1), ?_, fun m hm => ?_⟩
  · exact Nat.findGreatest_spec (P := fun m => HasMUBs d m) (m := 0) (Nat.zero_le _)
      (hasMUBs_of_le_internal (Nat.zero_le 3) (hasMUBs_three_internal d hd))
  · exact Nat.le_findGreatest (P := fun m => HasMUBs d m) (hasMUBs_le_internal d hd m hm) hm

theorem not_exists_isMaxMUBCount_one_internal : ¬ ∃ k, IsMaxMUBCount 1 k := by
  rintro ⟨k, hk⟩
  have := hk.2 (k + 1) (hasMUBs_one_dim_internal (k + 1))
  omega

theorem isMaxMUBCount_bounds_internal (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (h : IsMaxMUBCount d k) :
    3 ≤ k ∧ k ≤ d + 1 :=
  ⟨h.2 3 (hasMUBs_three_internal d hd), hasMUBs_le_internal d hd k h.1⟩

theorem mutuallyUnbiasedBases_dim6_bounds_internal : HasMUBs 6 3 ∧ ∀ m : ℕ, HasMUBs 6 m → m ≤ 7 :=
  ⟨hasMUBs_three_internal 6 (by norm_num), fun m hm => hasMUBs_le_internal 6 (by norm_num) m hm⟩

end QuantumDesigns
