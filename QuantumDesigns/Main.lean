module

public import QuantumDesigns.Bound
public import QuantumDesigns.Tensor
public import QuantumDesigns.PrimePow
public import QuantumDesigns.Small
public import QuantumDesigns.Chirp
public import QuantumDesigns.Gerzon
public import QuantumDesigns.SIC

/-!
# Assembly

Desk glue: the `IsMaxMUBCount` statements from `hasMUBs_le_internal` and the constructions; the iff for complete
sets; the three small dimensions from `Small.lean` (independent of the general `2ⁿ` route).
-/

@[expose] public section

namespace QuantumDesigns

theorem isMaxMUBCount_odd_prime_pow_internal (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    IsMaxMUBCount (p ^ k) (p ^ k + 1) := sorry

theorem isMaxMUBCount_two_pow_internal (n : ℕ) (hn : 1 ≤ n) : IsMaxMUBCount (2 ^ n) (2 ^ n + 1) := sorry

theorem isMaxMUBCount_prime_pow_internal (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    IsMaxMUBCount (p ^ k) (p ^ k + 1) := sorry

theorem hasCompleteMUBs_iff_isMaxMUBCount_internal (d : ℕ) (hd : 2 ≤ d) :
    HasCompleteMUBs d ↔ IsMaxMUBCount d (d + 1) := sorry

theorem isMaxMUBCount_two_internal : IsMaxMUBCount 2 3 := sorry

theorem isMaxMUBCount_four_internal : IsMaxMUBCount 4 5 := sorry

theorem isMaxMUBCount_eight_internal : IsMaxMUBCount 8 9 := sorry

end QuantumDesigns
