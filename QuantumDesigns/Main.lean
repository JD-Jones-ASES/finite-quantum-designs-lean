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

The `IsMaxMUBCount` statements from `hasMUBs_le_internal` and the constructions; the iff for complete
sets; the three small dimensions from `Small.lean` (independent of the general `2ⁿ` route).
-/

@[expose] public section

namespace QuantumDesigns

theorem isMaxMUBCount_odd_prime_pow_internal (p k : ℕ) (hp : p.Prime) (_hp2 : p ≠ 2) (hk : 1 ≤ k) :
    IsMaxMUBCount (p ^ k) (p ^ k + 1) :=
  ⟨hasCompleteMUBs_prime_pow_internal p k hp hk,
    fun m hm => hasMUBs_le_internal _ (hp.two_le.trans (Nat.le_self_pow (by omega) p)) m hm⟩

theorem isMaxMUBCount_two_pow_internal (n : ℕ) (hn : 1 ≤ n) : IsMaxMUBCount (2 ^ n) (2 ^ n + 1) :=
  ⟨hasCompleteMUBs_two_pow_internal n hn,
    fun m hm => hasMUBs_le_internal _ (Nat.le_self_pow (by omega) 2) m hm⟩

theorem isMaxMUBCount_prime_pow_internal (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    IsMaxMUBCount (p ^ k) (p ^ k + 1) :=
  ⟨hasCompleteMUBs_prime_pow_internal p k hp hk,
    fun m hm => hasMUBs_le_internal _ (hp.two_le.trans (Nat.le_self_pow (by omega) p)) m hm⟩

theorem hasCompleteMUBs_iff_isMaxMUBCount_internal (d : ℕ) (hd : 2 ≤ d) :
    HasCompleteMUBs d ↔ IsMaxMUBCount d (d + 1) :=
  ⟨fun h => ⟨h, fun m hm => hasMUBs_le_internal d hd m hm⟩, fun h => h.1⟩

theorem isMaxMUBCount_two_internal : IsMaxMUBCount 2 3 :=
  ⟨hasMUBs_two_three, fun m hm => hasMUBs_le_internal 2 le_rfl m hm⟩

theorem isMaxMUBCount_four_internal : IsMaxMUBCount 4 5 :=
  ⟨hasMUBs_four_five, fun m hm => hasMUBs_le_internal 4 (by norm_num) m hm⟩

theorem isMaxMUBCount_eight_internal : IsMaxMUBCount 8 9 :=
  ⟨hasMUBs_eight_nine, fun m hm => hasMUBs_le_internal 8 (by norm_num) m hm⟩

end QuantumDesigns
