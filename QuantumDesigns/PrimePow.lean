module

public import QuantumDesigns.OddField
public import QuantumDesigns.TwoPow

/-!
# Complete sets in every prime-power dimension (assembly)

`GaloisField p k` for `p` prime, `k ≥ 1`, has `p ^ k` elements (`GaloisField.card`), characteristic `p`;
for `p ≠ 2` apply `hasCompleteMUBs_of_odd_char_internal`; for `p = 2` apply `hasCompleteMUBs_two_pow_internal`.
-/

@[expose] public section

namespace QuantumDesigns

theorem hasCompleteMUBs_prime_pow_internal (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    HasCompleteMUBs (p ^ k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h2 : p = 2
  · subst h2
    exact hasCompleteMUBs_two_pow_internal k hk
  · letI : Fintype (GaloisField p k) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField p k) = p ^ k := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p k (by omega)
    have hchar : ringChar (GaloisField p k) ≠ 2 := by
      rw [ringChar.eq (GaloisField p k) p]
      exact h2
    have h := hasCompleteMUBs_of_odd_char_internal (GaloisField p k) hchar
    rwa [hcard] at h

end QuantumDesigns
