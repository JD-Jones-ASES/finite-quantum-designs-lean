module

public import QuantumDesigns.OddField
public import QuantumDesigns.TwoPow

/-!
# Complete sets in every prime-power dimension (assembly)

Desk glue: `GaloisField p k` for `p` prime, `k ≥ 1`, has `p ^ k` elements (`GaloisField.card`), characteristic `p`;
for `p ≠ 2` apply `hasCompleteMUBs_of_odd_char_internal`; for `p = 2` apply `hasCompleteMUBs_two_pow_internal`.
-/

@[expose] public section

namespace QuantumDesigns

theorem hasCompleteMUBs_prime_pow_internal (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    HasCompleteMUBs (p ^ k) := sorry

end QuantumDesigns
