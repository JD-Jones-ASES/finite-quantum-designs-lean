module

/-!
# Index arithmetic for the dimension-4 SIC-POVM

The sixteen Weyl–Heisenberg translates `S^a T^b ψ` of a vector `ψ ∈ ℂ⁴` (`a, b < 4`, `S` the cyclic shift,
`T` the clock with eigenvalue `iˣ` on the basis vector `eₓ`) are indexed by `k = 4a + b < 16`. Coordinate `x` of the
translate with index `k` is `i^{b (x − a)} ψ(x − a)`, the indices taken mod 4: `s4_sh` is the shifted coordinate
`x − a` and `s4_ph` the exponent `b (x − a)` of the phase. The overlap of the translates with indices `k` and `l` is,
up to a power of `i`, the overlap of `ψ` with its translate of index `s4_diff k l` (the difference of the two
displacements); `s4_diff_bounds` checks, by kernel evaluation, that this index is nonzero for `k ≠ l`. No imports.
-/

@[expose] public section

namespace QuantumDesigns

/-- The shifted coordinate `x − a (mod 4)` of the translate with index `k = 4a + b`. -/
def s4_sh (k x : Nat) : Nat := (x + 4 - k / 4) % 4

/-- The phase exponent `b (x − a) (mod 4)` of the translate with index `k = 4a + b`. -/
def s4_ph (k x : Nat) : Nat := k % 4 * s4_sh k x % 4

/-- The index of the difference of the displacements `(a, b)` and `(c, e)` of `k = 4a + b` and `l = 4c + e`:
`4 (c − a) + (e − b)`, each part mod 4. -/
def s4_diff (k l : Nat) : Nat := 4 * ((l / 4 + 4 - k / 4) % 4) + (l % 4 + 4 - k % 4) % 4

/-- Distinct translates differ by a nonzero displacement. -/
theorem s4_diff_bounds : ∀ k, k < 16 → ∀ l, l < 16 → k ≠ l → 1 ≤ s4_diff k l ∧ s4_diff k l < 16 := by
  decide +kernel

end QuantumDesigns
