module

public import QuantumDesigns.Defs

/-!
# Explicit complete sets in dimensions 2, 4 and 8, kernel-checked

Lane **small**. Every entry of the `d` non-standard bases is `c · i^E` with `E ∈ {0, 1, 2, 3}` and
`c = (√d)⁻¹`: for `d = 2`, `c = (√2)⁻¹`; for `d = 4`, `c = 1/2` (no root); for `d = 8`, `c = (1 + i)/4`
(`‖c‖² = 2/16 = 1/8`, no root). The exponent tables `E_a(x, b) = Q_a(x) + 2 b·x mod 4` are those of the desk's replay
(`bench/rt-069-finite-quantum-designs/lanes/desk/replay.py`, function `replay_even`; `S_a` from the trace form of
`𝔽_{2ⁿ}` in the polynomial basis — print them from the script and paste as `List`/`Fin`-indexed tables).

Route: a Mathlib-free leaf (or a module importing only what it needs) defines the tables as functions
`Fin d → Fin d → Fin d → ℕ` (basis, column, row) and a Gaussian-integer checker: for bases `a, a'` and columns
`b, b'`, the sum `Σ_x i^{E_{a'}(x,b') − E_a(x,b)}` as a pair of integers `(re, im)` (count the exponents mod 4);
the checker asserts `re² + im² = d²` or `0` inside a basis, and `= d` across bases; `decide +kernel` over all
`d² · d²` (`a, b, a', b'`) with `d` terms each (`8⁴ · 8 = 32768` terms for `d = 8`, well below the house's measured
ceiling; `kernel-bitset-coverage` and `kernel-list-enumeration-small-n` patterns). One generic soundness lemma
turns the integer verdict into `IsUnbiased`/unitarity over `ℂ`: `(c i^E)^* (c i^{E'}) = ‖c‖² i^{E' − E}` and
`Σ_x i^{k_x} = (re : ℂ) + (im : ℂ) I` where `re = #{k ≡ 0} − #{k ≡ 2}`, `im = #{k ≡ 1} − #{k ≡ 3}`; then
`‖·‖² = ‖c‖⁴ (re² + im²)`. Unitarity of the standard basis is `Matrix.unitaryGroup` of `1`; unbiasedness against it:
every entry has `‖c i^E‖² = 1/d`.

If `d = 8` is heavy, split the kernel check by basis pairs into separate declarations.
-/

@[expose] public section

namespace QuantumDesigns

theorem hasMUBs_two_three : HasMUBs 2 3 := sorry

theorem hasMUBs_four_five : HasMUBs 4 5 := sorry

theorem hasMUBs_eight_nine : HasMUBs 8 9 := sorry

end QuantumDesigns
