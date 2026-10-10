module

public import QuantumDesigns.Defs

/-!
# Three mutually unbiased bases in every dimension `d ≥ 2`, directly

Lane **chirp** (insurance for `hasMUBs_three`, which `Tensor.lean` derives from the prime-power theorem; this
module proves it without any finite field). Let `ω = exp(2πi/d)`, `ζ = exp(πi/d)` (so `ζ² = ω`), and take the three
bases: the standard basis `1`; the Fourier matrix `F j k = (√d)⁻¹ ω^{jk}`; the chirped Fourier matrix
`C j k = (√d)⁻¹ ζ^{j(j + d)} ω^{jk}`. The phase `j ↦ ζ^{j(j+d)}` is `d`-periodic for every `d` (shift `j ↦ j + d`
multiplies by `ζ^{2jd + 2d²} = 1`), and `ζ^{(j+t)(j+t+d) − j(j+d)} = ζ^{t(t+d)} ω^{jt}`.

- `F` unitary and unbiased to `1`: `Σ_j ω^{j(k' − k)} = d δ` (`ZMod.stdAddChar` with `AddChar.sum_mulShift`, or
  Mathlib's geometric sums of roots of unity: `IsPrimitiveRoot.geom_sum_eq_zero`); every entry has `‖·‖² = 1/d`.
- `C = D F` with `D` the diagonal unitary of the chirp, so `C` is unitary and unbiased to `1`.
- `F^* C` has `(k, k')` entry `(1/d) Σ_j ζ^{j(j+d)} ω^{j(k' − k)}`; its squared norm is
  `(1/d²) Σ_{j,j'} ζ^{j(j+d) − j'(j'+d)} ω^{(j − j')(k' − k)}`; substitute `j = j' + t` (mod `d`, using periodicity) to get
  `(1/d²) Σ_t ζ^{t(t+d)} ω^{t(k'−k)} Σ_{j'} ω^{j' t} = (1/d²) · d = 1/d`.

Index the three bases by `Fin 3` (`![1, F, C]`); `IsMUBFamily` by `Fin` case analysis with symmetry.
-/

@[expose] public section

namespace QuantumDesigns

theorem hasMUBs_three_chirp (d : ℕ) (hd : 2 ≤ d) : HasMUBs d 3 := sorry

end QuantumDesigns
