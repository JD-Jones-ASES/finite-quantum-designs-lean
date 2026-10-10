module

public import QuantumDesigns.Defs

/-!
# SIC-POVMs in dimensions 2, 3 and 8

Lane **hoggar**. **Dimension 8.** The fiducial `ψ = (−1 + 2i, 1, 1, 1, 1, 1, 1, 1)` (unnormalized, `‖ψ‖² = 12`) and the
64 vectors `v_{a,b}(x) = (−1)^{b·(x ⊕ a)} ψ(x ⊕ a)` for `a, b ∈ 𝔽₂³` (`x ⊕ a = x ^^^ a` on `Fin 8`, `b·y` the parity
of `b &&& y`): the desk's exact replay gives `‖v‖² = 12` and `‖⟨u, v⟩‖² = 16` on all 4032 ordered pairs of distinct
vectors, so `overlapSq = 16/144 = 1/9 = sicOverlapSq 8`. Route: encode each vector as a function `Fin 8 → ℤ × ℤ`
(Gaussian integers); a kernel-checked statement over all `64 × 64` ordered pairs that the integer inner product
`Σ_x conj(u x) v x` has `re² + im² = 144` on the diagonal and `16` off it (`decide +kernel` in a Mathlib-free leaf,
or `Nat`-encoded; below the measured ceilings); a generic cast lemma from the integer pair to `ℂ`
(`Complex.ext_iff`, `push_cast`; no case split); normalization `‖(√12)⁻¹ • ψ‖ = 1` through `EuclideanSpace.norm_eq`
and `Real.sq_sqrt`; the family `Φ : Fin 64 → StateVector 8`, `Φ i = (√12)⁻¹ • v_{i / 8, i % 8}` as
`WithLp.toLp 2 (fun x => …)`.

**Dimensions 2 and 3.** The tetrahedral family `(1, 0)`, `(√(1/3), √(2/3) ω^m)` (`m = 0, 1, 2`, `ω = e^{2πi/3}`) and
the Hesse family `(0, s, −s ω^m)`, `(−s ω^m, 0, s)`, `(s, −s ω^m, 0)` with `s = √(1/2)` (formal-conjectures'
`qubitSICFamily`, `hesseFamily`; zblore/csd-lean4 holds the overlaps in Lean in other vocabulary). Overlaps by
`Fin` case analysis and `norm_num` / `ring_nf` / `nlinarith` with `ω² = −1 − ω`, `‖ω‖ = 1`, `Real.sq_sqrt`; or the
Gaussian/Eisenstein-integer kernel route with the scale removed (the desk's replay checks both exactly).
-/

@[expose] public section

namespace QuantumDesigns

theorem hasSICPOVM_two_internal : HasSICPOVM 2 := sorry

theorem hasSICPOVM_three_internal : HasSICPOVM 3 := sorry

theorem hasSICPOVM_eight_internal : HasSICPOVM 8 := sorry

end QuantumDesigns
