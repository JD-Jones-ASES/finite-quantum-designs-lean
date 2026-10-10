module

public import QuantumDesigns.Defs

/-!
# Complete sets of mutually unbiased bases over a finite field of odd characteristic

Lane **oddfield**. Fix a finite field `F` with `ringChar F ≠ 2`, `q = Fintype.card F`, a nontrivial additive
character `ψ : AddChar F ℂ` (`AddChar.FiniteField.primitiveChar_to_Complex` with `..._isPrimitive`, or any `ψ ≠ 1`:
over a field a nontrivial character is primitive, `AddChar.IsPrimitive.of_ne_one`), and an equivalence
`e : F ≃ Fin q` (`Fintype.equivFin`).

**`quadSum_normSq`.** With `S = Σ_x ψ(c x² + e x)`: `‖S‖² = S * conj S`; `conj (ψ y) = ψ (−y)`
(`AddChar.map_neg_eq_conj`); reindex the inner sum by `x = y + t` (`Equiv.addRight`); `c(y+t)² + e(y+t) − c y² − e y
= c t² + e t + 2 c t y`; so `‖S‖² = Σ_t ψ(c t² + e t) Σ_y ψ((2 c t) y) = Σ_t ψ(c t² + e t) · (if 2 c t = 0 then q else 0)`
(`AddChar.sum_mulShift`); `2 c t = 0 ↔ t = 0` since `2 ≠ 0` (`ringChar F ≠ 2`: `Ring.two_ne_zero`) and `c ≠ 0`; the
`t = 0` term is `ψ 0 = 1`, so `‖S‖² = q`. No Gauss sums, no quadratic characters.

**The bases.** For `a : F`, `M a : Matrix (Fin q) (Fin q) ℂ`, `M a i j = (√q)⁻¹ * ψ (a * x ^ 2 + y * x)` with
`x = e.symm i` (row) and `y = e.symm j` (column). Unitarity: `(M a)^* (M a) = 1` entrywise is
`(1/q) Σ_x ψ((y' − y) x) = δ` (`sum_mulShift`). Unbiasedness against the standard basis `1`: every entry has
`‖·‖² = 1/q` (`AddChar.norm_apply`). Between `M a` and `M a'`, `a ≠ a'`: the `(j, j')` entry of `(M a)^* (M a')` is
`(1/q) Σ_x ψ((a' − a) x² + (y' − y) x)`, of squared norm `q / q² = 1/q` by `quadSum_normSq`. The family
`Fin (q + 1) → UMat q` is `Fin.cons 1 (fun a => ⟨M (e.symm a), _⟩)`; `IsMUBFamily` by cases on `Fin.cons`
(`Fin.cases`), using `IsUnbiased.symm` (prove it locally: `relativeUnitary V U = star (relativeUnitary U V)`).
-/

@[expose] public section

namespace QuantumDesigns

theorem quadSum_normSq_internal (F : Type) [Field F] [Fintype F] (h2 : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (c e : F) (hc : c ≠ 0) :
    ‖∑ x : F, ψ (c * x ^ 2 + e * x)‖ ^ (2 : ℕ) = Fintype.card F := sorry

theorem hasCompleteMUBs_of_odd_char_internal (F : Type) [Field F] [Fintype F] (h2 : ringChar F ≠ 2) :
    HasCompleteMUBs (Fintype.card F) := sorry

end QuantumDesigns
