module

public import QuantumDesigns.GapCore

/-!
# The Kadison–Schwarz defect of a Kraus map is a sum of squares

For matrices `K_i` with `Σ_i K_i^* K_i = 1` and `C = Σ_i K_i^* X K_i`:
`Σ_i (X K_i − K_i C)^* (X K_i − K_i C) = Σ_i K_i^* X^* X K_i − (Σ_i K_i^* X^* K_i) C − C^* (Σ_i K_i^* X K_i)
+ C^* (Σ_i K_i^* K_i) C`, and `Σ_i K_i^* X^* K_i = C^*`, so the right side is `Σ_i K_i^* X^* X K_i − C^* C`
(`gp_schwarz_defect`; the inequality `Φ(X^* X) ≥ Φ(X)^* Φ(X)` of Kadison and Choi, with its defect written out).
A sum of matrices `A_i^* A_i` with zero trace has every `A_i = 0`: `Tr(A^* A) = Σ_{a,b} ‖A_{ab}‖²`
(`gp_eq_zero_of_trace_sum_star_mul_self`). Hence if `C = X` (a fixed point) and the map preserves the trace of
`X^* X`, the defect has zero trace and every `X K_i = K_i X` (`gp_commute_of_fixed`).
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- The Kadison–Schwarz defect of a Kraus map with `Σ_i K_i^* K_i = 1` is a sum of squares. -/
theorem gp_schwarz_defect {d : ℕ} {ι : Type} [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∑ i, star (K i) * K i = 1) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, star (K i) * (star X * X) * K i -
        star (∑ i, star (K i) * X * K i) * (∑ i, star (K i) * X * K i) =
      ∑ i, star (X * K i - K i * (∑ j, star (K j) * X * K j)) *
        (X * K i - K i * (∑ j, star (K j) * X * K j)) := sorry

/-- A finite sum of matrices `A_i^* A_i` with zero trace has every term zero. -/
theorem gp_eq_zero_of_trace_sum_star_mul_self {d : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (h : Matrix.trace (∑ i, star (A i) * A i) = 0) : ∀ i, A i = 0 := sorry

/-- A fixed point of a Kraus map (`Σ_i K_i^* K_i = 1`) that preserves the trace of `X^* X` commutes with every
Kraus operator. -/
theorem gp_commute_of_fixed {d : ℕ} {ι : Type} [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∑ i, star (K i) * K i = 1) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∑ i, star (K i) * X * K i = X)
    (htr : Matrix.trace (∑ i, star (K i) * (star X * X) * K i) = Matrix.trace (star X * X)) :
    ∀ i, X * K i = K i * X := sorry

end QuantumDesigns
