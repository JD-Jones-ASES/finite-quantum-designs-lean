module

public import QuantumDesigns.GapCore

/-!
# The Kadison–Schwarz defect of a Kraus map is a sum of squares

For matrices `K_i` with `Σ_i K_i^* K_i = 1` and `C = Σ_i K_i^* X K_i`:
`Σ_i (X K_i − K_i C)^* (X K_i − K_i C) = Σ_i K_i^* X^* X K_i − (Σ_i K_i^* X^* K_i) C − C^* (Σ_i K_i^* X K_i)
+ C^* (Σ_i K_i^* K_i) C`, and `Σ_i K_i^* X^* K_i = C^*`, so the right side is `Σ_i K_i^* X^* X K_i − C^* C`
(`gp_schwarz_defect`; the inequality `Φ(X^* X) ≥ Φ(X)^* Φ(X)` of Kadison 1952 and Choi 1974, with its defect
written out). A sum of matrices `A_i^* A_i` with zero trace has every `A_i = 0`: `Tr(A^* A) = Σ_{a,b} ‖A_{ab}‖²`
(`gp_eq_zero_of_trace_sum_star_mul_self`). Hence if `C = X` (a fixed point) and the map preserves the trace of
`X^* X`, the defect has zero trace and every `X K_i = K_i X` (`gp_commute_of_fixed`).

In Weiner's Lemma 3.1 these two steps are Choi's Schwarz inequality for two-positive maps (Choi 1974, Corollary 2.8)
and Choi's multiplicative-domain theorem (Theorem 3.1); for a Kraus map the defect identity and the trace replace
both. The same elementary move, the squared Hilbert–Schmidt norm of each commutator in place of two-positivity and
the multiplicative domain, is made for general `n` in openai/math's
`lean/OAI/Analysis/MutuallyUnbiased/Completion/Kraus.lean` (openai/math@adc7f124, Apache-2.0;
`commutator_trace_identity`, `commute_of_kraus_fixed`), which was read here after this route was pinned.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- Pulling a left and a right factor out of a sum of matrix products: `Σ_i A (B_i) C = A (Σ_i B_i) C`. -/
theorem gp_sum_mul_mul_eq {d : ℕ} {ι : Type} [Fintype ι] (C A : Matrix (Fin d) (Fin d) ℂ) (B : ι → Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, A * B i * C = A * (∑ i, B i) * C := by
  rw [Finset.mul_sum, Finset.sum_mul]

open scoped ComplexOrder in
/-- If the traces `Tr(A_i^* A_i)` sum to zero, every `A_i` is zero: the traces are nonnegative, and
`Tr(A^* A) = 0` forces `A = 0`. -/
theorem gp_eq_zero_of_sum_trace {d : ℕ} {ι : Type} [Fintype ι] (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (h : ∑ i, Matrix.trace (star (A i) * A i) = 0) (i : ι) : A i = 0 := by
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ Matrix.trace (star (A j) * A j) := fun j _ => by
    rw [Matrix.star_eq_conjTranspose]
    exact (Matrix.posSemidef_conjTranspose_mul_self (A j)).trace_nonneg
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h i (Finset.mem_univ i)
  rw [Matrix.star_eq_conjTranspose] at h0
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0

/-- The Kadison–Schwarz defect of a Kraus map with `Σ_i K_i^* K_i = 1` is a sum of squares: with
`C = Σ_i K_i^* X K_i`, `Σ_i K_i^* X^* X K_i − C^* C = Σ_i (X K_i − K_i C)^* (X K_i − K_i C)`. -/
theorem gp_schwarz_defect {d : ℕ} {ι : Type} [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∑ i, star (K i) * K i = 1) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, star (K i) * (star X * X) * K i -
        star (∑ i, star (K i) * X * K i) * (∑ i, star (K i) * X * K i) =
      ∑ i, star (X * K i - K i * (∑ j, star (K j) * X * K j)) *
        (X * K i - K i * (∑ j, star (K j) * X * K j)) := by
  set C := ∑ i, star (K i) * X * K i with hC
  have hCs : star C = ∑ i, star (K i) * star X * K i := by
    rw [hC, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [star_mul, star_star, Matrix.mul_assoc]
  have hexp : ∀ i, star (X * K i - K i * C) * (X * K i - K i * C) =
      star (K i) * (star X * X) * K i - (star (K i) * star X * K i) * C -
        star C * (star (K i) * X * K i) + star C * (star (K i) * K i) * C := by
    intro i
    simp only [star_sub, star_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, gp_sum_mul_mul_eq C _ _, hK,
    ← hCs, ← hC, Matrix.mul_one]
  abel

/-- A finite sum of matrices `A_i^* A_i` with zero trace has every term zero. -/
theorem gp_eq_zero_of_trace_sum_star_mul_self {d : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (h : Matrix.trace (∑ i, star (A i) * A i) = 0) : ∀ i, A i = 0 := by
  intro i
  rw [Matrix.trace_sum] at h
  exact gp_eq_zero_of_sum_trace A h i

/-- A fixed point of a Kraus map (`Σ_i K_i^* K_i = 1`) that preserves the trace of `X^* X` commutes with every
Kraus operator. -/
theorem gp_commute_of_fixed {d : ℕ} {ι : Type} [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∑ i, star (K i) * K i = 1) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∑ i, star (K i) * X * K i = X)
    (htr : Matrix.trace (∑ i, star (K i) * (star X * X) * K i) = Matrix.trace (star X * X)) :
    ∀ i, X * K i = K i * X := by
  have hd := gp_schwarz_defect K hK X
  rw [hX] at hd
  have h0 : Matrix.trace (∑ i, star (X * K i - K i * X) * (X * K i - K i * X)) = 0 := by
    rw [← hd, Matrix.trace_sub, htr, sub_self]
  intro i
  have hi : X * K i - K i * X = 0 :=
    gp_eq_zero_of_trace_sum_star_mul_self (fun i => X * K i - K i * X) h0 i
  exact sub_eq_zero.1 hi

end QuantumDesigns
