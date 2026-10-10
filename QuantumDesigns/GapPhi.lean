module

public import QuantumDesigns.GapCore

/-!
# Weiner's projection: flat image, flat fixed points

Inside one basis `U` (columns `e_j`, projectors `P_j = e_j e_j^*`): `P_j X P_j = ⟨e_j, X e_j⟩ P_j`
(`gp_proj_mul_mul_proj`), `Σ_j P_j = 1` (`gp_sum_proj`, unitarity), so the pinching is `Σ_j x_j P_j` with
`x_j = gp_diag U X j` and `Σ_j x_j = Tr X`; `Tr(P_j P_l) = δ_{jl}` inside a basis and `Tr(P^U_j P^V_l) = 1/d` across
two unbiased bases (`bd_inner_proj_same`, `bd_inner_proj_unbiased`, read through `gp_diag_eq_inner`). Hence the
diagonal of a pinching: in its own basis it is the diagonal of `X`; in a basis unbiased to it, every entry is
`Σ_i x_i/d = Tr(X)/d`. Therefore, for `d` mutually unbiased bases, the diagonal of `Φ(X) = X + Tr(X)·1 − Σ_r E_r(X)`
in the basis `s` at `l` is `x_{s,l} + Tr X − x_{s,l} − (d − 1) Tr X/d = Tr X/d`: `Φ(X)` is flat (`gp_flat_Phi`).
If `X` is flat, every `E_r(X) = (Tr X/d) Σ_j P_{r,j} = (Tr X/d)·1`, so `Φ(X) = X` (`gp_Phi_of_flat`). The trace:
`Tr Φ(X) = Tr X + d Tr X − d Tr X`; `Φ(1) = 1`; `Φ` commutes with the adjoint (each pinching does, `P_j` being
Hermitian); flatness passes to the adjoint (`Tr(P X^*) = conj Tr(P X)`, `Tr X^* = conj Tr X`) and holds for `1`.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

theorem gp_diag_apply {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    gp_diag U X j = ∑ a : Fin d, ∑ b : Fin d,
      star ((U : Matrix (Fin d) (Fin d) ℂ) a j) * X a b * (U : Matrix (Fin d) (Fin d) ℂ) b j := sorry

theorem gp_proj_mul_mul_proj {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    bd_proj U j * X * bd_proj U j = gp_diag U X j • bd_proj U j := sorry

theorem gp_sum_proj {d : ℕ} (U : UMat d) : ∑ j : Fin d, bd_proj U j = 1 := sorry

theorem gp_trace_proj {d : ℕ} (U : UMat d) (j : Fin d) : Matrix.trace (bd_proj U j) = 1 := sorry

theorem gp_star_proj {d : ℕ} (U : UMat d) (j : Fin d) : star (bd_proj U j) = bd_proj U j := sorry

theorem gp_pinch_eq {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    gp_pinch U X = ∑ j : Fin d, gp_diag U X j • bd_proj U j := sorry

theorem gp_sum_diag {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ j : Fin d, gp_diag U X j = Matrix.trace X := sorry

theorem gp_diag_proj_same {d : ℕ} (U : UMat d) (j l : Fin d) :
    gp_diag U (bd_proj U l) j = if j = l then 1 else 0 := sorry

theorem gp_diag_proj_unbiased {d : ℕ} {U V : UMat d} (h : IsUnbiased U V) (j l : Fin d) :
    gp_diag U (bd_proj V l) j = (d : ℂ)⁻¹ := sorry

theorem gp_diag_pinch_same {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (l : Fin d) :
    gp_diag U (gp_pinch U X) l = gp_diag U X l := sorry

theorem gp_diag_pinch_unbiased {d : ℕ} {U V : UMat d} (h : IsUnbiased U V) (X : Matrix (Fin d) (Fin d) ℂ)
    (l : Fin d) : gp_diag U (gp_pinch V X) l = Matrix.trace X / d := sorry

theorem gp_Phi_one {d : ℕ} (B : Fin d → UMat d) : gp_Phi B 1 = 1 := sorry

theorem gp_Phi_trace {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (gp_Phi B X) = Matrix.trace X := sorry

theorem gp_Phi_star {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    gp_Phi B (star X) = star (gp_Phi B X) := sorry

/-- Weiner's projection maps into the flat matrices. -/
theorem gp_flat_Phi {d : ℕ} (B : Fin d → UMat d) (hB : IsMUBFamily B) (X : Matrix (Fin d) (Fin d) ℂ) :
    gp_Flat B (gp_Phi B X) := sorry

/-- Weiner's projection fixes the flat matrices. -/
theorem gp_Phi_of_flat {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (hX : gp_Flat B X) :
    gp_Phi B X = X := sorry

theorem gp_flat_star {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (hX : gp_Flat B X) :
    gp_Flat B (star X) := sorry

theorem gp_flat_one {d : ℕ} (B : Fin d → UMat d) : gp_Flat B 1 := sorry

end QuantumDesigns
