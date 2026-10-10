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
      star ((U : Matrix (Fin d) (Fin d) ℂ) a j) * X a b * (U : Matrix (Fin d) (Fin d) ℂ) b j := by
  simp only [gp_diag, Matrix.trace, Matrix.diag, Matrix.mul_apply, bd_proj]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem gp_proj_mul_mul_proj {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    bd_proj U j * X * bd_proj U j = gp_diag U X j • bd_proj U j := by
  ext a b
  rw [Matrix.smul_apply, gp_diag_apply, smul_eq_mul]
  simp only [Matrix.mul_apply, bd_proj, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem gp_sum_proj {d : ℕ} (U : UMat d) : ∑ j : Fin d, bd_proj U j = 1 := by
  ext a b
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp U.2) a) b
  simp only [Matrix.mul_apply, Matrix.star_apply] at h
  rw [Matrix.sum_apply]
  simpa [bd_proj] using h

theorem gp_trace_proj {d : ℕ} (U : UMat d) (j : Fin d) : Matrix.trace (bd_proj U j) = 1 := by
  have h := congrFun (congrFun (bd_rel_self U) j) j
  simp only [relativeUnitary, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← h]
  simp only [Matrix.trace, Matrix.diag, bd_proj]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem gp_star_proj {d : ℕ} (U : UMat d) (j : Fin d) : star (bd_proj U j) = bd_proj U j :=
  gp_proj_star U j

theorem gp_pinch_eq {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    gp_pinch U X = ∑ j : Fin d, gp_diag U X j • bd_proj U j :=
  Finset.sum_congr rfl fun j _ => gp_proj_mul_mul_proj U X j

/-! ### The diagonal is linear in the matrix -/

theorem gp_diag_add {d : ℕ} (U : UMat d) (X Y : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    gp_diag U (X + Y) j = gp_diag U X j + gp_diag U Y j := by
  simp only [gp_diag, Matrix.mul_add, Matrix.trace_add]

theorem gp_diag_sub {d : ℕ} (U : UMat d) (X Y : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    gp_diag U (X - Y) j = gp_diag U X j - gp_diag U Y j := by
  simp only [gp_diag, Matrix.mul_sub, Matrix.trace_sub]

theorem gp_diag_smul {d : ℕ} (U : UMat d) (c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    gp_diag U (c • X) j = c * gp_diag U X j := by
  simp only [gp_diag, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem gp_diag_sum {d : ℕ} {ι : Type*} (U : UMat d) (s : Finset ι)
    (f : ι → Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    gp_diag U (∑ i ∈ s, f i) j = ∑ i ∈ s, gp_diag U (f i) j := by
  simp only [gp_diag, Finset.mul_sum, Matrix.trace_sum]

theorem gp_diag_one {d : ℕ} (U : UMat d) (j : Fin d) : gp_diag U 1 j = 1 := by
  rw [gp_diag, mul_one, gp_trace_proj]

theorem gp_trace_star {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (star X) = star (Matrix.trace X) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]

theorem gp_diag_star {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    gp_diag U (star X) j = star (gp_diag U X j) := by
  rw [gp_diag, gp_diag]
  conv_lhs => rw [← gp_proj_star U j, ← star_mul, gp_trace_star, Matrix.trace_mul_comm]

theorem gp_sum_diag {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ j : Fin d, gp_diag U X j = Matrix.trace X := by
  unfold gp_diag
  rw [← Matrix.trace_sum, ← Finset.sum_mul, gp_sum_proj, one_mul]

theorem gp_diag_proj_same {d : ℕ} (U : UMat d) (j l : Fin d) :
    gp_diag U (bd_proj U l) j = if j = l then 1 else 0 := by
  rw [gp_diag_eq_inner, bd_inner_proj_same]

theorem gp_diag_proj_unbiased {d : ℕ} {U V : UMat d} (h : IsUnbiased U V) (j l : Fin d) :
    gp_diag U (bd_proj V l) j = (d : ℂ)⁻¹ := by
  rw [gp_diag_eq_inner, bd_inner_proj_unbiased U V h]

theorem gp_diag_pinch_same {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (l : Fin d) :
    gp_diag U (gp_pinch U X) l = gp_diag U X l := by
  rw [gp_pinch_eq, gp_diag_sum]
  simp only [gp_diag_smul, gp_diag_proj_same, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem gp_diag_pinch_unbiased {d : ℕ} {U V : UMat d} (h : IsUnbiased U V) (X : Matrix (Fin d) (Fin d) ℂ)
    (l : Fin d) : gp_diag U (gp_pinch V X) l = Matrix.trace X / d := by
  rw [gp_pinch_eq, gp_diag_sum]
  simp only [gp_diag_smul, gp_diag_proj_unbiased h]
  rw [← Finset.sum_mul, gp_sum_diag, div_eq_mul_inv]

theorem gp_trace_pinch {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (gp_pinch U X) = Matrix.trace X := by
  rw [gp_pinch_eq, Matrix.trace_sum]
  simp only [Matrix.trace_smul, gp_trace_proj, smul_eq_mul, mul_one]
  exact gp_sum_diag U X

theorem gp_pinch_one {d : ℕ} (U : UMat d) : gp_pinch U 1 = 1 := by
  rw [gp_pinch_eq]
  simp only [gp_diag_one, one_smul]
  exact gp_sum_proj U

theorem gp_pinch_star {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    gp_pinch U (star X) = star (gp_pinch U X) := by
  simp only [gp_pinch, star_sum, star_mul, gp_proj_star, mul_assoc]

theorem gp_Phi_one {d : ℕ} (B : Fin d → UMat d) : gp_Phi B 1 = 1 := by
  simp only [gp_Phi, gp_pinch_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Matrix.trace_one]
  rw [Nat.cast_smul_eq_nsmul ℂ, add_sub_cancel_right]

theorem gp_Phi_trace {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (gp_Phi B X) = Matrix.trace X := by
  simp only [gp_Phi, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum, gp_trace_pinch,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

theorem gp_Phi_star {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    gp_Phi B (star X) = star (gp_Phi B X) := by
  simp only [gp_Phi, star_sub, star_add, star_smul, star_one, star_sum, gp_trace_star, gp_pinch_star]

/-- Weiner's projection maps into the flat matrices. -/
theorem gp_flat_Phi {d : ℕ} (B : Fin d → UMat d) (hB : IsMUBFamily B) (X : Matrix (Fin d) (Fin d) ℂ) :
    gp_Flat B (gp_Phi B X) := by
  intro s l
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos s).ne'
  rw [gp_Phi_trace]
  have hsum : ∑ r : Fin d, gp_diag (B s) (gp_pinch (B r) X) l
      = gp_diag (B s) X l + ((d : ℂ) - 1) * (Matrix.trace X / d) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), gp_diag_pinch_same]
    congr 1
    rw [Finset.sum_congr rfl fun r hr =>
      gp_diag_pinch_unbiased (hB (Finset.ne_of_mem_erase hr).symm) X l]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (Fin.pos s), Nat.cast_one]
  simp only [gp_Phi, gp_diag_sub, gp_diag_add, gp_diag_smul, gp_diag_one, gp_diag_sum, hsum]
  field_simp
  ring

/-- Weiner's projection fixes the flat matrices. -/
theorem gp_Phi_of_flat {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (hX : gp_Flat B X) :
    gp_Phi B X = X := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hp : ∀ r, gp_pinch (B r) X = (Matrix.trace X / d) • 1 := by
    intro r
    rw [gp_pinch_eq]
    simp only [hX r, ← Finset.smul_sum, gp_sum_proj]
  have hc : (d : ℂ) * (Matrix.trace X / d) = Matrix.trace X := by field_simp
  simp only [gp_Phi, hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc, add_sub_cancel_right]

theorem gp_flat_star {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (hX : gp_Flat B X) :
    gp_Flat B (star X) := by
  intro s l
  rw [gp_diag_star, hX s l, gp_trace_star, star_div₀, star_natCast]

theorem gp_flat_one {d : ℕ} (B : Fin d → UMat d) : gp_Flat B 1 := by
  intro s l
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos s).ne'
  rw [gp_diag_one, Matrix.trace_one, Fintype.card_fin, div_self hd]

end QuantumDesigns
