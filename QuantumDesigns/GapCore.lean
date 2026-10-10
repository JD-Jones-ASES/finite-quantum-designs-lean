module

public import QuantumDesigns.Bound

/-!
# Weiner's gap: the objects

For `d` mutually unbiased bases `B : Fin d → UMat d` of `ℂ^d` (Weiner 2013), with `P_{r,j} = bd_proj (B r) j` the
rank-one projectors: `gp_diag U X j = Tr(P_j X) = ⟨e_j, X e_j⟩` is the diagonal of `X` in the basis `U`;
`gp_pinch U X = Σ_j P_j X P_j` is the pinching (the diagonal part of `X` in `U`); `gp_w U k = Σ_j ζ^{j(k+1)} P_j`
(`k < d − 1`, `ζ = exp(2πi/d)`) are the traceless combinations whose flattenings are `bd_w`; Weiner's projection
`gp_Phi B X = X + Tr(X)·1 − Σ_r gp_pinch (B r) X` is the orthogonal projection of the matrix space onto the
complement of the span of all `w_{r,k}`; and `gp_Flat B X` says that `X` has the constant diagonal `Tr(X)/d` in
every basis of the family (the complement, described by its diagonals).

The route to the theorem: `gp_Phi` maps into the flat matrices and fixes them (`GapPhi`); it has a Kraus form
`Σ_i K_i^* X K_i` over an orthonormal family completing the `w_{r,k}/√d` to a basis of the matrix space
(`GapKraus`, Weiner's Lemmas 2.1 and 3.2); the `K_i` are flat by Fourier inversion on the diagonal (`GapDFT`);
the Kadison–Schwarz defect of a Kraus map is a sum of squares, so a flat fixed point commutes with every `K_i`
(`GapSchwarz`); a commuting family of Hermitian matrices is simultaneously diagonalizable (`GapDiag`); the
projectors of the common eigenbasis are fixed by `gp_Phi`, hence flat, hence unbiased to every basis of the
family (`GapMain`).
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- The diagonal entry of `X` in the basis `U` at column `j`: `Tr(P_j X) = ⟨e_j, X e_j⟩`. -/
def gp_diag {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) : ℂ :=
  Matrix.trace (bd_proj U j * X)

/-- The pinching of `X` to the basis `U`: `Σ_j P_j X P_j`. -/
def gp_pinch {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ j : Fin d, bd_proj U j * X * bd_proj U j

/-- The weighted projector `w_k = Σ_j ζ^{j(k+1)} P_j` of one basis, as a matrix (`bd_w` is its flattening). -/
def gp_w {d : ℕ} (U : UMat d) (k : Fin (d - 1)) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ j : Fin d, (bd_zeta d ^ ((j : ℕ) * ((k : ℕ) + 1))) • bd_proj U j

/-- Weiner's projection for `d` bases of `ℂ^d`: `Φ(X) = X + Tr(X)·1 − Σ_r Σ_j P_{r,j} X P_{r,j}`. -/
def gp_Phi {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  X + Matrix.trace X • (1 : Matrix (Fin d) (Fin d) ℂ) - ∑ r : Fin d, gp_pinch (B r) X

/-- `X` is flat for the family: its diagonal in every basis of the family is the constant `Tr(X)/d`. -/
def gp_Flat {d : ℕ} (B : Fin d → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ s : Fin d, ∀ l : Fin d, gp_diag (B s) X l = Matrix.trace X / d

/-- The inverse of the flattening `bd_vec`. -/
def gp_unvec {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => v (a, b)

theorem gp_unvec_vec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : gp_unvec (bd_vec A) = A := sorry

theorem gp_vec_unvec {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d)) : bd_vec (gp_unvec v) = v := sorry

/-- The flattening of `gp_w` is `bd_w`. -/
theorem gp_vec_w {d : ℕ} (B : Fin d → UMat d) (r : Fin d) (k : Fin (d - 1)) :
    bd_vec (gp_w (B r) k) = bd_w B r k := sorry

/-- The Hilbert–Schmidt inner product of two flattened matrices is `Tr(A^* X)`. -/
theorem gp_inner_vec_eq_trace {d : ℕ} (A X : Matrix (Fin d) (Fin d) ℂ) :
    inner ℂ (bd_vec A) (bd_vec X) = Matrix.trace (star A * X) := sorry

/-- The diagonal entry is the Hilbert–Schmidt inner product with the projector (`P_j` is Hermitian). -/
theorem gp_diag_eq_inner {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    gp_diag U X j = inner ℂ (bd_vec (bd_proj U j)) (bd_vec X) := sorry

end QuantumDesigns
