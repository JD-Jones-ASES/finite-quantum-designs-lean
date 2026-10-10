module

public import QuantumDesigns.GapCore

/-!
# Fourier inversion on the diagonal

In a basis `U` with projectors `P_j`, the Hilbert–Schmidt inner product of `w_k = Σ_j ζ^{j(k+1)} P_j` with `X` is
`Σ_j conj(ζ^{j(k+1)}) x_j`, `x_j = gp_diag U X j = ⟨P_j, X⟩` (`gp_diag_eq_inner`): the discrete Fourier transform of
the diagonal `j ↦ x_j` at the frequency `k + 1 ∈ {1, …, d − 1}`. If every such transform vanishes, Fourier inversion
`x_l = (1/d) Σ_{m<d} ζ^{lm} Σ_j conj(ζ^{jm}) x_j` (the inner sums are `Σ_j ζ^{(l−j)m}`, which is `d δ_{jl}` summed
over `m`, `bd_geom_zero`) keeps only the frequency `m = 0`: `x_l = (1/d) Σ_j x_j = Tr(X)/d` (`gp_sum_diag`, or
directly `Σ_j Tr(P_j X) = Tr X` from `Σ_j P_j = 1`).
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- A matrix orthogonal (Hilbert–Schmidt) to every weighted projector `w_k`, `k < d − 1`, of a basis has the
constant diagonal `Tr(X)/d` in that basis. -/
theorem gp_flat_of_orth {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ k : Fin (d - 1), inner ℂ (bd_vec (gp_w U k)) (bd_vec X) = 0) (l : Fin d) :
    gp_diag U X l = Matrix.trace X / d := sorry

end QuantumDesigns
