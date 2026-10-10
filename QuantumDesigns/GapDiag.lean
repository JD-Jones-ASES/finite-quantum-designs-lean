module

public import QuantumDesigns.Defs

/-!
# Simultaneous diagonalization of commuting Hermitian matrices

A finite family of pairwise commuting Hermitian matrices `H_i` has a common orthonormal eigenbasis: the
operators `toEuclideanLin (H_i)` are symmetric (`Matrix.isHermitian_iff_isSymmetric`) and commute, so the joint
eigenspaces `⨅_i eigenspace (H_i) (χ i)` form an internal direct sum of `ℂ^d`
(`LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`), orthogonal across distinct `χ`
(`orthogonalFamily_iInf_eigenspaces`); collecting an orthonormal basis of each summand
(`DirectSum.IsInternal.collectedOrthonormalBasis`, `stdOrthonormalBasis`) gives an orthonormal basis of `ℂ^d` of
joint eigenvectors, reindexed along `Fin d`; the matrix `W` with these columns is unitary, and `W^* H_i W` is the
diagonal matrix of the eigenvalues `χ i` along the basis.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- A finite family of pairwise commuting Hermitian matrices is simultaneously unitarily diagonalizable. -/
theorem gp_simultaneous_diag {d : ℕ} {ι : Type} [Fintype ι] (H : ι → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ i, (H i).IsHermitian) (hc : ∀ i j, H i * H j = H j * H i) :
    ∃ W : UMat d, ∀ i, ∃ D : Fin d → ℂ,
      star (W : Matrix (Fin d) (Fin d) ℂ) * H i * (W : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal D := sorry

end QuantumDesigns
