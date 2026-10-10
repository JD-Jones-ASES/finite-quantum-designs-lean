module

public import QuantumDesigns.Defs

/-!
# Simultaneous diagonalization of commuting Hermitian matrices

A finite family of pairwise commuting Hermitian matrices `H_i` has a common orthonormal eigenbasis: the
operators `toEuclideanLin (H_i)` are symmetric (`Matrix.isSymmetric_toEuclideanLin_iff`) and commute
(`Matrix.toLpLin_mul_same`), so the joint eigenspaces `⨅_i eigenspace (H_i) (χ i)` form an internal direct sum of
`ℂ^d` (`LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`), orthogonal across distinct `χ`
(`orthogonalFamily_iInf_eigenspaces`). Only finitely many of them are nonzero
(`iSupIndep.fintypeNeBotOfFiniteDimensional`), and the nonzero ones still form an internal direct sum
(`DirectSum.isInternal_ne_bot_iff`); an orthonormal basis of `ℂ^d` indexed by `Fin d` and subordinate to them
(`DirectSum.IsInternal.subordinateOrthonormalBasis`, built from `stdOrthonormalBasis` of each summand) consists of
joint eigenvectors. The matrix `W` with these columns is unitary
(`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`), `H_i W = W D_i` column by column with `D_i` the
diagonal matrix of the eigenvalues `χ i` along the basis, and so `W^* H_i W = D_i`.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- A finite family of pairwise commuting Hermitian matrices is simultaneously unitarily diagonalizable. -/
theorem gp_simultaneous_diag {d : ℕ} {ι : Type} [Fintype ι] (H : ι → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ i, (H i).IsHermitian) (hc : ∀ i j, H i * H j = H j * H i) :
    ∃ W : UMat d, ∀ i, ∃ D : Fin d → ℂ,
      star (W : Matrix (Fin d) (Fin d) ℂ) * H i * (W : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal D := by
  classical
  let T : ι → Module.End ℂ (EuclideanSpace ℂ (Fin d)) := fun i => Matrix.toEuclideanLin (H i)
  have hT : ∀ i, (T i).IsSymmetric := fun i => Matrix.isSymmetric_toEuclideanLin_iff.mpr (hH i)
  have hC : Pairwise (Function.onFun Commute T) := by
    intro i j _
    show T i * T j = T j * T i
    simp only [T, Module.End.mul_eq_comp, ← Matrix.toLpLin_mul_same, hc i j]
  have hV := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT hC
  have hV' := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = d := finrank_euclideanSpace_fin
  let V : (ι → ℂ) → Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    fun χ => ⨅ j, Module.End.eigenspace (T j) (χ j)
  let _ : Fintype {χ // V χ ≠ ⊥} := hV.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hVk : DirectSum.IsInternal (fun k : {χ // V χ ≠ ⊥} => V k.1) :=
    DirectSum.isInternal_ne_bot_iff.mpr hV
  have hVk' : OrthogonalFamily ℂ (fun k : {χ // V χ ≠ ⊥} => V k.1)
      (fun k => (V k.1).subtypeₗᵢ) := hV'.comp Subtype.val_injective
  let b := hVk.subordinateOrthonormalBasis hn hVk'
  let χ : Fin d → ι → ℂ := fun a => (hVk.subordinateOrthonormalBasisIndex hn a hVk').1
  have hmem : ∀ a, b a ∈ ⨅ j, Module.End.eigenspace (T j) (χ a j) := fun a =>
    hVk.subordinateOrthonormalBasis_subordinate hn a hVk'
  have heig : ∀ i a, (H i).mulVec (b a).ofLp = χ a i • (b a).ofLp := by
    intro i a
    have h1 := (Submodule.mem_iInf _).mp (hmem a) i
    rw [Module.End.mem_eigenspace_iff] at h1
    have h2 := congrArg WithLp.ofLp h1
    simpa [T, Matrix.toLpLin_apply] using h2
  let W : UMat d := ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hW : ∀ x l, (W : Matrix (Fin d) (Fin d) ℂ) x l = (b l).ofLp x := fun x l => rfl
  refine ⟨W, fun i => ⟨fun l => χ l i, ?_⟩⟩
  have hHW : H i * (W : Matrix (Fin d) (Fin d) ℂ) =
      (W : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun l => χ l i) := by
    ext x l
    rw [Matrix.mul_diagonal, hW, Matrix.mul_apply]
    have := congrFun (heig i l) x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [hW, this]
    ring
  rw [mul_assoc, hHW, ← mul_assoc, Unitary.star_mul_self_of_mem W.2, one_mul]

end QuantumDesigns
