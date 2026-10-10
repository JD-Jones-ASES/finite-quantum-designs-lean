module

public import QuantumDesigns.GapCore
public import QuantumDesigns.GapPhi

/-!
# The Kraus form of Weiner's projection

**Weiner's Lemma 2.1.** For an orthonormal basis `b` of the matrix space (Hilbert–Schmidt inner product, through
the flattening `bd_vec`), `Σ_i b_i^* X b_i = Tr(X)·1`: the entry `(p, q)` of the left side is
`Σ_{a,c} X_{ac} Σ_i conj((b_i)_{ap}) (b_i)_{cq}`, and the inner sum is the Parseval identity
`⟨E_{ap}, E_{cq}⟩ = Σ_i ⟨E_{ap}, b_i⟩ ⟨b_i, E_{cq}⟩` for the matrix units (`OrthonormalBasis.sum_inner_mul_inner`),
which is `δ_{ac} δ_{pq}` (`gp_onb_sum`).

**The weighted projectors conjugate to the pinching.** `w_k = Σ_j ζ^{j(k+1)} P_j` gives
`w_k^* X w_k = Σ_{j,j'} ζ^{(j'−j)(k+1)} P_j X P_{j'}`; summing over `k + 1 ∈ {0, …, d − 1}` (the term `k + 1 = 0`
is `1·X·1 = X`) the geometric sums `Σ_m ζ^{(j'−j)m}` are `d δ_{jj'}` (`bd_geom_zero`), so
`Σ_{k < d−1} w_k^* X w_k = d Σ_j P_j X P_j − X` (`gp_w_sum`).

**Lemma 3.2 (the Kraus form).** For `d` mutually unbiased bases the `d(d − 1)` vectors `w_{r,k}/√d` are orthonormal
(`bd_inner_w_same_ne`, `bd_inner_w_diff`, `bd_inner_w_self`) in the space of dimension `d² = d(d − 1) + d`, so they
extend to an orthonormal basis indexed by `Fin d × Fin (d − 1) ⊕ Fin d`
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, with the index set `Fin d × Fin (d − 1) ⊕ Fin d` and the
subset `range Sum.inl`); let `K_i` (`i : Fin d`) be the matrices of the added vectors. Lemma 2.1 for this basis
and `gp_w_sum` for each `r` give `Σ_i K_i^* X K_i = Tr(X)·1 − Σ_r (E_r(X) − X/d) = Φ(X)`; the `K_i` are orthogonal to
every `w_{r,k}`; and `Σ_i K_i^* K_i = Φ(1) = 1` (`gp_Phi_one`).
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- Weiner's Lemma 2.1: an orthonormal basis of the flattened matrix space satisfies `Σ_i b_i^* X b_i = Tr(X)·1`. -/
theorem gp_onb_sum {d : ℕ} {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ (Fin d × Fin d))) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, star (gp_unvec (b i)) * X * gp_unvec (b i) = Matrix.trace X • (1 : Matrix (Fin d) (Fin d) ℂ) := sorry

/-- The weighted projectors of one basis conjugate to its pinching: `Σ_{k<d−1} w_k^* X w_k = d·Σ_j P_j X P_j − X`. -/
theorem gp_w_sum {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k : Fin (d - 1), star (gp_w U k) * X * gp_w U k = (d : ℂ) • gp_pinch U X - X := sorry

/-- The Kraus form of Weiner's projection (Weiner 2013, Lemma 3.2): for `d` mutually unbiased bases of `ℂ^d` there
are matrices `K_0, …, K_{d−1}`, each orthogonal (Hilbert–Schmidt) to every weighted projector of every basis, with
`Φ(X) = Σ_i K_i^* X K_i` for every `X` and `Σ_i K_i^* K_i = 1`. -/
theorem gp_exists_kraus {d : ℕ} (B : Fin d → UMat d) (hB : IsMUBFamily B) :
    ∃ K : Fin d → Matrix (Fin d) (Fin d) ℂ,
      (∀ i r k, inner ℂ (bd_w B r k) (bd_vec (K i)) = 0) ∧
      (∀ X, gp_Phi B X = ∑ i, star (K i) * X * K i) ∧
      ∑ i, star (K i) * K i = 1 := sorry

end QuantumDesigns
