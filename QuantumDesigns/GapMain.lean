module

public import QuantumDesigns.Bound
public import QuantumDesigns.GapCore
public import QuantumDesigns.GapPhi
public import QuantumDesigns.GapKraus
public import QuantumDesigns.GapDFT
public import QuantumDesigns.GapSchwarz
public import QuantumDesigns.GapDiag
public import QuantumDesigns.OddField

/-!
# Weiner's gap: `d` mutually unbiased bases of `ℂ^d` complete to `d + 1`

Given `B : Fin d → UMat d` pairwise unbiased (any `d`; no case split is needed): the Kraus family
`K_0, …, K_{d−1}` of `gp_exists_kraus`, orthogonal to every `w_{r,k}`, is flat (`gp_flat_of_orth` through
`gp_vec_w`), so `Φ(K_i) = K_i` and `Φ(K_i^*) = K_i^*` (`gp_Phi_of_flat`, `gp_flat_star`); `Φ` preserves traces
(`gp_Phi_trace`) and `Σ_i K_i^* K_i = 1`, so by `gp_commute_of_fixed` every `K_i` and every `K_i^*` commutes with
every `K_j`; hence the `2d` Hermitian matrices `K_i + K_i^*` and `i (K_i − K_i^*)` (`gp_herm`) pairwise commute
(`gp_herm_commute`; the adjoints commute by `Commute.star_star`), and `gp_simultaneous_diag` gives a unitary `W` in
which each of them is diagonal. A matrix diagonal in `W` commutes with every projector `Q_l = bd_proj W l`
(`gp_commute_proj_of_diag`: `X W = W D` and `W^* X = D W^*`), and `K_i = ((K_i + K_i^*) − i·(i (K_i − K_i^*)))/2`
(`gp_herm_recover`), so every `K_i` commutes with `Q_l` and `Φ(Q_l) = Σ_i K_i^* Q_l K_i = (Σ_i K_i^* K_i) Q_l = Q_l`.
By `gp_flat_Phi`, `Q_l` is flat: `gp_diag (B s) Q_l l' = Tr(Q_l)/d = 1/d` (`gp_trace_proj`), which
`gp_diag_eq_inner` and `bd_inner_proj` read as `‖((B s)^* W)_{l' l}‖² = 1/d`: `W` is unbiased to every `B s`. The
family `Fin.cons W B : Fin (d + 1) → UMat d` is then pairwise unbiased (the pairs inside `B` by hypothesis, the pairs
with `W` by the above and its symmetry `of_isUnbiased_symm`), and it keeps each `B r` at the index `r + 1`
(`Fin.cons_succ`): the extension form `exists_isMUBFamily_extension_internal`. The existence form
`hasCompleteMUBs_of_hasMUBs_self_internal` forgets the placement.

The corollaries: `d ≤ k` bases restrict to `d` (`hasMUBs_of_le_internal`); `IsMaxMUBCount d d` would put
`d + 1 ≤ d`; the dichotomy from the bound `k ≤ d + 1` (`hasMUBs_le_internal`); dimension six as the instance `d = 6`.

Neighbours: in openai/math's `lean/OAI/Analysis/MutuallyUnbiased/Completion/` (openai/math@adc7f1241b, Apache-2.0),
`six_extend_to_seven` is the instance `d = 6` of the completion, in its own vocabulary (orthonormal bases of
`EuclideanSpace ℂ (Fin 6)`), and its general-`n` lemmas `exists_joint_projection_basis` and
`exists_fixed_projection_basis` are the counterparts of `gp_simultaneous_diag` and of the fixed projectors `Q_l`
here; its `μ(6) ≤ 5` (`N6_le_five`) implies `not_isMaxMUBCount_six_six_internal`.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

open scoped ComplexConjugate

/-! ## The Hermitian parts of the Kraus family -/

/-- The Hermitian parts of a family of matrices: `K_j + K_j^*` at `inl j` and `i (K_j − K_j^*)` at `inr j`. -/
def gp_herm {d : ℕ} (K : Fin d → Matrix (Fin d) (Fin d) ℂ) : Fin d ⊕ Fin d → Matrix (Fin d) (Fin d) ℂ :=
  Sum.elim (fun j => K j + star (K j)) (fun j => Complex.I • (K j - star (K j)))

theorem gp_herm_isHermitian {d : ℕ} (K : Fin d → Matrix (Fin d) (Fin d) ℂ) (s : Fin d ⊕ Fin d) :
    (gp_herm K s).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  rcases s with j | j
  · simp only [gp_herm, Sum.elim_inl, Matrix.add_apply, Matrix.star_apply, star_add, star_star]
    ring
  · simp only [gp_herm, Sum.elim_inr, Matrix.smul_apply, Matrix.sub_apply, Matrix.star_apply, smul_eq_mul,
      star_mul', star_sub, star_star, hI]
    ring

/-- A family commuting with itself and with its adjoints has pairwise commuting Hermitian parts. -/
theorem gp_herm_commute {d : ℕ} (K : Fin d → Matrix (Fin d) (Fin d) ℂ)
    (h1 : ∀ i j, Commute (K i) (K j)) (h2 : ∀ i j, Commute (star (K i)) (K j)) (s t : Fin d ⊕ Fin d) :
    gp_herm K s * gp_herm K t = gp_herm K t * gp_herm K s := by
  have h3 : ∀ i j, Commute (K i) (star (K j)) := fun i j => (h2 j i).symm
  have h4 : ∀ i j, Commute (star (K i)) (star (K j)) := fun i j => (h1 i j).star_star
  have hp : ∀ i j, Commute (K i + star (K i)) (K j + star (K j)) := fun i j =>
    ((h1 i j).add_right (h3 i j)).add_left ((h2 i j).add_right (h4 i j))
  have hm : ∀ i j, Commute (K i + star (K i)) (K j - star (K j)) := fun i j =>
    ((h1 i j).sub_right (h3 i j)).add_left ((h2 i j).sub_right (h4 i j))
  have hm' : ∀ i j, Commute (K i - star (K i)) (K j - star (K j)) := fun i j =>
    ((h1 i j).sub_right (h3 i j)).sub_left ((h2 i j).sub_right (h4 i j))
  rcases s with i | i <;> rcases t with j | j <;> simp only [gp_herm, Sum.elim_inl, Sum.elim_inr]
  · exact (hp i j).eq
  · exact ((hm i j).smul_right Complex.I).eq
  · exact ((hm j i).symm.smul_left Complex.I).eq
  · exact (((hm' i j).smul_right Complex.I).smul_left Complex.I).eq

/-- A matrix is recovered from its Hermitian parts: `K_j = ((K_j + K_j^*) − i·(i (K_j − K_j^*)))/2`. -/
theorem gp_herm_recover {d : ℕ} (K : Fin d → Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    K j = (1 / 2 : ℂ) • (gp_herm K (Sum.inl j) - Complex.I • gp_herm K (Sum.inr j)) := by
  ext a b
  simp only [gp_herm, Sum.elim_inl, Sum.elim_inr, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    smul_eq_mul]
  linear_combination (1 / 2 * (K j a b - star (K j) a b)) * Complex.I_mul_I

/-! ## The common eigenbasis -/

/-- A matrix diagonal in the basis `W` commutes with every rank-one projector of `W`. -/
theorem gp_commute_proj_of_diag {d : ℕ} (W : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (D : Fin d → ℂ)
    (hX : star (W : Matrix (Fin d) (Fin d) ℂ) * X * (W : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal D)
    (l : Fin d) : Commute X (bd_proj W l) := by
  have hWW : (W : Matrix (Fin d) (Fin d) ℂ) * star (W : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp W.2
  have h1 : X * (W : Matrix (Fin d) (Fin d) ℂ) = (W : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal D := by
    rw [← hX]
    simp only [← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have h2 : star (W : Matrix (Fin d) (Fin d) ℂ) * X = Matrix.diagonal D * star (W : Matrix (Fin d) (Fin d) ℂ) := by
    rw [← hX]
    simp only [Matrix.mul_assoc, hWW, Matrix.mul_one]
  ext a b
  have e1 := congrFun (congrFun h1 a) l
  have e2 := congrFun (congrFun h2 l) b
  rw [Matrix.mul_diagonal] at e1
  rw [Matrix.diagonal_mul, Matrix.star_apply] at e2
  simp only [Matrix.mul_apply, Matrix.star_apply] at e1 e2
  show (X * bd_proj W l) a b = (bd_proj W l * X) a b
  simp only [Matrix.mul_apply, bd_proj]
  calc ∑ c, X a c * ((W : Matrix (Fin d) (Fin d) ℂ) c l * star ((W : Matrix (Fin d) (Fin d) ℂ) b l))
        = (∑ c, X a c * (W : Matrix (Fin d) (Fin d) ℂ) c l) * star ((W : Matrix (Fin d) (Fin d) ℂ) b l) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun c _ => by ring
    _ = (W : Matrix (Fin d) (Fin d) ℂ) a l *
          ∑ c, star ((W : Matrix (Fin d) (Fin d) ℂ) c l) * X c b := by
          rw [e1, e2]; ring
    _ = ∑ c, (W : Matrix (Fin d) (Fin d) ℂ) a l * star ((W : Matrix (Fin d) (Fin d) ℂ) c l) * X c b := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring

/-! ## Weiner's gap and its corollaries -/

/-- Weiner's Corollary 3.4 in its extension form: `d` mutually unbiased bases of `ℂ^d` extend, by one more basis,
to a complete set of `d + 1`, the given bases keeping their places. -/
theorem exists_isMUBFamily_extension_internal {d : ℕ} (B : Fin d → UMat d) (hB : IsMUBFamily B) :
    ∃ C : Fin (d + 1) → UMat d, IsMUBFamily C ∧ ∀ r : Fin d, C r.succ = B r := by
  obtain ⟨K, hKo, hKr, hKs⟩ := gp_exists_kraus B hB
  -- the Kraus operators are flat
  have hflat : ∀ i, gp_Flat B (K i) := fun i s l =>
    gp_flat_of_orth (B s) (K i) (fun k => by rw [gp_vec_w]; exact hKo i s k) l
  -- a flat matrix commutes with every Kraus operator
  have hfix : ∀ X, gp_Flat B X → ∀ j, Commute X (K j) := by
    intro X hX
    exact gp_commute_of_fixed K hKs X (by rw [← hKr X]; exact gp_Phi_of_flat B X hX)
      (by rw [← hKr (star X * X), gp_Phi_trace])
  have hA : ∀ i j, Commute (K i) (K j) := fun i => hfix (K i) (hflat i)
  have hA' : ∀ i j, Commute (star (K i)) (K j) := fun i => hfix _ (gp_flat_star B _ (hflat i))
  -- the common eigenbasis
  obtain ⟨W, hW⟩ := gp_simultaneous_diag (gp_herm K) (gp_herm_isHermitian K) (gp_herm_commute K hA hA')
  choose D hD using hW
  -- its projectors are fixed by Weiner's projection
  have hQ : ∀ l, gp_Phi B (bd_proj W l) = bd_proj W l := by
    intro l
    have hP : ∀ s, Commute (gp_herm K s) (bd_proj W l) := fun s =>
      gp_commute_proj_of_diag W _ (D s) (hD s) l
    have hc : ∀ i, Commute (bd_proj W l) (K i) := by
      intro i
      rw [gp_herm_recover K i]
      exact (((hP (Sum.inl i)).sub_left ((hP (Sum.inr i)).smul_left Complex.I)).smul_left
        (1 / 2 : ℂ)).symm
    rw [hKr]
    calc ∑ i, star (K i) * bd_proj W l * K i = ∑ i, star (K i) * K i * bd_proj W l := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Matrix.mul_assoc, (hc i).eq]
      _ = bd_proj W l := by rw [← Finset.sum_mul, hKs, Matrix.one_mul]
  -- hence flat, hence unbiased to every basis of the family
  have hWu : ∀ s, IsUnbiased (B s) W := by
    intro s l' l
    have h1 := gp_flat_Phi B hB (bd_proj W l) s l'
    rw [hQ, gp_diag_eq_inner, bd_inner_proj, gp_trace_proj] at h1
    change relativeUnitary (B s) W l' l * conj (relativeUnitary (B s) W l' l) = _ at h1
    rw [RCLike.mul_conj, one_div] at h1
    apply Complex.ofReal_injective
    push_cast at h1 ⊢
    exact h1
  refine ⟨Fin.cons W B, ?_, fun r => by simp⟩
  intro m n hmn
  induction m using Fin.cases with
  | zero =>
    induction n using Fin.cases with
    | zero => exact absurd rfl hmn
    | succ k => simpa using of_isUnbiased_symm (hWu k)
  | succ k =>
    induction n using Fin.cases with
    | zero => simpa using hWu k
    | succ k' =>
      have hk : k ≠ k' := fun h => hmn (by rw [h])
      simpa using hB hk

/-- Weiner's gap (Weiner 2013): `d` mutually unbiased bases of `ℂ^d` give a complete set of `d + 1` (the existence
form of Corollary 3.4). -/
theorem hasCompleteMUBs_of_hasMUBs_self_internal (d : ℕ) (h : HasMUBs d d) : HasCompleteMUBs d := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨C, hC, -⟩ := exists_isMUBFamily_extension_internal B hB
  exact ⟨C, hC⟩

theorem hasCompleteMUBs_of_le_hasMUBs_internal {d k : ℕ} (hk : d ≤ k) (h : HasMUBs d k) :
    HasCompleteMUBs d :=
  hasCompleteMUBs_of_hasMUBs_self_internal d (hasMUBs_of_le_internal hk h)

set_option linter.unusedVariables false in
theorem isMaxMUBCount_ne_self_internal (d : ℕ) (hd : 2 ≤ d) : ¬ IsMaxMUBCount d d := by
  intro h
  have h1 := h.2 (d + 1) (hasCompleteMUBs_of_hasMUBs_self_internal d h.1)
  omega

theorem isMaxMUBCount_dichotomy_internal (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (h : IsMaxMUBCount d k) :
    k = d + 1 ∨ k < d := by
  have h1 := hasMUBs_le_internal d hd k h.1
  rcases Nat.lt_or_ge k d with h2 | h2
  · exact Or.inr h2
  · left
    have h3 := h.2 (d + 1) (hasCompleteMUBs_of_le_hasMUBs_internal h2 h.1)
    omega

theorem not_isMaxMUBCount_six_six_internal : ¬ IsMaxMUBCount 6 6 :=
  isMaxMUBCount_ne_self_internal 6 (by norm_num)

end QuantumDesigns
