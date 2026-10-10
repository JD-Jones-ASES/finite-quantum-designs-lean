module

public import QuantumDesigns.Bound
public import QuantumDesigns.Gerzon

/-!
# Reconstruction: complete sets of mutually unbiased bases and SIC families are informationally complete

**A complete set of `d + 1` mutually unbiased bases** (after Ivanović 1981 and Wootters–Fields 1989, in the form
of Scott 2006, eqs. (9) and (56), where it follows from the 2-design identity; here from linear independence). With
`P_{s,l} = bd_proj (B s) l` and `T(X) = Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1` (`rc_T`, a linear map), it suffices
to check `T(X) = X` on a spanning family. The `d²` flattened vectors `1, w_{r,k}` of `bd_fam B` are linearly
independent (the family of `hasMUBs_le_internal`, with `m = d + 1`: `1 + (d + 1)(d − 1) = d²`; `rc_fam_linIndep`),
so the matrices behind them (`rc_F`: the identity and `Σ_j ζ^{j(k+1)} P_{r,j}`) are linearly independent and span
the matrix space (`LinearIndependent.of_comp` through the flattening, `LinearIndependent.span_eq_top_of_card_eq_finrank'`,
`Module.finrank_matrix`; `rc_F_span`). By linearity it remains to check `T(1) = 1` (`Σ_l P_{s,l} = 1` from
`U U^* = 1`, `Tr P_{s,l} = 1`, `Tr 1 = d`; `rc_T_one`) and `T(P_{r,j}) = P_{r,j}` (`Tr(P_{r,j} P_{s,l})` is the
Hilbert–Schmidt inner product, `δ_{jl}` for `s = r` and `1/d` for `s ≠ r`, `bd_inner_proj_same`,
`bd_inner_proj_unbiased`; the other `d` bases each contribute `(1/d) Σ_l P_{s,l} = (1/d)·1`, in all `1`, cancelled by
`Tr(P_{r,j})·1 = 1`; `rc_T_proj`). `d = 0` is the empty matrix (`mub_reconstruction_internal`).

**A SIC family** (informational completeness: Renes–Blume-Kohout–Scott–Caves 2004, §II, through the Gram matrix of
the projectors; the coefficients: Scott 2006, eq. (9) in the proof of Theorem 4, and Appleby–Dang–Fuchs, eq. (3),
for states). The `d²` projectors `P_i = gz_P (φ_i)` are linearly
independent: from `Σ_i g_i P_i = 0` the trace gives `Σ_i g_i = 0` and the pairing with `φ_j` (`gz_pair_eq`) gives
`(1 − c) g_j = 0`, with `c = 1/(d + 1) ≠ 1` (`rc_linIndep`). Being `d²` of them, they span the matrix space; writing
`X = Σ_i a_i P_i`, the pairing gives `Tr(X P_j) = (1 − c) a_j + c Σ_i a_i` (`rc_trace_eq_pair`) and the trace gives
`Tr X = Σ_i a_i`, so `a_j = ((d + 1) Tr(X P_j) − Tr X)/d` (`sic_reconstruction_internal`; `d = 0` is the empty
matrix).
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-! ## SIC families -/

/-- `Tr(X ψψ†) = ψ† X ψ`. -/
lemma rc_trace_eq_pair {d : ℕ} (ψ : StateVector d) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (X * gz_P ψ) = gz_pair ψ X := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gz_P, Matrix.vecMulVec_apply, gz_pair_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The projectors of a normalized family with constant pairwise squared overlap `c ≠ 1` are linearly independent,
whatever their number: the trace of a vanishing combination is its coefficient sum. -/
lemma rc_linIndep {d N : ℕ} {c : ℝ} (hc : c ≠ 1) {Φ : Fin N → StateVector d}
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    LinearIndependent ℂ (fun i => gz_P (Φ i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hS : ∑ i, g i = 0 := by
    have h := congrArg Matrix.trace hg
    rw [Matrix.trace_sum, Matrix.trace_zero] at h
    simpa only [Matrix.trace_smul, gz_trace_P (hn _), smul_eq_mul, mul_one] using h
  intro j
  have h := gz_pair_eq hn ho g j
  rw [hg, map_zero, hS, mul_zero, zero_add] at h
  have h1c : (1 - (c : ℂ)) ≠ 0 := by
    have : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    exact_mod_cast this
  exact (mul_eq_zero.mp h.symm).resolve_left h1c

/-! ## Complete sets of mutually unbiased bases -/

/-- The projector of the statement is `bd_proj`. -/
lemma rc_proj_eq {d : ℕ} (U : UMat d) (l : Fin d) :
    Matrix.vecMulVec (fun a => (U : Matrix (Fin d) (Fin d) ℂ) a l)
      (fun b => star ((U : Matrix (Fin d) (Fin d) ℂ) b l)) = bd_proj U l := by
  ext a b
  simp [bd_proj, Matrix.vecMulVec_apply]

/-- `Tr P_j = 1`. -/
lemma rc_trace_proj {d : ℕ} (U : UMat d) (j : Fin d) : Matrix.trace (bd_proj U j) = 1 := by
  have h := congrFun (congrFun (bd_rel_self U) j) j
  simp only [relativeUnitary, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← h]
  simp only [Matrix.trace, Matrix.diag, bd_proj]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The projectors of one basis sum to the identity (`U U^* = 1`). -/
lemma rc_sum_proj {d : ℕ} (U : UMat d) : ∑ l, bd_proj U l = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp U.2
  ext a b
  rw [Matrix.sum_apply, ← h, Matrix.mul_apply]
  simp only [bd_proj, Matrix.star_apply]

/-- `Tr(P_j^U P_l^V)` is the Hilbert–Schmidt inner product of the two projectors. -/
lemma rc_trace_mul_proj {d : ℕ} (U V : UMat d) (j l : Fin d) :
    Matrix.trace (bd_proj U j * bd_proj V l) =
      inner ℂ (bd_vec (bd_proj U j)) (bd_vec (bd_proj V l)) := by
  rw [bd_inner_vec]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [bd_proj, star_mul', star_star]
  ring

/-- The reconstruction map `X ↦ Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1`. -/
def rc_T {d : ℕ} (B : Fin (d + 1) → UMat d) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := ∑ s, ∑ l, Matrix.trace (X * bd_proj (B s) l) • bd_proj (B s) l - Matrix.trace X • 1
  map_add' X Y := by
    simp only [Matrix.add_mul, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c X := by
    simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum,
      RingHom.id_apply, smul_sub]

lemma rc_T_apply {d : ℕ} (B : Fin (d + 1) → UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    rc_T B X = ∑ s, ∑ l, Matrix.trace (X * bd_proj (B s) l) • bd_proj (B s) l - Matrix.trace X • 1 :=
  rfl

/-- `T(1) = 1`. -/
lemma rc_T_one {d : ℕ} (B : Fin (d + 1) → UMat d) : rc_T B 1 = 1 := by
  rw [rc_T_apply]
  simp only [Matrix.one_mul, rc_trace_proj, one_smul, rc_sum_proj, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Matrix.trace_one]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  push_cast
  rw [add_smul, one_smul, add_sub_cancel_left]

/-- `T(P_{r,j}) = P_{r,j}`. -/
lemma rc_T_proj {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B) (r : Fin (d + 1)) (j : Fin d) :
    rc_T B (bd_proj (B r) j) = bd_proj (B r) j := by
  have hd : d ≠ 0 := by have := j.2; omega
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hs : ∀ s, ∑ l, Matrix.trace (bd_proj (B r) j * bd_proj (B s) l) • bd_proj (B s) l =
      (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) +
        if s = r then bd_proj (B r) j - (d : ℂ)⁻¹ • 1 else 0 := by
    intro s
    by_cases hsr : s = r
    · subst hsr
      simp only [rc_trace_mul_proj, bd_inner_proj_same, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      abel
    · simp only [rc_trace_mul_proj, bd_inner_proj_unbiased (B r) (B s) (hB (Ne.symm hsr)),
        ← Finset.smul_sum, rc_sum_proj, hsr, ite_false, add_zero]
  rw [rc_T_apply]
  simp only [hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, rc_trace_proj, one_smul]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  linear_combination ((1 : Matrix (Fin d) (Fin d) ℂ) a b) * (mul_inv_cancel₀ hd0)

/-- The flattening `bd_vec` as a linear map. -/
def rc_vecL (d : ℕ) : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin d × Fin d) where
  toFun := bd_vec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The matrices behind `bd_fam`: the identity and the weighted projectors `Σ_j ζ^{j(k+1)} P_{r,j}`. -/
def rc_F {d m : ℕ} (B : Fin m → UMat d) : Option (Fin m × Fin (d - 1)) → Matrix (Fin d) (Fin d) ℂ
  | none => 1
  | some p => ∑ j : Fin d, (bd_zeta d ^ ((j : ℕ) * ((p.2 : ℕ) + 1))) • bd_proj (B p.1) j

lemma rc_vec_F {d m : ℕ} (B : Fin m → UMat d) : rc_vecL d ∘ rc_F B = bd_fam B := by
  funext i
  rcases i with _ | ⟨r, k⟩
  · rfl
  · simp only [Function.comp_apply, rc_F, map_sum, map_smul]
    rfl

/-- The family `bd_fam` of a complete set is linearly independent (the argument of `hasMUBs_le_internal`). -/
lemma rc_fam_linIndep {d : ℕ} (hd : d ≠ 0) (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B) :
    LinearIndependent ℂ (bd_fam B) := by
  have hne : ∀ i, bd_fam B i ≠ 0 := by
    rintro (_ | ⟨r, k⟩)
    · exact bd_one_ne_zero hd
    · exact bd_w_ne_zero B r k
  have horth : Pairwise fun i j => inner ℂ (bd_fam B i) (bd_fam B j) = 0 := by
    rintro (_ | ⟨r, k⟩) (_ | ⟨s, l⟩) hij
    · exact absurd rfl hij
    · exact bd_inner_one_w B s l
    · exact inner_eq_zero_symm.mp (bd_inner_one_w B r k)
    · change inner ℂ (bd_w B r k) (bd_w B s l) = 0
      by_cases hrs : r = s
      · subst hrs
        exact bd_inner_w_same_ne B r k l (fun h => hij (by rw [h]))
      · exact bd_inner_w_diff B hB r s hrs k l
  exact linearIndependent_of_ne_zero_of_inner_eq_zero hne horth

/-- The matrices `rc_F B` of a complete set span the matrix space. -/
lemma rc_F_span {d : ℕ} (hd : d ≠ 0) (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B) :
    Submodule.span ℂ (Set.range (rc_F B)) = ⊤ := by
  have hli : LinearIndependent ℂ (rc_F B) := by
    refine LinearIndependent.of_comp (rc_vecL d) ?_
    rw [rc_vec_F]
    exact rc_fam_linIndep hd B hB
  refine hli.span_eq_top_of_card_eq_finrank' ?_
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Module.finrank_matrix,
    Module.finrank_self, Nat.add_sub_cancel]
  ring

/-- `T` fixes every matrix. -/
lemma rc_T_fix {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B) (hd : d ≠ 0)
    (X : Matrix (Fin d) (Fin d) ℂ) : rc_T B X = X := by
  have hF : ∀ i, rc_T B (rc_F B i) = rc_F B i := by
    rintro (_ | ⟨r, k⟩)
    · exact rc_T_one B
    · simp only [rc_F, map_sum, map_smul, rc_T_proj B hB]
  have hX : X ∈ Submodule.span ℂ (Set.range (rc_F B)) := by
    rw [rc_F_span hd B hB]
    exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hX
  simp only [map_sum, map_smul, hF]

/-- A complete set of mutually unbiased bases reconstructs every matrix from its diagonals:
`X = Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1`. -/
theorem mub_reconstruction_internal {d : ℕ} (B : Fin (d + 1) → UMat d) (hB : IsMUBFamily B)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    X = ∑ s, ∑ l, Matrix.trace (X * Matrix.vecMulVec (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
          (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l))) •
        Matrix.vecMulVec (fun a => (B s : Matrix (Fin d) (Fin d) ℂ) a l)
          (fun b => star ((B s : Matrix (Fin d) (Fin d) ℂ) b l)) -
      Matrix.trace X • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · ext a b
    exact a.elim0
  · simp only [rc_proj_eq]
    have h := rc_T_fix B hB hd.ne' X
    rw [rc_T_apply] at h
    exact h.symm

/-- A SIC family reconstructs every matrix: `X = Σ_i ((d + 1) Tr(X P_i) − Tr X)/d · P_i`. -/
theorem sic_reconstruction_internal {d : ℕ} (Φ : Fin (d ^ 2) → StateVector d) (h : IsSICFamily d Φ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    X = ∑ i, ((((d : ℂ) + 1) * Matrix.trace (X * Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l))) -
          Matrix.trace X) / (d : ℂ)) • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · ext a b
    exact a.elim0
  have hli := rc_linIndep (gz_sic_ne_one hd) h.1 h.2
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_matrix, sq])
  have hX : X ∈ Submodule.span ℂ (Set.range fun i => gz_P (Φ i)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hX
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have htr : Matrix.trace X = ∑ i, a i := by
    rw [← ha, Matrix.trace_sum]
    simp only [Matrix.trace_smul, gz_trace_P (h.1 _), smul_eq_mul, mul_one]
  have hc : ((sicOverlapSq d : ℝ) : ℂ) = ((d : ℂ) + 1)⁻¹ := by
    unfold sicOverlapSq
    push_cast
    ring
  have hai : ∀ j, a j = (((d : ℂ) + 1) * Matrix.trace (X * gz_P (Φ j)) - Matrix.trace X) / (d : ℂ) := by
    intro j
    have hp := gz_pair_eq h.1 h.2 a j
    rw [ha, ← rc_trace_eq_pair, hc, ← htr] at hp
    rw [hp]
    field_simp
    ring
  calc X = ∑ i, a i • gz_P (Φ i) := ha.symm
    _ = _ := Finset.sum_congr rfl fun i _ => by rw [hai i]; rfl

end QuantumDesigns
