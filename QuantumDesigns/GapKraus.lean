module

public import QuantumDesigns.GapCore
public import QuantumDesigns.GapPhi

/-!
# The Kraus form of Weiner's projection

**Lemma 2.1 of Weiner 2013, recalled there from Werner 2001.** For an orthonormal basis `b` of the matrix space
(Hilbert–Schmidt inner product, through the flattening `bd_vec`), `Σ_i b_i^* X b_i = Tr(X)·1`: the entry `(p, q)` of
the left side is `Σ_{a,c} X_{ac} Σ_i conj((b_i)_{ap}) (b_i)_{cq}`, and the inner sum is the Parseval identity
`Σ_i ⟨E_{cq}, b_i⟩ ⟨b_i, E_{ap}⟩ = ⟨E_{cq}, E_{ap}⟩` for the matrix units (`OrthonormalBasis.sum_inner_mul_inner`;
Mathlib's inner product is conjugate-linear in its left argument, so `⟨E_{cq}, b_i⟩ = (b_i)_{cq}` and
`⟨b_i, E_{ap}⟩ = conj((b_i)_{ap})`), which is `δ_{ac} δ_{pq}` (`gp_onb_parseval`, `gp_onb_sum`).

**The weighted projectors conjugate to the pinching.** `w_k = Σ_j ζ^{j(k+1)} P_j` gives
`w_k^* X w_k = Σ_{j,j'} ζ^{(j'−j)(k+1)} P_j X P_{j'}`; summing over `k + 1 ∈ {0, …, d − 1}` (the term `k + 1 = 0`
is `1·X·1 = X`) the geometric sums `Σ_m ζ^{(j'−j)m}` are `d δ_{jj'}` (`gp_freq`, `gp_geom`, from `bd_geom_zero`), so
`Σ_{k < d−1} w_k^* X w_k = d Σ_j P_j X P_j − X` (`gp_w_sum`).

**Weiner's Lemma 3.2 (the Kraus form).** For `d` mutually unbiased bases the `d(d − 1)` vectors `w_{r,k}/√d` are orthonormal
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

open scoped ComplexConjugate

/-! ## Lemma 2.1 -/

/-- Parseval for the matrix units: `Σ_i conj((b_i)_{ap}) (b_i)_{cq} = δ_{(c,q),(a,p)}`. -/
lemma gp_onb_parseval {d : ℕ} {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ (Fin d × Fin d))) (a p c q : Fin d) :
    ∑ i, star (b i (a, p)) * b i (c, q) = if (c, q) = (a, p) then 1 else 0 := by
  have h := b.sum_inner_mul_inner (EuclideanSpace.single (c, q) (1 : ℂ))
    (EuclideanSpace.single (a, p) (1 : ℂ))
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, map_one, one_mul,
    PiLp.single_apply, starRingEnd_apply] at h
  have e : star (if (a, p) = (c, q) then (1 : ℂ) else 0) = if (c, q) = (a, p) then 1 else 0 := by
    by_cases hh : (c, q) = (a, p)
    · rw [ite_eq_left hh.symm, ite_eq_left hh, star_one]
    · rw [ite_eq_right (Ne.symm hh), ite_eq_right hh, star_zero]
  rw [e] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Lemma 2.1 of Weiner 2013 (recalled there from Werner 2001): an orthonormal basis of the flattened matrix space
satisfies `Σ_i b_i^* X b_i = Tr(X)·1`. -/
theorem gp_onb_sum {d : ℕ} {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ (Fin d × Fin d))) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, star (gp_unvec (b i)) * X * gp_unvec (b i) = Matrix.trace X • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext p q
  have e1 : ∀ i, (star (gp_unvec (b i)) * X * gp_unvec (b i)) p q =
      ∑ a, ∑ c, X a c * (star (b i (a, p)) * b i (c, q)) := by
    intro i
    simp only [Matrix.mul_apply, Matrix.star_apply, gp_unvec, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  have e2 : ∑ i, ∑ a, ∑ c, X a c * (star (b i (a, p)) * b i (c, q)) =
      ∑ a, ∑ c, X a c * (if (c, q) = (a, p) then 1 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum, gp_onb_parseval]
  rw [Matrix.sum_apply]
  simp only [e1]
  rw [e2]
  by_cases hpq : p = q
  · subst hpq
    simp [Matrix.trace]
  · simp [hpq, Ne.symm hpq]

/-! ## The weighted projectors and the pinching -/

/-- The frequency-`m` conjugation term `Σ_{j,j'} conj(ζ^{jm}) ζ^{j'm} P_j X P_{j'}`. -/
def gp_freq {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ j : Fin d, ∑ j' : Fin d,
    (star (bd_zeta d ^ ((j : ℕ) * m)) * bd_zeta d ^ ((j' : ℕ) * m)) • (bd_proj U j * X * bd_proj U j')

lemma gp_star_w_mul {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) (k : Fin (d - 1)) :
    star (gp_w U k) * X * gp_w U k = gp_freq U X ((k : ℕ) + 1) := by
  rw [gp_freq, gp_w, star_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [star_smul, gp_star_proj, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]

lemma gp_freq_zero {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) : gp_freq U X 0 = X := by
  simp only [gp_freq, mul_zero, pow_zero, star_one, mul_one, one_smul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, gp_sum_proj, one_mul, mul_one]

/-- `Σ_{m<d} conj(ζ^{jm}) ζ^{j'm} = d δ_{jj'}`. -/
lemma gp_geom {d : ℕ} (hd : d ≠ 0) (j j' : Fin d) :
    ∑ m : Fin d, star (bd_zeta d ^ ((j : ℕ) * (m : ℕ))) * bd_zeta d ^ ((j' : ℕ) * (m : ℕ)) =
      if j = j' then (d : ℂ) else 0 := by
  split_ifs with h
  · subst h
    refine (Finset.sum_congr rfl fun m _ => bd_conj_mul_self hd _).trans ?_
    simp
  · have hpt : ∀ m : Fin d, star (bd_zeta d ^ ((j : ℕ) * (m : ℕ))) * bd_zeta d ^ ((j' : ℕ) * (m : ℕ)) =
        (bd_zeta d ^ ((d - 1) * (j : ℕ) + (j' : ℕ))) ^ (m : ℕ) := by
      intro m
      rw [star_pow, bd_star_zeta hd, ← pow_mul, ← pow_add, ← pow_mul]
      congr 1; ring
    simp only [hpt]
    exact bd_geom_zero hd _ (bd_not_dvd j.2 j'.2 (fun e => h (Fin.ext e)))

lemma gp_sum_freq {d : ℕ} (hd : d ≠ 0) (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ m : Fin d, gp_freq U X m = (d : ℂ) • gp_pinch U X := by
  simp only [gp_freq, gp_pinch, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [Finset.sum_eq_single j]
  · rw [gp_geom hd, ite_eq_left rfl]
  · intro j' _ hj'
    rw [gp_geom hd, ite_eq_right (Ne.symm hj'), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The weighted projectors of one basis conjugate to its pinching: `Σ_{k<d−1} w_k^* X w_k = d·Σ_j P_j X P_j − X`. -/
theorem gp_w_sum {d : ℕ} (U : UMat d) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k : Fin (d - 1), star (gp_w U k) * X * gp_w U k = (d : ℂ) • gp_pinch U X - X := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · ext i
    exact i.elim0
  have hsplit : ∑ m : Fin d, gp_freq U X m =
      gp_freq U X 0 + ∑ k : Fin (d - 1), gp_freq U X ((k : ℕ) + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun m => gp_freq U X m),
      Fin.sum_univ_eq_sum_range (fun k => gp_freq U X (k + 1)),
      show Finset.range d = Finset.range (d - 1 + 1) from congrArg Finset.range (by omega),
      Finset.sum_range_succ']
    exact add_comm _ _
  have h := gp_sum_freq hd.ne' U X
  rw [hsplit, gp_freq_zero] at h
  simp only [gp_star_w_mul]
  rw [← h]
  abel

/-! ## Lemma 3.2 -/

/-- Scalars pass through the inverse flattening. -/
lemma gp_unvec_smul {d : ℕ} (c : ℂ) (v : EuclideanSpace ℂ (Fin d × Fin d)) :
    gp_unvec (c • v) = c • gp_unvec v := by
  ext a b
  simp [gp_unvec]

/-- The scaled weighted projectors `c • w_{r,k}`, padded with zero vectors. -/
def gp_kfam {d : ℕ} (B : Fin d → UMat d) (c : ℂ) :
    Fin d × Fin (d - 1) ⊕ Fin d → EuclideanSpace ℂ (Fin d × Fin d) :=
  Sum.elim (fun p => c • bd_w B p.1 p.2) (fun _ => 0)

/-- The normalizing scalar `1/√d`. -/
lemma gp_exists_scale {d : ℕ} (hd : d ≠ 0) :
    ∃ c : ℂ, conj c * c = (d : ℂ)⁻¹ ∧ star c * c = (d : ℂ)⁻¹ ∧ c ≠ 0 := by
  refine ⟨((Real.sqrt d)⁻¹ : ℝ), ?_, ?_, ?_⟩
  · rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_inv, Complex.ofReal_natCast]
  · change conj (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * _ = _
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_inv, Complex.ofReal_natCast]
  · have : Real.sqrt d ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.pos_of_ne_zero hd)
    exact_mod_cast inv_ne_zero this

lemma gp_kfam_orthonormal {d : ℕ} (hd : d ≠ 0) (B : Fin d → UMat d) (hB : IsMUBFamily B) {c : ℂ}
    (hc : conj c * c = (d : ℂ)⁻¹) :
    Orthonormal ℂ ((Set.range (Sum.inl : Fin d × Fin (d - 1) → Fin d × Fin (d - 1) ⊕ Fin d)).domRestrict
      (gp_kfam B c)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨_, ⟨r, k⟩, rfl⟩ ⟨_, ⟨s, l⟩, rfl⟩
  simp only [Set.domRestrict_apply, gp_kfam, Sum.elim_inl, inner_smul_left, inner_smul_right]
  by_cases hrs : r = s
  · subst hrs
    by_cases hkl : k = l
    · subst hkl
      rw [bd_inner_w_self, ite_eq_left rfl, mul_left_comm, ← mul_assoc, hc,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd)]
    · rw [bd_inner_w_same_ne B r k l hkl, ite_eq_right, mul_zero, mul_zero]
      intro h
      exact hkl (congrArg Prod.snd (Sum.inl_injective (congrArg Subtype.val h)))
  · rw [bd_inner_w_diff B hB r s hrs k l, ite_eq_right, mul_zero, mul_zero]
    intro h
    exact hrs (congrArg Prod.fst (Sum.inl_injective (congrArg Subtype.val h)))

/-- The Kraus form of Weiner's projection (Weiner 2013, Lemma 3.2): for `d` mutually unbiased bases of `ℂ^d` there
are matrices `K_0, …, K_{d−1}`, each orthogonal (Hilbert–Schmidt) to every weighted projector of every basis, with
`Φ(X) = Σ_i K_i^* X K_i` for every `X` and `Σ_i K_i^* K_i = 1`. -/
theorem gp_exists_kraus {d : ℕ} (B : Fin d → UMat d) (hB : IsMUBFamily B) :
    ∃ K : Fin d → Matrix (Fin d) (Fin d) ℂ,
      (∀ i r k, inner ℂ (bd_w B r k) (bd_vec (K i)) = 0) ∧
      (∀ X, gp_Phi B X = ∑ i, star (K i) * X * K i) ∧
      ∑ i, star (K i) * K i = 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨fun i => i.elim0, fun i => i.elim0, fun X => ?_, ?_⟩
    · ext i
      exact i.elim0
    · ext i
      exact i.elim0
  have hd0 : d ≠ 0 := hd.ne'
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  obtain ⟨c, hcc, hcs, hc0⟩ := gp_exists_scale hd0
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin d × Fin d)) =
      Fintype.card (Fin d × Fin (d - 1) ⊕ Fin d) := by
    rw [finrank_euclideanSpace]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard
    (gp_kfam_orthonormal hd0 B hB hcc)
  have hbl : ∀ r k, b (Sum.inl (r, k)) = c • bd_w B r k := fun r k =>
    (hb _ ⟨(r, k), rfl⟩).trans (by simp [gp_kfam])
  have hPhi : ∀ X, gp_Phi B X =
      ∑ i, star (gp_unvec (b (Sum.inr i))) * X * gp_unvec (b (Sum.inr i)) := by
    intro X
    have h := gp_onb_sum b X
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at h
    have hw : ∀ r, ∑ k : Fin (d - 1),
        star (gp_unvec (b (Sum.inl (r, k)))) * X * gp_unvec (b (Sum.inl (r, k))) =
          gp_pinch (B r) X - (d : ℂ)⁻¹ • X := by
      intro r
      have e : ∀ k, star (gp_unvec (b (Sum.inl (r, k)))) * X * gp_unvec (b (Sum.inl (r, k))) =
          (d : ℂ)⁻¹ • (star (gp_w (B r) k) * X * gp_w (B r) k) := by
        intro k
        rw [hbl, ← gp_vec_w B r k, gp_unvec_smul, gp_unvec_vec, star_smul, smul_mul_assoc,
          smul_mul_assoc, mul_smul_comm, smul_smul, hcs]
      simp only [e]
      rw [← Finset.smul_sum, gp_w_sum, smul_sub, smul_smul, inv_mul_cancel₀ hdC, one_smul]
    simp only [hw] at h
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hdC, one_smul] at h
    rw [gp_Phi, ← h]
    abel
  refine ⟨fun i => gp_unvec (b (Sum.inr i)), ?_, hPhi, ?_⟩
  · intro i r k
    simp only [gp_vec_unvec]
    have h0 := b.orthonormal.inner_eq_zero (i := Sum.inl (r, k)) (j := Sum.inr i) Sum.inl_ne_inr
    rw [hbl, inner_smul_left] at h0
    exact (mul_eq_zero.mp h0).resolve_left ((map_ne_zero (starRingEnd ℂ)).mpr hc0)
  · have h1 := hPhi 1
    rw [gp_Phi_one] at h1
    simp only [mul_one] at h1
    exact h1.symm

end QuantumDesigns
