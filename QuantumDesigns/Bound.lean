module

public import QuantumDesigns.Defs

/-!
# The bound `HasMUBs d m → m ≤ d + 1` for `d ≥ 2`, and its sharpness

The projector argument (Bandyopadhyay–Boykin–Roychowdhury–Vatan 2002, Theorem 3.5; the general-`d` lemmas of XC0R's
formalization of `d = 6`, adapted): for a basis `U` and a column `j`, `P_j = U_{·j} U_{·j}^*` is a rank-one projector
with `⟨P_j, P_l⟩ = δ_{jl}` inside a basis and `⟨P_j^U, P_l^V⟩ = 1/d` across two unbiased bases (Hilbert–Schmidt inner
product, flattened to `EuclideanSpace ℂ (Fin d × Fin d)`). With `ζ = exp(2πi/d)`, for each basis `r < m` and each
frequency `k ∈ {1, …, d − 1}`, the combination `w_{r,k} = Σ_j ζ^{jk} P_j^r` is traceless and `‖w_{r,k}‖² = d`; these
`m (d − 1)` vectors are pairwise orthogonal (frequency orthogonality inside a basis by the geometric sum of a
nontrivial `d`-th root of unity; across bases every `⟨P_j^r, P_l^s⟩ = 1/d` is constant, so the sum factors as
`(1/d) Σ_j conj(ζ^{jk}) Σ_l ζ^{lk'} = 0`), and all are orthogonal to the identity matrix (trace zero). Linear
independence of `1 + m(d − 1)` nonzero pairwise orthogonal vectors in a space of dimension `d²`
(`linearIndependent_of_ne_zero_of_inner_eq_zero`, `LinearIndependent.fintype_card_le_finrank`,
`finrank_euclideanSpace`) gives `1 + m(d − 1) ≤ d²`, hence `m ≤ d + 1` for `d ≥ 2`. Sharpness in dimension one
(any number of copies of the identity) and restriction to a subfamily close the module.
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

open scoped ComplexConjugate

/-! ## Rank-one projectors, flattened -/

/-- The rank-one projector onto column `j` of a unitary matrix, `(P_j)_{ab} = U_{aj} conj(U_{bj})`; adapts
`colProjector` of XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
def bd_proj {d : ℕ} (U : UMat d) (j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => (U : Matrix (Fin d) (Fin d) ℂ) a j * star ((U : Matrix (Fin d) (Fin d) ℂ) b j)

/-- A matrix flattened to a vector of `EuclideanSpace ℂ (Fin d × Fin d)`; adapts `matToEuc` of
XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
def bd_vec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

/-- The flattened inner product is the Hilbert–Schmidt inner product; adapts `inner_matToEuc` of
XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
lemma bd_inner_vec {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    inner ℂ (bd_vec A) (bd_vec B) = ∑ i : Fin d, ∑ j : Fin d, star (A i j) * B i j := by
  simp only [bd_vec, EuclideanSpace.inner_toLp_toLp, dotProduct, Fintype.sum_prod_type, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The inner product of two flattened projectors is `|(U^* V)_{jl}|²`; adapts `colProjector_inner_eq_mul` of
XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
lemma bd_inner_proj {d : ℕ} (U V : UMat d) (j l : Fin d) :
    inner ℂ (bd_vec (bd_proj U j)) (bd_vec (bd_proj V l)) =
      relativeUnitary U V j l * star (relativeUnitary U V j l) := by
  rw [bd_inner_vec]
  simp only [bd_proj, relativeUnitary, Matrix.mul_apply, Matrix.star_apply, star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [star_mul', star_star]
  ring

/-- The relative unitary of a basis with itself is the identity. -/
lemma bd_rel_self {d : ℕ} (U : UMat d) : relativeUnitary U U = 1 :=
  (Matrix.mem_unitaryGroup_iff').mp U.2

/-- Inside one basis the flattened projectors are orthonormal; adapts `colProjector_inner_self` and
`colProjector_inner_diff` of XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
lemma bd_inner_proj_same {d : ℕ} (U : UMat d) (j l : Fin d) :
    inner ℂ (bd_vec (bd_proj U j)) (bd_vec (bd_proj U l)) = if j = l then 1 else 0 := by
  rw [bd_inner_proj, bd_rel_self]
  by_cases h : j = l
  · subst h; simp
  · simp [Matrix.one_apply_ne h, h]

/-- Across two unbiased bases every pair of flattened projectors has inner product `1/d`; adapts
`colProjector_inner_unbiased` of XC0R/formal-conjectures@c8733543 (Apache-2.0). -/
lemma bd_inner_proj_unbiased {d : ℕ} (U V : UMat d) (hUV : IsUnbiased U V) (j l : Fin d) :
    inner ℂ (bd_vec (bd_proj U j)) (bd_vec (bd_proj V l)) = (d : ℂ)⁻¹ := by
  rw [bd_inner_proj]
  change relativeUnitary U V j l * conj (relativeUnitary U V j l) = _
  rw [RCLike.mul_conj]
  have h := congrArg ((↑) : ℝ → ℂ) (hUV j l)
  push_cast at h ⊢
  exact h

/-- The identity matrix has inner product `1` with every flattened projector (its trace). -/
lemma bd_inner_one_proj {d : ℕ} (U : UMat d) (j : Fin d) :
    inner ℂ (bd_vec (1 : Matrix (Fin d) (Fin d) ℂ)) (bd_vec (bd_proj U j)) = 1 := by
  rw [bd_inner_vec]
  have h := congrFun (congrFun (bd_rel_self U) j) j
  simp only [relativeUnitary, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp [bd_proj, mul_comm]
  · intro b _ hb; simp [Matrix.one_apply_ne (Ne.symm hb)]
  · simp

/-! ## The root of unity -/

/-- `ζ = exp(2πi/d)`. -/
def bd_zeta (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

lemma bd_zeta_prim {d : ℕ} (hd : d ≠ 0) : IsPrimitiveRoot (bd_zeta d) d :=
  Complex.isPrimitiveRoot_exp d hd

lemma bd_zeta_norm {d : ℕ} (hd : d ≠ 0) (n : ℕ) : ‖bd_zeta d ^ n‖ = 1 := by
  rw [norm_pow, (bd_zeta_prim hd).norm'_eq_one hd, one_pow]

lemma bd_conj_mul_self {d : ℕ} (hd : d ≠ 0) (n : ℕ) : star (bd_zeta d ^ n) * bd_zeta d ^ n = 1 := by
  change conj (bd_zeta d ^ n) * bd_zeta d ^ n = 1
  rw [RCLike.conj_mul, bd_zeta_norm hd]; simp

lemma bd_star_zeta {d : ℕ} (hd : d ≠ 0) : star (bd_zeta d) = bd_zeta d ^ (d - 1) := by
  have hne : bd_zeta d ≠ 0 := (bd_zeta_prim hd).ne_zero hd
  have h1 : bd_zeta d * star (bd_zeta d) = 1 := by
    rw [mul_comm]; simpa using bd_conj_mul_self hd 1
  have h2 : bd_zeta d * bd_zeta d ^ (d - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd), (bd_zeta_prim hd).pow_eq_one]
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

/-- `Σ_{x < d} (ζ^n)^x = 0` when `d ∤ n`. -/
lemma bd_geom_zero {d : ℕ} (hd : d ≠ 0) (n : ℕ) (hn : ¬ d ∣ n) :
    ∑ x : Fin d, (bd_zeta d ^ n) ^ (x : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun x => (bd_zeta d ^ n) ^ x)]
  have h1 : bd_zeta d ^ n ≠ 1 := fun h => hn (((bd_zeta_prim hd).pow_eq_one_iff_dvd n).mp h)
  have hdn : (bd_zeta d ^ n) ^ d = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, (bd_zeta_prim hd).pow_eq_one, one_pow]
  have key := geom_sum_mul (bd_zeta d ^ n) d
  rw [hdn, sub_self] at key
  exact (mul_eq_zero.mp key).resolve_right (sub_ne_zero.mpr h1)

/-- `d ∤ (d − 1) a + b` for `a ≠ b < d`. -/
lemma bd_not_dvd {d a b : ℕ} (ha : a < d) (hb : b < d) (hab : a ≠ b) : ¬ d ∣ (d - 1) * a + b := by
  rintro ⟨t, ht⟩
  have e : (d - 1) * a + b + a = d * a + b := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [ht] at e
  have h1 : (d * t + a) % d = (d * a + b) % d := by rw [e]
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  exact hab h1

/-! ## The weighted projectors -/

/-- `w_{r,k} = Σ_j ζ^{j(k+1)} P_j^r` for `k < d − 1`; adapts `dftProjector` of XC0R/formal-conjectures@c8733543
(Apache-2.0), with `ζ₆` replaced by `ζ = exp(2πi/d)`. -/
def bd_w {d m : ℕ} (B : Fin m → UMat d) (r : Fin m) (k : Fin (d - 1)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  ∑ j : Fin d, (bd_zeta d ^ ((j : ℕ) * ((k : ℕ) + 1))) • bd_vec (bd_proj (B r) j)

lemma bd_inner_w {d m : ℕ} (B : Fin m → UMat d) (r s : Fin m) (k l : Fin (d - 1)) :
    inner ℂ (bd_w B r k) (bd_w B s l) =
      ∑ x : Fin d, star (bd_zeta d ^ ((x : ℕ) * ((k : ℕ) + 1))) *
        ∑ y : Fin d, bd_zeta d ^ ((y : ℕ) * ((l : ℕ) + 1)) *
          inner ℂ (bd_vec (bd_proj (B r) x)) (bd_vec (bd_proj (B s) y)) := by
  rw [bd_w, bd_w, sum_inner]
  simp only [inner_smul_left, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_left_comm]; rfl

/-- Same basis: `⟨w_{r,k}, w_{r,l}⟩ = Σ_x conj(ζ^{x(k+1)}) ζ^{x(l+1)}`. -/
lemma bd_inner_w_same {d m : ℕ} (B : Fin m → UMat d) (r : Fin m) (k l : Fin (d - 1)) :
    inner ℂ (bd_w B r k) (bd_w B r l) =
      ∑ x : Fin d, star (bd_zeta d ^ ((x : ℕ) * ((k : ℕ) + 1))) *
        bd_zeta d ^ ((x : ℕ) * ((l : ℕ) + 1)) := by
  rw [bd_inner_w]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [Finset.sum_eq_single x]
  · rw [bd_inner_proj_same]; simp
  · intro y _ hy; rw [bd_inner_proj_same]; simp [Ne.symm hy]
  · simp

lemma bd_inner_w_same_ne {d m : ℕ} (B : Fin m → UMat d) (r : Fin m) (k l : Fin (d - 1))
    (hkl : k ≠ l) : inner ℂ (bd_w B r k) (bd_w B r l) = 0 := by
  have hd : d ≠ 0 := by have := k.2; omega
  rw [bd_inner_w_same]
  have hpt : ∀ x : Fin d, star (bd_zeta d ^ ((x : ℕ) * ((k : ℕ) + 1))) *
      bd_zeta d ^ ((x : ℕ) * ((l : ℕ) + 1)) =
      (bd_zeta d ^ ((d - 1) * ((k : ℕ) + 1) + ((l : ℕ) + 1))) ^ (x : ℕ) := by
    intro x
    rw [star_pow, bd_star_zeta hd, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1; ring
  simp only [hpt]
  refine bd_geom_zero hd _ (bd_not_dvd (by have := k.2; omega) (by have := l.2; omega) ?_)
  intro h; exact hkl (Fin.ext (by omega))

lemma bd_inner_w_self {d m : ℕ} (B : Fin m → UMat d) (r : Fin m) (k : Fin (d - 1)) :
    inner ℂ (bd_w B r k) (bd_w B r k) = d := by
  have hd : d ≠ 0 := by have := k.2; omega
  rw [bd_inner_w_same]
  refine (Finset.sum_congr rfl fun x _ => bd_conj_mul_self hd _).trans ?_
  simp

lemma bd_w_ne_zero {d m : ℕ} (B : Fin m → UMat d) (r : Fin m) (k : Fin (d - 1)) :
    bd_w B r k ≠ 0 := by
  have hd : d ≠ 0 := by have := k.2; omega
  intro h
  have := bd_inner_w_self B r k
  rw [h, inner_zero_left] at this
  exact hd (by exact_mod_cast this.symm)

lemma bd_inner_w_diff {d m : ℕ} (B : Fin m → UMat d) (hB : IsMUBFamily B) (r s : Fin m)
    (hrs : r ≠ s) (k l : Fin (d - 1)) : inner ℂ (bd_w B r k) (bd_w B s l) = 0 := by
  have hd : d ≠ 0 := by have := k.2; omega
  rw [bd_inner_w]
  simp only [bd_inner_proj_unbiased (B r) (B s) (hB hrs), ← Finset.sum_mul]
  have hg : ∑ y : Fin d, bd_zeta d ^ ((y : ℕ) * ((l : ℕ) + 1)) = 0 := by
    have := bd_geom_zero hd ((l : ℕ) + 1) (fun h => by
      have := Nat.le_of_dvd (by omega) h; have := l.2; omega)
    rw [← this]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← pow_mul, mul_comm]
  simp [hg]

lemma bd_inner_one_w {d m : ℕ} (B : Fin m → UMat d) (r : Fin m) (k : Fin (d - 1)) :
    inner ℂ (bd_vec (1 : Matrix (Fin d) (Fin d) ℂ)) (bd_w B r k) = 0 := by
  have hd : d ≠ 0 := by have := k.2; omega
  simp only [bd_w, inner_sum, inner_smul_right, bd_inner_one_proj, mul_one]
  have := bd_geom_zero hd ((k : ℕ) + 1) (fun h => by
      have := Nat.le_of_dvd (by omega) h; have := k.2; omega)
  rw [← this]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← pow_mul, mul_comm]

lemma bd_one_ne_zero {d : ℕ} (hd : d ≠ 0) : bd_vec (1 : Matrix (Fin d) (Fin d) ℂ) ≠ 0 := by
  intro h
  have := congrArg (fun v : EuclideanSpace ℂ (Fin d × Fin d) => v (⟨0, by omega⟩, ⟨0, by omega⟩)) h
  simp [bd_vec] at this

/-- The family of the identity and the weighted projectors. -/
def bd_fam {d m : ℕ} (B : Fin m → UMat d) :
    Option (Fin m × Fin (d - 1)) → EuclideanSpace ℂ (Fin d × Fin d)
  | none => bd_vec 1
  | some p => bd_w B p.1 p.2

theorem hasMUBs_le_internal (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (h : HasMUBs d m) : m ≤ d + 1 := by
  obtain ⟨B, hB⟩ := h
  have hd0 : d ≠ 0 := by omega
  have hne : ∀ i, bd_fam B i ≠ 0 := by
    rintro (_ | ⟨r, k⟩)
    · exact bd_one_ne_zero hd0
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
  have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hne horth
  have hcard := hli.fintype_card_le_finrank
  rw [finrank_euclideanSpace] at hcard
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin] at hcard
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  simp only [show e + 2 - 1 = e + 1 by omega] at hcard
  nlinarith

theorem hasMUBs_one_dim_internal (m : ℕ) : HasMUBs 1 m := by
  refine ⟨fun _ => 1, fun _ _ _ i j => ?_⟩
  have h : relativeUnitary (1 : UMat 1) 1 = 1 := bd_rel_self 1
  rw [h, Subsingleton.elim i j, Matrix.one_apply_eq]
  norm_num

theorem hasMUBs_of_le_internal {d k l : ℕ} (hkl : k ≤ l) (h : HasMUBs d l) : HasMUBs d k := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B ∘ Fin.castLE hkl, hB.comp_of_injective (Fin.castLE_injective hkl)⟩

end QuantumDesigns
