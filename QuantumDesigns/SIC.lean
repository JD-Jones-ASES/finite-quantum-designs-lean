module

public import QuantumDesigns.Defs
public import QuantumDesigns.SICTables

/-!
# SIC-POVMs in dimensions 2, 3 and 8

**Dimension 8.** The fiducial `ψ = (−1 + 2i, 1, 1, 1, 1, 1, 1, 1)` (unnormalized, `‖ψ‖² = 12`) and the
64 vectors `v_{a,b}(x) = (−1)^{b·(x ⊕ a)} ψ(x ⊕ a)` for `a, b ∈ 𝔽₂³` (`x ⊕ a = x ^^^ a` on `Fin 8`, `b·y` the parity
of `b &&& y`): an exact computation gives `‖v‖² = 12` and `‖⟨u, v⟩‖² = 16` on all 4032 ordered pairs of distinct
vectors, so `overlapSq = 16/144 = 1/9 = sicOverlapSq 8`. Route: encode each vector as a function `Fin 8 → ℤ × ℤ`
(Gaussian integers); a kernel-checked statement over all `64 × 64` ordered pairs that the integer inner product
`Σ_x conj(u x) v x` has `re² + im² = 144` on the diagonal and `16` off it (`decide +kernel` in the Mathlib-free leaf
`QuantumDesigns.SICTables`); a generic cast lemma from the integer pair to `ℂ`
(`Complex.ext_iff`, `push_cast`; no case split); normalization `‖(√12)⁻¹ • ψ‖ = 1` through `EuclideanSpace.norm_eq`
and `Real.sq_sqrt`; the family `Φ : Fin 64 → StateVector 8`, `Φ i = (√12)⁻¹ • v_{i / 8, i % 8}` as
`WithLp.toLp 2 (fun x => …)`.

**Dimensions 2 and 3.** The tetrahedral family `(1, 0)`, `(√(1/3), √(2/3) ω^m)` (`m = 0, 1, 2`, `ω = e^{2πi/3}`) and
the Hesse family `(0, s, −s ω^m)`, `(−s ω^m, 0, s)`, `(s, −s ω^m, 0)` with `s = √(1/2)` (formal-conjectures'
`qubitSICFamily`, `hesseFamily`; zblore/csd-lean4 holds the overlaps in Lean in other vocabulary). Both
families are stated for real parameters `a, b, r` (resp. `s, r`) with `ω = −1/2 + (r/2) i`; the overlaps follow by
`Fin` case analysis, `ring_nf` and the squares `a² = 1/3`, `b² = 2/3`, `s² = 1/2`, `r² = 3`, and `Real.sq_sqrt`
supplies the parameters.
-/

@[expose] public section

namespace QuantumDesigns

open Complex

/-! ## Dimension 8 -/

/-- The Gaussian integer `vr + vi i` as a complex number. -/
def hg_z (i : ℕ) (x : Fin 8) : ℂ := (hg_vr i x.val : ℂ) + (hg_vi i x.val : ℂ) * I

/-- The Hoggar family: `(√12)⁻¹ v_{i / 8, i % 8}`. -/
noncomputable def hg_hoggar (i : Fin (8 ^ 2)) : StateVector 8 :=
  WithLp.toLp 2 (fun x => (((Real.sqrt 12)⁻¹ : ℝ) : ℂ) * hg_z i.val x)

theorem hg_term (r s r' s' : ℤ) :
    star ((r : ℂ) + (s : ℂ) * I) * ((r' : ℂ) + (s' : ℂ) * I)
      = ((r * r' + s * s' : ℤ) : ℂ) + ((r * s' - s * r' : ℤ) : ℂ) * I := by
  apply Complex.ext
  · simp
  · simp; ring

theorem hg_sum_z (i j : ℕ) :
    ∑ x : Fin 8, star (hg_z i x) * hg_z j x
      = (hg_ipRe i j : ℂ) + (hg_ipIm i j : ℂ) * I := by
  simp only [hg_z, hg_term]
  rw [Fin.sum_univ_eight]
  simp only [hg_ipRe, hg_ipIm, hg_tr, hg_ti, Fin.val_zero, Fin.val_one, Fin.val_two]
  push_cast
  simp only [show ((3 : Fin 8) : ℕ) = 3 from rfl, show ((4 : Fin 8) : ℕ) = 4 from rfl,
    show ((5 : Fin 8) : ℕ) = 5 from rfl, show ((6 : Fin 8) : ℕ) = 6 from rfl,
    show ((7 : Fin 8) : ℕ) = 7 from rfl]
  ring

theorem hg_inner (i j : Fin (8 ^ 2)) :
    ∑ x : Fin 8, star (hg_hoggar i x) * hg_hoggar j x
      = ((1 / 12 : ℝ) : ℂ) * ((hg_ipRe i j : ℂ) + (hg_ipIm i j : ℂ) * I) := by
  have h12 : (Real.sqrt 12)⁻¹ * (Real.sqrt 12)⁻¹ = 1 / 12 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  have : ∀ x : Fin 8, star (hg_hoggar i x) * hg_hoggar j x
      = ((1 / 12 : ℝ) : ℂ) * (star (hg_z i x) * hg_z j x) := by
    intro x
    simp only [hg_hoggar, PiLp.toLp_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [← h12]; push_cast; ring
  rw [Finset.sum_congr rfl (fun x _ => this x), ← Finset.mul_sum, hg_sum_z]

theorem hg_lt (i : Fin (8 ^ 2)) : i.val < 64 := i.isLt

theorem hasSICPOVM_eight_internal : HasSICPOVM 8 := by
  refine ⟨hg_hoggar, fun i => ?_, fun i j hij => ?_⟩
  · have hd := hg_diag i.val (hg_lt i)
    have hs : ∑ x : Fin 8, ((‖hg_hoggar i x‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have : ∀ x : Fin 8, ((‖hg_hoggar i x‖ ^ 2 : ℝ) : ℂ) = star (hg_hoggar i x) * hg_hoggar i x := by
        intro x
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, Complex.star_def]
      rw [Finset.sum_congr rfl (fun x _ => this x), hg_inner, hd.1, hd.2]
      push_cast; ring
    have hs' : ∑ x : Fin 8, ‖hg_hoggar i x‖ ^ 2 = 1 := by
      exact_mod_cast hs
    unfold IsNormalized
    rw [EuclideanSpace.norm_eq, hs', Real.sqrt_one]
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have ho := hg_overlaps i.val (hg_lt i) j.val (hg_lt j) hne
    show overlapSq (hg_hoggar i) (hg_hoggar j) = sicOverlapSq 8
    unfold overlapSq sicOverlapSq
    rw [hg_inner]
    have hc : ((1 / 12 : ℝ) : ℂ) * ((hg_ipRe i j : ℂ) + (hg_ipIm i j : ℂ) * I)
        = (((1 / 12 : ℝ) * hg_ipRe i j : ℝ) : ℂ) + (((1 / 12 : ℝ) * hg_ipIm i j : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hc, Complex.normSq_add_mul_I]
    have ho' : ((hg_ipRe i j : ℝ)) * hg_ipRe i j + (hg_ipIm i j : ℝ) * hg_ipIm i j = 16 := by
      exact_mod_cast ho
    push_cast
    nlinarith [ho']

/-! ## Dimension 2 -/

/-- The tetrahedral qubit family `(1, 0)`, `(a, b ω^m)` with `ω = −1/2 + (r/2) i`, for real parameters `a, b, r`
(at `a = √(1/3)`, `b = √(2/3)`, `r = √3`); adapts `qubitSICFamily` of google-deepmind/formal-conjectures
`OpenQuantumProblems/23.lean` (Apache-2.0). -/
noncomputable def hg_qubit (a b r : ℝ) : Fin 4 → StateVector 2 :=
  ![WithLp.toLp 2 ![⟨1, 0⟩, ⟨0, 0⟩],
    WithLp.toLp 2 ![⟨a, 0⟩, ⟨b, 0⟩],
    WithLp.toLp 2 ![⟨a, 0⟩, ⟨-b / 2, b * r / 2⟩],
    WithLp.toLp 2 ![⟨a, 0⟩, ⟨-b / 2, -(b * r / 2)⟩]]

theorem hg_qubit_sic (a b r : ℝ) (ha : a ^ 2 = 1 / 3) (hb : b ^ 2 = 2 / 3) (hr : r ^ 2 = 3) :
    (∀ i, IsNormalized (hg_qubit a b r i)) ∧ HasConstantOverlapSq (sicOverlapSq 2) (hg_qubit a b r) := by
  have ha4 : a ^ 4 = 1 / 9 := by rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ha]; norm_num
  have hb4 : b ^ 4 = 4 / 9 := by rw [show b ^ 4 = (b ^ 2) ^ 2 by ring, hb]; norm_num
  have hr4 : r ^ 4 = 9 := by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr]; norm_num
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · unfold IsNormalized
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    fin_cases i <;>
      simp [hg_qubit, Complex.sq_norm, Complex.normSq_apply, Fin.sum_univ_two] <;>
      ring_nf <;> simp only [ha, hb, hr] <;> norm_num
  · show overlapSq (hg_qubit a b r i) (hg_qubit a b r j) = sicOverlapSq 2
    unfold overlapSq sicOverlapSq
    fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
      simp [hg_qubit, Complex.normSq_apply, Fin.sum_univ_two] <;>
      ring_nf <;> simp only [ha, hb, hr, ha4, hb4, hr4] <;> norm_num

theorem hasSICPOVM_two_internal : HasSICPOVM 2 :=
  ⟨hg_qubit (Real.sqrt (1 / 3)) (Real.sqrt (2 / 3)) (Real.sqrt 3),
    hg_qubit_sic _ _ _ (Real.sq_sqrt (by norm_num)) (Real.sq_sqrt (by norm_num))
      (Real.sq_sqrt (by norm_num))⟩

/-! ## Dimension 3 -/

/-- The Hesse qutrit family `(0, s, −s ω^m)`, `(−s ω^m, 0, s)`, `(s, −s ω^m, 0)` with `ω = −1/2 + (r/2) i`, for real
parameters `s, r` (at `s = √(1/2)`, `r = √3`); adapts `hesseFamily` of google-deepmind/formal-conjectures
`OpenQuantumProblems/23.lean` (Apache-2.0). -/
noncomputable def hg_hesse (s r : ℝ) : Fin 9 → StateVector 3 :=
  ![WithLp.toLp 2 ![⟨0, 0⟩, ⟨s, 0⟩, ⟨-s, 0⟩],
    WithLp.toLp 2 ![⟨0, 0⟩, ⟨s, 0⟩, ⟨s / 2, -(s * r / 2)⟩],
    WithLp.toLp 2 ![⟨0, 0⟩, ⟨s, 0⟩, ⟨s / 2, s * r / 2⟩],
    WithLp.toLp 2 ![⟨-s, 0⟩, ⟨0, 0⟩, ⟨s, 0⟩],
    WithLp.toLp 2 ![⟨s / 2, -(s * r / 2)⟩, ⟨0, 0⟩, ⟨s, 0⟩],
    WithLp.toLp 2 ![⟨s / 2, s * r / 2⟩, ⟨0, 0⟩, ⟨s, 0⟩],
    WithLp.toLp 2 ![⟨s, 0⟩, ⟨-s, 0⟩, ⟨0, 0⟩],
    WithLp.toLp 2 ![⟨s, 0⟩, ⟨s / 2, -(s * r / 2)⟩, ⟨0, 0⟩],
    WithLp.toLp 2 ![⟨s, 0⟩, ⟨s / 2, s * r / 2⟩, ⟨0, 0⟩]]

theorem hg_hesse_sic (s r : ℝ) (hs : s ^ 2 = 1 / 2) (hr : r ^ 2 = 3) :
    (∀ i, IsNormalized (hg_hesse s r i)) ∧ HasConstantOverlapSq (sicOverlapSq 3) (hg_hesse s r) := by
  have hs4 : s ^ 4 = 1 / 4 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs]; norm_num
  have hr4 : r ^ 4 = 9 := by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr]; norm_num
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · unfold IsNormalized
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    fin_cases i <;>
      simp [hg_hesse, Complex.sq_norm, Complex.normSq_apply, Fin.sum_univ_three] <;>
      ring_nf <;> simp only [hs, hr] <;> norm_num
  · show overlapSq (hg_hesse s r i) (hg_hesse s r j) = sicOverlapSq 3
    unfold overlapSq sicOverlapSq
    fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
      simp [hg_hesse, Complex.normSq_apply, Fin.sum_univ_three] <;>
      ring_nf <;> simp only [hr, hs4, hr4] <;> norm_num

theorem hasSICPOVM_three_internal : HasSICPOVM 3 :=
  ⟨hg_hesse (Real.sqrt (1 / 2)) (Real.sqrt 3),
    hg_hesse_sic _ _ (Real.sq_sqrt (by norm_num)) (Real.sq_sqrt (by norm_num))⟩


end QuantumDesigns
