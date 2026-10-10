module

public import QuantumDesigns.Defs
public import QuantumDesigns.SIC4Tables

/-!
# A SIC-POVM in dimension 4

**The fiducial.** Appleby, *SIC-POVMs and the extended Clifford group*, J. Math. Phys. 46, 052107 (2005),
arXiv:quant-ph/0412001v2, §8 ("Dimension 4"), eq. (149), p. 21 (a fiducial found by Zauner, 1999, and by
Renes–Blume-Kohout–Scott–Caves, 2004):
`ψ = √((5 − √5)/40) (2 cos(π/8) e₀ + i (e^{−iπ/8} + √(2 + √5) e^{iπ/8}) e₁ + 2i sin(π/8) e₂
  + i (e^{−iπ/8} − √(2 + √5) e^{iπ/8}) e₃)`.
With `c = cos(π/8)`, `s = sin(π/8)`, `q = √(2 + √5)` this is `ψ = N u`, `N² = (5 − √5)/40`, and
`u = (2c, s(1 − q) + c(1 + q) i, 2s i, s(1 + q) + c(1 − q) i)`, `‖u‖² = 6 + 2q² = 10 + 2√5`.

**The family.** The sixteen vectors `S^a T^b ψ`, `(S^a T^b ψ)(x) = i^{b (x − a)} ψ(x − a)` (indices mod 4; Appleby's
displacement operators `D_{(a,b)} = τ^{ab} S^a T^b`, Eqs. (6)–(8), without the phase `τ^{ab}`), with index `k = 4a + b`.

**Route.** The translates of a vector with real parts `ur` and imaginary parts `ui` are written in real coordinates
(`s4_vr`, `s4_vi`, through the index arithmetic of the Mathlib-free leaf `QuantumDesigns.SIC4Tables`), with the real
and imaginary parts `s4_ipRe`, `s4_ipIm` of their inner products and the squared modulus `s4_osq`. Weyl–Heisenberg
covariance, `s4_wh`: for arbitrary `ur, ui`, the squared overlap of the translates `k` and `l` is that of `u` with its
translate of index `s4_diff k l` (sixteen row lemmas `s4_wh_k`, by `interval_cases`, `simp +decide only` and `ring`);
`s4_diff_bounds` (kernel evaluation) places that index in `1, …, 15` when `k ≠ l`. The fifteen overlaps of `u`,
`s4_base`: `|⟨u, S^a T^b u⟩|² = (6 + 2q²)²/5`, by `linear_combination` from the relations `c² + s² = 1`,
`c² − s² = 2cs` and `q⁴ = 4q² + 1` with explicit polynomial coefficients; the norms, `s4_norm`. The bridge to `ℂ⁴`
follows the dimension-8 file: `s4_term`, `s4_sum_z` and `s4_inner` give the inner sum of the family
`s4_fam c s q N k = N u_k` as `N² (s4_ipRe + s4_ipIm · i)`; with `N² (6 + 2q²) = 1` the vectors are unit vectors and
the squared overlaps are `(N² (6 + 2q²))²/5 = 1/5 = sicOverlapSq 4` (`s4_sic`). `hasSICPOVM_four_internal` supplies
`c = cos(π/8)`, `s = sin(π/8)` (`Real.cos_two_mul'`, `Real.sin_two_mul`, `cos(π/4) = sin(π/4)`), `q = √(2 + √5)`
and `N = √((5 − √5)/40)` (`Real.sq_sqrt`).
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

open Complex

/-! ## Weyl–Heisenberg translates in real coordinates -/

/-- Real part of `iⁿ (r + t i)` for `n < 4`. -/
def s4_rotRe (n : ℕ) (r t : ℝ) : ℝ :=
  if n = 0 then r else if n = 1 then -t else if n = 2 then -r else t

/-- Imaginary part of `iⁿ (r + t i)` for `n < 4`. -/
def s4_rotIm (n : ℕ) (r t : ℝ) : ℝ :=
  if n = 0 then t else if n = 1 then r else if n = 2 then -t else -r

/-- Real part of coordinate `x` of the translate `S^a T^b u` with index `k = 4a + b`, for the vector `u` with real
parts `ur` and imaginary parts `ui`: `(S^a T^b u)(x) = i^{b (x − a)} u(x − a)`. -/
def s4_vr (ur ui : ℕ → ℝ) (k x : ℕ) : ℝ := s4_rotRe (s4_ph k x) (ur (s4_sh k x)) (ui (s4_sh k x))

/-- Imaginary part of coordinate `x` of the translate with index `k`. -/
def s4_vi (ur ui : ℕ → ℝ) (k x : ℕ) : ℝ := s4_rotIm (s4_ph k x) (ur (s4_sh k x)) (ui (s4_sh k x))

/-- One term of the real part of the inner product of the translates `k` and `l`. -/
def s4_tr (ur ui : ℕ → ℝ) (k l x : ℕ) : ℝ :=
  s4_vr ur ui k x * s4_vr ur ui l x + s4_vi ur ui k x * s4_vi ur ui l x

/-- One term of the imaginary part of the inner product of the translates `k` and `l`. -/
def s4_ti (ur ui : ℕ → ℝ) (k l x : ℕ) : ℝ :=
  s4_vr ur ui k x * s4_vi ur ui l x - s4_vi ur ui k x * s4_vr ur ui l x

/-- Real part of the inner product of the translates `k` and `l`. -/
def s4_ipRe (ur ui : ℕ → ℝ) (k l : ℕ) : ℝ :=
  s4_tr ur ui k l 0 + s4_tr ur ui k l 1 + s4_tr ur ui k l 2 + s4_tr ur ui k l 3

/-- Imaginary part of the inner product of the translates `k` and `l`. -/
def s4_ipIm (ur ui : ℕ → ℝ) (k l : ℕ) : ℝ :=
  s4_ti ur ui k l 0 + s4_ti ur ui k l 1 + s4_ti ur ui k l 2 + s4_ti ur ui k l 3

/-- The squared modulus of the inner product of the translates `k` and `l`. -/
def s4_osq (ur ui : ℕ → ℝ) (k l : ℕ) : ℝ := s4_ipRe ur ui k l ^ 2 + s4_ipIm ur ui k l ^ 2

/-- Weyl–Heisenberg covariance for the translate `S^0 T^0` (index 0). -/
theorem s4_wh_0 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 0 l = s4_osq ur ui 0 (s4_diff 0 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte]

/-- Weyl–Heisenberg covariance for the translate `S^0 T^1` (index 1). -/
theorem s4_wh_1 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 1 l = s4_osq ur ui 0 (s4_diff 1 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^0 T^2` (index 2). -/
theorem s4_wh_2 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 2 l = s4_osq ur ui 0 (s4_diff 2 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^0 T^3` (index 3). -/
theorem s4_wh_3 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 3 l = s4_osq ur ui 0 (s4_diff 3 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^1 T^0` (index 4). -/
theorem s4_wh_4 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 4 l = s4_osq ur ui 0 (s4_diff 4 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^1 T^1` (index 5). -/
theorem s4_wh_5 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 5 l = s4_osq ur ui 0 (s4_diff 5 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^1 T^2` (index 6). -/
theorem s4_wh_6 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 6 l = s4_osq ur ui 0 (s4_diff 6 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^1 T^3` (index 7). -/
theorem s4_wh_7 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 7 l = s4_osq ur ui 0 (s4_diff 7 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^2 T^0` (index 8). -/
theorem s4_wh_8 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 8 l = s4_osq ur ui 0 (s4_diff 8 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^2 T^1` (index 9). -/
theorem s4_wh_9 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 9 l = s4_osq ur ui 0 (s4_diff 9 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^2 T^2` (index 10). -/
theorem s4_wh_10 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 10 l = s4_osq ur ui 0 (s4_diff 10 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^2 T^3` (index 11). -/
theorem s4_wh_11 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 11 l = s4_osq ur ui 0 (s4_diff 11 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^3 T^0` (index 12). -/
theorem s4_wh_12 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 12 l = s4_osq ur ui 0 (s4_diff 12 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^3 T^1` (index 13). -/
theorem s4_wh_13 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 13 l = s4_osq ur ui 0 (s4_diff 13 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^3 T^2` (index 14). -/
theorem s4_wh_14 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 14 l = s4_osq ur ui 0 (s4_diff 14 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance for the translate `S^3 T^3` (index 15). -/
theorem s4_wh_15 (ur ui : ℕ → ℝ) : ∀ l, l < 16 → s4_osq ur ui 15 l = s4_osq ur ui 0 (s4_diff 15 l) := by
  intro l hl
  interval_cases l <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_diff, s4_rotRe,
      s4_rotIm, ↓reduceIte] <;> ring

/-- Weyl–Heisenberg covariance: the overlap of the translates `k` and `l` has the modulus of the overlap of `u` with
its translate by the difference of the displacements. -/
theorem s4_wh (ur ui : ℕ → ℝ) :
    ∀ k, k < 16 → ∀ l, l < 16 → s4_osq ur ui k l = s4_osq ur ui 0 (s4_diff k l) := by
  intro k hk
  interval_cases k
  · exact s4_wh_0 ur ui
  · exact s4_wh_1 ur ui
  · exact s4_wh_2 ur ui
  · exact s4_wh_3 ur ui
  · exact s4_wh_4 ur ui
  · exact s4_wh_5 ur ui
  · exact s4_wh_6 ur ui
  · exact s4_wh_7 ur ui
  · exact s4_wh_8 ur ui
  · exact s4_wh_9 ur ui
  · exact s4_wh_10 ur ui
  · exact s4_wh_11 ur ui
  · exact s4_wh_12 ur ui
  · exact s4_wh_13 ur ui
  · exact s4_wh_14 ur ui
  · exact s4_wh_15 ur ui

/-- The inner product of a translate with itself is `‖u‖²`. -/
theorem s4_diag (ur ui : ℕ → ℝ) : ∀ k, k < 16 →
    s4_ipRe ur ui k k = ur 0 ^ 2 + ui 0 ^ 2 + ur 1 ^ 2 + ui 1 ^ 2 + ur 2 ^ 2 + ui 2 ^ 2 + ur 3 ^ 2 + ui 3 ^ 2
      ∧ s4_ipIm ur ui k k = 0 := by
  intro k hk
  interval_cases k <;>
    simp +decide only [s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_sh, s4_rotRe, s4_rotIm,
      ↓reduceIte] <;>
    constructor <;> ring

/-! ## The fiducial -/

/-- Real parts of `u = (2c, s(1 − q) + c(1 + q) i, 2s i, s(1 + q) + c(1 − q) i)`. -/
def s4_ur (c s q : ℝ) (y : ℕ) : ℝ :=
  if y = 0 then 2 * c else if y = 1 then s * (1 - q) else if y = 2 then 0 else s * (1 + q)

/-- Imaginary parts of `u`. -/
def s4_ui (c s q : ℝ) (y : ℕ) : ℝ :=
  if y = 0 then 0 else if y = 1 then c * (1 + q) else if y = 2 then 2 * s else c * (1 - q)

/-- `‖u‖² = 6 + 2q²`, and every translate has the same norm. -/
theorem s4_norm (c s q : ℝ) (h1 : c ^ 2 + s ^ 2 = 1) : ∀ k, k < 16 →
    s4_ipRe (s4_ur c s q) (s4_ui c s q) k k = 6 + 2 * q ^ 2
      ∧ s4_ipIm (s4_ur c s q) (s4_ui c s q) k k = 0 := by
  intro k hk
  obtain ⟨hr, hi⟩ := s4_diag (s4_ur c s q) (s4_ui c s q) k hk
  refine ⟨?_, hi⟩
  rw [hr]
  simp +decide only [s4_ur, s4_ui, ↓reduceIte]
  linear_combination (2 * q ^ 2 + 6) * h1

/-- The fifteen overlaps of `u` with its nontrivial translates: `|⟨u, S^a T^b u⟩|² = (6 + 2q²)² / 5`. -/
theorem s4_base (c s q : ℝ) (h1 : c ^ 2 + s ^ 2 = 1) (h2 : c ^ 2 - s ^ 2 = 2 * c * s)
    (h3 : q ^ 4 = 4 * q ^ 2 + 1) : ∀ m, 1 ≤ m → m < 16 →
    s4_osq (s4_ur c s q) (s4_ui c s q) 0 m = (6 + 2 * q ^ 2) ^ 2 / 5 := by
  intro m hm0 hm
  interval_cases m <;>
    simp +decide only [s4_osq, s4_ipRe, s4_ipIm, s4_tr, s4_ti, s4_vr, s4_vi, s4_rotRe, s4_rotIm, s4_ur,
      s4_ui, ↓reduceIte]
  · linear_combination (-8 * (q ^ 2 + 1) * (-2 * c ^ 2 + 2 * c * s - 1)) * h1
      + (-8 * (q ^ 2 + 1) * (-2 * c * s + 2 * s ^ 2 - 1)) * h2
      + (-4 / 5) * h3
  · linear_combination (4 * (q - 1) ^ 2 * (q + 1) ^ 2 * (c ^ 2 + s ^ 2 + 1)) * h1
      + (16 / 5) * h3
  · linear_combination (-8 * (q ^ 2 + 1) * (-2 * c ^ 2 + 2 * c * s - 1)) * h1
      + (-8 * (q ^ 2 + 1) * (-2 * c * s + 2 * s ^ 2 - 1)) * h2
      + (-4 / 5) * h3
  · linear_combination (-8 * (-2 * c ^ 2 * q ^ 2 + 2 * c * q ^ 2 * s - 2 * c * s - q ^ 2 - 2 * s ^ 2 - 1)) * h1
      + (-8 * (q - 1) * (q + 1) * (-2 * c * s + 2 * s ^ 2 - 1)) * h2
      + (-4 / 5) * h3
  · linear_combination (8 * (q ^ 2 + 1) * (c ^ 2 + s ^ 2 + 1)) * h1
      + (-4 / 5) * h3
  · linear_combination (8 * (2 * c ^ 2 + 2 * c * q ^ 2 * s - 2 * c * s + 2 * q ^ 2 * s ^ 2 + q ^ 2 + 1)) * h1
      + (8 * (q - 1) * (q + 1) * (-2 * c * s + 2 * s ^ 2 - 1)) * h2
      + (-4 / 5) * h3
  · linear_combination (8 * (q ^ 2 + 1) * (c ^ 2 + s ^ 2 + 1)) * h1
      + (-4 / 5) * h3
  · linear_combination (4 * (q - 1) ^ 2 * (q + 1) ^ 2 * (c ^ 2 + s ^ 2 + 1)) * h1
      + (16 / 5) * h3
  · linear_combination (8 * (q ^ 2 + 1) * (2 * c * s + 2 * s ^ 2 + 1)) * h1
      + (8 * (q ^ 2 + 1) * (-2 * c * s + 2 * s ^ 2 - 1)) * h2
      + (-4 / 5) * h3
  · linear_combination (4 * (q - 1) ^ 2 * (q + 1) ^ 2 * (c ^ 2 + s ^ 2 + 1)) * h1
      + (16 / 5) * h3
  · linear_combination (8 * (q ^ 2 + 1) * (2 * c * s + 2 * s ^ 2 + 1)) * h1
      + (8 * (q ^ 2 + 1) * (-2 * c * s + 2 * s ^ 2 - 1)) * h2
      + (-4 / 5) * h3
  · linear_combination (-8 * (-2 * c ^ 2 * q ^ 2 + 2 * c * q ^ 2 * s - 2 * c * s - q ^ 2 - 2 * s ^ 2 - 1)) * h1
      + (-8 * (q - 1) * (q + 1) * (-2 * c * s + 2 * s ^ 2 - 1)) * h2
      + (-4 / 5) * h3
  · linear_combination (8 * (q ^ 2 + 1) * (c ^ 2 + s ^ 2 + 1)) * h1
      + (-4 / 5) * h3
  · linear_combination (8 * (2 * c ^ 2 + 2 * c * q ^ 2 * s - 2 * c * s + 2 * q ^ 2 * s ^ 2 + q ^ 2 + 1)) * h1
      + (8 * (q - 1) * (q + 1) * (-2 * c * s + 2 * s ^ 2 - 1)) * h2
      + (-4 / 5) * h3
  · linear_combination (8 * (q ^ 2 + 1) * (c ^ 2 + s ^ 2 + 1)) * h1
      + (-4 / 5) * h3

/-! ## The family in `ℂ⁴` -/

/-- Coordinate `x` of the translate with index `k` of `u`, as a complex number. -/
def s4_z (c s q : ℝ) (k : ℕ) (x : Fin 4) : ℂ :=
  (s4_vr (s4_ur c s q) (s4_ui c s q) k x.val : ℂ) + (s4_vi (s4_ur c s q) (s4_ui c s q) k x.val : ℂ) * I

/-- The sixteen vectors `N · S^a T^b u`, `k = 4a + b`. -/
noncomputable def s4_fam (c s q N : ℝ) (k : Fin (4 ^ 2)) : StateVector 4 :=
  WithLp.toLp 2 (fun x => (N : ℂ) * s4_z c s q k.val x)

theorem s4_term (r t r' t' : ℝ) :
    star ((r : ℂ) + (t : ℂ) * I) * ((r' : ℂ) + (t' : ℂ) * I)
      = ((r * r' + t * t' : ℝ) : ℂ) + ((r * t' - t * r' : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp
  · simp; ring

theorem s4_sum_z (c s q : ℝ) (k l : ℕ) :
    ∑ x : Fin 4, star (s4_z c s q k x) * s4_z c s q l x
      = (s4_ipRe (s4_ur c s q) (s4_ui c s q) k l : ℂ)
        + (s4_ipIm (s4_ur c s q) (s4_ui c s q) k l : ℂ) * I := by
  simp only [s4_z, s4_term]
  rw [Fin.sum_univ_four]
  simp only [s4_ipRe, s4_ipIm, s4_tr, s4_ti, Fin.val_zero, Fin.val_one, Fin.val_two]
  push_cast
  simp only [show ((3 : Fin 4) : ℕ) = 3 from rfl]
  ring

theorem s4_inner (c s q N : ℝ) (k l : Fin (4 ^ 2)) :
    ∑ x : Fin 4, star (s4_fam c s q N k x) * s4_fam c s q N l x
      = ((N * N : ℝ) : ℂ) * ((s4_ipRe (s4_ur c s q) (s4_ui c s q) k.val l.val : ℂ)
        + (s4_ipIm (s4_ur c s q) (s4_ui c s q) k.val l.val : ℂ) * I) := by
  have : ∀ x : Fin 4, star (s4_fam c s q N k x) * s4_fam c s q N l x
      = ((N * N : ℝ) : ℂ) * (star (s4_z c s q k.val x) * s4_z c s q l.val x) := by
    intro x
    simp only [s4_fam, PiLp.toLp_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun x _ => this x), ← Finset.mul_sum, s4_sum_z]

theorem s4_lt (i : Fin (4 ^ 2)) : i.val < 16 := i.isLt

/-- The SIC property for any parameters with `c² + s² = 1`, `c² − s² = 2cs`, `q⁴ = 4q² + 1` and
`N² (6 + 2q²) = 1`. -/
theorem s4_sic (c s q N : ℝ) (h1 : c ^ 2 + s ^ 2 = 1) (h2 : c ^ 2 - s ^ 2 = 2 * c * s)
    (h3 : q ^ 4 = 4 * q ^ 2 + 1) (hN : N ^ 2 * (6 + 2 * q ^ 2) = 1) :
    IsSICFamily 4 (s4_fam c s q N) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨hr, hm⟩ := s4_norm c s q h1 i.val (s4_lt i)
    have hs : ∑ x : Fin 4, ((‖s4_fam c s q N i x‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have : ∀ x : Fin 4, ((‖s4_fam c s q N i x‖ ^ 2 : ℝ) : ℂ)
          = star (s4_fam c s q N i x) * s4_fam c s q N i x := by
        intro x
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, Complex.star_def]
      rw [Finset.sum_congr rfl (fun x _ => this x), s4_inner, hr, hm]
      rw [show ((N * N : ℝ) : ℂ) * (((6 + 2 * q ^ 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)
          = ((N ^ 2 * (6 + 2 * q ^ 2) : ℝ) : ℂ) by push_cast; ring, hN]
      simp
    have hs' : ∑ x : Fin 4, ‖s4_fam c s q N i x‖ ^ 2 = 1 := by
      exact_mod_cast hs
    unfold IsNormalized
    rw [EuclideanSpace.norm_eq, hs', Real.sqrt_one]
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    obtain ⟨hm1, hm16⟩ := s4_diff_bounds i.val (s4_lt i) j.val (s4_lt j) hne
    have ho : s4_osq (s4_ur c s q) (s4_ui c s q) i.val j.val = (6 + 2 * q ^ 2) ^ 2 / 5 := by
      rw [s4_wh _ _ _ (s4_lt i) _ (s4_lt j)]
      exact s4_base c s q h1 h2 h3 _ hm1 hm16
    unfold s4_osq at ho
    show overlapSq (s4_fam c s q N i) (s4_fam c s q N j) = sicOverlapSq 4
    unfold overlapSq sicOverlapSq
    rw [s4_inner]
    set re := s4_ipRe (s4_ur c s q) (s4_ui c s q) i.val j.val
    set im := s4_ipIm (s4_ur c s q) (s4_ui c s q) i.val j.val
    have hc : ((N * N : ℝ) : ℂ) * ((re : ℂ) + (im : ℂ) * I)
        = ((N * N * re : ℝ) : ℂ) + ((N * N * im : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hc, Complex.normSq_add_mul_I]
    have he : (N * N * re) ^ 2 + (N * N * im) ^ 2 = (N ^ 2 * (6 + 2 * q ^ 2)) ^ 2 / 5 := by
      rw [show (N * N * re) ^ 2 + (N * N * im) ^ 2 = (N ^ 2) ^ 2 * (re ^ 2 + im ^ 2) by ring, ho]
      ring
    rw [he, hN]
    norm_num

/-- A SIC-POVM in dimension 4: the sixteen Weyl–Heisenberg translates of Appleby's fiducial (2005, eq. (149)),
`c = cos(π/8)`, `s = sin(π/8)`, `q = √(2 + √5)`, `N = √((5 − √5)/40)`. -/
theorem hasSICPOVM_four_internal : HasSICPOVM 4 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5n : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5le : Real.sqrt 5 ≤ 5 := by nlinarith
  have hq : Real.sqrt (2 + Real.sqrt 5) ^ 2 = 2 + Real.sqrt 5 := Real.sq_sqrt (by positivity)
  have hN : Real.sqrt ((5 - Real.sqrt 5) / 40) ^ 2 = (5 - Real.sqrt 5) / 40 := Real.sq_sqrt (by linarith)
  have hc2 := Real.cos_two_mul' (Real.pi / 8)
  have hs2 := Real.sin_two_mul (Real.pi / 8)
  rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four] at hc2
  rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.sin_pi_div_four] at hs2
  refine ⟨s4_fam (Real.cos (Real.pi / 8)) (Real.sin (Real.pi / 8)) (Real.sqrt (2 + Real.sqrt 5))
    (Real.sqrt ((5 - Real.sqrt 5) / 40)), s4_sic _ _ _ _ (Real.cos_sq_add_sin_sq _) ?_ ?_ ?_⟩
  · linear_combination hs2 - hc2
  · rw [show Real.sqrt (2 + Real.sqrt 5) ^ 4 = (Real.sqrt (2 + Real.sqrt 5) ^ 2) ^ 2 by ring, hq]
    linear_combination h5
  · rw [hN, hq]
    linear_combination (-1 / 20) * h5

end QuantumDesigns
