module

public import QuantumDesigns.Bound
public import QuantumDesigns.Gerzon

/-!
# Welch's bound

For unit vectors `φ_1, …, φ_N` of `ℂ^d` with projectors `P_i = gz_P (φ_i) = |φ_i⟩⟨φ_i|` and frame operator
`S = Σ_i P_i`: `Tr S = N` (`gz_trace_P`) and `Tr(S^* S) = Σ_{i,j} Tr(P_i P_j) = Σ_{i,j} overlapSq (φ_i) (φ_j)`
(`gz_pair_P`: the pairing of `P_j` with `φ_i` is the squared overlap). The Cauchy–Schwarz inequality in the
flattened matrix space (`bd_vec`, `bd_inner_vec`; `inner_mul_inner_self_le`) for the identity and `S`:
`|⟨1, S⟩|² ≤ ‖1‖² ‖S‖²` with `⟨1, S⟩ = N` and `‖1‖² = d` (`wl_main`), that is
`N² ≤ d · Σ_{i,j} overlapSq (φ_i) (φ_j)` (`welch_bound_internal`; at `d = 0` the left side `N²/d` is `0`).
This is the case `k = 1` of Welch's bounds on `Σ_{i,j} |⟨φ_i, φ_j⟩|^{2k}` (Welch 1974, as restated by
Datta–Howard–Cochran, eq. (2), and by Mixon–Needham–Shonkwiler–Villar, Proposition 1), in the frame-potential form
(the name of Benedetto–Fickus 2003).
With a constant overlap `c` on the `N(N − 1)` pairs: `N²/d ≤ N + N(N − 1) c`, so `c ≥ (N − d)/(d(N − 1))` for
`N ≥ 2` (`welch_bound_of_constantOverlap_internal`, Datta–Howard–Cochran's eq. (1) with `k = 1`;
`c ≥ 0` is automatic, a squared norm). With every pairwise overlap at most `α` and `α d < 1`:
`N²/d ≤ N + N(N − 1) α`, so `N (1 − α d) ≤ d (1 − α)` (`welch_card_bound_internal`; `N = 0` is immediate); at
`α = 1/(d + 1)` this is `N ≤ d²` (`card_le_of_overlapSq_le_sic_internal`): a SIC family is a largest family of
unit vectors at or below the SIC angle (for `d ≥ 2`, the relative bound also shows that `d²` unit vectors cannot all
stay strictly below it).
-/

@[expose] public section
noncomputable section

namespace QuantumDesigns

/-- The frame operator `Σ_i φ_i φ_i†` of a family of vectors. -/
def wl_S {d N : ℕ} (Φ : Fin N → StateVector d) : Matrix (Fin d) (Fin d) ℂ := ∑ i, gz_P (Φ i)

lemma wl_S_apply {d N : ℕ} (Φ : Fin N → StateVector d) (a b : Fin d) :
    wl_S Φ a b = ∑ i, Φ i a * star (Φ i b) := by
  simp [wl_S, Matrix.sum_apply, gz_P, Matrix.vecMulVec_apply]

lemma wl_star_S_apply {d N : ℕ} (Φ : Fin N → StateVector d) (a b : Fin d) :
    star (wl_S Φ a b) = ∑ i, star (Φ i a) * Φ i b := by
  rw [wl_S_apply, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_star, mul_comm]

lemma wl_trace_S {d N : ℕ} {Φ : Fin N → StateVector d} (hn : ∀ i, IsNormalized (Φ i)) :
    (wl_S Φ).trace = N := by
  rw [wl_S, Matrix.trace_sum]
  simp [gz_trace_P (hn _)]

lemma wl_inner_one_S {d N : ℕ} {Φ : Fin N → StateVector d} (hn : ∀ i, IsNormalized (Φ i)) :
    inner ℂ (bd_vec (1 : Matrix (Fin d) (Fin d) ℂ)) (bd_vec (wl_S Φ)) = (N : ℂ) := by
  rw [bd_inner_vec, ← wl_trace_S hn]
  simp [Matrix.one_apply, Matrix.trace, Matrix.diag]

lemma wl_inner_S_one {d N : ℕ} {Φ : Fin N → StateVector d} (hn : ∀ i, IsNormalized (Φ i)) :
    inner ℂ (bd_vec (wl_S Φ)) (bd_vec (1 : Matrix (Fin d) (Fin d) ℂ)) = (N : ℂ) := by
  rw [← inner_conj_symm, wl_inner_one_S hn]
  simp

lemma wl_inner_one_one (d : ℕ) :
    inner ℂ (bd_vec (1 : Matrix (Fin d) (Fin d) ℂ)) (bd_vec (1 : Matrix (Fin d) (Fin d) ℂ)) = (d : ℂ) := by
  rw [bd_inner_vec]
  simp [Matrix.one_apply]

lemma wl_inner_S_S {d N : ℕ} (Φ : Fin N → StateVector d) :
    inner ℂ (bd_vec (wl_S Φ)) (bd_vec (wl_S Φ)) = ((∑ i, ∑ j, overlapSq (Φ i) (Φ j) : ℝ) : ℂ) := by
  have h1 : inner ℂ (bd_vec (wl_S Φ)) (bd_vec (wl_S Φ)) = ∑ i, gz_pair (Φ i) (wl_S Φ) := by
    rw [bd_inner_vec]
    calc ∑ a, ∑ b, star (wl_S Φ a b) * wl_S Φ a b
        = ∑ a, ∑ b, ∑ i, wl_S Φ a b * (star (Φ i a) * Φ i b) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [wl_star_S_apply, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ a, ∑ i, ∑ b, wl_S Φ a b * (star (Φ i a) * Φ i b) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, wl_S Φ a b * (star (Φ i a) * Φ i b) := Finset.sum_comm
      _ = ∑ i, gz_pair (Φ i) (wl_S Φ) := by simp only [gz_pair_apply]
  rw [h1]
  simp only [wl_S, map_sum, gz_pair_P]
  push_cast
  exact Finset.sum_comm

lemma wl_overlapSq_nonneg {d : ℕ} (φ ψ : StateVector d) : 0 ≤ overlapSq φ ψ :=
  Complex.normSq_nonneg _

/-- The frame-potential inequality `N² ≤ d · Σ_{i,j} |⟨φ_i, φ_j⟩|²`. -/
theorem wl_main {d N : ℕ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i)) :
    (N : ℝ) ^ 2 ≤ (d : ℝ) * ∑ i, ∑ j, overlapSq (Φ i) (Φ j) := by
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (bd_vec (1 : Matrix (Fin d) (Fin d) ℂ)) (bd_vec (wl_S Φ))
  rw [wl_inner_one_S hn, wl_inner_S_one hn, wl_inner_one_one, wl_inner_S_S] at h
  simp only [Complex.norm_natCast, RCLike.re_to_complex, Complex.natCast_re, Complex.ofReal_re] at h
  nlinarith [h]

/-- Off the diagonal at most `α`: `Σ_{i,j} |⟨φ_i, φ_j⟩|² ≤ N (1 + (N − 1) α)`. -/
theorem wl_sum_le {d N : ℕ} {α : ℝ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i))
    (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ α) :
    ∑ i, ∑ j, overlapSq (Φ i) (Φ j) ≤ (N : ℝ) * (1 + ((N : ℝ) - 1) * α) := by
  have hi : ∀ i, ∑ j, overlapSq (Φ i) (Φ j) ≤ 1 + ((N : ℝ) - 1) * α := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), gz_overlap_self (hn i)]
    have hle : ∑ j ∈ Finset.univ.erase i, overlapSq (Φ i) (Φ j) ≤ ∑ j ∈ Finset.univ.erase i, α :=
      Finset.sum_le_sum fun j hj => ho i j (Finset.ne_of_mem_erase hj).symm
    have hcard : ∑ j ∈ Finset.univ.erase i, α = ((N : ℝ) - 1) * α := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have h1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne'
      push_cast [Nat.cast_sub h1]
      ring
    linarith
  calc ∑ i, ∑ j, overlapSq (Φ i) (Φ j) ≤ ∑ _i : Fin N, (1 + ((N : ℝ) - 1) * α) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = (N : ℝ) * (1 + ((N : ℝ) - 1) * α) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma wl_dim_pos {d N : ℕ} (hN : 1 ≤ N) (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i)) :
    1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact absurd (hn ⟨0, hN⟩) (gz_not_normalized_zero _)
  · exact hd

/-- Welch's bound: `N` unit vectors of `ℂ^d` have `Σ_{i,j} |⟨φ_i, φ_j⟩|² ≥ N²/d`. -/
theorem welch_bound_internal {d N : ℕ} (Φ : Fin N → StateVector d) (hn : ∀ i, IsNormalized (Φ i)) :
    (N : ℝ) ^ 2 / (d : ℝ) ≤ ∑ i, ∑ j, overlapSq (Φ i) (Φ j) := by
  have hT : 0 ≤ ∑ i, ∑ j, overlapSq (Φ i) (Φ j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => wl_overlapSq_nonneg _ _
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using hT
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [div_le_iff₀ hd']
    have := wl_main Φ hn
    linarith

/-- Welch's bound for a constant overlap: `c ≥ (N − d)/(d(N − 1))` for `N ≥ 2`. -/
theorem welch_bound_of_constantOverlap_internal {d N : ℕ} {c : ℝ} (hN : 2 ≤ N) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    ((N : ℝ) - d) / ((d : ℝ) * ((N : ℝ) - 1)) ≤ c := by
  have ho' : Pairwise fun i j => overlapSq (Φ i) (Φ j) = c := ho
  have hle := wl_sum_le (α := c) Φ hn fun i j hij => (ho' hij).le
  have hmain := wl_main Φ hn
  have hd : 1 ≤ d := wl_dim_pos (by omega) Φ hn
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (d : ℝ) * ((N : ℝ) - 1) := by
    apply mul_pos <;> linarith
  rw [div_le_iff₀ hpos]
  have h2 : (N : ℝ) * (N : ℝ) ≤ (N : ℝ) * ((d : ℝ) * (1 + ((N : ℝ) - 1) * c)) := by
    have : (d : ℝ) * ∑ i, ∑ j, overlapSq (Φ i) (Φ j) ≤ (d : ℝ) * ((N : ℝ) * (1 + ((N : ℝ) - 1) * c)) :=
      mul_le_mul_of_nonneg_left hle (by linarith)
    nlinarith
  have h3 := le_of_mul_le_mul_left h2 (by linarith)
  nlinarith

/-- The relative bound: every pairwise squared overlap at most `α`, `α d < 1`, gives `N (1 − α d) ≤ d (1 − α)`. -/
theorem welch_card_bound_internal {d N : ℕ} {α : ℝ} (hα : α * (d : ℝ) < 1) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ α) :
    (N : ℝ) * (1 - α * (d : ℝ)) ≤ (d : ℝ) * (1 - α) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hα1 : α < 1 := by nlinarith
      simp only [Nat.cast_zero, zero_mul]
      nlinarith
  · have hle := wl_sum_le Φ hn ho
    have hmain := wl_main Φ hn
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : (N : ℝ) * (N : ℝ) ≤ (N : ℝ) * ((d : ℝ) * (1 + ((N : ℝ) - 1) * α)) := by
      have : (d : ℝ) * ∑ i, ∑ j, overlapSq (Φ i) (Φ j) ≤ (d : ℝ) * ((N : ℝ) * (1 + ((N : ℝ) - 1) * α)) :=
        mul_le_mul_of_nonneg_left hle hd0
      nlinarith
    have h3 := le_of_mul_le_mul_left h2 hN'
    nlinarith

/-- At most `d²` unit vectors of `ℂ^d` have every pairwise squared overlap at most `1/(d + 1)`. -/
theorem card_le_of_overlapSq_le_sic_internal {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : ∀ i j, i ≠ j → overlapSq (Φ i) (Φ j) ≤ sicOverlapSq d) :
    N ≤ d ^ 2 := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hu : sicOverlapSq d * ((d : ℝ) + 1) = 1 := by
    rw [sicOverlapSq]
    exact inv_mul_cancel₀ hd1.ne'
  have hu0 : 0 < sicOverlapSq d := by
    rw [sicOverlapSq]
    exact inv_pos.mpr hd1
  have hud : sicOverlapSq d * (d : ℝ) < 1 := by linarith
  have h := welch_card_bound_internal hud Φ hn ho
  have e1 : (N : ℝ) * (1 - sicOverlapSq d * d) = (N : ℝ) * sicOverlapSq d := by
    linear_combination (-(N : ℝ)) * hu
  have e2 : (d : ℝ) * (1 - sicOverlapSq d) = (d : ℝ) ^ 2 * sicOverlapSq d := by
    linear_combination (-(d : ℝ)) * hu
  rw [e1, e2] at h
  have h' : (N : ℝ) ≤ (d : ℝ) ^ 2 := le_of_mul_le_mul_right h hu0
  exact_mod_cast h'

end QuantumDesigns
