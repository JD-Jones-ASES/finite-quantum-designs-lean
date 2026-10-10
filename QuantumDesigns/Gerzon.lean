module

public import QuantumDesigns.Defs

/-!
# Gerzon's bound over `ℂ`, its sharpness, the equality case, the frame identity

Lane **gerzon**. For `Φ : Fin N → StateVector d` with every `Φ i` normalized and `overlapSq (Φ i) (Φ j) = c` for
`i ≠ j`, let `P_i : Matrix (Fin d) (Fin d) ℂ := vecMulVec (Φ i) (star ∘ Φ i)` (entries `Φ i k * conj (Φ i l)`).

**Pairing identity.** For any `A : Matrix (Fin d) (Fin d) ℂ`, `Σ_{k,l} A k l * conj (Φ j k) * Φ j l = ⟨P_j, A⟩`-style:
in particular `Σ_{k,l} P_i k l * conj (Φ j k) * Φ j l = (Σ_k Φ i k conj (Φ j k)) (Σ_l conj (Φ i l) Φ j l) =
overlapSq (Φ i) (Φ j)` as a complex number (`Finset.sum_mul_sum`, `Fintype.sum_prod_type`, `Complex.mul_conj`,
`Complex.normSq_eq_conj_mul_self`), which is `1` for `i = j` (normalization: `EuclideanSpace.norm_eq`,
`Real.sq_sqrt`, `‖ψ‖² = Σ ‖ψ k‖² = Σ conj(ψ k) ψ k`) and `c` for `i ≠ j`.

**Bound.** Suppose `Σ_i g_i • P_i = 0` with `g : Fin N → ℂ`. Pairing with `Φ j` gives
`g_j + c Σ_{i ≠ j} g_i = 0`, i.e. `(1 − c) g_j + c S = 0` with `S = Σ_i g_i`. Summing over `j`:
`(1 − c) S + N c S = 0`, so `S (1 − c + N c) = 0`. If `N ≥ 2` then `c ≥ 0` (`Complex.normSq_nonneg`) and
`1 − c + N c = 1 + (N − 1) c > 0`, so `S = 0` and then `(1 − c) g_j = 0`, `g_j = 0` (`c ≠ 1`). If `N ≤ 1` the bound
`N ≤ d²` needs `d ≥ 1` when `N = 1`: a normalized vector exists only for `d ≥ 1` (`StateVector 0` has norm `0`).
So the `P_i` are linearly independent in `Matrix (Fin d) (Fin d) ℂ` of finrank `d²`
(`Fintype.linearIndependent_iff`, `LinearIndependent.fintype_card_le_finrank`, `Module.finrank_matrix` or
`Module.finrank_fintype_fun_eq_card` through `Matrix (Fin d) (Fin d) ℂ ≃ₗ (Fin d × Fin d → ℂ)`).

**Sharpness.** `Φ i = EuclideanSpace.single 0 1` for all `i` (`d ≥ 1`): normalized, every overlap `1`.

**Equality.** `N = d²`, `d ≥ 2`: the `P_i` form a basis (`LinearIndependent.span_eq_top_of_card_eq_finrank`), so
`1 = Σ_i a_i • P_i` (`Submodule.mem_span_range_iff_exists_fun`). Pairing with `Φ j`: `Σ_{k,l} δ_{kl} conj(Φ j k) Φ j l
= 1`, so `(1 − c) a_j + c A = 1` with `A = Σ a_i`; all `a_j` equal (`c ≠ 1`), `a_j = a`; the trace of `1` is `d` and
the trace of `P_i` is `1`, so `A = d² a = d`, `a = 1/d`; then `(1 − c)/d + c d = 1`, i.e. `c (d² − 1) = d − 1`,
`c = 1/(d + 1)` (`d ≥ 2` so `d − 1 ≠ 0`). The frame identity is `1 = Σ (1/d) • P_i`. `hasSICPOVM_iff_equiangular`:
`→` with `c = 1/(d + 1) ≠ 1`; `←` by `gerzon_equality`. `card_le_of_sicOverlapSq` is `gerzon_bound` with
`sicOverlapSq d ≠ 1` (`(d + 1)⁻¹ < 1` for `d ≥ 1`; at `d = 0`, `N = 0` since no vector of `ℂ⁰` is normalized).
-/

@[expose] public section

namespace QuantumDesigns

theorem gerzon_bound_internal {d N : ℕ} {c : ℝ} (hc : c ≠ 1) (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) : N ≤ d ^ 2 := sorry

theorem gerzon_sharp_internal (d N : ℕ) (hd : 1 ≤ d) :
    ∃ Φ : Fin N → StateVector d, (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq 1 Φ := sorry

theorem gerzon_equality_internal {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : c ≠ 1) (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) : c = sicOverlapSq d := sorry

theorem gerzon_frame_internal {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : c ≠ 1) (Φ : Fin (d ^ 2) → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq c Φ) :
    ∑ i, (d : ℂ)⁻¹ • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) = 1 := sorry

theorem isSICFamily_frame_internal {d : ℕ} (hd : 2 ≤ d) (Φ : Fin (d ^ 2) → StateVector d)
    (h : IsSICFamily d Φ) :
    ∑ i, (d : ℂ)⁻¹ • Matrix.vecMulVec (fun k => Φ i k) (fun l => star (Φ i l)) = 1 := sorry

theorem hasSICPOVM_iff_equiangular_internal (d : ℕ) (hd : 2 ≤ d) :
    HasSICPOVM d ↔ ∃ c : ℝ, c ≠ 1 ∧ ∃ Φ : Fin (d ^ 2) → StateVector d,
      (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq c Φ := sorry

theorem card_le_of_sicOverlapSq_internal {d N : ℕ} (Φ : Fin N → StateVector d)
    (hn : ∀ i, IsNormalized (Φ i)) (ho : HasConstantOverlapSq (sicOverlapSq d) Φ) : N ≤ d ^ 2 := sorry

end QuantumDesigns
