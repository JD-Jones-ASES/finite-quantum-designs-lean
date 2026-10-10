# The proofs, with the Lean names

The definitions are in `QuantumDesigns/Defs.lean`, identical to those of `Challenge.lean` (formal-conjectures'
vocabulary, see NOTICE). Each Challenge theorem is the `_internal` theorem of the same name in the module named in
VERIFICATION.md, restated in `Solution.lean`. `UMat d` is `Matrix.unitaryGroup (Fin d) ℂ`; `relativeUnitary U V =
U† V`; `StateVector d` is `EuclideanSpace ℂ (Fin d)`, with coordinates `ψ i`; `overlapSq φ ψ = ‖Σ_i conj(φ i) ψ i‖²`.

## 1. The bound (`QuantumDesigns/Bound.lean`)

For a basis `U` and a column `j`, `bd_proj U j` is the rank-one projector `(P_j)_{ab} = U_{aj} conj(U_{bj})`, and
`bd_vec` flattens a matrix to `EuclideanSpace ℂ (Fin d × Fin d)`, where the inner product is the Hilbert–Schmidt one
(`bd_inner_vec`). `bd_inner_proj`: `⟨P_j^U, P_l^V⟩ = R_{jl} conj(R_{jl})` with `R = relativeUnitary U V`; so inside one
basis the projectors are orthonormal (`bd_inner_proj_same`, from `U†U = 1`) and across two unbiased bases every pair
has inner product `1/d` (`bd_inner_proj_unbiased`); the identity matrix has inner product `1` with every projector
(`bd_inner_one_proj`, the trace). With `ζ = exp(2πi/d)` (`bd_zeta`, a primitive root: `Complex.isPrimitiveRoot_exp`),
for a basis `r` and a frequency `k + 1 ∈ {1, …, d − 1}` the vector `w_{r,k} = Σ_j ζ^{j(k+1)} P_j^r` (`bd_w`) has
`⟨w_{r,k}, w_{r,l}⟩ = Σ_x conj(ζ^{x(k+1)}) ζ^{x(l+1)}` (`bd_inner_w_same`), which is `d` for `k = l` and `0` otherwise
(`bd_geom_zero`: the geometric sum of `ζ^n` over `x < d` vanishes when `d ∤ n`, and `bd_not_dvd`: `d ∤ (d−1)(k+1) +
(l+1)` for `k ≠ l`); across two bases `r ≠ s` every `⟨P_j^r, P_l^s⟩ = 1/d`, so the inner product factors as
`(1/d) Σ_j conj(ζ^{j(k+1)}) Σ_y ζ^{y(l+1)} = 0` (`bd_inner_w_diff`); and `⟨1, w_{r,k}⟩ = Σ_j ζ^{j(k+1)} = 0`
(`bd_inner_one_w`). The family `bd_fam B : Option (Fin m × Fin (d − 1)) → EuclideanSpace ℂ (Fin d × Fin d)` (the
identity at `none`) is therefore pairwise orthogonal and nonzero, hence linearly independent
(`linearIndependent_of_ne_zero_of_inner_eq_zero`), so `1 + m(d − 1) ≤ d · d`
(`LinearIndependent.fintype_card_le_finrank`, `finrank_euclideanSpace`), and `m ≤ d + 1` for `d ≥ 2`
(`hasMUBs_le_internal`). The route is BBRV's Theorems 3.4–3.5 with the identity term, which XC0R's `d = 6` instance
omits (without it the count gives only `m ≤ 4` at `d = 2`).

`hasMUBs_one_dim_internal`: the constant family `fun _ => 1`, since `relativeUnitary 1 1 = 1` and `‖1‖² = 1 = 1⁻¹`.
`hasMUBs_of_le_internal`: `B ∘ Fin.castLE hkl`, with `Pairwise.comp_of_injective`.

## 2. The tensor bound (`QuantumDesigns/Tensor.lean`)

`tn_kroneckerUMat`: the Kronecker product of two unitaries, reindexed along `finProdFinEquiv` to `Fin (m * n)`, is
unitary (`Matrix.mul_kronecker_mul`, `Matrix.one_kronecker_one`). `tn_relativeUnitary_kronecker`: the relative unitary
of two Kronecker products is the Kronecker product of the relative unitaries; `tn_isUnbiased_kronecker`: entries
multiply, so squared norms `1/m` and `1/n` give `1/(mn)`; `hasMUBs_mul_internal` applies this to the `k` pairs. These
four adapt XC0R's `kroneckerUMat`, `relativeUnitary_kronecker`, `isUnbiased_kronecker` and `hasMUBs_mul`.
`hasMUBs_of_forall_primePow_internal` inducts with `Nat.recOnPosPrimePosCoprime`: `d = 1` is `hasMUBs_one_dim_internal`;
a prime power `pʲ` (`j ≥ 1`) has `primeFactors = {p}` and exponent `j` (`Nat.primeFactors_prime_pow`,
`Nat.Prime.factorization_pow`), so `k ≤ pʲ + 1` and restriction (`hasMUBs_of_le_internal`) of the complete set
(`hasCompleteMUBs_prime_pow_internal`) gives `HasMUBs pʲ k`; for coprime `a b` the exponents split
(`Nat.factorization_mul`; a prime dividing both would divide their gcd), so the hypothesis passes to both factors and
`hasMUBs_mul_internal` finishes. `hasMUBs_three_internal`: every exact prime-power divisor is `≥ 2`
(`Nat.Prime.factorization_pos_of_dvd`, `Nat.le_self_pow`), so `3 ≤ q + 1`.

## 3. Complete sets over a finite field of odd characteristic (`QuantumDesigns/OddField.lean`)

`quadSum_normSq_internal` by Weyl differencing: `RCLike.conj_mul` turns `‖S‖²` into `conj(S) · S`, a double sum; the
inner sum is reindexed by `x = y + t` (`Fintype.sum_equiv (Equiv.addLeft t)`), `conj(ψ A) ψ B = ψ(B − A)`
(`of_conj_mul_apply`), and `c(y + t)² + e(y + t) − c y² − e y = (c t² + e t) + (2 c t) y`, so the inner sum is
`Σ_y ψ((2ct) y)`, which `AddChar.sum_mulShift` (with `AddChar.IsPrimitive.of_ne_one`) evaluates to `|F|` if `2ct = 0` and
`0` otherwise; `2ct = 0` only at `t = 0` (`Ring.two_ne_zero h2`, `hc`; `Finset.sum_eq_single 0`), where the term is
`ψ 0 = 1`. `hasCompleteMUBs_of_odd_char_internal`: `ψ = AddChar.FiniteField.primitiveChar_to_Complex F` (nontrivial by
its primitivity at `1`), `e = Fintype.equivFin F`, and `of_M a` the matrix with entries `(√q)⁻¹ ψ(a x² + y x)`
(row `x = e.symm i`, column `y = e.symm j`); `of_M_entry`: `(M_a† M_{a'})_{j j'} = q⁻¹ Σ_x ψ((a' − a) x² + (y' − y) x)`;
`of_M_unitary` (the case `a = a'`, by `sum_mulShift`); unbiasedness to `1` by `AddChar.norm_apply` and
`Real.sq_sqrt`; between `M_a` and `M_{a'}`, `a ≠ a'`, by `quadSum_normSq_internal` with `c = a' − a`. The family
`Fin.cons 1 (fun k => M (e.symm k)) : Fin (q + 1) → UMat q` is pairwise unbiased by nested `Fin.cases`
(`of_isUnbiased_symm` for the symmetric cases).

## 4. Complete sets in dimension `2ⁿ` (`QuantumDesigns/TwoPow.lean`)

Signs and powers of `i`: `tp_sgn v = ±1` on `ZMod 2` (multiplicative, `tp_sgn_add`), `tp_om m = iᵐ` for `m : ℤ`
(`tp_om_add`, `tp_om_four_mul`, `tp_om_two_mul : i^{2m} = tp_sgn m`), `tp_u : ZMod 2 → ℤ` the `{0, 1}` lift with
`tp_u (a + b) = tp_u a + tp_u b − 2 tp_u a tp_u b` (`tp_u_add`). For a symmetric `S : Matrix (Fin n) (Fin n) (ZMod 2)`,
`tp_Q S x = Σ_{j,k} S̃_{jk} x̃_j x̃_k ∈ ℤ` and `tp_P S x t = Σ_{j,k} S̃_{jk} x̃_j t̃_k`; the ℤ/4 identity is exact over `ℤ`:
`tp_Q S (x + t) = tp_Q S x + tp_Q S t + 2 tp_P S x t + 4 m` (`tp_Q_add`, from `tp_u_add` and the antisymmetry lemma
`tp_antisym_sum`; symmetry of `S` is all it needs), so `tp_om_Q_add`: `i^{Q(x+t)} = i^{Q x} i^{Q t} tp_sgn(P(x, t))`
(`tp_P_cast`). `tp_sum_sgn`: `Σ_y tp_sgn(w · y) = 2ⁿ [w = 0]`; `tp_normSq_sum`: for a matrix `D` with `D t = 0 → t = 0` and
a unimodular `g` with `g(x + t) = g(x) g(t) tp_sgn(x · D t)`, `‖Σ_x g(x) tp_sgn(c · x)‖² = 2ⁿ`, by the substitution
`x = y + t` (`tp_unbiased` applies it with `g = i^{Q_S − Q_{S'}}` and `D = S − S'`; `tp_add_eq_sub`, `y + z = y − z` on
`Fin n → ZMod 2`, serves `tp_mat_unitary`). The bases: `tp_e n : Fin (2ⁿ) ≃ (Fin n → ZMod 2)` (`Fintype.equivFinOfCardEq`, `tp_card_V`),
`tp_mat S` with entry `(√2ⁿ)⁻¹ i^{Q_S x} tp_sgn(b · x)` at row `x`, column `b` (`tp_c_sq`, `tp_gram`, `tp_mat_unitary`,
`tp_norm_entry` against the standard basis, `tp_unbiased` for two symmetric `S`, `S'` whose difference is injective).
`tp_mubs_of_symmetric_spread`: a family `S : Fin (2ⁿ) → Matrix … (ZMod 2)` of symmetric matrices with
`(S a − S a') t = 0 → t = 0` for `a ≠ a'` gives `HasCompleteMUBs (2ⁿ)` (the family `Fin.cases 1 (fun a => tp_mat (S a))`),
for every `n`. `tp_exists_spread` (`n ≥ 1`): `K = GaloisField 2 n` (`Fintype.ofFinite`), a basis `β` of `K` over `ZMod 2`
(`Module.finBasisOfFinrankEq`, `GaloisField.finrank`), `S_a j k = trace(a β_j β_k)`; `S_a − S_{a'} = S_{a − a'}`, and `S_c t = 0` forces `trace(c x y) = 0`
for all `y` with `x = Σ t_j β_j`, so `c x = 0` by `traceForm_nondegenerate` (finite fields are separable), so `t = 0`;
`a` ranges over `K ≃ Fin (2ⁿ)` (`GaloisField.card`). `hasCompleteMUBs_two_pow_internal` combines the two.

## 5. Dimensions 2, 4, 8 by tables (`QuantumDesigns/Small.lean`, `SmallTables.lean`)

`SmallTables.lean` is a leaf importing only `Init`: the exponent tables `sm_tab2`, `sm_tab4`, `sm_tab8` (basis `a`,
column `b`, row `x`; the entry of the basis matrix is `c · i^E`, with `E = xᵀS_a x + 2 b·x mod 4` from the trace form of
`𝔽_{2ⁿ}` in the polynomial basis, as `scripts/check_designs.py` prints them) and a checker built from explicit `Nat.rec`
definitions (`sm_re`, `sm_im`, `sm_sumRe`, `sm_sumIm`, `sm_all`, `sm_E`, `sm_pairOK`, `sm_check`): for every pair of
columns `(a, b)`, `(a', b')` it sums `i^{3E + E'}` over the rows as integer real and imaginary parts and requires `(d, 0)`
on the diagonal, `(0, 0)` for two columns of one basis, and `re² + im² = d` across bases. `sm_tab2_ok`, `sm_tab4_ok`,
`sm_tab8_ok` are `decide +kernel`. `Small.lean` turns the verdict into the statement over
`ℂ`: `sm_I_pow` (`i^k = re k + im k · i`), `sm_star_I_pow` (`conj(i^e) = i^{3e}`), `sm_sum_I_pow`, the matrix `sm_M`
with entries `c · i^{E_a(b, x)}`, `sm_relEntry` (an entry of `M_a† M_{a'}` is `‖c‖² (re + im · i)`), `sm_unitary`,
`sm_cross` (`‖·‖² = ‖c‖⁴ (re² + im²) = 1/d`), `sm_entry_normSq` (against the standard basis), and the generic
`sm_hasMUBs`: a table passing `sm_check` with `‖c‖² = 1/d` gives `HasMUBs d (d + 1)` through the family `Fin.cons 1 U`.
The three theorems are one application each, with `c = (√2)⁻¹`, `1/2` and `(1 + i)/4`.

## 6. Three bases in every dimension, directly (`QuantumDesigns/Chirp.lean`)

A second proof of `hasMUBs_three`, without finite fields (`hasMUBs_three_chirp`). Write `d = N = n + 2` and index by
`ZMod N` (definitionally `Fin N`), with the primitive character `ψ = ZMod.stdAddChar` and `ζ = exp(πi/N)` (`ch_z`).
The three bases are `1`, the Fourier matrix `F j k = (√N)⁻¹ ψ(jk)` and the chirped Fourier matrix
`C j k = (√N)⁻¹ χ(j) ψ(jk)` (`ch_mat`) with `χ(j) = ζ^{j̃ (j̃ + N)}`, `j̃ = j.val` (`ch_chi`). `ch_exp_key`: the exponents of
`χ(j + t)` and of `χ(j) χ(t) ψ(jt)` agree modulo `2N` (split on whether `j̃ + t̃` wraps), so `χ(j + t) = χ(j) χ(t) ψ(jt)`
for every `N`, even or odd (`ch_chi_add`). `ch_orth` (the orthogonality relation of a primitive character,
`AddChar.sum_mulShift`) gives unitarity of `F` and `C` (`ch_mat_unitary`) and their unbiasedness to `1`
(`ch_unbiased_one`); `ch_cross_sum`: for `S = Σ_j χ(j) ψ(jm)`, substituting `j = j' + t` (`Equiv.sum_comp
(Equiv.addLeft j')`) and the functional equation give `conj(S) S = N`, hence every entry of `F† C` has squared norm `1/N`
(`ch_norm_sq_cross`, `ch_unbiased_FC`); `![1, F, C]` is pairwise unbiased by `fin_cases` (`ch_unbiased_symm`).

## 7. The assembly (`QuantumDesigns/PrimePow.lean`, `QuantumDesigns/Main.lean`)

`hasCompleteMUBs_prime_pow_internal`: `p = 2` is `hasCompleteMUBs_two_pow_internal`; otherwise `GaloisField p k`
(`Fintype.ofFinite`) has `p ^ k` elements (`GaloisField.card`) and characteristic `p ≠ 2` (`ringChar.eq`), so
`hasCompleteMUBs_of_odd_char_internal` applies. In `Main.lean` every `IsMaxMUBCount` is the pair of the construction and
`hasMUBs_le_internal` (with `2 ≤ pᵏ` from `Nat.Prime.two_le` and `Nat.le_self_pow`): `isMaxMUBCount_odd_prime_pow_internal`,
`isMaxMUBCount_two_pow_internal`, `isMaxMUBCount_prime_pow_internal`, and `isMaxMUBCount_two_internal`, `isMaxMUBCount_four_internal`, `isMaxMUBCount_eight_internal`
from `Small.lean`'s tables; `hasCompleteMUBs_iff_isMaxMUBCount_internal` is the same pair in one direction and the
first component in the other.

## 8. Gerzon's bound and the equality case (`QuantumDesigns/Gerzon.lean`)

`gz_P ψ = vecMulVec ψ (star ∘ ψ)` is the matrix `|ψ⟩⟨ψ|`, and `gz_pair ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ` is the
pairing `A ↦ Σ_{k,l} A k l · conj(ψ k) ψ l`, linear so that it passes through `Σ g_i • P_i` (`map_sum`, `map_smul`).
`gz_pairing`, `gz_pair_P`: `gz_pair ψ (gz_P φ) = overlapSq φ ψ` as a complex number (`Finset.sum_mul_sum`,
`Complex.normSq_eq_conj_mul_self`);
`gz_normalized`: `Σ_k conj(ψ k) ψ k = 1` for a unit vector (`EuclideanSpace.norm_sq_eq`, `Complex.normSq_eq_norm_sq`); hence
`gz_pair_one` (`gz_pair ψ 1 = 1`), `gz_overlap_self` and `gz_trace_P` (`trace (gz_P ψ) = 1`). `gz_pair_eq`: pairing
`Σ_i g_i • P_i` with `Φ_j` gives `c S + (1 − c) g_j` where `S = Σ g_i` (the `i = j` term is `g_j`, the others `c g_i`).
`gz_linIndep`: for `N ≥ 2` and `c ≠ 1` the `P_i` are linearly independent — from `Σ g_i • P_i = 0` every
`(1 − c) g_j + c S = 0`; summing over `j`, `S (1 − c + N c) = 0`, and `c ≥ 0` (a squared norm), so `S = 0` and `g_j = 0`.
`gerzon_bound_internal`: `N ≤ 1` is immediate when `d ≥ 1`, and `N = 1`, `d = 0` is impossible since no vector of `ℂ⁰`
is normalized (`gz_not_normalized_zero`); for `N ≥ 2`, `LinearIndependent.fintype_card_le_finrank` in
`Matrix (Fin d) (Fin d) ℂ`, of finrank `d · d`. `gerzon_sharp_internal`: `EuclideanSpace.single 0 1` repeated.
`gz_core` (`N = d²`, `d ≥ 2`): the `P_i` span (`LinearIndependent.span_eq_top_of_card_eq_finrank'`), so
`1 = Σ a_i • P_i`; pairing with each `Φ_j` gives `c A + (1 − c) a_j = 1` with `A = Σ a_i`, and the trace gives `A = d`;
summing the pairing equations over `j`: `d³ c + (1 − c) d = d²`, i.e. `d (d − 1)(c (d + 1) − 1) = 0`, so
`c = 1/(d + 1)` (`gerzon_equality_internal`); then each `a_j = 1/d` by one linear combination, which is the frame
identity (`gerzon_frame_internal`). `isSICFamily_frame_internal`: `sicOverlapSq d ≠ 1` for `d ≥ 1` (`gz_sic_ne_one`).
`hasSICPOVM_iff_equiangular_internal`: forward with `c = 1/(d + 1)`; backward by `gerzon_equality_internal`.
`card_le_of_sicOverlapSq_internal`: `d = 0` forces `N = 0` (no normalized vector); `d ≥ 1` is `gerzon_bound_internal`.

## 9. SIC-POVMs in dimensions 2, 3 and 8 (`QuantumDesigns/SIC.lean`, `SICTables.lean`)

**Dimension 8.** `SICTables.lean` is a leaf with no imports: the 64 vectors `v_i(x) = sign · ψ(x ⊕ ⌊i/8⌋)` with
`ψ = (−1 + 2i, 1, 1, 1, 1, 1, 1, 1)`, the sign the parity of `(i mod 8) ∧ (x ⊕ ⌊i/8⌋)` (a 3-bit xor of shifts), the real
and imaginary parts of the Gaussian-integer inner products `hg_ipRe`, `hg_ipIm` as integer functions on `ℕ` with the 8-term
sums written out; `hg_diag` (`hg_ipRe i i = 12`, `hg_ipIm i i = 0`) and `hg_overlaps` (`re² + im² = 16` for `i ≠ j`, all
4032 ordered pairs) are `decide +kernel`. `SIC.lean`: `hg_hoggar i = toLp 2 (fun x => (√12)⁻¹ (vr + vi · I))`;
`hg_term` (the generic product `conj(r + s i)(r' + s' i)` as integer real and imaginary parts), `hg_sum_z` (the eight
terms, `Fin.sum_univ_eight`), `hg_inner` (the inner sum is `(1/12)(hg_ipRe + hg_ipIm · i)`); normalization through
`EuclideanSpace.norm_eq` and `Real.mul_self_sqrt`, the overlaps through `Complex.normSq_add_mul_I`:
`16/144 = 1/9 = sicOverlapSq 8` (`hasSICPOVM_eight_internal`).

**Dimensions 2 and 3.** The tetrahedral family `hg_qubit a b r` (`(1, 0)` and `(a, b ω^m)`, `ω = −1/2 + (r/2) i`) and
the Hesse family `hg_hesse s r` (the nine vectors `(0, s, −s ω^m)`, `(−s ω^m, 0, s)`, `(s, −s ω^m, 0)`), with explicit
real and imaginary parts, adapt formal-conjectures' `qubitSICFamily` and `hesseFamily`; `hg_qubit_sic` and
`hg_hesse_sic` prove the SIC property for any parameters with `a² = 1/3`, `b² = 2/3`, `r² = 3` (resp. `s² = 1/2`,
`r² = 3`) by `fin_cases`, `simp`, `ring_nf`, the square relations and `norm_num`; the final theorems supply the parameters with
`Real.sq_sqrt` (`hasSICPOVM_two_internal`, `hasSICPOVM_three_internal`).
