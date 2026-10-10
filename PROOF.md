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

## 10. Weiner's gap (`QuantumDesigns/GapCore.lean`, `GapPhi.lean`, `GapKraus.lean`, `GapDFT.lean`, `GapSchwarz.lean`, `GapDiag.lean`, `GapMain.lean`)

The route is Weiner's proof (Weiner 2013, read as arXiv:0902.0635v2, §§2–3) with its operator-algebra steps written
out. The paper's Lemma 2.1, which it recalls from Werner 2001, and its Lemma 3.2, the Kraus form of the projection onto
the complement of the traceless parts of the `d` diagonal algebras, are used as they stand, with the Fourier basis
`w_{r,k}/√d` of each traceless part. Its Lemma 3.1 takes the Schwarz inequality for 2-positive maps and the
multiplicative domain from Choi 1974; here the Kadison–Schwarz defect of the Kraus form is written out as a sum of
squares of commutators, so a fixed point commutes with the Kraus operators, the step that openai/math's
`Completion/Kraus.lean` (commit `adc7f12`, 2026-10-06) takes for general `n` (`commutator_trace_identity`,
`commute_of_kraus_fixed`); that file was read after the route here was pinned. Its Proposition 3.3 (the complement is
a maximal abelian subalgebra, by a double-commutant argument) is not proved: a common eigenbasis of the commuting Kraus
operators gives the missing basis directly. Corollary 3.4 is proved for every `d`, in its extension form (the given
bases keep their places) and in its existence form.

**`GapCore`.** For a basis `U` with projectors `P_j = bd_proj U j`: `gp_diag U X j = Tr(P_j X)`, the diagonal of `X` in
`U`; `gp_pinch U X = Σ_j P_j X P_j`, the pinching (the paper's (4)); `gp_w U k = Σ_j ζ^{j(k+1)} P_j` for `k < d − 1`,
whose flattening is `bd_w` (`gp_vec_w`). For `d` bases `B`, Weiner's projection is `gp_Phi B X = X + Tr(X)·1 −
Σ_r gp_pinch (B r) X` (the paper's (13)–(14), rearranged), and `gp_Flat B X` says that the diagonal of `X` in every
`B s` is the constant `Tr(X)/d`. `gp_unvec` inverts the flattening (`gp_unvec_vec`, `gp_vec_unvec`);
`gp_inner_vec_eq_trace` reads the flattened inner product as `Tr(A^* X)`, and `gp_diag_eq_inner` the diagonal as
`⟨P_j, X⟩` (`gp_proj_star`: the projectors are Hermitian).

**`GapPhi`.** Inside one basis `P_j X P_j = x_j P_j` with `x_j = gp_diag U X j` (`gp_proj_mul_mul_proj`) and
`Σ_j P_j = 1` (`gp_sum_proj`, from `U U^* = 1`), so the pinching is `Σ_j x_j P_j` (`gp_pinch_eq`) and `Σ_j x_j = Tr X`
(`gp_sum_diag`). The diagonal of a pinching in its own basis is `x` (`gp_diag_pinch_same`, from `gp_diag_proj_same`:
`Tr(P_j P_l) = δ_{jl}`) and in an unbiased basis the constant `Tr(X)/d` (`gp_diag_pinch_unbiased`, from
`gp_diag_proj_unbiased`: `Tr(P^U_j P^V_l) = 1/d`); the diagonal is linear (`gp_diag_add`, `gp_diag_sub`, `gp_diag_smul`,
`gp_diag_sum`). So for `d` mutually unbiased bases the diagonal of `gp_Phi B X` in the basis `s` at `l` is
`x_{s,l} + Tr X − x_{s,l} − (d − 1) Tr(X)/d = Tr(X)/d`: `gp_Phi B X` is flat (`gp_flat_Phi`). A flat `X` has every
pinching equal to `(Tr(X)/d)·1`, so `gp_Phi B X = X` (`gp_Phi_of_flat`). Also `gp_Phi_one`, `gp_Phi_trace`
(`Tr Φ(X) = Tr X + d Tr X − d Tr X`), `gp_Phi_star`, and the flatness of `X^*` and of `1` (`gp_flat_star`, `gp_flat_one`).

**`GapKraus`.** The paper's Lemma 2.1: for an orthonormal basis `b` of the flattened matrix space,
`Σ_i b_i^* X b_i = Tr(X)·1` (`gp_onb_sum`); entry `(p, q)` is `Σ_{a,c} X_{ac} Σ_i conj((b_i)_{ap}) (b_i)_{cq}`, and the
inner sum is Parseval's identity for the matrix units, `δ_{ac} δ_{pq}` (`gp_onb_parseval`,
`OrthonormalBasis.sum_inner_mul_inner`). The weighted projectors conjugate to the pinching: `w_k^* X w_k =
Σ_{j,j'} ζ^{(j'−j)(k+1)} P_j X P_{j'}` (`gp_star_w_mul`), and over the frequencies `0, …, d − 1` (frequency `0` gives
`X`) the geometric sums are `d δ_{jj'}` (`gp_freq`, `gp_freq_zero`, `gp_geom`, `gp_sum_freq`, from `bd_geom_zero`), so
`Σ_{k<d−1} w_k^* X w_k = d Σ_j P_j X P_j − X` (`gp_w_sum`; the paper's (11) with its basis of each traceless part taken
to be the `w_k/√d`). The Kraus form, the paper's Lemma 3.2 (`gp_exists_kraus`): the `d(d − 1)` vectors `w_{r,k}/√d`
(`gp_kfam`, `gp_exists_scale`) are orthonormal (`gp_kfam_orthonormal`, from `bd_inner_w_self`, `bd_inner_w_same_ne`,
`bd_inner_w_diff`) in a space of dimension `d² = d(d − 1) + d`, so they extend to an orthonormal basis indexed by
`Fin d × Fin (d − 1) ⊕ Fin d` (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`); the `d` added vectors, as
matrices `K_i`, are orthogonal to every `w_{r,k}`, and `gp_onb_sum` with `gp_w_sum` for each basis gives
`Σ_i K_i^* X K_i = Tr(X)·1 − Σ_r (E_r(X) − X/d) = gp_Phi B X` and `Σ_i K_i^* K_i = gp_Phi B 1 = 1`.

**`GapDFT`.** In a basis `U`, `⟨w_k, X⟩ = Σ_j conj(ζ^{j(k+1)}) x_j` (`gp_dft_inner_w`, through `gp_dft_vec_sum` and
`gp_diag_eq_inner`): the discrete Fourier transform of the diagonal at the frequency `k + 1`. If it vanishes at every
frequency `1, …, d − 1`, Fourier inversion (`gp_dft_orth`: `Σ_{m<d} ζ^{lm} conj(ζ^{jm}) = d δ_{jl}`, from `bd_geom_zero`
and `bd_not_dvd`) keeps only the frequency `0`: `d x_l = Σ_j x_j = Tr X` (`gp_dft_sum_diag`, `gp_dft_sum_proj`). So a
matrix orthogonal to every `w_k` of `U` has the constant diagonal `Tr(X)/d` in `U` (`gp_flat_of_orth`), the description
of the complement by its diagonals that the paper leaves implicit.

**`GapSchwarz`.** For matrices `K_i` with `Σ_i K_i^* K_i = 1` and `C = Σ_i K_i^* X K_i`,
`Σ_i K_i^* X^* X K_i − C^* C = Σ_i (X K_i − K_i C)^* (X K_i − K_i C)` (`gp_schwarz_defect`, by expanding the right side,
with `gp_sum_mul_mul_eq`): the Kadison–Schwarz defect of a Kraus map is a sum of squares. A sum of matrices `A_i^* A_i`
with zero trace has every `A_i = 0`, since `Tr(A^* A) = Σ_{a,b} ‖A_{ab}‖²` (`gp_eq_zero_of_sum_trace`,
`gp_eq_zero_of_trace_sum_star_mul_self`). So a fixed point `X` (`C = X`) of a Kraus map that preserves the trace of
`X^* X` commutes with every `K_i` (`gp_commute_of_fixed`), the standard fact that the fixed points of a unital,
trace-preserving channel commute with its Kraus operators.

**`GapDiag`.** `gp_simultaneous_diag`: a finite family of pairwise commuting Hermitian matrices `H_i` has a unitary `W`
with every `W^* H_i W` diagonal. The operators `toEuclideanLin (H_i)` are symmetric
(`Matrix.isSymmetric_toEuclideanLin_iff`) and commute, so the joint eigenspaces `⨅_i eigenspace (H_i) (χ i)` form an
internal direct sum (`LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`), orthogonal across distinct `χ`
(`orthogonalFamily_iInf_eigenspaces`); finitely many are nonzero (`iSupIndep.fintypeNeBotOfFiniteDimensional`,
`DirectSum.isInternal_ne_bot_iff`), and an orthonormal basis indexed by `Fin d` and subordinate to them
(`DirectSum.IsInternal.subordinateOrthonormalBasis`) gives the columns of `W`
(`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`).

**`GapMain`.** Given `B : Fin d → UMat d` pairwise unbiased, let `K` be the Kraus family of `gp_exists_kraus`. Each
`K_i` is orthogonal to every `w_{r,k}`, hence flat (`gp_flat_of_orth` through `gp_vec_w`); a flat `X` is fixed
(`gp_Phi_of_flat`) and `gp_Phi` preserves traces (`gp_Phi_trace`), so by `gp_commute_of_fixed` every flat matrix
commutes with every `K_j`, in particular `K_i` and `K_i^*` (`gp_flat_star`). The `2d` Hermitian parts `K_i + K_i^*` and
`i (K_i − K_i^*)` (`gp_herm`, `gp_herm_isHermitian`) therefore commute pairwise (`gp_herm_commute`), and
`gp_simultaneous_diag` gives a unitary `W` in which all of them are diagonal. A matrix diagonal in `W` commutes with
every projector `Q_l = bd_proj W l` (`gp_commute_proj_of_diag`), and `K_i = ((K_i + K_i^*) − i·i(K_i − K_i^*))/2`
(`gp_herm_recover`), so every `K_i` commutes with `Q_l` and `gp_Phi B Q_l = Σ_i K_i^* Q_l K_i = (Σ_i K_i^* K_i) Q_l =
Q_l`. By `gp_flat_Phi`, `Q_l` is flat: `gp_diag (B s) Q_l l' = Tr(Q_l)/d = 1/d` (`gp_trace_proj`), which
`gp_diag_eq_inner` and `bd_inner_proj` read as `‖((B s)^* W)_{l'l}‖² = 1/d`. So `W` is unbiased to every `B s`, and
`Fin.cons W B : Fin (d + 1) → UMat d` is pairwise unbiased (`of_isUnbiased_symm` for the symmetric pairs), with
`B r` at `r.succ` (`Fin.cons_succ`): `exists_isMUBFamily_extension_internal`, of which
`hasCompleteMUBs_of_hasMUBs_self_internal` keeps the family. The corollaries: `hasCompleteMUBs_of_le_hasMUBs_internal` restricts
`k ≥ d` bases to `d` (`hasMUBs_of_le_internal`); `isMaxMUBCount_ne_self_internal`: `IsMaxMUBCount d d` would give
`d + 1 ≤ d`; `isMaxMUBCount_dichotomy_internal` adds the bound `k ≤ d + 1` (`hasMUBs_le_internal`);
`not_isMaxMUBCount_six_six_internal` is the instance `d = 6`.

## 11. The maximal number (`QuantumDesigns/Count.lean`)

`hasMUBs_two_internal`: for `d ≥ 2` restriction of three bases (`hasMUBs_three_internal`, `hasMUBs_of_le_internal`);
`d = 1` is `hasMUBs_one_dim_internal`; at `d = 0` the constant family `fun _ => 1` is unbiased vacuously (`Fin 0` has no
entries). `hasMUBs_prime_pow_iff_internal`: forward, the maximality clause of `isMaxMUBCount_prime_pow_internal`;
backward, restriction of its complete set. `isMaxMUBCount_unique_internal`: two maxima bound each other
(`le_antisymm`). `exists_isMaxMUBCount_internal`: `Nat.findGreatest (HasMUBs d) (d + 1)`, which satisfies `HasMUBs d`
since `HasMUBs d 0` holds (`Nat.findGreatest_spec`, restriction of three bases) and bounds every `m` with `HasMUBs d m`,
each at most `d + 1` (`hasMUBs_le_internal`, `Nat.le_findGreatest`). `not_exists_isMaxMUBCount_one_internal`:
`HasMUBs 1 (k + 1)` exceeds any candidate `k`. `isMaxMUBCount_bounds_internal`: `3 ≤ k` by maximality against
`hasMUBs_three_internal`, `k ≤ d + 1` by `hasMUBs_le_internal`. `mutuallyUnbiasedBases_dim6_bounds_internal` is the pair
of `hasMUBs_three_internal` and `hasMUBs_le_internal` at `d = 6`, formal-conjectures' statement as written there.

## 12. Reconstruction (`QuantumDesigns/Reconstruct.lean`)

**A complete set** (`mub_reconstruction_internal`; the formula as printed in Scott 2006, eq. (9), with the weights
`1/(d(d + 1))`, after Ivanović 1981 and Wootters–Fields 1989). With `P_{s,l} = bd_proj (B s) l` (`rc_proj_eq`: the
projector of the statement), `T(X) = Σ_{s,l} Tr(X P_{s,l}) P_{s,l} − Tr(X)·1` is linear (`rc_T`, `rc_T_apply`). It fixes
`1` (`rc_T_one`: `Σ_l P_{s,l} = 1`, `rc_sum_proj`; `Tr P_{s,l} = 1`, `rc_trace_proj`; `Tr 1 = d`) and every `P_{r,j}`
(`rc_T_proj`: `Tr(P_{r,j} P_{s,l})` is the Hilbert–Schmidt inner product, `rc_trace_mul_proj`, so `δ_{jl}` for `s = r`
and `1/d` otherwise; the other `d` bases contribute `(1/d) Σ_l P_{s,l} = (1/d)·1` each, in all `1`, which `Tr(P_{r,j})·1`
cancels). The identity and the `(d + 1)(d − 1)` matrices `Σ_j ζ^{j(k+1)} P_{r,j}` (`rc_F`, whose flattening is
`bd_fam B`, `rc_vec_F` with `rc_vecL` the flattening as a linear map) are linearly independent by the argument of
`hasMUBs_le_internal` (`rc_fam_linIndep`, `LinearIndependent.of_comp`); they are `d²`, so they span the matrix space
(`rc_F_span`, `LinearIndependent.span_eq_top_of_card_eq_finrank'`, `Module.finrank_matrix`), and `T` fixes every matrix
(`rc_T_fix`). At `d = 0` the matrices are empty.

**A SIC family** (`sic_reconstruction_internal`; the informational completeness is Renes–Blume-Kohout–Scott–Caves 2004,
§II, and the coefficients are Scott 2006, eq. (9), with the weights `1/d²`). The `d²` projectors `P_i = gz_P (φ_i)` are
linearly independent (`rc_linIndep`: from `Σ_i g_i P_i = 0` the trace gives `Σ_i g_i = 0` and the pairing with `φ_j`,
`gz_pair_eq`, gives `(1 − c) g_j = 0`, with `c = 1/(d + 1) ≠ 1`), so they span the matrix space. Write
`X = Σ_i a_i P_i`; `Tr(X P_j)` is the pairing of `X` with `φ_j` (`rc_trace_eq_pair`), so `gz_pair_eq` gives
`Tr(X P_j) = (1 − c) a_j + c Σ_i a_i`, and the trace gives `Tr X = Σ_i a_i`; hence `a_j = ((d + 1) Tr(X P_j) − Tr X)/d`.
At `d = 0` the matrices are empty.

## 13. Welch's bound (`QuantumDesigns/Welch.lean`)

With `P_i = gz_P (φ_i)` and the frame operator `S = Σ_i P_i` (`wl_S`, `wl_S_apply`, `wl_star_S_apply`): `Tr S = N`
(`wl_trace_S`, from `gz_trace_P`) and `⟨S, S⟩ = Σ_{i,j} Tr(P_i P_j) = Σ_{i,j} overlapSq (φ_i) (φ_j)` (`wl_inner_S_S`,
through `gz_pair_P`). The Cauchy–Schwarz inequality in the flattened matrix space (`bd_vec`, `bd_inner_vec`,
`inner_mul_inner_self_le`) for `1` and `S`, with `⟨1, S⟩ = ⟨S, 1⟩ = N` (`wl_inner_one_S`, `wl_inner_S_one`) and
`⟨1, 1⟩ = d` (`wl_inner_one_one`), is `N² ≤ d Σ_{i,j} overlapSq (φ_i) (φ_j)` (`wl_main`); dividing by `d` gives
`welch_bound_internal` (at `d = 0` the left side is `N²/0 = 0`). With every pairwise overlap at most `α`,
`Σ_{i,j} overlapSq ≤ N (1 + (N − 1) α)` (`wl_sum_le`, `wl_overlapSq_nonneg`). A constant overlap `c` gives
`N² ≤ d (N + N (N − 1) c)` with `d ≥ 1` (`wl_dim_pos`: no unit vector lives in `ℂ⁰`), so `c ≥ (N − d)/(d(N − 1))` for
`N ≥ 2` (`welch_bound_of_constantOverlap_internal`); `α d < 1` gives `N (1 − α d) ≤ d (1 − α)`
(`welch_card_bound_internal`; `N = 0` is immediate); and `α = 1/(d + 1)` gives `N ≤ d²`
(`card_le_of_overlapSq_le_sic_internal`). The bound is Welch
1974 (closed access, not read), in the form stated by Datta–Howard–Cochran, eq. (2) with `k = 1`, and by
Mixon–Needham–Shonkwiler–Villar, Proposition 1; `Σ_{i,j} |⟨φ_i, φ_j⟩|²` is the frame potential of Benedetto–Fickus 2003.

## 14. A SIC-POVM in dimension 4 (`QuantumDesigns/SIC4.lean`, `SIC4Tables.lean`)

**The fiducial** is Appleby's (Appleby 2005, §8, eq. (149), which credits Zauner 1999 and Renes–Blume-Kohout–Scott–Caves
2004): with `c = cos(π/8)`, `s = sin(π/8)`, `q = √(2 + √5)` and `N² = (5 − √5)/40`, `ψ = N u` where
`u = (2c, s(1 − q) + c(1 + q) i, 2s i, s(1 + q) + c(1 − q) i)` (`s4_ur`, `s4_ui`) and `‖u‖² = 6 + 2q²` (`s4_norm`).
**The family** is the sixteen translates `(S^a T^b u)(x) = i^{b(x − a)} u(x − a)`, indices mod 4, numbered `k = 4a + b`
(the paper's displacement operators, eqs. (6)–(8), without the phase `τ^{ab}`). `SIC4Tables.lean` is a leaf with no
imports: the shifted coordinate `s4_sh` (`x − a`), the phase exponent `s4_ph` (`b(x − a)`), the index `s4_diff k l` of
the difference of two displacements, and `s4_diff_bounds` (`decide +kernel`: `1 ≤ s4_diff k l ≤ 15` for `k ≠ l`).
`SIC4.lean` writes the translates of a vector with arbitrary real parts `ur` and imaginary parts `ui` in real
coordinates (`s4_rotRe`, `s4_rotIm` for the factor `iⁿ`; `s4_vr`, `s4_vi`), with the real and imaginary parts of their
inner products (`s4_tr`, `s4_ti`, `s4_ipRe`, `s4_ipIm`) and the squared modulus `s4_osq`. Weyl–Heisenberg covariance,
`s4_wh`: for arbitrary `ur`, `ui`, the squared overlap of the translates `k` and `l` is that of `u` with its translate
`s4_diff k l` (sixteen row lemmas `s4_wh_0` … `s4_wh_15`, by `interval_cases`, `simp +decide only` and `ring`); a
translate's inner product with itself is `‖u‖²` (`s4_diag`). The fifteen base overlaps, `s4_base`:
`|⟨u, S^a T^b u⟩|² = (6 + 2q²)²/5`, by `linear_combination` with explicit polynomial coefficients from `c² + s² = 1`,
`c² − s² = 2cs` and `q⁴ = 4q² + 1`. The bridge to `ℂ⁴` follows `hg_inner` of §9: `s4_z`, `s4_fam c s q N k = N u_k`,
`s4_term`, `s4_sum_z`, `s4_inner` (the inner sum is `N² (s4_ipRe + s4_ipIm · i)`); `s4_sic`: for any parameters with
these relations and `N² (6 + 2q²) = 1` the sixteen vectors are unit vectors with squared overlaps
`(N² (6 + 2q²))²/5 = 1/5 = sicOverlapSq 4`. `hasSICPOVM_four_internal` supplies `c` and `s` (`Real.cos_two_mul'`,
`Real.sin_two_mul`, `cos_pi_div_four`, `sin_pi_div_four`), `q` and `N` (`Real.sq_sqrt`). No table of overlaps is
kernel-checked; only the index arithmetic is.
