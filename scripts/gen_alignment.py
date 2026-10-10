#!/usr/bin/env python3
"""Desk tooling (not published): regenerates the `main_results:` list and the `alignment:` block of
formalization.yaml from Challenge.lean's theorem order and the ALIGN map below (source attribution and a one-line
note per theorem), so the yaml, comparator.json and VERIFICATION.md never drift. The yaml must contain the lines
`  main_results:` and `# END-MAIN-RESULTS` (the list between them is rewritten) and end with the `alignment:` block
(rewritten from that line on)."""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
NS = "QuantumDesigns"
KR = "Klappenecker-Rötteler 2004"
BBRV = "Bandyopadhyay-Boykin-Roychowdhury-Vatan 2002, Theorem 3.5"
ROY = "Roy 2005, Corollary 3.3.2 (the absolute bound of Delsarte-Goethals-Seidel 1975)"
RBSC = "Renes-Blume-Kohout-Scott-Caves 2004, section II"
JW = "Jedwab-Wiebe 2015, Example 4"
FC23 = "formal-conjectures OpenQuantumProblems/23.lean (the witness families)"
WEINER = "Weiner 2013"
WF = "Wootters-Fields 1989"
IVAN = "Ivanović 1981"
WELCH = "Welch 1974"
BF = "Benedetto-Fickus 2003"
SIC4SRC = "Appleby 2005, section 8, eq. (149) (the fiducial; Zauner 1999)"
SCOTT = "Scott 2006, eq. (9)"
RDHC = "as restated by Datta-Howard-Cochran"

ALIGN = {
    "hasMUBs_le": (BBRV, "At most d + 1 mutually unbiased bases in dimension d >= 2 (the source states it for every d; the formal statement needs d >= 2, see hasMUBs_one_dim)."),
    "hasMUBs_one_dim": ("this development", "In dimension 1 every two bases are unbiased, so the hypothesis d >= 2 of the bound is necessary."),
    "hasMUBs_of_le": ("this development", "A subfamily of mutually unbiased bases is one."),
    "hasMUBs_mul": (KR + ", Lemma 3", "The tensor bound: Kronecker products of k unbiased bases of C^m and of C^n are k unbiased bases of C^(mn)."),
    "hasMUBs_of_forall_primePow": (KR + ", Lemma 3", "N(d) >= min over the exact prime-power divisors q of d of (q + 1), stated as HasMUBs d k for every k at most that minimum."),
    "hasMUBs_three": (KR + ", remark after Lemma 3", "N(d) >= 3 for every d >= 2."),
    "quadSum_normSq": (KR + ", Lemma 1 (Weil sums), proved here by Weyl differencing", "The squared norm of the quadratic-phase sum over an odd-characteristic finite field is the field's size, for c != 0."),
    "hasCompleteMUBs_of_odd_char": (KR + ", Theorem 2", "The standard basis and the q bases psi(a x^2 + b x)/sqrt q are q + 1 mutually unbiased bases of C^q, for any finite field of odd characteristic."),
    "isMaxMUBCount_odd_prime_pow": (KR + ", Theorem 2, with " + BBRV, "mu(p^k) = p^k + 1 for odd p and k >= 1."),
    "hasCompleteMUBs_two_pow": (KR + ", Theorem 3 (an equivalent family in Z/4 trace-form coordinates)", "2^n + 1 mutually unbiased bases of C^(2^n) for n >= 1."),
    "isMaxMUBCount_two_pow": (KR + ", Theorem 3, with " + BBRV, "mu(2^n) = 2^n + 1 for n >= 1."),
    "isMaxMUBCount_prime_pow": (KR + ", Theorems 2 and 3, with " + BBRV, "mu(p^k) = p^k + 1 for every prime power."),
    "hasCompleteMUBs_iff_isMaxMUBCount": ("this development", "For d >= 2 a complete set exists iff d + 1 is the maximal number."),
    "isMaxMUBCount_two": ("formal-conjectures OpenQuantumProblems/13.lean, mutuallyUnbiasedBases_dim2 (re-proved by a kernel-checked table)", "mu(2) = 3."),
    "isMaxMUBCount_four": ("this development (a kernel-checked table)", "mu(4) = 5."),
    "isMaxMUBCount_eight": ("this development (a kernel-checked table)", "mu(8) = 9."),
    "gerzon_bound": (ROY, "N unit vectors of C^d with one squared overlap c != 1 on every pair satisfy N <= d^2."),
    "gerzon_sharp": ("this development", "With c = 1 the family may be any length, so c != 1 is necessary."),
    "gerzon_equality": (ROY + "; " + RBSC, "For d >= 2, d^2 such vectors have c = 1/(d + 1)."),
    "gerzon_frame": (RBSC, "For d >= 2, d^2 such vectors resolve the identity with weights 1/d."),
    "isSICFamily_frame": (RBSC, "Every SIC family is a POVM."),
    "hasSICPOVM_iff_equiangular": (ROY + ", Corollary 3.5.15 (context)", "For d >= 2, HasSICPOVM d iff d^2 equiangular unit vectors exist."),
    "card_le_of_sicOverlapSq": (ROY, "A family at the SIC angle has at most d^2 members."),
    "hasSICPOVM_two": (FC23, "The tetrahedral SIC-POVM of the qubit (formal-conjectures' hasSICPOVM_two, left with sorry there)."),
    "hasSICPOVM_three": (FC23, "The Hesse SIC-POVM of the qutrit (formal-conjectures' hasSICPOVM_three, left with sorry there)."),
    "hasSICPOVM_eight": (JW, "Hoggar's 64 lines as the three-qubit Pauli orbit of (-1 + 2i, 1, ..., 1)/sqrt 12, kernel-checked."),
    "hasCompleteMUBs_of_hasMUBs_self": (WEINER + ", Corollary 3.4 (the existence form)", "Weiner's gap: if d mutually unbiased bases of C^d exist, so does a complete set of d + 1 (the existence form of Corollary 3.4; for every d, trivially for d <= 1)."),
    "exists_isMUBFamily_extension": (WEINER + ", Corollary 3.4", "Weiner's gap in its extension form: any d mutually unbiased bases of C^d extend, by one more basis, to a complete set of d + 1, the given bases keeping their places."),
    "hasCompleteMUBs_of_le_hasMUBs": (WEINER + ", Corollary 3.4 (with restriction)", "k >= d mutually unbiased bases of C^d give a complete set."),
    "isMaxMUBCount_ne_self": (WEINER + ", p. 1 (N(d) != d)", "For d >= 2, d is never the maximal number of mutually unbiased bases."),
    "isMaxMUBCount_dichotomy": (WEINER + ", p. 1 (for d > 1, N(d) = d + 1 or N(d) <= d - 1)", "For d >= 2 the maximal number is d + 1 or at most d - 1."),
    "hasMUBs_two": ("this development (a restriction of hasMUBs_three for d >= 2)", "Two mutually unbiased bases in every dimension."),
    "hasMUBs_prime_pow_iff": (KR + ", Theorems 2 and 3, with " + BBRV, "In a prime-power dimension q, m mutually unbiased bases exist iff m <= q + 1."),
    "isMaxMUBCount_unique": ("this development", "The maximal number is unique."),
    "exists_isMaxMUBCount": ("this development (from the bound)", "For d >= 2 the maximal number exists."),
    "not_exists_isMaxMUBCount_one": ("this development", "In dimension 1 there is no maximal number."),
    "isMaxMUBCount_bounds": (KR + ", remark after Lemma 3, with " + BBRV, "For d >= 2 the maximal number lies in [3, d + 1]."),
    "mutuallyUnbiasedBases_dim6_bounds": ("formal-conjectures OpenQuantumProblems/13.lean, mutuallyUnbiasedBases_dim6_bounds (left with sorry there)", "3 <= mu(6) <= 7, in formal-conjectures' own statement."),
    "not_isMaxMUBCount_six_six": (WEINER + ", Corollary 3.4 at d = 6", "mu(6) != 6 (implied also by openai/math's N6_le_five, mu(6) <= 5)."),
    "mub_reconstruction": (SCOTT + ", for a complete set as a 2-design of weight 1/(d(d + 1)) (p. 11; after " + IVAN + " and " + WF + ")", "A complete set of d + 1 mutually unbiased bases determines every matrix from its diagonals: X = sum_{s,l} Tr(X P_{s,l}) P_{s,l} - Tr(X) 1."),
    "sic_reconstruction": (SCOTT + " with weight 1/d^2; " + RBSC + " (the projectors are linearly independent)", "A SIC family determines every matrix: X = sum_i ((d + 1) Tr(X P_i) - Tr X)/d P_i."),
    "welch_bound": (WELCH + ", the bound for k = 1 (" + RDHC + ", eq. (2)); " + BF + " (the frame potential)", "N unit vectors of C^d have sum_{i,j} |<phi_i, phi_j>|^2 >= N^2/d."),
    "welch_bound_of_constantOverlap": (WELCH + " (" + RDHC + ", eq. (1), k = 1); Roy 2005, Corollary 6.0.4 (equiangular lines)", "N >= 2 unit vectors with one squared overlap c on every pair have c >= (N - d)/(d (N - 1))."),
    "welch_card_bound": ("Roy 2005, Corollary 3.5.5 (the relative bound of Delsarte-Goethals-Seidel 1975, for equiangular lines); " + WELCH + ", the bound for k = 1, rearranged", "Every pairwise squared overlap at most alpha with alpha d < 1 gives N (1 - alpha d) <= d (1 - alpha), the relative bound."),
    "card_le_of_overlapSq_le_sic": (WELCH + ", the bound for k = 1, at alpha = 1/(d + 1)", "At most d^2 unit vectors of C^d have every pairwise squared overlap at most 1/(d + 1)."),
    "hasSICPOVM_four": (SIC4SRC, "A SIC-POVM in dimension 4: the Weyl-Heisenberg orbit of Appleby's exact fiducial, the overlaps by exact trigonometric and radical identities."),
}


def main():
    chal = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    names = re.findall(r"^theorem (\w+)", chal, flags=re.M)
    missing = [n for n in names if n not in ALIGN]
    if missing:
        raise SystemExit(f"ALIGN lacks: {missing}")
    path = ROOT / "formalization.yaml"
    text = path.read_text(encoding="utf-8")
    a = text.index("  main_results:\n") + len("  main_results:\n")
    b = text.index("# END-MAIN-RESULTS")
    mains = "".join(
        f'    - declaration: "{NS}.{n}"\n      file: "Solution.lean"\n      sorry_count: 0\n'
        f'      axioms: ["propext", "Classical.choice", "Quot.sound"]\n      comparator_config: "comparator.json"\n'
        for n in names)
    text = text[:a] + mains + text[b:]
    head = text[: text.index("\nalignment:") + 1]
    out = [head, "alignment:\n", f'  namespace: "{NS}"\n', "  statements:\n"]
    for n in names:
        src, note = ALIGN[n]
        out.append(f'    - source: "{src}"\n      lean: "{NS}.{n}"\n      module: "Solution"\n      status: "proved"\n      note: "{note}"\n')
    path.write_text("".join(out), encoding="utf-8", newline="\n")
    print(f"main_results and alignment: {len(names)} statements")


if __name__ == "__main__":
    main()
