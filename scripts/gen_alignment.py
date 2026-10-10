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

ALIGN = {
    "hasMUBs_le": (BBRV, "At most d + 1 mutually unbiased bases in dimension d >= 2 (the source states it for every d; the formal statement needs d >= 2, see hasMUBs_one_dim)."),
    "hasMUBs_one_dim": ("this development", "In dimension 1 every two bases are unbiased, so the hypothesis d >= 2 of the bound is necessary."),
    "hasMUBs_of_le": ("this development", "A subfamily of mutually unbiased bases is one."),
    "hasMUBs_mul": (KR + ", Lemma 3", "The tensor bound: Kronecker products of k unbiased bases of C^m and of C^n are k unbiased bases of C^(mn)."),
    "hasMUBs_of_forall_primePow": (KR + ", Lemma 3", "N(d) >= min over the exact prime-power divisors q of d of (q + 1), stated as HasMUBs d k for every k below that minimum."),
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
