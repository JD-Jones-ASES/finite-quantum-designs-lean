# Disclosure

JD Jones directed this project. Claude (Anthropic) in Claude Code was used throughout: the statements, the Lean proofs,
the standard-library replay, the literature and prior-art searches, the checkers and the repository were produced in that
process; Weiner's paper (arXiv:0902.0635v2) was read in full, openai/math's Completion files only after the route of
PROOF.md §10 was fixed (nothing was copied from them), and Zauner's 1999 thesis, which Appleby 2005 credits for the
dimension-4 fiducial, was not read. A GPT-6 Pro (OpenAI) consult on 2026-10-10 reviewed the repository and contributed
statements 47–58 and 60 (`QuantumDesigns/Tomography.lean`, `QuantumDesigns/WelchEquality.lean`) with their Lean proofs, the
`--skip-build` reporting of `scripts/verify.py`, explicit failures in place of `assert` in `scripts/check_designs.py` and two
wording corrections; Claude rebuilt and audited these against the sources, dropped the hypothesis `d ≥ 1` from four of them,
renamed one, added statement 59 and wrote the final documents. The definitions are those of google-deepmind/formal-conjectures
(Open Quantum Problems 13 and 23, Apache-2.0; see NOTICE), restated character for character; the dimension-2 and 3 witness
families adapt its 23.lean and several lemmas adapt XC0R's fork, as their docstrings say. The theorems are published results
or direct corollaries of them; the proofs follow the published or standard routes, written for Mathlib. Verification status
is stated in VERIFICATION.md. No independent human review or source-author endorsement is claimed.
