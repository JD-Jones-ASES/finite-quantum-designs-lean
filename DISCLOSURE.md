# Disclosure

JD Jones directed this project. Claude (Anthropic) in Claude Code was used throughout, in two sessions: the statements,
the Lean proofs, the standard-library replay, the literature and prior-art searches, the checkers and the repository
were produced in that process. In the second session, which added statements 27–46, Weiner's paper (arXiv:0902.0635v2)
was read in full; openai/math's Completion files were read only after the route of PROOF.md §10 was fixed, and nothing
was copied from them; the dimension-4 fiducial was taken from Appleby 2005 (eqs. (6)–(8), (149)), and Zauner's 1999
thesis, which it credits, was not read. The definitions are those of google-deepmind/formal-conjectures (Open Quantum
Problems 13 and 23, Apache-2.0; see NOTICE), restated character for character; the dimension-2 and 3 witness families
adapt its 23.lean and several lemmas adapt XC0R's fork, as their docstrings say. The theorems are published results;
the proofs follow the published or standard routes, written for Mathlib. Verification status is stated in
VERIFICATION.md. No independent human review or source-author endorsement is claimed.
