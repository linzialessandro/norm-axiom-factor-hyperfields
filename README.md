# The norm axiom and factor hyperfields

Source for the note *The norm axiom and factor hyperfields* (Alessandro Linzi).

arXiv: to be added

It concerns Question 1 of Touchard and the author (J. Pure Appl. Algebra 229 (2025) 107985):
is every valued hyperfield of the form H_rho(K) for a valued field K and an initial
segment rho? The note

- completes the proof of Proposition 4.11 in the author's Israel J. Math. 267 (2025) paper, so the
  question is equivalent to asking whether every Krasner valued hyperfield is a factor
  hyperfield (Theorem A);
- answers the question positively for value group Z (Theorem B);
- shows that a layering M ⋊ Γ is a factor hyperfield if and only if M is, which answers
  Section 7(2) of the author's 2025 paper negatively (Theorem C).

## Layout

- `paper/`: LaTeX source (amsart) and the built `main.pdf`. Build with `latexmk -pdf main.tex`.
- `scripts/`: brute-force checks in Python for the finite examples and lemmas.
