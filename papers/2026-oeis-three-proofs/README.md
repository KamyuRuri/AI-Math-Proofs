# Resolved Conjectures on OEIS A352834, A304362, and A174013
# 三个 OEIS 猜想的完整证明与 Lean 4 形式化验证

[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.36.0-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](../../LICENSE)

**Authors / 作者:** Gemini, ChatGPT, and JiaZhuang Wang\* (\*Corresponding author / 通讯作者)

Complete mathematical proofs, independent exact-arithmetic verification, a publication-ready LaTeX/PDF paper, and full **Lean 4 + Mathlib4** formalization (zero `sorry`, zero `native_decide`) resolving three open conjectures on the On-Line Encyclopedia of Integer Sequences (OEIS): **A352834**, **A304362**, and **A174013**.

本项目包含三个 OEIS 公开猜想（**A352834**、**A304362**、**A174013**）的完整数学证明、独立 Python 精确算术校验、LaTeX/PDF 论文以及 **Lean 4 (v4.36.0) + Mathlib4** 形式化验证（无任何 `sorry` 与 `native_decide`）。

---

## Summary of Results / 核心结论

| Sequence | Main Result / 核心定理 | Lean 4 Module & Key Theorems | Paper |
| :--- | :--- | :--- | :--- |
| **[A352834](https://oeis.org/A352834)** | $a(n) = O_\varepsilon(n^\varepsilon)$ for all $\varepsilon > 0$ via explicit Bernoulli divisor bound; $a(n)/n^{1/3}$ attains its unique global maximum $840/154440^{1/3} \approx 15.656428$ strictly at $n = 154440$ ($a(154440)=840$). | [`OEISThreeProofs/A352834.lean`](OEISThreeProofs/A352834.lean)<br>`IsValidA352834_iff_den`, `divisor_bound_explicit`, `a352834_subpolynomial`, `a352834_154440`, `a352834_global_bound`, `a352834_strict_of_ne`, `a352834_real_extremum` | Section 2 |
| **[A304362](https://oeis.org/A304362)** | Every integer $z \in \mathbb{Z}$ is attained infinitely often ($b : \mathbb{N}_{>0} \to \mathbb{Z}$ is surjective with infinite fibers), via explicit Fermat–CRT exponents $u_i = Q_i^{q_i-1} + Q$. Includes worked example $b(2^{36} \cdot 3^{21} \cdot 5^{15}) = -4$. | [`OEISThreeProofs/A304362.lean`](OEISThreeProofs/A304362.lean)<br>`b304362_prime`, `b304362_example`, `a304362_infinite_fibers`, `a304362_surjective` | Section 3 |
| **[A174013](https://oeis.org/A174013)** | From the quadratic generating function, derives a square-root-free linear ODE, a $6$-th order recurrence $E_n = 0$ ($n \ge 5$), and Mathar's $7$-th order recurrence via $M_n = E_n + 4E_{n-1} = 0$ for all $n \ge 6$ (extending OEIS's $n \ge 7$ bound). | [`OEISThreeProofs/A174013.lean`](OEISThreeProofs/A174013.lean)<br>`A174013_quadratic`, `A174013_genfun_sq`, `A174013_unique`, `ode_of_genfun_sq`, `a174013_sixth_order`, `a174013_mathar_recurrence`, `a174013_initial_terms` | Section 4 |

All 18 primary Lean 4 theorems were audited with `#print axioms` and depend exclusively on the standard Lean axioms `{propext, Classical.choice, Quot.sound}`.

> **Priority Attribution (OEIS A263160):** An earlier note considered OEIS A263160; independent verification shows a complete proof of A263160 was publicly released by **Le Duy Phuc** on Nov. 25, 2026 ([doi:10.5281/zenodo.24520339](https://doi.org/10.5281/zenodo.24520339)). Out of respect for scientific priority, this repository makes no claim on A263160.

---

## Repository Structure / 目录结构

```text
.
├── OEISThreeProofs.lean            # Root Lean 4 library importing all three modules
├── OEISThreeProofs/
│   ├── A352834.lean                # Subpolynomial bound, 240-box elimination, extremum at 154440
│   ├── A304362.lean                # Infinite fibers & surjectivity of A304362
│   └── A174013.lean                # Quadratic g.f., ODE, 6th-order & Mathar 7th-order recurrences
├── lean-toolchain                  # leanprover/lean4:v4.36.0
├── lakefile.toml                   # Lake configuration (Mathlib v4.36.0)
├── OEIS-three-proofs.md            # Detailed Chinese mathematical notes & theorem index
├── paper/
│   ├── oeis-three-proofs.tex       # LaTeX manuscript
│   └── oeis-three-proofs.pdf       # Compiled PDF paper
├── scripts/
│   └── verify_all.py               # Independent Python exact-arithmetic verification
├── .gitignore
├── LICENSE                         # MIT License
└── README.md
```

---

## Reproducing All Checks / 复现与验证

### 1. Lean 4 Formal Verification

Requires Lean `v4.36.0` (managed by `elan`):

```bash
lake exe cache get   # Optional: download prebuilt Mathlib v4.36.0 .olean files
lake build OEISThreeProofs
```

### 2. Independent Python Exact-Arithmetic Verification

```bash
python3 scripts/verify_all.py
```

Verifies the prime-by-prime optimization, all 240 box elements → 57 with $H(m) \ge T$ → all 21 integral candidates for A352834, the worked example and explicit $u_i$ constructions for A304362, and the polynomial/ODE/recurrence identities for A174013 up to $n=40$.

### 3. Building the PDF Paper

```bash
cd paper
pdflatex oeis-three-proofs.tex
pdflatex oeis-three-proofs.tex
```
