# AI-Math-Proofs

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Repository:** [https://github.com/KamyuRuri/AI-Math-Proofs](https://github.com/KamyuRuri/AI-Math-Proofs)  
**Corresponding Author / 通讯作者:** JiaZhuang Wang (with AI co-authors Gemini & ChatGPT)

A curated collection of mathematical proofs, **Lean 4 / Mathlib4** formal verifications, independent exact-arithmetic verification scripts, and publication-ready LaTeX/PDF papers.

本仓库收录由 AI 与人类研究者共同完成的数学猜想证明、**Lean 4 / Mathlib4** 形式化验证、独立精确数值校验脚本以及 LaTeX/PDF 学术论文。

---

## Index of Papers by Topic / 按学科方向论文总目

### Number Theory, OEIS Conjectures & Generating Functions / 数论、OEIS 猜想与生成函数

| Year | Title & Scope / 论文与研究范围 | Formal Verification | Materials / 资料直达 |
| :---: | :--- | :--- | :--- |
| **2026** | **Resolved Conjectures on OEIS A352834, A304362, and A174013**<br>• **A352834**: $a(n) = O_\varepsilon(n^\varepsilon)$ and strict global maximum $a(n)/n^{1/3} \le 840/154440^{1/3}$ uniquely at $n=154440$.<br>• **A304362**: Surjectivity onto $\mathbb{Z}$ and infinite fibers via explicit Fermat–CRT exponents $u_i = Q_i^{q_i - 1} + Q$.<br>• **A174013**: Quadratic g.f. $\to$ linear ODE $\to$ $6$-th order recurrence ($n \ge 5$) and Mathar's $7$-th order recurrence ($n \ge 6$). | Lean `v4.36.0` + Mathlib4<br>(18 theorems, zero `sorry`, zero `native_decide`) | [Folder](papers/2026-oeis-three-proofs/) · [PDF Paper](papers/2026-oeis-three-proofs/paper/oeis-three-proofs.pdf) · [TeX](papers/2026-oeis-three-proofs/paper/oeis-three-proofs.tex) · [中文证明](papers/2026-oeis-three-proofs/OEIS-three-proofs.md) · [Lean 4](papers/2026-oeis-three-proofs/OEISThreeProofs/) · [Verify Script](papers/2026-oeis-three-proofs/scripts/verify_all.py) |

### Combinatorics & Discrete Mathematics / 组合数学与离散数学

*(More papers will be added here as the collection grows.)*

### Algebra & Analysis / 代数与分析

*(More papers will be added here as the collection grows.)*

---

## Repository Conventions / 仓库组织规范

To avoid Mathlib/toolchain version conflicts across papers written over time (and because mathematical papers frequently span multiple subfields), this repository separates **physical storage** from **topical classification**:

- **Self-contained folders under `papers/<year>-<slug>/`**: Each paper maintains its own `lean-toolchain`, `lakefile.toml`, Lean modules, LaTeX/PDF manuscript, and verification scripts, so older proofs always remain reproducible under their pinned toolchain.
- **Logical topic index in this root `README.md`**: Every new paper is linked in the topical tables above (cross-listed if interdisciplinary).

---

## License

This repository is released under the [MIT License](LICENSE).
