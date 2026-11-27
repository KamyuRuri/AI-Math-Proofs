# A sharp bound on the distance between maximum-degree vertices

**Graffiti.pc Conjecture 271 · 第 271 号猜想**

**Author / 作者**　ChatGPT

[PDF](paper/graffiti-271.pdf) · [LaTeX](paper/graffiti-271.tex) · [Python verification / Python 核验](scripts/verify_graffiti271.py) · [MIT License](../../LICENSE)

## Result

In a finite simple connected graph on at least two vertices, let $k$ be its total domination number and let $d_M$ be the greatest distance in the graph between vertices of maximum degree. Then $k^2\ge 2d_M$, which proves Graffiti.pc Conjecture 271. Equality before rounding holds exactly when an adjacent pair totally dominates the graph and two vertices of maximum degree are nonadjacent. Every balanced complete bipartite graph $K_{m,m}$ with $m\ge2$ attains equality. The manuscript credits the earlier diameter bound to DeLaViña, Liu, Pepper, Waller, and West (2007) and includes an elementary proof.

## 中文简介

设 $k$ 是全支配数，$d_M$ 是最大度顶点两两之间在原图中的最大距离。本文证明 $k^2\ge 2d_M$，从而解决 Graffiti.pc 第 271 号猜想。等号成立当且仅当存在一条边，其两个端点全支配整张图，且存在两个互不相邻的最大度顶点。完全二部图 $K_{m,m}$（$m\ge2$）给出无穷多个等号例子。证明中引用的直径界归于 DeLaViña 等人 2007 年的工作，文中也给出按距离分层的自包含证明。

## Reproduction / 复现

Run from this paper's directory with Python 3.8 or later and pdfLaTeX. 在本篇目录运行：

```sh
python scripts/verify_graffiti271.py
cd paper
pdflatex -interaction=nonstopmode -halt-on-error graffiti-271.tex
pdflatex -interaction=nonstopmode -halt-on-error graffiti-271.tex
```

The Python script enumerates all 27,475 connected labeled graphs on 2–6 vertices and checks the inequality and equality criterion. Exactly 2,408 graphs have $k^2=2d_M$. The general proof is in the PDF and TeX. Verification status: mathematical proof and exhaustive finite Python check. No Lean formalization is included.

Python 脚本逐一核验 2–6 阶的全部 27,475 张有标号连通简单图，其中恰有 2,408 张取得未取整不等式的等号。所有阶数的证明见正文。

## Sources / 文献

- Ermelinda DeLaViña, *Written on the Wall II*, Conjecture 271, February 23, 2007. [Catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)
- E. DeLaViña, Q. Liu, R. Pepper, B. Waller, and D. B. West, “Some conjectures of Graffiti.pc on total domination,” *Congressus Numerantium* 185 (2007), 81–95, Lemma 3 and equation (5). [Paper](https://www.uhd.edu/documents/academics/sciences/total-dom-2007.pdf)

Released under the repository's [MIT License](../../LICENSE), copyright © 2026 JiaZhuang Wang.
