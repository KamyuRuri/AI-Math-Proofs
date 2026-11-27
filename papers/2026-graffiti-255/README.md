# An 11-vertex counterexample to Graffiti.pc Conjecture 255

**Graffiti.pc 第 255 号猜想的 11 阶反例、最小阶数与最佳常数**

ChatGPT (OpenAI, GPT-6), Gemini, and JiaZhuang Wang (corresponding author / 通讯作者).

[Paper / 论文 PDF](paper/graffiti-255.pdf) · [LaTeX](paper/graffiti-255.tex) · [Python verification / 校验脚本](scripts/verify_graffiti255.py)

## Results / 主要结论

For a finite simple connected graph of order at least two, let $C$ be its center, $\gamma_t$ its total domination number, and $M$ the largest size of the union of the open neighborhoods of the endpoints of an edge. Graffiti.pc Conjecture 255 proposed $\gamma_t M\ge 2|C|$.

在至少含两个顶点的有限简单连通图中，$C$ 为所有离心率最小的顶点，$\gamma_t$ 为全支配数，$M$ 为沿一条边取两端点的开邻域之并所能得到的最大基数。原猜想断言 $\gamma_t M\ge 2|C|$。

| Result / 结论 | Construction or bound / 构造或界 |
| --- | --- |
| Minimum counterexample order / 最小反例阶数 | Subdivide all five edges incident with a fixed vertex of $K_6$ once. 将 $K_6$ 中一个顶点关联的五条边各细分一次，得到 11 个顶点、20 条边，$\gamma_t=3$，$M=7$，$\lvert C\rvert=11$，故 $21<22$。The paper proves that every connected graph of order at most ten in the stated domain satisfies the conjecture. |
| Infinite family / 无穷反例族 | The same construction on $K_{t+1}$ gives $2\lvert C\rvert-\gamma_t M=t-4$ for $t\ge2$. 每个 $t\ge5$ 都给出反例。 |
| Sharp constant / 最佳常数 | Every graph in the stated domain satisfies $\gamma_t M\ge \lvert C\rvert$. 对增广的车图族 $H_k$，比值 $\gamma_t M/\lvert C\rvert$ 趋于 $1$，故任意大于 $1$ 的统一系数都会失效。 |

## Reproduction / 复现

From this directory, with Python 3.10 or later and the standard library, run the following command. 在本目录下用 Python 3.10 或更高版本执行，无需第三方包。

```sh
python -B scripts/verify_graffiti255.py
```

The script checks $G_t$ for $2\le t\le12$, including the five minimum total dominating triples of $G_5$. It checks distances, degrees, an explicit total dominating set, and the edge-neighborhood bound on $H_k$ for $k=2,3,4$. It also enumerates all 27,475 connected labeled graphs of orders two through six. A successful run ends with `ALL VERIFICATIONS PASSED.`

程序从边集重算上述实例，另穷举 2 至 6 阶的全部 27,475 个带标号连通图。论文给出覆盖任意阶数的数学证明，包括排除所有 10 阶及以下反例的论证。本版的计算校验使用 Python，未提供经过构建验证的 Lean 形式化证明。

To rebuild the PDF with pdfLaTeX, run the following commands from this directory. 从本目录运行下列命令可重编译论文。

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error graffiti-255.tex
pdflatex -interaction=nonstopmode -halt-on-error graffiti-255.tex
```

## Source and priority / 来源与优先权

Ermelinda DeLaViña announced entry 255 on February 23, 2007. The catalogue reports earlier computational checks on all connected graphs through order ten. We credit that computation in the paper. Searches on GitHub, arXiv, and Zenodo by conjecture number and by the graph invariants did not locate an earlier resolution of entry 255. 目录对至多 10 阶图的计算检验早于本工作。2026 年 11 月 21 日的目录备注将相邻第 256 题的 14 阶反例归于 Tony Newton。该题的分子涉及最小度顶点的邻域。[Original catalogue / 猜想原始目录](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalogue PDF / 目录 PDF](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf)

Copyright (c) 2026 JiaZhuang Wang. [MIT License](../../LICENSE).
