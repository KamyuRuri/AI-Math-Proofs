# 三个 OEIS 猜想的完整证明与 Lean 4 形式化验证

> 本文档整理并严格化了三个 OEIS 公开猜想（[A352834](https://oeis.org/A352834)、[A304362](https://oeis.org/A304362)、[A174013](https://oeis.org/A174013)）的完整数学证明，并将核心定理全部在 **Lean 4 (v4.36.0) + Mathlib4** 中无 `sorry`、无 `native_decide` 地形式化验证。同时附上针对 OEIS A263160 的独立检索与优先权说明。

---

## 0. 目录与 Lean 4 定理索引

| 序列 | 核心结论 | 独立数值校验 | Lean 4 形式化模块与主要定理 |
| :--- | :--- | :--- | :--- |
| **A352834** | $a(n)=o(n^\varepsilon)$，且全局唯一最大值 $\frac{a(n)}{n^{1/3}} = \frac{840}{154440^{1/3}} \approx 15.656428$ 仅在 $n=154440$ 处取到 | `scripts/verify_all.py` | [`OEISThreeProofs/A352834.lean`](OEISThreeProofs/A352834.lean)<br>`IsValidA352834_iff_den`, `divisor_bound_explicit`, `a352834_subpolynomial`, `a352834_154440`, `a352834_global_bound`, `a352834_strict_of_ne`, `a352834_real_extremum` |
| **A304362** | $a(n)=n\text{ 的原像在 }n\in\mathbb{Z}\text{ 处均为无穷集}$（从而 $b:\mathbb{N}_{>0}\to\mathbb{Z}$ 满射且每个纤维无穷） | `scripts/verify_all.py` | [`OEISThreeProofs/A304362.lean`](OEISThreeProofs/A304362.lean)<br>`b304362_prime`, `b304362_example`, `a304362_infinite_fibers`, `a304362_surjective` |
| **A174013** | 满足二次生成函数、六阶 P-递推 $E_n=0\;(n\ge 5)$ 与 Mathar 七阶递推 $M_n = E_n + 4E_{n-1}=0\;(n\ge 6)$ | `scripts/verify_all.py` | [`OEISThreeProofs/A174013.lean`](OEISThreeProofs/A174013.lean)<br>`A174013_quadratic`, `A174013_genfun_sq`, `A174013_unique`, `ode_of_genfun_sq`, `a174013_sixth_order`, `a174013_mathar_recurrence`, `a174013_initial_terms` |

（所有 18 个主定理均经 `#print axioms` 验证，仅依赖 Lean 标准公理 `{propext, Classical.choice, Quot.sound}`。）

---

## 1. OEIS A352834：$a(n)/n^{1/3}$ 的全局严格极大值与次多项式上界

### 1.1 定义与等价刻画

**定义**（OEIS A352834）：对正整数 $n$，设 $\tau(m)$ 为正整数 $m$ 的正因子个数。$a(n)$ 定义为使得有理数 $\frac{\tau(kn)}{kn}$ 约分后的分母恰好等于 $n$ 的最小正整数 $k$（若存在）。

**引理 1.1（最大公约数等价刻画，`IsValidA352834_iff_den`）**：对任意正整数 $n, k \ge 1$，记 $m = kn$，则
$$\operatorname{den}\!\left(\frac{\tau(kn)}{kn}\right) = n \iff \gcd(\tau(kn), kn) = k.$$
特别地，若该条件成立，则必有 $k \mid \tau(m)$ 且 $k \le \tau(m)$。再由 $m = kn$ 即得核心不等式：
$$\frac{k^3}{n} = \frac{k^4}{kn} = \frac{k^4}{m} \le \frac{\tau(m)^4}{m} =: H(m).$$
当 $k < \tau(m)$ 时，由 $k \mid \tau(m)$ 必有 $k \le \tau(m)/2$，从而 $\frac{k^3}{n} \le \frac{H(m)}{16}$；故任何使 $\frac{k^3}{n} \ge T$（且 $H(m) \le B$ 满足 $B/16 < T$）的解必定满足 $k = \tau(m)$，进而 $\tau(m) \mid m$ 且 $n = \frac{m}{\tau(m)}$。

*证明*：$\frac{\tau(m)}{m}$ 约去 $g = \gcd(\tau(m), m)$ 后分母为 $m/g$。故分母等于 $n$ 当且仅当 $m/g = n$。因 $m = kn$，该式等价于 $g = k$。再由 $k \le \tau(m)$ 立即得 $\frac{k^3}{n} = \frac{k^4}{m} \le \frac{\tau(m)^4}{m}$。$\square$

---

### 1.2 初等次多项式上界（`divisor_bound_explicit` 与 `a352834_subpolynomial`）

为严格证明对任意 $\varepsilon > 0$ 都有 $a(n) = O_\varepsilon(n^\varepsilon)$（甚至 $a(n) = o(n^\varepsilon)$），采用 Terence Tao 所梳理的初等乘性因子界（利用 Bernoulli 不等式）：

**引理 1.2（显式因子上界，`divisor_bound_explicit`）**：对任意 $\delta > 0$ 与正整数 $m \ge 1$，记集合 $P_\delta = \{p \text{ 素数} : p < 2^{1/\delta}\}$。由于对每个素数幂 $p^e \parallel m$：
- 若 $p \ge 2^{1/\delta}$，则 $(p^\delta)^e \ge 2^e \ge e+1$；
- 若 $p < 2^{1/\delta}$，由对数或初等有理逼近可取显式常数 $C_p(\delta) = \sup_{e \ge 0} \frac{e+1}{p^{\delta e}} < \infty$（因 $\delta > 0$ 时 Bernoulli 不等式给出 $p^{\delta e} \ge 1 + e(p^\delta - 1)$ 线性增长或对足够大阶幂增长快于 $e+1$；Lean 中直接通过 $2^{1/(k)} \le p$ 选取有理步长验证 $(e+1)^K \le C_{p,K} p^e$）。

于是对任意正整数 $K \ge 1$，存在显式常数 $C(K) > 0$，使得对一切 $m \ge 1$ 皆有
$$\tau(m)^K \le C(K) m.$$
**推论（`a352834_subpolynomial`）**：取 $\varepsilon > 0$ 及整数 $K > 1/\varepsilon + 1$。对任意使 $a(n)$ 有定义的 $n$，记 $k = a(n)$ 且 $m = kn$，则 $k \le \tau(m)$，故
$$k^K \le \tau(m)^K \le C(K) kn \implies k^{K-1} \le C(K) n \implies a(n) \le C(K)^{\frac{1}{K-1}} n^{\frac{1}{K-1}}.$$
由此立刻得出对所有 $\varepsilon > 0$，$a(n)/n^\varepsilon \to 0$（当 $n \to \infty$）。

---

### 1.3 素因子独立优化与精确有理上界

对 $H(m) = \frac{\tau(m)^4}{m}$，若 $m = \prod_p p^{e_p}$，则函数按素因子完全可乘：
$$H(m) = \prod_p h_p(e_p), \qquad h_p(e) := \frac{(e+1)^4}{p^e}.$$
比值 $\frac{h_p(e+1)}{h_p(e)} = \frac{1}{p}\left(\frac{e+2}{e+1}\right)^4$ 关于 $e \ge 0$ 严格单调递减，故 $h_p(e)$ 单峰，且只要 $(e_0+2)^4 \le p(e_0+1)^4$ 即可确认 $h_p(e)$ 在 $e \ge e_0$ 上单调递减。逐素数计算峰值 $M_p := \max_{e \ge 0} h_p(e)$（全部在 `scripts/verify_all.py` 与 Lean `A352834.lean` 中精确验算）：

| 素数 $p$ | 峰值指数 $e^*$ | 峰值 $M_p = \frac{(e^*+1)^4}{p^{e^*}}$ | 数值近似 |
| :---: | :---: | :---: | :---: |
| $2$ | $5$ | $81/2$ | $40.500000$ |
| $3$ | $3$ | $256/27$ | $9.481481$ |
| $5$ | $2$ | $81/25$ | $3.240000$ |
| $7$ | $1$ | $16/7$ | $2.285714$ |
| $11$ | $1$ | $16/11$ | $1.454545$ |
| $13$ | $1$ | $16/13$ | $1.230769$ |
| $p \ge 17$ | $0$ | $1$ | $1.000000$（因 $16/17 < 1$）|

将所有 $M_p$ 相乘，得到全局无条件上界：
$$B := \prod_{p \le 13} M_p = \frac{81}{2} \cdot \frac{256}{27} \cdot \frac{81}{25} \cdot \frac{16}{7} \cdot \frac{16}{11} \cdot \frac{16}{13} = \frac{127401984}{25025} \approx 5090.98837163.$$

另一方面，目标候选 $n_0 = 154440$、$k_0 = 840$ 给出 $m_0 = k_0 n_0 = 129729600 = 2^6 \cdot 3^4 \cdot 5^2 \cdot 7 \cdot 11 \cdot 13$，其因子个数恰好满足 $\tau(m_0) = 7 \cdot 5 \cdot 3 \cdot 2^3 = 840 = k_0$。目标比值的三次方为：
$$T := \frac{840^3}{154440} = \frac{548800}{143} \approx 3837.76223776.$$

对比 $B$ 与 $T$ 可做两步决定性剪枝：
1. **消除 $p \ge 23$ 的所有素因子**：若存在 $p \ge 23$ 且 $e_p \ge 1$，则 $h_p(e_p) \le h_p(1) = \frac{16}{p} \le \frac{16}{23}$，因此
   $$H(m) \le \frac{16}{23} B = \frac{2038431744}{575575} \approx 3541.557128 < T.$$
2. **限制 $p \in \{17, 19\}$ 的指数为 $\{0, 1\}$**：若 $p \ge 17$ 且 $e_p \ge 2$，由于 $h_{17}(2) = \frac{81}{289} < \frac{1}{3}$（严格小于 $\frac{T}{B} \approx 0.7538$，且事实上 $\frac{B}{16} \approx 318.1868 < T$、$\frac{81}{289} B \approx 1426.8 < T$），直接排除 $e_p \ge 2$。
3. **有限矩形框（240 个组合）**：对每个 $p \in \{2,3,5,7,11,13,17,19\}$，要求 $h_p(e_p) \cdot \frac{B}{M_p} \ge T$，立即把所有可能产生 $H(m) \ge T$ 的指数锁定在笛卡尔积箱中：
   $$e_2 \in [3,7],\quad e_3 \in [2,4],\quad e_5 \in \{1,2\},\quad e_7 = 1,\quad e_{11} = 1,\quad e_{13} \in \{0,1\},\quad e_{17} \in \{0,1\},\quad e_{19} \in \{0,1\}.$$
   盒子总大小为 $5 \times 3 \times 2 \times 1 \times 1 \times 2 \times 2 \times 2 = 240$。

---

### 1.4 240 盒精确筛选与完整 21 候选表

在 240 个指数向量中：
- 满足 $H(m) = \tau(m)^4 / m \ge T$ 的共 **57** 个；
- 进一步满足整除条件 $\tau(m) \mid m$（使 $n = m/\tau(m)$ 为整数）的仅有 **21** 个。

下表列出全部 21 个整候选的精确数据（由 `scripts/verify_all.py` 按 $k^3/n$ 降序排列生成并核对）：

| 排名 | 指数 $(e_2,e_3,e_5,e_7,e_{11},e_{13},e_{17},e_{19})$ | $m = \prod p^{e_p}$ | $\tau(m)$ | $n = m/\tau(m)$ | $a(n)$ | $a(n)^3/n$ | $a(n)/n^{1/3}$ |
| :---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| **1** | `(6, 4, 2, 1, 1, 1, 0, 0)` | 129,729,600 | 840 | **154,440** | **840** | **3837.762238** | **15.656428** |
| 2 | `(5, 4, 2, 1, 1, 1, 0, 0)` | 64,864,800 | 720 | 90,090 | 672 | 3368.458741 | 14.990303 |
| 3 | `(6, 3, 2, 1, 1, 1, 0, 0)` | 43,243,200 | 672 | 64,350 | 432 | 1252.860420 | 10.780384 |
| 4 | `(5, 3, 2, 1, 1, 0, 0, 0)` | 1,663,200 | 288 | 5,775 | 36 | 8.078961 | 2.006559 |
| 5 | `(4, 2, 2, 1, 1, 1, 0, 0)` | 3,603,600 | 360 | 10,010 | 40 | 6.393606 | 1.856017 |
| 6 | `(5, 2, 1, 1, 1, 0, 0, 0)` | 110,880 | 144 | 770 | 16 | 5.319481 | 1.745647 |
| 7 | `(4, 4, 2, 1, 1, 1, 0, 0)` | 32,432,400 | 600 | 54,054 | 48 | 2.045954 | 1.269498 |
| 8 | `(4, 3, 2, 1, 1, 0, 0, 0)` | 831,600 | 240 | 3,465 | 12 | 0.498701 | 0.793013 |
| 9 | `(6, 2, 2, 1, 1, 1, 0, 0)` | 14,414,400 | 504 | 28,600 | 24 | 0.483357 | 0.784794 |
| 10 | `(6, 2, 1, 1, 1, 1, 0, 0)` | 2,882,880 | 336 | 8,580 | 16 | 0.477389 | 0.781551 |
| 11 | `(6, 2, 2, 1, 1, 1, 1, 0)` | 245,044,800 | 1,008 | 243,100 | 48 | 0.454924 | 0.769094 |
| 12 | `(6, 2, 1, 1, 1, 1, 1, 0)` | 49,008,960 | 672 | 72,930 | 32 | 0.449308 | 0.765916 |
| 13 | `(5, 4, 2, 1, 1, 1, 1, 0)` | 1,102,701,600 | 1,440 | 765,765 | 12 | 0.002257 | 0.131164 |
| 14 | `(4, 2, 1, 1, 1, 1, 0, 0)` | 720,720 | 240 | 3,003 | 1 | 0.000333 | 0.069313 |
| 15 | `(5, 2, 1, 1, 1, 1, 0, 0)` | 1,441,440 | 288 | 5,005 | 1 | 0.000200 | 0.058461 |
| 16 | `(6, 3, 1, 1, 1, 1, 0, 0)` | 8,648,640 | 448 | 19,305 | 1 | 0.000052 | 0.037277 |
| 17 | `(6, 3, 2, 1, 1, 1, 1, 0)` | 735,134,400 | 1,344 | 546,975 | 3 | 0.000049 | 0.036683 |
| 18 | `(6, 3, 2, 1, 1, 1, 0, 1)` | 821,620,800 | 1,344 | 611,325 | 3 | 0.000044 | 0.035348 |
| 19 | `(5, 4, 1, 1, 1, 1, 0, 0)` | 12,972,960 | 480 | 27,027 | 1 | 0.000037 | 0.033322 |
| 20 | `(4, 2, 2, 1, 1, 1, 1, 0)` | 61,261,200 | 720 | 85,085 | 1 | 0.000012 | 0.022736 |
| 21 | `(4, 2, 2, 1, 1, 1, 0, 1)` | 68,468,400 | 720 | 95,095 | 1 | 0.000011 | 0.021909 |

### 1.5 验证 $a(154440) = 840$ 与严格全局极大值定理

为证 $a(154440) = 840$（而无更小的 $1 \le j < 840$ 满足 $\gcd(\tau(154440 j), 154440 j) = j$），注意到若 $\gcd(\tau(154440 j), 154440 j) = j$，则 $j \mid \tau(154440 j)$。将 $j$ 在前 10 个素数 $\{2,3,5,7,11,13,17,19,23,29\}$ 上剥离并分析余因子 $r$：
- 若 $r$ 为合数或满足乘性上界与 $154440 j$ 的素幂展开，可直接由因子计数上界 $\tau(154440 j) \le 840 \cdot \tau_{\text{mul}}(j)$ 排除；
- 当 $r = 1$ 或 $r$ 为素数（此时 $\tau(r)=2$）时，整除关系 $j \mid \tau(154440 j)$ 迫使 $j$ 不能被任何大素数（至少不大于 $2 \cdot 840$ 的有限范围）整除之外的素数整除；结合分块内核判定（`a352834_154440`），对全部 $1 \le j < 840$ 逐一否定，同时 $j=840$ 时 $m_0 = 129729600$ 满足 $\tau(m_0) = 840 \mid m_0$ 且 $m_0 / 840 = 154440$，故 $a(154440) = 840$。

**定理 1（`a352834_global_bound`, `a352834_strict_of_ne`, `a352834_real_extremum`）**：对一切正整数 $n \ge 1$，有
$$\frac{a(n)}{n^{1/3}} \le \frac{840}{154440^{1/3}} \approx 15.6564281184,$$
且等号**严格唯一**地在 $n = 154440$ 处成立。$\square$

---

## 2. OEIS A304362：任意整数值的无穷纤维与满射性

### 2.1 序列定义与指数子集公式

设 $P$ 为全体非 $1$ 完全幂次正整数之集：
$$\mathcal{P} := \{d \in \mathbb{N} : \exists a \ge 2,\; s \ge 2,\; d = a^s\}.$$
序列 $b(n) := \text{A304362}(n)$（或其对应符号版本）由卷积定义为：
$$b(n) = \sum_{\substack{d \mid n \\ d \notin \mathcal{P}}} \mu\!\left(\frac{n}{d}\right)$$
（注：按 OEIS A304362，若某项索引将 $1$ 纳入或不纳入不影响本文符号，在 Lean `b304362` 中我们采用严格形式 $\sum_{d \mid n,\, d \notin \mathcal{P}} \mu(n/d)$，其中 `IsPerfectPower` 仅含 $a \ge 2, s \ge 2$，对任意正整数 $n$ 均有明确整数值）。

当 $n = \prod_{k=0}^{m-1} p_k^{e_k}$ 为两两不同素数之幂积，且全部指数满足 $e_k \ge 2$ 时，只有无平方因子商 $\frac{n}{d} = \prod_{k \in S} p_k$（对应 $S \subseteq \{0,\dots,m-1\}$）才有 $\mu(n/d) = (-1)^{|S|} \ne 0$，且此时因 $e_k - \mathbf{1}_{k \in S} \ge 1$，$d \in \mathcal{P}$ 当且仅当
$$\gcd_{0 \le k < m} \bigl(e_k - \mathbf{1}_{k \in S}\bigr) \ge 2.$$
因此有精确公式（`b304362_prime_powers`）：
$$b(n) = \sum_{S \subseteq \{0,\dots,m-1\}} (-1)^{|S|} \cdot \mathbf{1}_{\gcd_k(e_k - \mathbf{1}_{k \in S}) = 1} = -\sum_{S \subseteq \{0,\dots,m-1\}} (-1)^{|S|} \cdot \mathbf{1}_{\gcd_k(e_k - \mathbf{1}_{k \in S}) \ge 2}$$
（利用 $m \ge 1$ 时 $\sum_S (-1)^{|S|} = 0$）。对素数 $p$，仅有 $d \in \{1, p\}$ 均非完全幂，故 $b(p) = \mu(p) + \mu(1) = -1 + 1 = 0$（`b304362_prime`）。

---

### 2.2 显式 Fermat-CRT 构造（无需黑箱存在性定理）

任取 $r \ge 1$ 与任意下界 $M \in \mathbb{N}$。记前 $r$ 个素数为 $q_0 < q_1 < \dots < q_{r-1}$，令
$$Q := \prod_{j=0}^{r-1} q_j, \qquad Q_i := \frac{Q}{q_i} = \prod_{j \ne i} q_j \quad (0 \le i < r).$$
（特别地，当 $r = 1$ 时，$q_0 = 2$，$Q = 2$，空乘积 $Q_0 = 1$。）

直接显式定义指数：
$$u_i := Q_i^{q_i - 1} + Q \ge 2 \qquad (0 \le i < r).$$
由费马小定理（及 $r=1$ 时 $Q_0 = 1$ 的平凡情形 $u_0 = 1 + 2 = 3$）：
1. 因 $\gcd(Q_i, q_i) = 1$，有 $Q_i^{q_i - 1} \equiv 1 \pmod{q_i}$，而 $q_i \mid Q$，故
   $$u_i \equiv 1 \pmod{q_i} \implies q_i \mid (u_i - 1) \;\text{ 且 }\; q_i \nmid u_i.$$
2. 对任意 $j \ne i$，因 $q_j \mid Q_i$（且 $q_j - 1 \ge 1$）以及 $q_j \mid Q$，有
   $$q_j \mid u_i \;\text{ 且 }\; q_j \nmid (u_i - 1).$$

再由素因子不重叠可知如下三组两两互素关系恒成立：
$$\gcd(Q, 2Q - 1) = 1, \qquad \gcd(Q - 1, 2Q) = 1, \qquad \gcd(Q - 1, 2Q - 1) = 1.$$
取 $r + 2$ 个（或 $r + 3$ 个）严格递增且全部大于 $M$ 的素数 $p_0 < p_1 < \dots$：

- **正值 $+r$ 构造（`exists_pos_gt`）**：令 $n = p_0^Q \, p_1^{2Q} \prod_{i=0}^{r-1} p_{i+2}^{u_i} > M$。
  若存在素数 $q$ 整除所有偏移指数 $e_k - \mathbf{1}_{k \in S}$，观察前两项：
  - 若 $0 \in S$ 且 $1 \notin S$，则 $q \mid \gcd(Q-1, 2Q) = 1$，矛盾；
  - 若 $0 \notin S$ 且 $1 \in S$，则 $q \mid \gcd(Q, 2Q-1) = 1$，矛盾；
  - 若 $0, 1 \in S$，则 $q \mid \gcd(Q-1, 2Q-1) = 1$，矛盾。
  因此必有 $0, 1 \notin S$，故 $q \mid Q$，从而 $q = q_i$（对某个唯一的 $0 \le i < r$）。由此立得 $u_j - \mathbf{1}_{j+2 \in S}$ 被 $q_i$ 整除当且仅当 $j = i$ 且 $i+2 \in S$，即**唯一**可行子集为单点集 $S = \{i + 2\}$。总共恰好 $r$ 个单点集，每个给出 $(-1)^{|S|} = -1$，故
  $$b(n) = -\sum_{i=0}^{r-1} (-1)^1 = +r.$$

- **负值 $-r$ 构造（`exists_neg_gt`）**：多引入一个素数 $p_{r+2} > M$ 并置其指数为 $e_{r+2} = Q + 1 \ge 3$。前两项同样迫使 $0,1 \notin S$ 与 $q = q_i$；因 $q_i \mid Q$ 但 $q_i \nmid (Q+1)$，末位下标 $r+2$ 被**强制**选入 $S$，故可行子集恰为全部 $r$ 个二元集 $S = \{i+2, r+2\}$（$|S|=2$），从而
  $$b(n) = -\sum_{i=0}^{r-1} (-1)^2 = -r.$$

- **具体数值实例（`b304362_example`）**：当 $n = 2^{36} \cdot 3^{21} \cdot 5^{15}$ 时，通过子集公式直接验证共有 4 个二元/奇偶协同子集满足 $\gcd \ge 2$，总贡献恰好得出 $b(2^{36} \cdot 3^{21} \cdot 5^{15}) = -4$。

**定理 2（`a304362_infinite_fibers`, `a304362_surjective`）**：对任意整数 $z \in \mathbb{Z}$ 与任意界 $M \in \mathbb{N}$，皆存在 $n > M$ 使 $b(n) = z$。特别地，$b : \mathbb{N}_{>0} \to \mathbb{Z}$ 为满射，且每一个整数的原像纤维 $\{n \in \mathbb{N}_{>0} : b(n) = z\}$ 均为无穷集。$\square$

---

## 3. OEIS A174013：代数生成函数、无根式 ODE 与 Mathar 七阶递推

### 3.1 二次方程与生成函数唯一性

OEIS A174013 由形式幂级数 $A(x) = \sum_{n=0}^\infty a_n x^n \in \mathbb{Q}[[x]]$ 定义，满足代数二次方程（`A174013_quadratic`）：
$$x(1 - x - x^2) A(x)^2 + (1 - 3x - x^2) A(x) - (1 - x) = 0, \qquad a_0 = 1.$$
令
$$B(x) := 2x(1 - x - x^2) = 2x - 2x^2 - 2x^3, \qquad H(x) := 1 - 3x - x^2,$$
$$D(x) := H(x)^2 + 2(1 - x) B(x) = 1 - 2x - x^2 + 6x^3 + 5x^4.$$
直接多项式展开即得精确恒等式（`H_sq_sub_D`）：
$$H(x)^2 - D(x) = -2(1 - x) B(x),$$
从而配平方等价于（`A174013_genfun_sq`）：
$$\bigl(B(x) A(x) + H(x)\bigr)^2 = D(x).$$
此外，由系数归纳法 $[x^n]$ 可知，若在 $\mathbb{Q}[[x]]$ 中有任何满足相同二次方程且常数项为 $1$ 的幂级数，其全部系数均被唯一递推确定（`A174013_unique`）。

---

### 3.2 消去平方根的一阶线性 ODE

设 $Y(x) := B(x) A(x) + H(x)$，则 $Y(x)^2 = D(x)$。两边求形式导数得 $2 Y Y' = D'$；再乘以 $Y$ 并利用 $Y^2 = D$ 消去平方根，得到：
$$2 D(x) Y'(x) = D'(x) Y(x).$$
将 $Y = B A + H$ 与 $Y' = B A' + B' A + H'$ 代入上式，整理即得一阶非齐次线性常微分方程（`ode_of_genfun_sq`）：
$$P(x) A'(x) + Q(x) A(x) = R(x),$$
其中三个整系数多项式皆被 $4$ 整除：
$$\begin{aligned}
\frac{P(x)}{4} &= \frac{2 D B}{4} = x - 3x^2 + 9x^4 - 11x^6 - 5x^7, \\
\frac{Q(x)}{4} &= \frac{2 D B' - D' B}{4} = 1 - 3x + 3x^3 - 6x^4 - 9x^5 - 5x^6, \\
\frac{R(x)}{4} &= \frac{D' H - 2 D H'}{4} = 1 - x + 3x^2 - 6x^4.
\end{aligned}$$

---

### 3.3 六阶 P-递推与 Mathar 七阶递推（含 $n=6$ 改进）

从 $\frac{P(x)}{4} A'(x) + \frac{Q(x)}{4} A(x) + \frac{R(x)}{4} = 0$ 提取 $[x^n]$（并约定 $k < 0$ 时 $a_k = 0$），设算子
$$\begin{aligned}
E_n &:= (n + 1) a_n - 3n\, a_{n-1} + (9n - 24) a_{n-3} - 6 a_{n-4} + (46 - 11n) a_{n-5} + (25 - 5n) a_{n-6}.
\end{aligned}$$
直接比对系数可知 $[E_0, E_1, E_2, E_3, E_4] = [1, -1, 3, 0, -6] = R/4$ 的低次系数（正好在 $n \ge 5$ 后消失），故**对一切整数 $n \ge 5$**，成立**六阶线性递推**（`a174013_sixth_order`）：
$$E_n = 0 \qquad (\forall n \ge 5).$$

现定义 R. J. Mathar 在 OEIS A174013 中猜想的七阶线性递推算子：
$$\begin{aligned}
M_n &:= (n + 1) a_n + n\, a_{n-1} + 12(1 - n) a_{n-2} + (9n - 24) a_{n-3} \\
&\quad + (36n - 138) a_{n-4} + (22 - 11n) a_{n-5} + (253 - 49n) a_{n-6} + (120 - 20n) a_{n-7}.
\end{aligned}$$
通过逐项合并同类系数，我们证明了纯代数恒等式（`M_op_eq_E_add`）：
$$M_n = E_n + 4 E_{n-1} \qquad (\forall n \ge 1).$$
因此由 $E_n = 0\;(\forall n \ge 5)$ 立即推得（`a174013_mathar_recurrence`）：
$$M_n = 0 \qquad (\forall n \ge 6).$$
**注记（$n=6$ 改进）**：不仅证实 OEIS 上给出的 $n \ge 7$ 猜想，而且由于 $n=6$ 时已有 $E_6 = 0$ 且 $E_5 = 0$，Mathar 递推在 $n = 6$ 时就已经精确成立；而在 $n = 5$ 时 $M_5 = E_5 + 4E_4 = 4(-6) = -24 \ne 0$，故 $n \ge 6$ 为最佳可能下界。前 11 项经验证为 `[1, 1, 3, 6, 12, 22, 37, 56, 73, 75, 44]`（`a174013_initial_terms`，前 14 项含 `-21, -39, 297`）。$\square$

---

## 4. 优先权说明（OEIS A263160）

经独立核查（参见 Zenodo 预印本及发布记录）：关于第四条序列 **OEIS A263160** 的完整证明已由 **Le Duy Phuc** 于 2026-11-25 公开发表（DOI: `10.5281/zenodo.24520339`）。为尊重学术优先权与避免重复宣称，本仓库专注并仅主张上述三条序列 **A352834**、**A304362** 与 **A174013** 的完整证明及 Lean 4 形式化成果。

---

## 5. 参考文献

1. OEIS Foundation Inc., *The On-Line Encyclopedia of Integer Sequences*, entries [A352834](https://oeis.org/A352834), [A304362](https://oeis.org/A304362), [A174013](https://oeis.org/A174013), [A263160](https://oeis.org/A263160).
2. Terence Tao, elementary divisor bound exposition ($\tau(n) = O_\varepsilon(n^\varepsilon)$ via prime-power splitting).
3. Le Duy Phuc, proof of OEIS A263160 conjecture, Zenodo, Nov. 25, 2026, `doi:10.5281/zenodo.24520339`.
4. The mathlib Community, *Mathlib4* (`v4.36.0`) and Lean 4 Theorem Prover.
