# Lean 4 形式化（`StarTheorem/`）

按约定优先级对 report.md §8 的定理做 Lean 4 + Mathlib 形式化。
**状态：约定的全部优先级 1、1b、2、3、4、4b、5 以及探索 A1/A3 均已机器验证
（`lake build` 通过，2384 行，97 条定理/引理，全库无 `sorry`）。形式化计划内已无遗留项。**

## 优先级与状态

| 优先级 | 定理 | Lean 名称 | 状态 |
|---|---|---|---|
| 1 | 星形最大化 $C(G)\le m(m-1)c(m,1)$ | `C_le_star` | ✅ **已验证** |
| 2 | $C(G)=0\iff G$ 是匹配 | `C_eq_zero_iff` | ✅ **已验证** |
| 3 | 正则图精确值 $C=N\,r(r-1)c(r,r)$ | `C_of_regular` | ✅ **已验证** |
| 4 | 尖锐夹逼 $\mathrm{psiSum}\le C\le\sqrt2\,\mathrm{psiSum}$ | `psiSum_le_C`, `C_le_sqrt2_psiSum` | ✅ **已验证** |
| 1b | 星形定理的**等号刻画** | `C_eq_star_iff` | ✅ **已验证** |
| 4b | Zagreb/Forgotten 夹逼 $Z/(4\Delta-1)\le C\le(\sqrt2/3)Z$ | `zagreb_sandwich` | ✅ **已验证** |
| 5 | 通用删边恒等式 $\sum_e T_f(G-e)=(m-1)T_f(G)-C_f(G)$ | `deletion_identity` | ✅ **已验证（无条件）** |

已验证的完整清单（`results/formalisation_status.json` 由脚本生成）：

```
Defs.lean       c, phi, C, M1, Z, psiSum, degSeqBound 的定义
Kernel.lean     c_mul_denom, denom_pos, c_eq_div, c_pos, c_pos_nat,
                c_antitone_right_nat, c_succ_left_nat, c_monotone_left_nat,
                c_le_c_m_one, degree_pos_of_adj, one_le_degree_of_adj,
                neighborFinset_eq_empty_of_degree_eq_zero
StarMax.lean    eq_sym2_of_mem_of_mem, edge_degree_add_le, neighbor_sum_swap,
                two_mul_M1, M1_le, C_le_M1, C_le_star
ZeroIff.lean    C_summand_nonneg, C_summand_pos, C_eq_zero_iff
Regular.lean    c_self, C_of_regular, C_of_regular_le_star
Sandwich.lean   sqrt_sq_add_sq_le, le_sqrt_sq_add_sq, denom_bounds,
                two_a_two_b_sub_one_pos, c_ge_div, c_le_sqrt2_div,
                psiSum_le_C, C_le_sqrt2_psiSum
DeletionIdentity.lean  Tf, Cf, deltaOrd 的定义；PART 1 双重计数 sum_deltaOrd；
                PART 2 删边度数更新（Mathlib 缺失）neighborFinset_deleteEdges,
                neighborFinset_deleteEdges_left/right/of_ne, degree_deleteEdges_left/right/of_ne,
                degree_deleteEdges_ite, degree_deleteEdges_ite_real；
                PART 3 局部公式 sum_univ_split_pair, sum_neighborFinset_*,
                deltaOrd_block_left/right/rest, ordered_sum_deleteEdges, Tf_delete_singleton；
                装配 deletion_identity_of_local, deletion_identity（27 条）
Zagreb.lean     Z_eq_sum_ordered, three_le_denom, denom_le_four_maxDegree,
                Z_div_le_C, C_le_sqrt2_three_Z, zagreb_sandwich
StarEquality.lean  defC_nonneg, defC_sum, c_eq_of_defect_zero,
                C_eq_star_iff_aux, C_eq_star_iff
Kernel.lean（新增） c_antitone_right_nat_lt, c_succ_left_nat_lt, c_lt_left_nat,
                c_eq_c_m_one_iff, mem_incidenceFinset_iff
A1EdgeTypes.lean  edgeTypeCount、fxy 及 Tf/Cf 精确求值；edgeTypeCount_symm, fxy_symm,
                Tf_fxy_ne, Tf_fxy_eq, Cf_fxy_ne, Cf_fxy_eq, edgeType_deletion_identity（7 条）
A3Delta.lean    Delta 定义；telescoping_one/two 与两个实例, within_type_coincidence,
                Delta_diagonal_union, Delta_diagonal_of_same_union,
                Delta_sqrt20_left/right/coincidence, Delta_sqrt52_left/right/coincidence,
                sqrt20_ne_sqrt52（14 条）
```

## 构建（本机实测）

```bash
export ELAN_HOME="$(cd .. && pwd)/.elan"    # 发布包中即 code/.elan（与 check_formalisation.sh 一致）
export PATH=$ELAN_HOME/bin:$PATH ELAN_NO_RCFILE=1
export XDG_CACHE_HOME=$PWD/.cache          # $HOME 只读，缓存必须重定向
lake build                                  # 或运行 ./check_formalisation.sh（build + sorry 检查 + 定理计数）
```

环境获取要点（本机 GitHub 主站被重置，下载 0 B/s）：

1. **工具链**（`.elan/`，Lean 4 v4.34.0）：`raw.githubusercontent.com` 可达，用 elan 安装脚本，
   并设 `ELAN_NO_RCFILE=1` 避免写 `~/.profile` 失败。
2. **Mathlib 源码**：改用镜像 `https://ghfast.top/https://github.com/...`（实测 4.7 MB/s，
   比直连 codeload 的 19 KB/s 快约 250 倍），tarball 23.8 MB → 解压 118 MB。
3. **Mathlib 的 8 个依赖包**（batteries / aesop / Qq / proofwidgets / importGraph /
   LeanSearchClient / plausible / Cli）：用 git 的 `url.<mirror>.insteadOf` 注入重写，
   逐仓 `--depth 1` 克隆到 `.lake/packages/` 并 checkout 到 manifest 指定的 revision。
4. **olean 缓存**：`lake exe cache get`（8906 个 olean，448 MB，走官方 cache 服务器）。

## 与计算部分的对应

形式化的每条陈述在计算部分都有独立证据（`results/inequality_audit.json`）：
R1 星形定理、R9 $C=0$ 刻画、R6a/R6b 夹逼、R10–R11 删边恒等式在 $n\le9$ 穷举与
$n\le300$ 大图上零违反。现在其中 1–4 已从"有穷举支持的命题"升级为**机器检查的定理**。

## 优先级 5 的证明结构（本次完成）

`DeletionIdentity.lean` 把通用删边恒等式拆成三段，全部无条件证明：

1. **双重计数**（`sum_deltaOrd`）——局部增量
   $\delta(u,v)=f(d_u,d_v)+\sum_{x\in N(u)\setminus v}(f(d_u,d_x)-f(d_u-1,d_x))
   +\sum_{y\in N(v)\setminus u}(f(d_v,d_y)-f(d_v-1,d_y))$
   满足 $\sum_{(u,v)}\delta(u,v)=2T_f+2C_f$。中块用重指标引理 `sum_erase_sum`
   $\sum_{v\in s}\sum_{x\in s\setminus v}g(x)=(|s|-1)\sum_{x\in s}g(x)$
   （每个 $x$ 被 $d_u$ 个 $v$ 中的 $d_u-1$ 个漏掉）化为 $\sum_u(d_u-1)\sum_{x\in N(u)}(\cdot)$，
   末块交换求和指标后同理。
2. **删边度数更新**（Mathlib 缺失）：`SimpleGraph/DeleteEdges.lean` 只有 `deleteEdges_adj` 与
   `edgeFinset_deleteEdges`，没有度数引理。这里证明 `degree_deleteEdges_left/right`
   （$u,v$ 的度各减一）、`degree_deleteEdges_of_ne`（其余顶点度数不变）、
   `neighborFinset_deleteEdges_left/right/of_ne`（$v\notin N(u)$、$u\notin N(v)$、其余邻域不变）
   以及单 if 形式 `degree_deleteEdges_ite_real`。
3. **删边局部公式**（`Tf_delete_singleton`）：比较两张图的**有序**二重和，用 `sum_univ_split_pair`
   把顶点和拆成 $u$、$v$、其余三块，三块分别贡献 $-S_u-f(d_u,d_v)$、$-S_v-f(d_v,d_u)$、
   $-S_u-S_v$（$S_u=\sum_{x\in N(u)\setminus v}(f(d_u,d_x)-f(d_u-1,d_x))$）；
   「其余」块携带 $S_u,S_v$ 的第二份拷贝（每条边被两个端点各数一次），这正是修正项 $C_f$ 的来源。
   装配 `deletion_identity` 在 $2m$ 个有序对上求和再除以 2。

## 形式化边界（诚实清单）

报告中的实验部分（牌组枚举、碰撞搜索、残差熵、ML 任务）是数据而非定理；
距离型（Wiener）删边求和**不是** $(m-1)T-C$ 的形状（report.md §9 有严格反证证书），
因此没有该形状的命题可供形式化。
Δ 分类的穷举计算部分（`explorations/A3_classify*.py`，含 D≤8 扫描）是数据而非定理；
其中两个跨类型家族证书（√20、√52）已在 `A3Delta.lean` 中机器验证。
