/-
  StarTheorem/Zagreb.lean -- priority 4, second half: the Zagreb/Forgotten sandwich

      Z(G) / (4Δ - 1)  ≤  C(G)  ≤  (√2/3) · Z(G),

  where  Z(G) = Σ_u d_u(d_u-1)(2d_u-1) = 2F - 3M1 + 2m  (Δ = max degree).

  Proof.  `Z` is the ordered sum of the numerators of `psiSum`:

      Z(G) = Σ_u Σ_{v ∈ N(u)} (d_u-1)(2d_u-1)          (Z_eq_sum_ordered),

  because each vertex `u` occurs as the first coordinate exactly `d_u` times.
  For an adjacent pair with `d_u,d_v ≥ 1` one has

      3 ≤ 2d_u + 2d_v - 1 ≤ 4Δ - 1,

  so each summand of `psiSum` lies between its counterpart with denominator
  `4Δ-1` and its counterpart with denominator `3`; summing and using the already
  proven sharp sandwich `psiSum ≤ C ≤ √2 · psiSum` gives the claim.
-/

import StarTheorem.Kernel
import StarTheorem.Sandwich

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordered sum of the numerators of `psiSum` is `Z`. -/
theorem Z_eq_sum_ordered (G : SimpleGraph V) [DecidableRel G.Adj] :
    Z G = ∑ u, ∑ _v ∈ G.neighborFinset u,
      ((G.degree u : ℝ) - 1) * (2 * (G.degree u : ℝ) - 1) := by
  simp only [Z, Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
  exact Finset.sum_congr rfl fun u _ => by ring

/-- For an adjacent pair, the denominator `2d_u+2d_v-1` is at least `3`. -/
theorem three_le_denom {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    (3 : ℝ) ≤ 2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1 := by
  have h1 : 1 ≤ G.degree u := one_le_degree_of_adj h.symm
  have h2 : 1 ≤ G.degree v := one_le_degree_of_adj h
  have h1' : (1 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast h1
  have h2' : (1 : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast h2
  linarith

/-- For an adjacent pair, the denominator `2d_u+2d_v-1` is at most `4Δ-1`. -/
theorem denom_le_four_maxDegree {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1
      ≤ 4 * (G.maxDegree : ℝ) - 1 := by
  have h1 : G.degree u ≤ G.maxDegree := G.degree_le_maxDegree u
  have h2 : G.degree v ≤ G.maxDegree := G.degree_le_maxDegree v
  have h1' : (G.degree u : ℝ) ≤ (G.maxDegree : ℝ) := by exact_mod_cast h1
  have h2' : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by exact_mod_cast h2
  linarith

/-- **Lower half of the Zagreb sandwich**: `Z(G)/(4Δ-1) ≤ C(G)`. -/
theorem Z_div_le_C (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 0 < G.edgeFinset.card) :
    Z G / (4 * (G.maxDegree : ℝ) - 1) ≤ C G := by
  have hD1 : 1 ≤ G.maxDegree := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hm
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hadj : G.Adj u v := by
        have h1 : s(u, v) ∈ G.edgeSet := (G.mem_edgeFinset).mp he
        rwa [G.mem_edgeSet] at h1
      exact le_trans (one_le_degree_of_adj hadj.symm) (G.degree_le_maxDegree u)
  have hpos : (0 : ℝ) < 4 * (G.maxDegree : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (G.maxDegree : ℝ) := by exact_mod_cast hD1
    linarith
  have hstep : Z G / (4 * (G.maxDegree : ℝ) - 1) ≤ psiSum G := by
    rw [Z_eq_sum_ordered G, psiSum, Finset.sum_div]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun v hv => ?_
    have hadj : G.Adj u v := (G.mem_neighborFinset u v).mp hv
    have hdu : 1 ≤ G.degree u := one_le_degree_of_adj hadj.symm
    have hdu' : (1 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast hdu
    have hnum : (0 : ℝ) ≤ ((G.degree u : ℝ) - 1) * (2 * (G.degree u : ℝ) - 1) := by
      have : (0 : ℝ) ≤ (G.degree u : ℝ) - 1 := by linarith
      have : (0 : ℝ) ≤ 2 * (G.degree u : ℝ) - 1 := by linarith
      positivity
    have hden3 : (0 : ℝ) < 2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1 := by
      linarith [three_le_denom hadj]
    have hle := denom_le_four_maxDegree (G := G) (u := u) (v := v)
    exact div_le_div_of_nonneg_left hnum hden3 hle
  exact le_trans hstep (psiSum_le_C G)

/-- **Upper half of the Zagreb sandwich**: `C(G) ≤ (√2/3)·Z(G)`. -/
theorem C_le_sqrt2_three_Z (G : SimpleGraph V) [DecidableRel G.Adj] :
    C G ≤ Real.sqrt 2 / 3 * Z G := by
  have hstep : psiSum G ≤ Z G / 3 := by
    rw [Z_eq_sum_ordered G, psiSum, Finset.sum_div]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun v hv => ?_
    have hadj : G.Adj u v := (G.mem_neighborFinset u v).mp hv
    have hdu : 1 ≤ G.degree u := one_le_degree_of_adj hadj.symm
    have hdu' : (1 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast hdu
    have hnum : (0 : ℝ) ≤ ((G.degree u : ℝ) - 1) * (2 * (G.degree u : ℝ) - 1) := by
      have : (0 : ℝ) ≤ (G.degree u : ℝ) - 1 := by linarith
      have : (0 : ℝ) ≤ 2 * (G.degree u : ℝ) - 1 := by linarith
      positivity
    have hden3 : (0 : ℝ) < 3 := by norm_num
    have hle : (3 : ℝ) ≤ 2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1 := three_le_denom hadj
    exact div_le_div_of_nonneg_left hnum hden3 hle
  calc C G ≤ Real.sqrt 2 * psiSum G := C_le_sqrt2_psiSum G
    _ ≤ Real.sqrt 2 * (Z G / 3) := by
        exact mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 / 3 * Z G := by ring

/-- **The Zagreb/Forgotten sandwich** in one statement. -/
theorem zagreb_sandwich (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 0 < G.edgeFinset.card) :
    Z G / (4 * (G.maxDegree : ℝ) - 1) ≤ C G ∧ C G ≤ Real.sqrt 2 / 3 * Z G :=
  ⟨Z_div_le_C G hm, C_le_sqrt2_three_Z G⟩

end StarTheorem
