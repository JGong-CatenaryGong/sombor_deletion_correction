/-
  StarTheorem/Sandwich.lean -- priority 4 of the formalisation plan.

  (a) per-pair bounds:  (2a-1)/(2a+2b-1) ≤ c(a,b) ≤ √2 · (2a-1)/(2a+2b-1)   (a,b ≥ 1);
  (b) consequently, with psiSum G = Σ_{uv} Ψ_uv/(2d_u+2d_v-1),
        psiSum G ≤ C(G) ≤ √2 · psiSum G.

  Proof of (a): rationalise, c(a,b) = (2a-1)/D with
  D = √(a²+b²) + √((a-1)²+b²) > 0, and bound D by
      (2a+2b-1)/√2 ≤ D ≤ 2a+2b-1,
  the left inequality from 2(x²+y²) ≥ (x+y)² and the right from x²+y² ≤ (x+y)².
-/

import StarTheorem.Kernel

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### elementary sqrt bounds -/

/-- `√(x²+y²) ≤ x+y` for `x,y ≥ 0`. -/
theorem sqrt_sq_add_sq_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x ^ 2 + y ^ 2) ≤ x + y := by
  have hX : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hsq : Real.sqrt (x ^ 2 + y ^ 2) ^ 2 ≤ (x + y) ^ 2 := by
    rw [Real.sq_sqrt hX]
    nlinarith [mul_nonneg hx hy]
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by linarith)] at h

/-- `√(x²+y²) ≥ (x+y)/√2` for `x,y ≥ 0`. -/
theorem le_sqrt_sq_add_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) / Real.sqrt 2 ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  have hX : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : ((x + y) / Real.sqrt 2) ^ 2 ≤ Real.sqrt (x ^ 2 + y ^ 2) ^ 2 := by
    rw [Real.sq_sqrt hX, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [sq_nonneg (x - y)]
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (by positivity), abs_of_nonneg (Real.sqrt_nonneg _)] at h

/-- Denominator bounds: `(2a+2b-1)/√2 ≤ D ≤ 2a+2b-1`, where `D` is the rationalised
denominator of the kernel. -/
theorem denom_bounds {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (2 * a + 2 * b - 1) / Real.sqrt 2
        ≤ Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt ((a - 1) ^ 2 + b ^ 2)
      ∧ Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt ((a - 1) ^ 2 + b ^ 2) ≤ 2 * a + 2 * b - 1 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have ha1 : 0 ≤ a - 1 := by linarith
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h1 := sqrt_sq_add_sq_le ha0 hb0
  have h2' := sqrt_sq_add_sq_le ha1 hb0
  have h3 := le_sqrt_sq_add_sq ha0 hb0
  have h4 := le_sqrt_sq_add_sq ha1 hb0
  have hsum := add_le_add h3 h4
  have heq : (a + b) / Real.sqrt 2 + ((a - 1) + b) / Real.sqrt 2
      = (2 * a + 2 * b - 1) / Real.sqrt 2 := by ring
  constructor
  · rw [← heq]
    exact hsum
  · linarith

/-- The denominator `2a+2b-1` is positive on the domain `a,b ≥ 1`. -/
theorem two_a_two_b_sub_one_pos {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (0 : ℝ) < 2 * a + 2 * b - 1 := by linarith

/-- Lower bound for the kernel. -/
theorem c_ge_div {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (2 * a - 1) / (2 * a + 2 * b - 1) ≤ c a b := by
  rw [c_eq_div]
  have hD := (denom_bounds ha hb).2
  have hDpos := denom_pos a b
  have hpos := two_a_two_b_sub_one_pos ha hb
  have hnum : (0 : ℝ) ≤ 2 * a - 1 := by linarith
  exact div_le_div_of_nonneg_left hnum hDpos hD

/-- Upper bound for the kernel. -/
theorem c_le_sqrt2_div {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    c a b ≤ Real.sqrt 2 * ((2 * a - 1) / (2 * a + 2 * b - 1)) := by
  set D := Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt ((a - 1) ^ 2 + b ^ 2) with hDdef
  have hDpos : 0 < D := denom_pos a b
  have hpos := two_a_two_b_sub_one_pos ha hb
  have hnum : (0 : ℝ) ≤ 2 * a - 1 := by linarith
  have hD := (denom_bounds ha hb).1
  -- key: 2a+2b-1 ≤ √2 * D
  have hkey : 2 * a + 2 * b - 1 ≤ Real.sqrt 2 * D := by
    have h := hD
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))] at h
    linarith
  have h1 : (1 : ℝ) ≤ (Real.sqrt 2 / (2 * a + 2 * b - 1)) * D := by
    have heq : (Real.sqrt 2 / (2 * a + 2 * b - 1)) * D
        = Real.sqrt 2 * D / (2 * a + 2 * b - 1) := by ring
    rw [heq]
    exact (le_div_iff₀ hpos).mpr (by linarith)
  have hinv : 1 / D ≤ Real.sqrt 2 / (2 * a + 2 * b - 1) := by
    rw [div_le_iff₀ hDpos]
    exact h1
  rw [c_eq_div, ← hDdef]
  calc (2 * a - 1) / D
      = (2 * a - 1) * (1 / D) := by ring
    _ ≤ (2 * a - 1) * (Real.sqrt 2 / (2 * a + 2 * b - 1)) :=
        mul_le_mul_of_nonneg_left hinv hnum
    _ = Real.sqrt 2 * ((2 * a - 1) / (2 * a + 2 * b - 1)) := by ring


/-! ### (b) the sharp sandwich for `C` -/

/-- **Lower half of the sharp sandwich**: `psiSum G ≤ C G`. -/
theorem psiSum_le_C (G : SimpleGraph V) [DecidableRel G.Adj] : psiSum G ≤ C G := by
  rw [psiSum, C]
  refine Finset.sum_le_sum fun u _ => ?_
  rcases Nat.eq_zero_or_pos (G.degree u) with h0 | hpos
  · rw [neighborFinset_eq_empty_of_degree_eq_zero h0, h0]
    simp
  · have hdu : 1 ≤ G.degree u := hpos
    have hfac : (0 : ℝ) ≤ (G.degree u : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast hdu
      linarith
    have hL : (∑ v ∈ G.neighborFinset u,
          ((G.degree u : ℝ) - 1) * (2 * (G.degree u : ℝ) - 1)
            / (2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1))
        = ((G.degree u : ℝ) - 1) * ∑ v ∈ G.neighborFinset u,
            (2 * (G.degree u : ℝ) - 1)
              / (2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hL]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v hv => ?_) hfac
    have hadj : G.Adj u v := (G.mem_neighborFinset u v).mp hv
    have hdv : 1 ≤ G.degree v := one_le_degree_of_adj hadj
    exact c_ge_div (by exact_mod_cast hdu) (by exact_mod_cast hdv)

/-- **Upper half of the sharp sandwich**: `C G ≤ √2 * psiSum G`. -/
theorem C_le_sqrt2_psiSum (G : SimpleGraph V) [DecidableRel G.Adj] :
    C G ≤ Real.sqrt 2 * psiSum G := by
  rw [psiSum, C, Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  rcases Nat.eq_zero_or_pos (G.degree u) with h0 | hpos
  · rw [neighborFinset_eq_empty_of_degree_eq_zero h0, h0]
    simp
  · have hdu : 1 ≤ G.degree u := hpos
    have hfac : (0 : ℝ) ≤ (G.degree u : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast hdu
      linarith
    have hL : ((G.degree u : ℝ) - 1) *
          (∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v))
        ≤ ((G.degree u : ℝ) - 1) * (Real.sqrt 2 * ∑ v ∈ G.neighborFinset u,
            (2 * (G.degree u : ℝ) - 1)
              / (2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ hfac
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun v hv => ?_
      have hadj : G.Adj u v := (G.mem_neighborFinset u v).mp hv
      have hdv : 1 ≤ G.degree v := one_le_degree_of_adj hadj
      exact c_le_sqrt2_div (by exact_mod_cast hdu) (by exact_mod_cast hdv)
    have hS' : (∑ v ∈ G.neighborFinset u,
          ((G.degree u : ℝ) - 1) * (2 * (G.degree u : ℝ) - 1)
            / (2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1))
        = ((G.degree u : ℝ) - 1) * ∑ v ∈ G.neighborFinset u,
            (2 * (G.degree u : ℝ) - 1)
              / (2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hS']
    rw [show Real.sqrt 2 * (((G.degree u : ℝ) - 1) *
          ∑ v ∈ G.neighborFinset u, (2 * (G.degree u : ℝ) - 1)
            / (2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1))
        = ((G.degree u : ℝ) - 1) * (Real.sqrt 2 *
          ∑ v ∈ G.neighborFinset u, (2 * (G.degree u : ℝ) - 1)
            / (2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1)) by ring]
    exact hL

end StarTheorem
