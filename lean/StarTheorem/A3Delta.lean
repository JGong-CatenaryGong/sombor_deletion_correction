/-
  StarTheorem/A3Delta.lean -- exploration A3: the algebraic structure behind the
  exact Delta coincidences of report section 7.4.

      Delta(a,b,A,B) = sqrt(a^2+b^2) + sum_{x in A} c(a,x) + sum_{y in B} c(b,y)

  Formalised here:
  * the two telescoping identities: whenever a1^2+x^2 = (a2-1)^2+y^2 (resp.
    (a1-1)^2+x^2 = a2^2+y^2), the sum c(a1,x)+c(a2,y) collapses to a single
    difference of square roots -- the mechanism producing the abundant
    within-type coincidences (explorations/A3_classification.md);
  * the diagonal-union theorem: for a = b >= 0, Delta depends only on the
    concatenated list A ++ B (since c(a,.) = c(b,.)), explaining every
    diagonal-type coincidence;
  * the two cross-type identities of the report, as exact equalities:
      Delta(2,2,[1],[1])     = Delta(1,3,[],[1,6])    = 2*sqrt 5   (sqrt 20 family)
      Delta(3,3,[2,3],[2,2]) = Delta(2,4,[1],[3,4,6]) = 2*sqrt 13  (sqrt 52 family)
    and the two families are distinct (2*sqrt 5 ≠ 2*sqrt 13);
  * a concrete telescoping instance: c(2,2)+c(3,2) = c(2,3)+c(3,1) = sqrt13-sqrt5.

  The full *classification* (normal forms over the multiquadratic basis and the
  exhaustive degree-<=7 scan proving these are the only cross-type families in
  that range) is computational: explorations/A3_classify.py.
-/

import StarTheorem.Defs
import Mathlib.Tactic

namespace StarTheorem

/-- The local edge-deletion increment of a configuration `(a, b, A, B)`. -/
noncomputable def Delta (a b : ℝ) (A B : List ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2) + (A.map (c a)).sum + (B.map (c b)).sum

/-! ### Telescoping identities -/

/-- If `a₁² + x² = (a₂-1)² + y²`, the two kernels telescope. -/
theorem telescoping_one (a₁ x a₂ y : ℝ) (h : a₁ ^ 2 + x ^ 2 = (a₂ - 1) ^ 2 + y ^ 2) :
    c a₁ x + c a₂ y = Real.sqrt (a₂ ^ 2 + y ^ 2) - Real.sqrt ((a₁ - 1) ^ 2 + x ^ 2) := by
  simp only [c]
  rw [h]
  ring

/-- If `(a₁-1)² + x² = a₂² + y²`, the two kernels telescope (other direction). -/
theorem telescoping_two (a₁ x a₂ y : ℝ) (h : (a₁ - 1) ^ 2 + x ^ 2 = a₂ ^ 2 + y ^ 2) :
    c a₁ x + c a₂ y = Real.sqrt (a₁ ^ 2 + x ^ 2) - Real.sqrt ((a₂ - 1) ^ 2 + y ^ 2) := by
  simp only [c]
  rw [h]
  ring

/-- Concrete instance: `c(2,2) + c(3,2) = sqrt 13 - sqrt 5` (via 2²+2² = (3-1)²+2²). -/
theorem telescoping_example : c 2 2 + c 3 2 = Real.sqrt 13 - Real.sqrt 5 := by
  have h := telescoping_one (2 : ℝ) 2 3 2 (by norm_num)
  norm_num at h
  exact h

/-- Concrete instance: `c(2,3) + c(3,1) = sqrt 13 - sqrt 5` (via (2-1)²+3² = 3²+1²). -/
theorem telescoping_example' : c 2 3 + c 3 1 = Real.sqrt 13 - Real.sqrt 5 := by
  have h := telescoping_two (2 : ℝ) 3 3 1 (by norm_num)
  norm_num at h
  exact h

/-- Two different telescoping routes to the same binomial: a within-type
coincidence for the edge type (2,3). -/
theorem within_type_coincidence : c 2 2 + c 3 2 = c 2 3 + c 3 1 := by
  rw [telescoping_example, telescoping_example']

/-! ### Diagonal configurations depend only on the union A ⊔ B -/

/-- For `a = b` (and `a >= 0`), `Delta a a A B = a*sqrt 2 + sum_{x in A++B} c(a,x)`:
the split of the neighbour-degree multiset between the two endpoints is irrelevant. -/
theorem Delta_diagonal_union (a : ℝ) (ha : 0 ≤ a) (A B : List ℝ) :
    Delta a a A B = a * Real.sqrt 2 + ((A ++ B).map (c a)).sum := by
  have hsq : Real.sqrt (a ^ 2 + a ^ 2) = a * Real.sqrt 2 := by
    have h2 : a ^ 2 + a ^ 2 = 2 * a ^ 2 := by ring
    rw [h2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq ha]
    ring
  simp only [Delta]
  rw [hsq, List.map_append, List.sum_append]
  ring

/-- Consequence: for equal endpoint degrees, redistributing degrees between A and B
(with the same union) preserves Delta. -/
theorem Delta_diagonal_of_same_union (a : ℝ) (ha : 0 ≤ a)
    (A₁ B₁ A₂ B₂ : List ℝ) (h : A₁ ++ B₁ = A₂ ++ B₂) :
    Delta a a A₁ B₁ = Delta a a A₂ B₂ := by
  rw [Delta_diagonal_union a ha, Delta_diagonal_union a ha, h]

/-! ### Numerical witnesses: the two cross-type families -/

private theorem sqrt8_eq : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]

private theorem sqrt18_eq : Real.sqrt 18 = 3 * Real.sqrt 2 := by
  rw [show (18 : ℝ) = 3 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3 ^ 2), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3)]

private theorem sqrt20_eq : Real.sqrt 20 = 2 * Real.sqrt 5 := by
  rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]

private theorem sqrt40_eq : Real.sqrt 40 = 2 * Real.sqrt 10 := by
  rw [show (40 : ℝ) = 2 ^ 2 * 10 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]

private theorem sqrt45_eq : Real.sqrt 45 = 3 * Real.sqrt 5 := by
  rw [show (45 : ℝ) = 3 ^ 2 * 5 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3 ^ 2), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3)]

private theorem sqrt25_eq : Real.sqrt 25 = 5 := by
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 5)]

private theorem sqrt32_eq : Real.sqrt 32 = 4 * Real.sqrt 2 := by
  rw [show (32 : ℝ) = 4 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 ^ 2), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4)]

private theorem sqrt52_eq : Real.sqrt 52 = 2 * Real.sqrt 13 := by
  rw [show (52 : ℝ) = 2 ^ 2 * 13 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]

private theorem c21 : c 2 1 = Real.sqrt 5 - Real.sqrt 2 := by
  simp only [c]
  rw [show (2 : ℝ) ^ 2 + 1 ^ 2 = 5 by norm_num, show (2 - 1 : ℝ) ^ 2 + 1 ^ 2 = 2 by norm_num]

private theorem c31 : c 3 1 = Real.sqrt 10 - Real.sqrt 5 := by
  simp only [c]
  rw [show (3 : ℝ) ^ 2 + 1 ^ 2 = 10 by norm_num, show (3 - 1 : ℝ) ^ 2 + 1 ^ 2 = 5 by norm_num]

private theorem c32 : c 3 2 = Real.sqrt 13 - 2 * Real.sqrt 2 := by
  simp only [c]
  rw [show (3 : ℝ) ^ 2 + 2 ^ 2 = 13 by norm_num, show (3 - 1 : ℝ) ^ 2 + 2 ^ 2 = 8 by norm_num,
    sqrt8_eq]

private theorem c33 : c 3 3 = 3 * Real.sqrt 2 - Real.sqrt 13 := by
  simp only [c]
  rw [show (3 : ℝ) ^ 2 + 3 ^ 2 = 18 by norm_num, show (3 - 1 : ℝ) ^ 2 + 3 ^ 2 = 13 by norm_num,
    sqrt18_eq]

private theorem c36 : c 3 6 = 3 * Real.sqrt 5 - 2 * Real.sqrt 10 := by
  simp only [c]
  rw [show (3 : ℝ) ^ 2 + 6 ^ 2 = 45 by norm_num, show (3 - 1 : ℝ) ^ 2 + 6 ^ 2 = 40 by norm_num,
    sqrt45_eq, sqrt40_eq]

private theorem c43 : c 4 3 = 5 - 3 * Real.sqrt 2 := by
  simp only [c]
  rw [show (4 : ℝ) ^ 2 + 3 ^ 2 = 25 by norm_num, show (4 - 1 : ℝ) ^ 2 + 3 ^ 2 = 18 by norm_num,
    sqrt25_eq, sqrt18_eq]

private theorem c44 : c 4 4 = 4 * Real.sqrt 2 - 5 := by
  simp only [c]
  rw [show (4 : ℝ) ^ 2 + 4 ^ 2 = 32 by norm_num, show (4 - 1 : ℝ) ^ 2 + 4 ^ 2 = 25 by norm_num,
    sqrt32_eq, sqrt25_eq]

private theorem c46 : c 4 6 = 2 * Real.sqrt 13 - 3 * Real.sqrt 5 := by
  simp only [c]
  rw [show (4 : ℝ) ^ 2 + 6 ^ 2 = 52 by norm_num, show (4 - 1 : ℝ) ^ 2 + 6 ^ 2 = 45 by norm_num,
    sqrt52_eq, sqrt45_eq]

/-- The √20 family, side 1: `Delta(2,2,[1],[1]) = 2√5`. -/
theorem Delta_sqrt20_left : Delta 2 2 [1] [1] = 2 * Real.sqrt 5 := by
  have hd : Delta 2 2 [1] [1] = Real.sqrt (2 ^ 2 + 2 ^ 2) + c 2 1 + c 2 1 := by
    simp only [Delta, List.map_singleton, List.sum_singleton]
  rw [hd, show (2 : ℝ) ^ 2 + 2 ^ 2 = 8 by norm_num, sqrt8_eq, c21]
  ring

/-- The √20 family, side 2: `Delta(1,3,[],[1,6]) = 2√5`. -/
theorem Delta_sqrt20_right : Delta 1 3 [] [1, 6] = 2 * Real.sqrt 5 := by
  have hd : Delta 1 3 [] [1, 6] = Real.sqrt (1 ^ 2 + 3 ^ 2) + (c 3 1 + c 3 6) := by
    simp only [Delta, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
      List.map_singleton, List.sum_singleton, add_zero, zero_add]
  rw [hd, show (1 : ℝ) ^ 2 + 3 ^ 2 = 10 by norm_num, c31, c36]
  ring

/-- **Cross-type coincidence 1 (report 7.4)**: two different edge types attain the
same exact Delta value √20 = 2√5. -/
theorem Delta_sqrt20_coincidence : Delta 2 2 [1] [1] = Delta 1 3 [] [1, 6] := by
  rw [Delta_sqrt20_left, Delta_sqrt20_right]

/-- The √52 family, side 1: `Delta(3,3,[2,3],[2,2]) = 2√13`. -/
theorem Delta_sqrt52_left : Delta 3 3 [2, 3] [2, 2] = 2 * Real.sqrt 13 := by
  have hd : Delta 3 3 [2, 3] [2, 2]
      = Real.sqrt (3 ^ 2 + 3 ^ 2) + (c 3 2 + c 3 3) + (c 3 2 + c 3 2) := by
    simp only [Delta, List.map_cons, List.sum_cons, List.map_singleton, List.sum_singleton,
      List.map_nil, List.sum_nil, add_zero, zero_add]
  rw [hd, show (3 : ℝ) ^ 2 + 3 ^ 2 = 18 by norm_num, sqrt18_eq, c32, c33]
  ring

/-- The √52 family, side 2: `Delta(2,4,[1],[3,4,6]) = 2√13`. -/
theorem Delta_sqrt52_right : Delta 2 4 [1] [3, 4, 6] = 2 * Real.sqrt 13 := by
  have hd : Delta 2 4 [1] [3, 4, 6]
      = Real.sqrt (2 ^ 2 + 4 ^ 2) + c 2 1 + (c 4 3 + c 4 4 + c 4 6) := by
    simp only [Delta, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
      List.map_singleton, List.sum_singleton, add_zero, zero_add]
    ring
  rw [hd, show (2 : ℝ) ^ 2 + 4 ^ 2 = 20 by norm_num, sqrt20_eq, c21, c43, c44, c46]
  ring

/-- **Cross-type coincidence 2 (report 7.4)**: √52 = 2√13 attained by two edge types. -/
theorem Delta_sqrt52_coincidence : Delta 3 3 [2, 3] [2, 2] = Delta 2 4 [1] [3, 4, 6] := by
  rw [Delta_sqrt52_left, Delta_sqrt52_right]

/-- The two families are genuinely distinct values. -/
theorem sqrt20_ne_sqrt52 : Delta 2 2 [1] [1] ≠ Delta 3 3 [2, 3] [2, 2] := by
  rw [Delta_sqrt20_left, Delta_sqrt52_left]
  intro h
  have h2 : (2 * Real.sqrt 5) ^ 2 = (2 * Real.sqrt 13) ^ 2 := by rw [h]
  have e1 : (2 * Real.sqrt 5) ^ 2 = (20 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 5)]
    norm_num
  have e2 : (2 * Real.sqrt 13) ^ 2 = (52 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 13)]
    norm_num
  have h3 : (20 : ℝ) = 52 := calc
    (20 : ℝ) = (2 * Real.sqrt 5) ^ 2 := e1.symm
    _ = (2 * Real.sqrt 13) ^ 2 := h2
    _ = 52 := e2
  norm_num at h3

end StarTheorem
