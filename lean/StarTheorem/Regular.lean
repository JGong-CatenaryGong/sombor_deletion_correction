/-
  StarTheorem/Regular.lean -- priority 3 of the formalisation plan:

      for an r-regular graph on N vertices,
        C(G) = N * r * (r-1) * c(r,r),
      with  c(r,r) = r*sqrt(2) - sqrt(2r^2-2r+1).

  Human proof: every edge joins two vertices of degree r, so
      C(G) = sum_u (r-1) * sum_{v in N(u)} c(r,r) = sum_u (r-1)*r*c(r,r) = N*(r-1)*r*c(r,r).
-/

import StarTheorem.Kernel
import StarTheorem.StarMax

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Closed form of the kernel at equal arguments: `c(r,r) = r√2 - √(2r²-2r+1)`. -/
theorem c_self (r : ℝ) (hr : 0 ≤ r) :
    c r r = r * Real.sqrt 2 - Real.sqrt (2 * r ^ 2 - 2 * r + 1) := by
  have h2 : (r - 1) ^ 2 + r ^ 2 = 2 * r ^ 2 - 2 * r + 1 := by ring
  have hsqrt : Real.sqrt (r ^ 2 + r ^ 2) = r * Real.sqrt 2 := by
    rw [show r ^ 2 + r ^ 2 = r ^ 2 * 2 by ring,
      Real.sqrt_mul (sq_nonneg r) 2, Real.sqrt_sq hr]
  rw [c, hsqrt, h2]

/-- **Regular-graph value of `C`.** -/
theorem C_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hreg : ∀ u, G.degree u = r) :
    C G = (Fintype.card V : ℝ) * (r : ℝ) * ((r : ℝ) - 1) * c (r : ℝ) (r : ℝ) := by
  have hinner : ∀ u : V, (∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v))
      = (r : ℝ) * c (r : ℝ) (r : ℝ) := by
    intro u
    have hconst : ∀ v ∈ G.neighborFinset u,
        c (G.degree u) (G.degree v) = c (r : ℝ) (r : ℝ) := by
      intro v _
      rw [hreg u, hreg v]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, G.card_neighborFinset_eq_degree,
      hreg u, nsmul_eq_mul]
  have hstep : ∀ u : V, ((G.degree u : ℝ) - 1) *
        (∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v))
      = ((r : ℝ) - 1) * ((r : ℝ) * c (r : ℝ) (r : ℝ)) := by
    intro u
    rw [hinner u, hreg u]
  rw [C]
  rw [Finset.sum_congr rfl fun u _ => hstep u]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The exact regular value is compatible with the universal star bound. -/
theorem C_of_regular_le_star (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hreg : ∀ u, G.degree u = r) (hm : 2 ≤ G.edgeFinset.card) :
    C G ≤ (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) - 1)
            * c (G.edgeFinset.card : ℝ) 1 :=
  C_le_star G hm

end StarTheorem
