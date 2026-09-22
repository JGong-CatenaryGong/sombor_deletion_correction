/-
  StarTheorem/Defs.lean -- definitions for the formalisation of the
  edge-deletion correction term C(G).

  Companion to report.md §8.  Everything here is deliberately minimal so that the
  statements can be type-checked with a small slice of Mathlib
  (`Combinatorics.SimpleGraph.*` plus `Analysis.SpecialFunctions.Sqrt`).
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Sombor deletion kernel `c(a,b) = sqrt(a^2+b^2) - sqrt((a-1)^2+b^2)`. -/
noncomputable def c (a b : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2) - Real.sqrt ((a - 1) ^ 2 + b ^ 2)

/-- The per-edge contribution `phi(a,b) = (a-1)c(a,b) + (b-1)c(b,a)`. -/
noncomputable def phi (a b : ℝ) : ℝ := (a - 1) * c a b + (b - 1) * c b a

/-- The correction term `C(G)`, in the vertex form used in the report:

      C(G) = sum_u (d_u - 1) * sum_{v in N(u)} c(d_u, d_v).
-/
noncomputable def C (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ u, ((G.degree u : ℝ) - 1) * (∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v))

/-- `m = |E(G)|` as a real number, the quantity appearing in every bound. -/
noncomputable def mR (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ := (G.edgeFinset.card : ℝ)

/-- `M1(G) = sum_u d_u^2` (first Zagreb index), as a real number. -/
noncomputable def M1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ u, (G.degree u : ℝ) ^ 2

/-- `Z(G) = 2F - 3M1 + 2m = sum_u d_u(d_u-1)(2d_u-1)`, the quantity in the
Zagreb/Forgotten sandwich. -/
noncomputable def Z (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ u, (G.degree u : ℝ) * ((G.degree u : ℝ) - 1) * (2 * (G.degree u : ℝ) - 1)

/-- `Psi_uv = (d_u-1)(2d_u-1) + (d_v-1)(2d_v-1)` for an edge `uv`. -/
noncomputable def Psi (a b : ℝ) : ℝ := (a - 1) * (2 * a - 1) + (b - 1) * (2 * b - 1)

/-- The sharp lower/upper sum `sum_{uv} Psi_uv / (2 d_u + 2 d_v - 1)` of the report,
written as an *ordered* sum over half of `Psi`: by symmetry of adjacency this equals
the edge sum, because the ordered sum of the second half of `Psi` equals the first. -/
noncomputable def psiSum (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ u, ∑ v ∈ G.neighborFinset u,
    ((G.degree u : ℝ) - 1) * (2 * (G.degree u : ℝ) - 1)
      / (2 * (G.degree u : ℝ) + 2 * (G.degree v : ℝ) - 1)

/-- The degree-sequence upper bound `sum_u d_u(d_u-1) c(d_u,1)`. -/
noncomputable def degSeqBound (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ u, (G.degree u : ℝ) * ((G.degree u : ℝ) - 1) * c (G.degree u) 1

end StarTheorem
