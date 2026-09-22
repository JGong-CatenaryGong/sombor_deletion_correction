/-
  StarTheorem/ZeroIff.lean -- priority 2 of the formalisation plan:

      C(G) = 0  ↔  G is a matching (every degree ≤ 1).

  Human proof (report.md §8.3):
  (⇐) if every d_u ≤ 1 then each summand (d_u - 1) * (…) vanishes: for d_u = 0 the
      neighbour set is empty, for d_u = 1 the factor (d_u - 1) is zero;
  (⇒) each summand is ≥ 0, and for a vertex u with d_u ≥ 2 every neighbour v has
      d_v ≥ 1, whence c(d_u,d_v) > 0 and the u-th summand is > 0, contradicting C = 0.
-/

import StarTheorem.Kernel

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every summand of `C` is nonnegative. -/
theorem C_summand_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    0 ≤ ((G.degree u : ℝ) - 1) * ∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v) := by
  rcases Nat.eq_zero_or_pos (G.degree u) with h0 | hpos
  · rw [neighborFinset_eq_empty_of_degree_eq_zero h0, h0]
    simp
  · have h1 : (0 : ℝ) ≤ (G.degree u : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast hpos
      linarith
    refine mul_nonneg h1 (Finset.sum_nonneg fun v hv => ?_)
    have hadj : G.Adj u v := (G.mem_neighborFinset u v).mp hv
    have hdv : 1 ≤ G.degree v := one_le_degree_of_adj hadj
    exact le_of_lt (c_pos (by exact_mod_cast hpos) (by exact_mod_cast hdv))

/-- The `u`-th summand of `C` is positive as soon as `d_u ≥ 2`. -/
theorem C_summand_pos (G : SimpleGraph V) [DecidableRel G.Adj] {u : V} (hu : 2 ≤ G.degree u) :
    0 < ((G.degree u : ℝ) - 1) * ∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v) := by
  obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj u).mp (by omega : 0 < G.degree u)
  have hmem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hv
  have hdv : 1 ≤ G.degree v := one_le_degree_of_adj hv
  have hc : 0 < c (G.degree u) (G.degree v) :=
    c_pos (by exact_mod_cast (by omega : 1 ≤ G.degree u)) (by exact_mod_cast hdv)
  have hnn : ∀ x ∈ G.neighborFinset u, (0 : ℝ) ≤ c (G.degree u) (G.degree x) := by
    intro x hx
    have hadj : G.Adj u x := (G.mem_neighborFinset u x).mp hx
    have hdx : 1 ≤ G.degree x := one_le_degree_of_adj hadj
    exact le_of_lt (c_pos (by exact_mod_cast (by omega : 1 ≤ G.degree u))
      (by exact_mod_cast hdx))
  have hsum : 0 < ∑ x ∈ G.neighborFinset u, c (G.degree u) (G.degree x) :=
    Finset.sum_pos' hnn ⟨v, hmem, hc⟩
  have h1 : (0 : ℝ) < (G.degree u : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast hu
    linarith
  exact mul_pos h1 hsum

/-- **`C(G) = 0` iff `G` is a matching** (all degrees at most 1). -/
theorem C_eq_zero_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    C G = 0 ↔ ∀ u, G.degree u ≤ 1 := by
  constructor
  · intro h u
    by_contra hu
    push_neg at hu
    have hnn : ∀ w ∈ (Finset.univ : Finset V),
        (0 : ℝ) ≤ ((G.degree w : ℝ) - 1) *
          ∑ v ∈ G.neighborFinset w, c (G.degree w) (G.degree v) :=
      fun w _ => C_summand_nonneg G w
    have hpos : ∃ w ∈ (Finset.univ : Finset V),
        0 < ((G.degree w : ℝ) - 1) *
          ∑ v ∈ G.neighborFinset w, c (G.degree w) (G.degree v) :=
      ⟨u, Finset.mem_univ u, C_summand_pos G hu⟩
    have hlt : 0 < C G := Finset.sum_pos' hnn hpos
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · intro h
    refine Finset.sum_eq_zero fun u _ => ?_
    rcases Nat.eq_zero_or_pos (G.degree u) with h0 | hpos
    · rw [neighborFinset_eq_empty_of_degree_eq_zero h0, h0]
      simp
    · have h1 : G.degree u = 1 := by have := h u; omega
      rw [h1]
      simp

end StarTheorem
