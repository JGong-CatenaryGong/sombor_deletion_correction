/-
  StarTheorem/StarMax.lean -- priority 1 of the formalisation plan:

      THEOREM (star maximisation).  For every finite simple graph G with m ≥ 2 edges,
        C(G) ≤ m (m-1) c(m,1) = C(K_{1,m}),
      with equality iff G is the star K_{1,m} plus isolated vertices.

  Human proof (report.md §8.3), three ingredients:

    (L1) c is increasing in its first and decreasing in its second argument   [Kernel.lean]
           ⇒ for every edge uv:  c(d_u,d_v) ≤ c(m,1),  c(d_v,d_u) ≤ c(m,1);
    (L2) d_u + d_v ≤ m + 1 for every edge uv                                  [this file]
    (L3) M1 = Σ_u d_u² = Σ_uv (d_u + d_v) ≤ m(m+1)                            [this file]

  Assembly:
    C(G) = Σ_u (d_u-1) Σ_{v∈N(u)} c(d_u,d_v)
         ≤ Σ_u (d_u-1) · d_u · c(m,1)             (by L1)
         = (M1 - 2m) c(m,1)                       (Σ d_u = 2m)
         ≤ (m² + m - 2m) c(m,1) = m(m-1) c(m,1)   (by L3).
-/

import StarTheorem.Kernel

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### (L2) the degree sum along an edge -/

/-- Two distinct edges of a simple graph share at most one vertex: if `u ≠ v` both
belong to `e`, then `e = s(u,v)`. -/
theorem eq_sym2_of_mem_of_mem {u v : V} (huv : u ≠ v) {e : Sym2 V}
    (hu : u ∈ e) (hv : v ∈ e) : e = s(u, v) := by
  obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hu
  rcases Sym2.mem_iff'.mp hv with h | h
  · exact absurd h.symm huv
  · rw [h]

/-- **(L2)**: for an edge `uv` of a graph with `m` edges, `d_u + d_v ≤ m + 1`. -/
theorem edge_degree_add_le (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    G.degree u + G.degree v ≤ G.edgeFinset.card + 1 := by
  have huv : u ≠ v := G.ne_of_adj h
  have hmem : ∀ (w : V) (e : Sym2 V), e ∈ G.incidenceFinset w ↔ e ∈ G.edgeFinset ∧ w ∈ e := by
    intro w e
    rw [G.incidenceFinset_eq_filter, Finset.mem_filter]
  have hle1 : (G.incidenceFinset u ∩ G.incidenceFinset v).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_inter] at ha hb
    have hau : u ∈ a := ((hmem u a).mp ha.1).2
    have hav : v ∈ a := ((hmem v a).mp ha.2).2
    have hbu : u ∈ b := ((hmem u b).mp hb.1).2
    have hbv : v ∈ b := ((hmem v b).mp hb.2).2
    rw [eq_sym2_of_mem_of_mem huv hau hav, eq_sym2_of_mem_of_mem huv hbu hbv]
  have hunion : (G.incidenceFinset u ∪ G.incidenceFinset v).card ≤ G.edgeFinset.card :=
    Finset.card_le_card (Finset.union_subset (G.incidenceFinset_subset u)
      (G.incidenceFinset_subset v))
  have hsum := Finset.card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
  rw [G.card_incidenceFinset_eq_degree u, G.card_incidenceFinset_eq_degree v] at hsum
  omega

/-! ### (L3) the Zagreb bound -/

/-- Swapping the order of the double sum over neighbours. -/
theorem neighbor_sum_swap (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    (∑ u, ∑ v ∈ G.neighborFinset u, f v) = ∑ v, ∑ u ∈ G.neighborFinset v, f v := by
  simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  by_cases h : G.Adj u v
  · simp [h, (G.adj_comm u v).mp h]
  · have h' : ¬ G.Adj v u := fun hvu => h ((G.adj_comm v u).mp hvu)
    simp [h, h']

/-- `2 * M1 = Σ_u Σ_{v ∈ N(u)} (d_u + d_v)`. -/
theorem two_mul_M1 (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * M1 G = ∑ u, ∑ v ∈ G.neighborFinset u, ((G.degree u : ℝ) + (G.degree v : ℝ)) := by
  have hsplit : (∑ u, ∑ v ∈ G.neighborFinset u, ((G.degree u : ℝ) + (G.degree v : ℝ)))
      = (∑ u, ∑ _v ∈ G.neighborFinset u, (G.degree u : ℝ))
        + ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree v : ℝ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_add_distrib
  have hfirst : (∑ u, ∑ _v ∈ G.neighborFinset u, (G.degree u : ℝ)) = M1 G := by
    simp only [M1, Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul, sq]
  have hsecond : (∑ u, ∑ v ∈ G.neighborFinset u, (G.degree v : ℝ)) = M1 G := by
    rw [neighbor_sum_swap]
    simp only [M1, Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul, sq]
  rw [hsplit, hfirst, hsecond]
  ring

/-- **(L3)**: `M1(G) ≤ m(m+1)`. -/
theorem M1_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    M1 G ≤ (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) + 1) := by
  have hterm : ∀ u : V, ∀ v ∈ G.neighborFinset u,
      ((G.degree u : ℝ) + (G.degree v : ℝ)) ≤ (G.edgeFinset.card : ℝ) + 1 := by
    intro u v hv
    have hadj : G.Adj u v := (G.mem_neighborFinset u v).mp hv
    have := edge_degree_add_le G hadj
    exact_mod_cast this
  have hbound : (∑ u, ∑ v ∈ G.neighborFinset u, ((G.degree u : ℝ) + (G.degree v : ℝ)))
      ≤ ∑ u, ∑ _v ∈ G.neighborFinset u, ((G.edgeFinset.card : ℝ) + 1) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v hv => hterm u v hv
  have hrhs : (∑ u, ∑ _v ∈ G.neighborFinset u, ((G.edgeFinset.card : ℝ) + 1))
      = 2 * (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) + 1) := by
    simp only [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
    have h2m : (∑ u, (G.degree u : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
      have := G.sum_degrees_eq_twice_card_edges
      exact_mod_cast this
    rw [← Finset.sum_mul, h2m]
  rw [← two_mul_M1, hrhs] at hbound
  linarith

/-! ### Assembly -/

/-- `C(G) ≤ (M1 - 2m) c(m,1)`. -/
theorem C_le_M1 (G : SimpleGraph V) [DecidableRel G.Adj] :
    C G ≤ (M1 G - 2 * (G.edgeFinset.card : ℝ)) * c (G.edgeFinset.card : ℝ) 1 := by
  have hinner : ∀ u : V, (∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v))
      ≤ (G.degree u : ℝ) * c (G.edgeFinset.card : ℝ) 1 := by
    intro u
    by_cases hu : G.degree u = 0
    · have hempty : G.neighborFinset u = ∅ :=
        Finset.card_eq_zero.mp (by rw [G.card_neighborFinset_eq_degree, hu])
      rw [hempty, hu]
      simp
    · have hle : ∀ v ∈ G.neighborFinset u,
          c (G.degree u) (G.degree v) ≤ c (G.edgeFinset.card : ℝ) 1 := by
        intro v hv
        have hadj : G.Adj u v := (G.mem_neighborFinset u v).mp hv
        have hdu : 1 ≤ G.degree u := by omega
        have hdv : 1 ≤ G.degree v := one_le_degree_of_adj hadj
        have hdum : G.degree u ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset u
        exact c_le_c_m_one hdu hdum hdv
      calc (∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v))
          ≤ ∑ _v ∈ G.neighborFinset u, c (G.edgeFinset.card : ℝ) 1 :=
            Finset.sum_le_sum hle
        _ = (G.degree u : ℝ) * c (G.edgeFinset.card : ℝ) 1 := by
            rw [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
  have hstep : ∀ u : V,
      ((G.degree u : ℝ) - 1) * (∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v))
        ≤ ((G.degree u : ℝ) - 1) * ((G.degree u : ℝ) * c (G.edgeFinset.card : ℝ) 1) := by
    intro u
    by_cases hu : G.degree u = 0
    · have hempty : G.neighborFinset u = ∅ :=
        Finset.card_eq_zero.mp (by rw [G.card_neighborFinset_eq_degree, hu])
      rw [hempty, hu]
      simp
    · have h1 : (0 : ℝ) ≤ (G.degree u : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast (by omega : 1 ≤ G.degree u)
        linarith
      exact mul_le_mul_of_nonneg_left (hinner u) h1
  have hsum_deg : (∑ u, (G.degree u : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    have := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast this
  calc C G = ∑ u, ((G.degree u : ℝ) - 1) *
        (∑ v ∈ G.neighborFinset u, c (G.degree u) (G.degree v)) := by
        simp only [C]
    _ ≤ ∑ u, ((G.degree u : ℝ) - 1) * ((G.degree u : ℝ) * c (G.edgeFinset.card : ℝ) 1) :=
        Finset.sum_le_sum fun u _ => hstep u
    _ = (M1 G - 2 * (G.edgeFinset.card : ℝ)) * c (G.edgeFinset.card : ℝ) 1 := by
        have hfac : (∑ u, ((G.degree u : ℝ) - 1) *
              ((G.degree u : ℝ) * c (G.edgeFinset.card : ℝ) 1))
            = (∑ u, (((G.degree u : ℝ) - 1) * (G.degree u : ℝ)))
              * c (G.edgeFinset.card : ℝ) 1 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun u _ => by ring
        have hsq : (∑ u, (((G.degree u : ℝ) - 1) * (G.degree u : ℝ)))
            = (∑ u, (G.degree u : ℝ) ^ 2) - (∑ u, (G.degree u : ℝ)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun u _ => by ring
        rw [hfac, hsq, hsum_deg]
        simp only [M1]

/-- **THEOREM (star maximisation)**: `C(G) ≤ m(m-1) c(m,1)`. -/
theorem C_le_star (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 2 ≤ G.edgeFinset.card) :
    C G ≤ (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) - 1)
            * c (G.edgeFinset.card : ℝ) 1 := by
  have hcm1 : 0 < c (G.edgeFinset.card : ℝ) 1 :=
    c_pos (by exact_mod_cast (by omega : 1 ≤ G.edgeFinset.card)) (by norm_num)
  have hM1 := M1_le G
  have h1 : M1 G - 2 * (G.edgeFinset.card : ℝ)
      ≤ (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) + 1)
        - 2 * (G.edgeFinset.card : ℝ) := by linarith
  calc C G ≤ (M1 G - 2 * (G.edgeFinset.card : ℝ)) * c (G.edgeFinset.card : ℝ) 1 := C_le_M1 G
    _ ≤ ((G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) + 1)
          - 2 * (G.edgeFinset.card : ℝ)) * c (G.edgeFinset.card : ℝ) 1 :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hcm1)
    _ = (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) - 1)
          * c (G.edgeFinset.card : ℝ) 1 := by ring

end StarTheorem
