/-
  StarTheorem/StarEquality.lean -- priority 1, second half:
  the EQUALITY CHARACTERISATION of the star-maximisation theorem.

      C(G) = m(m-1) c(m,1)   ↔   G is a star plus isolated vertices,

  the right-hand side being formalised as
      ∃ u, G.degree u = m ∧ ∀ v ≠ u, G.degree v ≤ 1.

  Human proof (report.md §8.3):
  1. `C ≤ (M1-2m)k ≤ m(m-1)k` with `k = c(m,1) > 0`.  Equality in the outer chain
     forces `M1 = m²+m` and `C = (M1-2m)k`.
  2. The defect
        D_w := (d_w - 1) · ( d_w·k - Σ_{x ∈ N(w)} c(d_w,d_x) )   ≥ 0
     satisfies Σ_w D_w = (M1-2m)k - C = 0, hence every D_w = 0.
  3. For a vertex u with d_u ≥ 2 this gives Σ_{x ∈ N(u)} c(d_u,d_x) = d_u·k, and
     since every summand is ≤ k, every summand equals k; by the strict form
     `c_eq_c_m_one_iff`, d_u = m and every neighbour of u has degree 1.
  4. A vertex with d_u ≥ 2 exists (otherwise C = 0 < m(m-1)k).  Then u is incident
     with m = |E| edges, so *every* edge is incident with u; hence any v ≠ u has all
     its neighbours equal to u, i.e. d_v ≤ 1.
  5. Conversely, if d_u = m and d_v ≤ 1 for v ≠ u, then each neighbour of u has
     degree exactly 1 and C = (m-1)·m·c(m,1).
-/

import StarTheorem.StarMax
import StarTheorem.ZeroIff

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### the defect of the intermediate bound -/

/-- Each defect summand is nonnegative. -/
theorem defC_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) :
    0 ≤ ((G.degree w : ℝ) - 1) *
      ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1
        - ∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x)) := by
  rcases Nat.eq_zero_or_pos (G.degree w) with h0 | hpos
  · rw [neighborFinset_eq_empty_of_degree_eq_zero h0, h0]
    simp
  · have h1 : (0 : ℝ) ≤ (G.degree w : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (G.degree w : ℝ) := by exact_mod_cast hpos
      linarith
    have h2 : (0 : ℝ) ≤ (G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1
        - ∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x) := by
      have hle : ∀ x ∈ G.neighborFinset w,
          c (G.degree w) (G.degree x) ≤ c (G.edgeFinset.card : ℝ) 1 := by
        intro x hx
        have hadj : G.Adj w x := (G.mem_neighborFinset w x).mp hx
        exact c_le_c_m_one hpos (G.degree_le_card_edgeFinset w) (one_le_degree_of_adj hadj)
      have hsum : (∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x))
          ≤ (G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1 := by
        calc (∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x))
            ≤ ∑ _x ∈ G.neighborFinset w, c (G.edgeFinset.card : ℝ) 1 :=
              Finset.sum_le_sum hle
          _ = (G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1 := by
              rw [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
      linarith
    exact mul_nonneg h1 h2

/-- The total defect equals `(M1 - 2m)·c(m,1) - C`. -/
theorem defC_sum (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ w, ((G.degree w : ℝ) - 1) *
      ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1
        - ∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x)))
      = (M1 G - 2 * (G.edgeFinset.card : ℝ)) * c (G.edgeFinset.card : ℝ) 1 - C G := by
  have hpoint : ∀ w : V, ((G.degree w : ℝ) - 1) *
      ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1
        - ∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x))
      = ((G.degree w : ℝ) - 1) * ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1)
        - ((G.degree w : ℝ) - 1)
            * (∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x)) := by
    intro w
    ring
  have hsum_deg : (∑ u, (G.degree u : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    have := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast this
  rw [Finset.sum_congr rfl fun w _ => hpoint w, Finset.sum_sub_distrib]
  have hfirst : (∑ w, ((G.degree w : ℝ) - 1) * ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1))
      = (M1 G - 2 * (G.edgeFinset.card : ℝ)) * c (G.edgeFinset.card : ℝ) 1 := by
    have hfac : (∑ w, ((G.degree w : ℝ) - 1) * ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1))
        = (∑ w, (((G.degree w : ℝ) - 1) * (G.degree w : ℝ)))
          * c (G.edgeFinset.card : ℝ) 1 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ => by ring
    have hsq : (∑ w, (((G.degree w : ℝ) - 1) * (G.degree w : ℝ)))
        = (∑ w, (G.degree w : ℝ) ^ 2) - (∑ w, (G.degree w : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [hfac, hsq, hsum_deg]
    simp only [M1]
  have hsecond : (∑ w, ((G.degree w : ℝ) - 1)
      * (∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x))) = C G := by
    simp only [C]
  rw [hfirst, hsecond]

/-! ### (E1) a vertex of degree ≥ 2 forces `c(d_u,d_v) = c(m,1)` on its edges -/

theorem c_eq_of_defect_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdef : ∀ w : V, ((G.degree w : ℝ) - 1) *
      ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1
        - ∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x)) = 0)
    {u : V} (hu : 2 ≤ G.degree u) {v : V} (hv : v ∈ G.neighborFinset u) :
    c (G.degree u : ℝ) (G.degree v : ℝ) = c (G.edgeFinset.card : ℝ) 1 := by
  have hdu : 1 ≤ G.degree u := by omega
  have hfac : (0 : ℝ) < (G.degree u : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast hu
    linarith
  have hzero : (G.degree u : ℝ) * c (G.edgeFinset.card : ℝ) 1
      - ∑ x ∈ G.neighborFinset u, c (G.degree u) (G.degree x) = 0 :=
    (mul_eq_zero.mp (hdef u)).resolve_left (ne_of_gt hfac)
  have hnn : ∀ x ∈ G.neighborFinset u,
      (0 : ℝ) ≤ c (G.edgeFinset.card : ℝ) 1 - c (G.degree u) (G.degree x) := by
    intro x hx
    have hadj : G.Adj u x := (G.mem_neighborFinset u x).mp hx
    have := c_le_c_m_one hdu (G.degree_le_card_edgeFinset u) (one_le_degree_of_adj hadj)
    linarith
  have hsum0 : (∑ x ∈ G.neighborFinset u,
      (c (G.edgeFinset.card : ℝ) 1 - c (G.degree u) (G.degree x))) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
    linarith
  by_contra hne
  have hne0 : c (G.edgeFinset.card : ℝ) 1 - c (G.degree u) (G.degree v) ≠ 0 := by
    intro hzero'
    exact hne (sub_eq_zero.mp hzero').symm
  have hpos : 0 < c (G.edgeFinset.card : ℝ) 1 - c (G.degree u) (G.degree v) :=
    lt_of_le_of_ne (hnn v hv) (Ne.symm hne0)
  have := Finset.sum_pos' (fun x hx => hnn x hx) ⟨v, hv, hpos⟩
  linarith

/-! ### the equality characterisation -/

/-- **Equality case of the star bound**: `C(G) = m(m-1)c(m,1)` holds exactly for the
star `K_{1,m}` plus isolated vertices, expressed as: there is a vertex of degree `m`
and every other vertex has degree at most 1. -/
theorem C_eq_star_iff_aux (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ)
    (hmdef : m = G.edgeFinset.card) (hm : 2 ≤ m) :
    C G = (m : ℝ) * ((m : ℝ) - 1) * c (G.edgeFinset.card : ℝ) 1
      ↔ ∃ u : V, G.degree u = G.edgeFinset.card ∧ ∀ v, v ≠ u → G.degree v ≤ 1 := by
  subst hmdef
  have hm2 : (2 : ℝ) ≤ (G.edgeFinset.card : ℝ) := by exact_mod_cast hm
  have hk : 0 < c (G.edgeFinset.card : ℝ) 1 := c_pos (by linarith) (by norm_num)
  constructor
  · intro h
    -- step 1: M1 = m²+m and C = (M1-2m)k
    have hM1_le := M1_le G
    have hC_le := C_le_M1 G
    have hM1_eq : M1 G = (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) + 1) := by
      have h1 : ((G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) - 1)) * c (G.edgeFinset.card : ℝ) 1
          ≤ (M1 G - 2 * (G.edgeFinset.card : ℝ)) * c (G.edgeFinset.card : ℝ) 1 := by
        rw [← h]
        exact hC_le
      have h2 : (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) - 1)
          ≤ M1 G - 2 * (G.edgeFinset.card : ℝ) :=
        le_of_mul_le_mul_right h1 hk
      nlinarith
    have hC_eq : C G = (M1 G - 2 * (G.edgeFinset.card : ℝ)) * c (G.edgeFinset.card : ℝ) 1 := by
      rw [hM1_eq, h]
      ring
    -- step 2: every defect vanishes
    have hdef : ∀ w : V, ((G.degree w : ℝ) - 1) *
        ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1
          - ∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x)) = 0 := by
      intro w
      have htotal : (∑ w, ((G.degree w : ℝ) - 1) *
          ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1
            - ∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x))) = 0 := by
        rw [defC_sum, hC_eq]
        ring
      by_contra hne
      have hpos : 0 < ∑ w, ((G.degree w : ℝ) - 1) *
          ((G.degree w : ℝ) * c (G.edgeFinset.card : ℝ) 1
            - ∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x)) := by
        refine Finset.sum_pos' (fun w _ => ?_) ⟨w, Finset.mem_univ w, ?_⟩
        · exact defC_nonneg G w
        · exact lt_of_le_of_ne (defC_nonneg G w) (Ne.symm hne)
      linarith
    -- step 3: some vertex has degree ≥ 2
    have hex : ∃ u : V, 2 ≤ G.degree u := by
      by_contra hcon
      push_neg at hcon
      have hall : ∀ u : V, G.degree u ≤ 1 := fun u => by have := hcon u; omega
      have hC0 : C G = 0 := (C_eq_zero_iff G).mpr hall
      have hpos : 0 < (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) - 1)
          * c (G.edgeFinset.card : ℝ) 1 := by
        have h1 : (0 : ℝ) < (G.edgeFinset.card : ℝ) := by linarith
        have h2 : (0 : ℝ) < (G.edgeFinset.card : ℝ) - 1 := by linarith
        positivity
      rw [hC0] at h
      linarith
    obtain ⟨u, hu⟩ := hex
    -- step 4: d_u = m, and u is incident with every edge
    have hdu : G.degree u = G.edgeFinset.card := by
      obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj u).mp (by omega : 0 < G.degree u)
      have hmem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hv
      have hc := c_eq_of_defect_zero G hdef hu hmem
      exact ((c_eq_c_m_one_iff (a := G.degree u) (b := G.degree v) (m := G.edgeFinset.card)
        (by omega) (G.degree_le_card_edgeFinset u) (one_le_degree_of_adj hv)).mp hc).1
    refine ⟨u, hdu, ?_⟩
    have hinc : G.incidenceFinset u = G.edgeFinset := by
      refine Finset.eq_of_subset_of_card_le (G.incidenceFinset_subset u) ?_
      rw [G.card_incidenceFinset_eq_degree, hdu]
    intro v hvne
    have hsub : G.neighborFinset v ⊆ {u} := by
      intro w hw
      have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
      have he : s(v, w) ∈ G.edgeFinset := (G.mem_edgeFinset).mpr ((G.mem_edgeSet).mpr hadj)
      rw [← hinc] at he
      have huw : u ∈ s(v, w) := ((mem_incidenceFinset_iff G u _).mp he).2
      rcases Sym2.mem_iff'.mp huw with h' | h'
      · exact absurd h'.symm hvne
      · simp [h']
    have hcard : (G.neighborFinset v).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' : a = u := by simpa using hsub ha
      have hb' : b = u := by simpa using hsub hb
      rw [ha', hb']
    simpa using hcard
  · rintro ⟨u, hdu, hv⟩
    have hneigh : ∀ x ∈ G.neighborFinset u, G.degree x = 1 := by
      intro x hx
      have hxu : x ≠ u := by
        intro hxu
        rw [hxu] at hx
        exact G.irrefl ((G.mem_neighborFinset u u).mp hx)
      have h1 : G.degree x ≤ 1 := hv x hxu
      have h2 : 1 ≤ G.degree x := one_le_degree_of_adj ((G.mem_neighborFinset u x).mp hx)
      omega
    have hinner : (∑ x ∈ G.neighborFinset u, c (G.degree u) (G.degree x))
        = (G.degree u : ℝ) * c (G.edgeFinset.card : ℝ) 1 := by
      have hconst : ∀ x ∈ G.neighborFinset u,
          c (G.degree u) (G.degree x) = c (G.edgeFinset.card : ℝ) 1 := by
        intro x hx
        rw [hdu, hneigh x hx]
        norm_num
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, G.card_neighborFinset_eq_degree,
        hdu, nsmul_eq_mul]
    have hzero : ∀ w : V, w ≠ u → ((G.degree w : ℝ) - 1) *
        (∑ x ∈ G.neighborFinset w, c (G.degree w) (G.degree x)) = 0 := by
      intro w hw
      rcases Nat.eq_zero_or_pos (G.degree w) with h0 | hpos
      · rw [neighborFinset_eq_empty_of_degree_eq_zero h0, h0]
        simp
      · have h1 : G.degree w = 1 := by have := hv w hw; omega
        rw [h1]
        simp
    have hsingle : C G = ((G.degree u : ℝ) - 1) *
        (∑ x ∈ G.neighborFinset u, c (G.degree u) (G.degree x)) := by
      rw [C]
      refine Finset.sum_eq_single u (fun w _ hw => hzero w hw) ?_
      intro hnotin
      exact absurd (Finset.mem_univ u) hnotin
    rw [hsingle, hinner, hdu]
    ring


/-- **Equality case of the star bound**: `C(G) = m(m-1)c(m,1)` holds exactly for the
star `K_{1,m}` plus isolated vertices, formalised as: there is a vertex of degree `m`
and every other vertex has degree at most 1. -/
theorem C_eq_star_iff (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 2 ≤ G.edgeFinset.card) :
    C G = (G.edgeFinset.card : ℝ) * ((G.edgeFinset.card : ℝ) - 1)
        * c (G.edgeFinset.card : ℝ) 1
      ↔ ∃ u : V, G.degree u = G.edgeFinset.card ∧ ∀ v, v ≠ u → G.degree v ≤ 1 :=
  C_eq_star_iff_aux G G.edgeFinset.card rfl hm

end StarTheorem
