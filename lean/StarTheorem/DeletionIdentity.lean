/-
  StarTheorem/DeletionIdentity.lean -- priority 5 of the formalisation plan:

      THEOREM (general edge-deletion identity).  For a symmetric kernel `f`,
        T_f(G) = Σ_{uv ∈ E} f(d_u,d_v),      (edge-additive degree index)
        C_f(G) = Σ_u (d_u - 1) Σ_{v ∈ N(u)} (f(d_u,d_v) - f(d_u-1,d_v)),
      one has
        Σ_{e ∈ E} T_f(G - e) = (m - 1) T_f(G) - C_f(G).

  FULLY PROVED: the proof is complete, with no unproved steps.  The Sombor index is the special
  case `f(a,b) = sqrt(a^2+b^2)`, for which `C_f` is the correction term `C` of §7.7, so
  the classical identity `Σ_e SO(G-e) = (m-1) SO(G) - C(G)` follows.

  Structure of the proof.

  PART 1 (`sum_deltaOrd`): the double counting.  With the local increment
      deltaOrd(u,v) = f(d_u,d_v)
                      + Σ_{x ∈ N(u)\{v\}} (f(d_u,d_x) - f(d_u-1,d_x))
                      + Σ_{y ∈ N(v)\{u\}} (f(d_v,d_y) - f(d_v-1,d_y))
  one has Σ_{(u,v)} deltaOrd(u,v) = 2 T_f(G) + 2 C_f(G): the re-indexing lemma
  `sum_erase_sum` turns the middle block into `Σ_u (d_u-1) Σ_{x∈N(u)} …` (each `x` is
  missed by exactly one of the `d_u` choices of `v`) and the last block is the same
  argument after swapping the two summation indices.

  PART 2 (the degree update for `SimpleGraph.deleteEdges`, absent from Mathlib):
  `Mathlib/Combinatorics/SimpleGraph/DeleteEdges.lean` provides `deleteEdges_adj` and
  `edgeFinset_deleteEdges` but no degree lemma.  Proved here: deleting `s(u,v)` lowers
  the degree at `u` and at `v` by one, removes `v` from `N(u)` and `u` from `N(v)`, and
  leaves the degree and the neighbourhood of every other vertex unchanged
  (`degree_deleteEdges_left/right/of_ne`, `neighborFinset_deleteEdges_left/right/of_ne`),
  together with the single `if`-expression version `degree_deleteEdges_ite_real`.

  PART 3 (`Tf_delete_singleton`): the local deletion formula
  T_f(G - s(u,v)) = T_f(G) - deltaOrd(u,v).  Comparing the ordered double sums over the
  two graphs and splitting the vertex sum into the blocks `u`, `v` and the rest
  (`sum_univ_split_pair`) gives three contributions
      left  : -S_u - f(d_u,d_v),   right : -S_v - f(d_v,d_u),   rest : -S_u - S_v,
  where S_u = Σ_{x ∈ N(u)\{v\}} (f(d_u,d_x) - f(d_u-1,d_x)) and S_v is the same at `v`;
  the `rest` block carries the second copy of `S_u` and `S_v` (every edge is counted from
  both of its endpoints), and this is what produces the correction term `C_f`.

  ASSEMBLY (`deletion_identity`): summing the local formula over the `2m` ordered pairs
  and dividing by two.
-/

import StarTheorem.Kernel
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge-additive index `T_f(G) = Σ_{uv∈E} f(d_u,d_v)`, written as half the
ordered sum over neighbours (each edge is counted twice, once from each endpoint). -/
noncomputable def Tf (f : ℝ → ℝ → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (1 / 2) * ∑ u, ∑ v ∈ G.neighborFinset u, f (G.degree u) (G.degree v)

/-- The correction term `C_f` attached to a symmetric kernel `f`. -/
noncomputable def Cf (f : ℝ → ℝ → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ u, ((G.degree u : ℝ) - 1) *
    ∑ v ∈ G.neighborFinset u,
      (f (G.degree u) (G.degree v) - f ((G.degree u : ℝ) - 1) (G.degree v))

/-- The local deletion increment of the ordered adjacent pair `(u,v)`. -/
noncomputable def deltaOrd (f : ℝ → ℝ → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : ℝ :=
  f (G.degree u) (G.degree v)
    + ∑ x ∈ (G.neighborFinset u).erase v,
        (f (G.degree u) (G.degree x) - f ((G.degree u : ℝ) - 1) (G.degree x))
    + ∑ y ∈ (G.neighborFinset v).erase u,
        (f (G.degree v) (G.degree y) - f ((G.degree v : ℝ) - 1) (G.degree y))

/-! ### PART 1: the double counting -/

/-- Swapping the order of a two-variable double sum over neighbours. -/
theorem neighbor_sum_swap₂ (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → V → ℝ) :
    (∑ u, ∑ v ∈ G.neighborFinset u, f u v) = ∑ v, ∑ u ∈ G.neighborFinset v, f u v := by
  simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  by_cases h : G.Adj u v
  · simp [h, (G.adj_comm u v).mp h]
  · have h' : ¬ G.Adj v u := fun hvu => h ((G.adj_comm v u).mp hvu)
    simp [h, h']

/-- **The re-indexing lemma**: summing `Σ_{x ∈ s.erase v} g x` over all `v ∈ s` counts
every `x ∈ s` exactly `#s - 1` times. -/
theorem sum_erase_sum (s : Finset V) (g : V → ℝ) :
    (∑ v ∈ s, ∑ x ∈ s.erase v, g x) = ((s.card : ℝ) - 1) * ∑ x ∈ s, g x := by
  have h : ∀ v ∈ s, (∑ x ∈ s.erase v, g x) = (∑ x ∈ s, g x) - g v := by
    intro v hv
    rw [Finset.sum_erase_eq_sub hv]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The double counting**: `Σ_{(u,v)} deltaOrd(u,v) = 2 T_f(G) + 2 C_f(G)`. -/
theorem sum_deltaOrd (f : ℝ → ℝ → ℝ) (hsym : ∀ a b, f a b = f b a)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ u, ∑ v ∈ G.neighborFinset u, deltaOrd f G u v) = 2 * Tf f G + 2 * Cf f G := by
  have hpt : ∀ u v : V, deltaOrd f G u v
      = f (G.degree u) (G.degree v)
        + (∑ x ∈ (G.neighborFinset u).erase v,
            (f (G.degree u) (G.degree x) - f ((G.degree u : ℝ) - 1) (G.degree x)))
        + (∑ y ∈ (G.neighborFinset v).erase u,
            (f (G.degree v) (G.degree y) - f ((G.degree v : ℝ) - 1) (G.degree y))) :=
    fun u v => rfl
  -- block A: the edge terms
  have hA : (∑ u, ∑ v ∈ G.neighborFinset u, f (G.degree u) (G.degree v)) = 2 * Tf f G := by
    rw [Tf]
    ring
  -- block B: the terms at `u`
  have hB : (∑ u, ∑ v ∈ G.neighborFinset u,
        ∑ x ∈ (G.neighborFinset u).erase v,
          (f (G.degree u) (G.degree x) - f ((G.degree u : ℝ) - 1) (G.degree x))) = Cf f G := by
    rw [Cf]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [sum_erase_sum, G.card_neighborFinset_eq_degree]
  -- block C: the terms at `v`, via the swap of the two summation indices
  have hC : (∑ u, ∑ v ∈ G.neighborFinset u,
        ∑ y ∈ (G.neighborFinset v).erase u,
          (f (G.degree v) (G.degree y) - f ((G.degree v : ℝ) - 1) (G.degree y))) = Cf f G := by
    rw [neighbor_sum_swap₂ G (fun u v => ∑ y ∈ (G.neighborFinset v).erase u,
        (f (G.degree v) (G.degree y) - f ((G.degree v : ℝ) - 1) (G.degree y)))]
    rw [Cf]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [sum_erase_sum, G.card_neighborFinset_eq_degree]
  -- split the sum of `deltaOrd` into the three blocks
  calc (∑ u, ∑ v ∈ G.neighborFinset u, deltaOrd f G u v)
      = ∑ u, ((∑ v ∈ G.neighborFinset u, f (G.degree u) (G.degree v))
          + (∑ v ∈ G.neighborFinset u, ∑ x ∈ (G.neighborFinset u).erase v,
              (f (G.degree u) (G.degree x) - f ((G.degree u : ℝ) - 1) (G.degree x)))
          + (∑ v ∈ G.neighborFinset u, ∑ y ∈ (G.neighborFinset v).erase u,
              (f (G.degree v) (G.degree y) - f ((G.degree v : ℝ) - 1) (G.degree y)))) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        have h1 : (∑ v ∈ G.neighborFinset u, deltaOrd f G u v)
            = ∑ v ∈ G.neighborFinset u, (f (G.degree u) (G.degree v)
                + (∑ x ∈ (G.neighborFinset u).erase v,
                    (f (G.degree u) (G.degree x) - f ((G.degree u : ℝ) - 1) (G.degree x)))
                + (∑ y ∈ (G.neighborFinset v).erase u,
                    (f (G.degree v) (G.degree y) - f ((G.degree v : ℝ) - 1) (G.degree y)))) :=
          Finset.sum_congr rfl fun v _ => hpt u v
        rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ u, ∑ v ∈ G.neighborFinset u, f (G.degree u) (G.degree v))
        + (∑ u, ∑ v ∈ G.neighborFinset u, ∑ x ∈ (G.neighborFinset u).erase v,
            (f (G.degree u) (G.degree x) - f ((G.degree u : ℝ) - 1) (G.degree x)))
        + (∑ u, ∑ v ∈ G.neighborFinset u, ∑ y ∈ (G.neighborFinset v).erase u,
            (f (G.degree v) (G.degree y) - f ((G.degree v : ℝ) - 1) (G.degree y))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = 2 * Tf f G + 2 * Cf f G := by
        rw [hA, hB, hC]
        ring



/-- Splitting an `if`-sum at a single point of a finset. -/
theorem sum_ite_eq_add (s : Finset V) (a : V) (p q : V → ℝ) :
    (∑ x ∈ s, (if x = a then p x else q x))
      = (∑ x ∈ s, q x) + (if a ∈ s then (p a - q a) else 0) := by
  have h1 : ∀ x ∈ s, (if x = a then p x else q x)
      = q x + (if x = a then (p x - q x) else 0) := by
    intro x _
    by_cases hx : x = a <;> simp [hx]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  congr 1
  simpa using Finset.sum_eq_ite (s := s) (f := fun x => if x = a then (p x - q x) else 0) a
    (fun b _ hb => by simp [hb])

/-- The same, splitting off two distinct points. -/
theorem sum_ite_eq_add_two (s : Finset V) (a b : V) (hab : a ≠ b) (pa pb : ℝ) (q : V → ℝ) :
    (∑ x ∈ s, (if x = a then pa else if x = b then pb else q x))
      = (∑ x ∈ s, q x) + (if a ∈ s then (pa - q a) else 0)
        + (if b ∈ s then (pb - q b) else 0) := by
  rw [sum_ite_eq_add s a (fun _ => pa) (fun x => if x = b then pb else q x), if_neg hab,
    sum_ite_eq_add s b (fun _ => pb) q]
  ring

/-- The neighbour set of the graph with `s(u,v)` deleted. -/
theorem neighborFinset_deleteEdges {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V} :
    (G.deleteEdges {s(u, v)}).neighborFinset w
      = (G.neighborFinset w).filter (fun x => s(w, x) ≠ s(u, v)) := by
  ext x
  simp [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]

theorem neighborFinset_deleteEdges_left {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).neighborFinset u = (G.neighborFinset u).erase v := by
  rw [neighborFinset_deleteEdges, Finset.filter_congr (s := G.neighborFinset u)
      (p := fun x => s(u, x) ≠ s(u, v)) (q := fun x => x ≠ v) (fun x _ => ?_),
    Finset.filter_ne']
  constructor
  · intro hne hxv
    exact hne (by rw [hxv])
  · intro hne heq
    rcases Sym2.eq_iff.mp heq with ⟨-, rfl⟩ | ⟨huv, -⟩
    · exact hne rfl
    · exact G.ne_of_adj h huv

theorem neighborFinset_deleteEdges_right {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).neighborFinset v = (G.neighborFinset v).erase u := by
  rw [show s(u, v) = s(v, u) from Sym2.eq_swap]
  exact neighborFinset_deleteEdges_left (G := G) h.symm

theorem neighborFinset_deleteEdges_of_ne {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V} (hu : w ≠ u) (hv : w ≠ v) :
    (G.deleteEdges {s(u, v)}).neighborFinset w = G.neighborFinset w := by
  rw [neighborFinset_deleteEdges, Finset.filter_true_of_mem]
  intro x _
  intro heq
  rcases Sym2.eq_iff.mp heq with ⟨hw, -⟩ | ⟨hw, -⟩
  · exact hu hw
  · exact hv hw

theorem degree_deleteEdges_left {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).degree u = G.degree u - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_deleteEdges_left h,
    Finset.card_erase_of_mem ((G.mem_neighborFinset u v).mpr h),
    SimpleGraph.card_neighborFinset_eq_degree]

theorem degree_deleteEdges_right {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).degree v = G.degree v - 1 := by
  rw [show s(u, v) = s(v, u) from Sym2.eq_swap]
  exact degree_deleteEdges_left (G := G) h.symm

theorem degree_deleteEdges_of_ne {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V}
    (hu : w ≠ u) (hv : w ≠ v) :
    (G.deleteEdges {s(u, v)}).degree w = G.degree w := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_deleteEdges_of_ne hu hv,
    SimpleGraph.card_neighborFinset_eq_degree]

/-- The degree of the deleted graph, as a single `if`-expression. -/
theorem degree_deleteEdges_ite {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) (x : V) :
    (G.deleteEdges {s(u, v)}).degree x
      = if x = u then G.degree u - 1 else if x = v then G.degree v - 1 else G.degree x := by
  by_cases h1 : x = u
  · rw [if_pos h1, h1]; exact degree_deleteEdges_left h
  · rw [if_neg h1]
    by_cases h2 : x = v
    · rw [if_pos h2, h2]; exact degree_deleteEdges_right h
    · rw [if_neg h2]; exact degree_deleteEdges_of_ne h1 h2

/-- The same, cast to `ℝ`, in the shape needed for the comparison. -/
theorem degree_deleteEdges_ite_real {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) (x : V) :
    (((G.deleteEdges {s(u, v)}).degree x : ℕ) : ℝ)
      = if x = u then (G.degree u : ℝ) - 1
        else if x = v then (G.degree v : ℝ) - 1 else (G.degree x : ℝ) := by
  by_cases h1 : x = u
  · rw [if_pos h1, h1, degree_deleteEdges_left h]
    exact (Nat.cast_sub (one_le_degree_of_adj h.symm)).trans (by norm_num)
  · rw [if_neg h1]
    by_cases h2 : x = v
    · rw [if_pos h2, h2, degree_deleteEdges_right h]
      exact (Nat.cast_sub (one_le_degree_of_adj h)).trans (by norm_num)
    · rw [if_neg h2, degree_deleteEdges_of_ne h1 h2]


/-! ### Block computations -/

/-- Splitting a sum over all vertices at two distinct vertices. -/
theorem sum_univ_split_pair (D : V → ℝ) {u v : V} (hne : v ≠ u) :
    (∑ w, D w) = D u + (D v + ∑ w ∈ (Finset.univ.erase u).erase v, D w) := by
  rw [← Finset.add_sum_erase Finset.univ D (a := u) (Finset.mem_univ u),
    ← Finset.add_sum_erase (Finset.univ.erase u) D (a := v)
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ v⟩)]

/-- The ordered neighbour sum at `u` after deleting the edge. -/
theorem sum_neighborFinset_deleteEdges_left (f : ℝ → ℝ → ℝ) {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (h : G.Adj u v) :
    (∑ x ∈ (G.deleteEdges {s(u, v)}).neighborFinset u,
        f ((G.deleteEdges {s(u, v)}).degree u) ((G.deleteEdges {s(u, v)}).degree x))
      = ∑ x ∈ (G.neighborFinset u).erase v, f ((G.degree u : ℝ) - 1) (G.degree x) := by
  have hcast : ((G.degree u - 1 : ℕ) : ℝ) = (G.degree u : ℝ) - 1 :=
    (Nat.cast_sub (one_le_degree_of_adj h.symm)).trans (by norm_num)
  rw [neighborFinset_deleteEdges_left h, degree_deleteEdges_left h, hcast]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hxv, hxN⟩ := Finset.mem_erase.mp hx
  rw [degree_deleteEdges_of_ne (G := G) ((G.ne_of_adj ((G.mem_neighborFinset u x).mp hxN)).symm) hxv]

/-- The ordered neighbour sum at `v` after deleting the edge. -/
theorem sum_neighborFinset_deleteEdges_right (f : ℝ → ℝ → ℝ) {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (h : G.Adj u v) :
    (∑ y ∈ (G.deleteEdges {s(u, v)}).neighborFinset v,
        f ((G.deleteEdges {s(u, v)}).degree v) ((G.deleteEdges {s(u, v)}).degree y))
      = ∑ y ∈ (G.neighborFinset v).erase u, f ((G.degree v : ℝ) - 1) (G.degree y) := by
  have hcast : ((G.degree v - 1 : ℕ) : ℝ) = (G.degree v : ℝ) - 1 :=
    (Nat.cast_sub (one_le_degree_of_adj h)).trans (by norm_num)
  rw [neighborFinset_deleteEdges_right h, degree_deleteEdges_right h, hcast]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨hyu, hyN⟩ := Finset.mem_erase.mp hy
  rw [degree_deleteEdges_of_ne (G := G) hyu ((G.ne_of_adj ((G.mem_neighborFinset v y).mp hyN)).symm)]

/-- The ordered neighbour sum at `u` before the deletion, split at `v`. -/
theorem sum_neighborFinset_split_left (f : ℝ → ℝ → ℝ) {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (h : G.Adj u v) :
    (∑ x ∈ G.neighborFinset u, f (G.degree u) (G.degree x))
      = (∑ x ∈ (G.neighborFinset u).erase v, f (G.degree u) (G.degree x))
        + f (G.degree u) (G.degree v) := by
  rw [← Finset.sum_erase_add (G.neighborFinset u) (fun x => f (G.degree u) (G.degree x))
    (a := v) ((G.mem_neighborFinset u v).mpr h)]

/-- The ordered neighbour sum at `v` before the deletion, split at `u`. -/
theorem sum_neighborFinset_split_right (f : ℝ → ℝ → ℝ) {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (h : G.Adj u v) :
    (∑ y ∈ G.neighborFinset v, f (G.degree v) (G.degree y))
      = (∑ y ∈ (G.neighborFinset v).erase u, f (G.degree v) (G.degree y))
        + f (G.degree v) (G.degree u) := by
  rw [← Finset.sum_erase_add (G.neighborFinset v) (fun y => f (G.degree v) (G.degree y))
    (a := u) ((G.mem_neighborFinset v u).mpr h.symm)]

/-- The ordered neighbour sum at a vertex `w ∉ {u,v}`, where only the degrees change. -/
theorem sum_neighborFinset_deleteEdges_of_ne (f : ℝ → ℝ → ℝ) {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V}
    (h : G.Adj u v) (hu : w ≠ u) (hv : w ≠ v) :
    (∑ x ∈ (G.deleteEdges {s(u, v)}).neighborFinset w,
        f ((G.deleteEdges {s(u, v)}).degree w) ((G.deleteEdges {s(u, v)}).degree x))
      = (∑ x ∈ G.neighborFinset w, f (G.degree w) (G.degree x))
        + (if w ∈ G.neighborFinset u then
            f (G.degree w) ((G.degree u : ℝ) - 1) - f (G.degree w) (G.degree u) else 0)
        + (if w ∈ G.neighborFinset v then
            f (G.degree w) ((G.degree v : ℝ) - 1) - f (G.degree w) (G.degree v) else 0) := by
  have hiff_u : (u ∈ G.neighborFinset w) ↔ (w ∈ G.neighborFinset u) := by
    simp only [SimpleGraph.mem_neighborFinset]
    exact (G.adj_comm u w).symm
  have hiff_v : (v ∈ G.neighborFinset w) ↔ (w ∈ G.neighborFinset v) := by
    simp only [SimpleGraph.mem_neighborFinset]
    exact (G.adj_comm v w).symm
  rw [neighborFinset_deleteEdges_of_ne (G := G) hu hv, degree_deleteEdges_of_ne (G := G) hu hv]
  simp only [degree_deleteEdges_ite_real (G := G) h]
  rw [show (∑ x ∈ G.neighborFinset w,
        f (G.degree w) (if x = u then (G.degree u : ℝ) - 1
          else if x = v then (G.degree v : ℝ) - 1 else (G.degree x : ℝ)))
      = ∑ x ∈ G.neighborFinset w, (if x = u then f (G.degree w) ((G.degree u : ℝ) - 1)
          else if x = v then f (G.degree w) ((G.degree v : ℝ) - 1)
          else f (G.degree w) (G.degree x)) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = u
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx]
      by_cases hx2 : x = v
      · rw [if_pos hx2, if_pos hx2]
      · rw [if_neg hx2, if_neg hx2]]
  rw [sum_ite_eq_add_two (G.neighborFinset w) u v (G.ne_of_adj h)
    (f (G.degree w) ((G.degree u : ℝ) - 1)) (f (G.degree w) ((G.degree v : ℝ) - 1))
    (fun x => f (G.degree w) (G.degree x))]
  simp only [hiff_u, hiff_v]

/-- Block `u`: the change of the ordered neighbour sum at `u`. -/
theorem deltaOrd_block_left (f : ℝ → ℝ → ℝ) {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (h : G.Adj u v) :
    (∑ x ∈ (G.deleteEdges {s(u, v)}).neighborFinset u,
        f ((G.deleteEdges {s(u, v)}).degree u) ((G.deleteEdges {s(u, v)}).degree x))
      - (∑ x ∈ G.neighborFinset u, f (G.degree u) (G.degree x))
      = - (∑ x ∈ (G.neighborFinset u).erase v,
            (f (G.degree u) (G.degree x) - f ((G.degree u : ℝ) - 1) (G.degree x)))
        - f (G.degree u) (G.degree v) := by
  rw [sum_neighborFinset_deleteEdges_left f h, sum_neighborFinset_split_left f h, Finset.sum_sub_distrib]
  ring

/-- Block `v`: the change of the ordered neighbour sum at `v`. -/
theorem deltaOrd_block_right (f : ℝ → ℝ → ℝ) {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (h : G.Adj u v) :
    (∑ y ∈ (G.deleteEdges {s(u, v)}).neighborFinset v,
        f ((G.deleteEdges {s(u, v)}).degree v) ((G.deleteEdges {s(u, v)}).degree y))
      - (∑ y ∈ G.neighborFinset v, f (G.degree v) (G.degree y))
      = - (∑ y ∈ (G.neighborFinset v).erase u,
            (f (G.degree v) (G.degree y) - f ((G.degree v : ℝ) - 1) (G.degree y)))
        - f (G.degree v) (G.degree u) := by
  rw [sum_neighborFinset_deleteEdges_right f h, sum_neighborFinset_split_right f h, Finset.sum_sub_distrib]
  ring

/-- Block `rest`: the change at the vertices other than `u` and `v`. -/
theorem deltaOrd_block_rest (f : ℝ → ℝ → ℝ) (hsym : ∀ a b, f a b = f b a)
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    (∑ w ∈ (Finset.univ.erase u).erase v,
      ((∑ x ∈ (G.deleteEdges {s(u, v)}).neighborFinset w,
          f ((G.deleteEdges {s(u, v)}).degree w) ((G.deleteEdges {s(u, v)}).degree x))
        - (∑ x ∈ G.neighborFinset w, f (G.degree w) (G.degree x))))
      = - (∑ x ∈ (G.neighborFinset u).erase v,
            (f (G.degree u) (G.degree x) - f ((G.degree u : ℝ) - 1) (G.degree x)))
        - (∑ y ∈ (G.neighborFinset v).erase u,
            (f (G.degree v) (G.degree y) - f ((G.degree v : ℝ) - 1) (G.degree y))) := by
  have hpt : ∀ w ∈ (Finset.univ.erase u).erase v,
      ((∑ x ∈ (G.deleteEdges {s(u, v)}).neighborFinset w,
          f ((G.deleteEdges {s(u, v)}).degree w) ((G.deleteEdges {s(u, v)}).degree x))
        - (∑ x ∈ G.neighborFinset w, f (G.degree w) (G.degree x)))
      = (if w ∈ G.neighborFinset u then
            f (G.degree w) ((G.degree u : ℝ) - 1) - f (G.degree w) (G.degree u) else 0)
        + (if w ∈ G.neighborFinset v then
            f (G.degree w) ((G.degree v : ℝ) - 1) - f (G.degree w) (G.degree v) else 0) := by
    intro w hw
    obtain ⟨hwv, hw'⟩ := Finset.mem_erase.mp hw
    obtain ⟨hwu, -⟩ := Finset.mem_erase.mp hw'
    rw [sum_neighborFinset_deleteEdges_of_ne f h hwu hwv]
    ring
  have hset_u : ((Finset.univ.erase u).erase v).filter (fun w => w ∈ G.neighborFinset u)
      = (G.neighborFinset u).erase v := by
    refine Finset.ext fun w => ?_
    constructor
    · intro hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      obtain ⟨hwv, hwu'⟩ := Finset.mem_erase.mp hw1
      exact Finset.mem_erase.mpr ⟨hwv, hw2⟩
    · intro hw
      obtain ⟨hwv, hw2⟩ := Finset.mem_erase.mp hw
      refine Finset.mem_filter.mpr ⟨?_, hw2⟩
      exact Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr
        ⟨(G.ne_of_adj ((G.mem_neighborFinset u w).mp hw2)).symm, Finset.mem_univ w⟩⟩
  have hset_v : ((Finset.univ.erase u).erase v).filter (fun w => w ∈ G.neighborFinset v)
      = (G.neighborFinset v).erase u := by
    refine Finset.ext fun w => ?_
    constructor
    · intro hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      obtain ⟨-, hwu'⟩ := Finset.mem_erase.mp hw1
      obtain ⟨hwu, -⟩ := Finset.mem_erase.mp hwu'
      exact Finset.mem_erase.mpr ⟨hwu, hw2⟩
    · intro hw
      obtain ⟨hwu, hw2⟩ := Finset.mem_erase.mp hw
      refine Finset.mem_filter.mpr ⟨?_, hw2⟩
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset v w).mp hw2)).symm,
        Finset.mem_erase.mpr ⟨hwu, Finset.mem_univ w⟩⟩
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_filter, hset_u, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsym (G.degree x) ((G.degree u : ℝ) - 1), hsym (G.degree x) (G.degree u)]
    ring
  · rw [← Finset.sum_filter, hset_v, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hsym (G.degree y) ((G.degree v : ℝ) - 1), hsym (G.degree y) (G.degree v)]
    ring

/-! ### The local formula and the general edge-deletion identity -/

/-- **The ordered double sum over the graph with one edge deleted.** -/
theorem ordered_sum_deleteEdges (f : ℝ → ℝ → ℝ) (hsym : ∀ a b, f a b = f b a)
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    (∑ w, ∑ x ∈ (G.deleteEdges {s(u, v)}).neighborFinset w,
        f ((G.deleteEdges {s(u, v)}).degree w) ((G.deleteEdges {s(u, v)}).degree x))
      = (∑ w, ∑ x ∈ G.neighborFinset w, f (G.degree w) (G.degree x))
        - 2 * deltaOrd f G u v := by
  have hkey : (∑ w, ∑ x ∈ (G.deleteEdges {s(u, v)}).neighborFinset w,
        f ((G.deleteEdges {s(u, v)}).degree w) ((G.deleteEdges {s(u, v)}).degree x))
      - (∑ w, ∑ x ∈ G.neighborFinset w, f (G.degree w) (G.degree x))
      = - 2 * deltaOrd f G u v := by
    have hsplit := sum_univ_split_pair (u := u) (v := v) (hne := (G.ne_of_adj h).symm)
      (D := fun w => (∑ x ∈ (G.deleteEdges {s(u, v)}).neighborFinset w,
          f ((G.deleteEdges {s(u, v)}).degree w) ((G.deleteEdges {s(u, v)}).degree x))
        - (∑ x ∈ G.neighborFinset w, f (G.degree w) (G.degree x)))
    rw [← Finset.sum_sub_distrib, hsplit, deltaOrd_block_left f h, deltaOrd_block_right f h, deltaOrd_block_rest f hsym h,
      deltaOrd, hsym (G.degree v) (G.degree u)]
    ring
  linarith

/-- **The local deletion formula**: deleting `s(u,v)` lowers the edge-additive
index by exactly `deltaOrd`. -/
theorem Tf_delete_singleton (f : ℝ → ℝ → ℝ) (hsym : ∀ a b, f a b = f b a)
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    Tf f (G.deleteEdges {s(u, v)}) = Tf f G - deltaOrd f G u v := by
  have hkey := ordered_sum_deleteEdges f hsym h
  rw [Tf, Tf, hkey]
  ring

/-- **Assembly step**: the general edge-deletion identity follows from `sum_deltaOrd`
(PART 1) once the local formula `T_f(G - s(u,v)) = T_f(G) - deltaOrd(u,v)` is available
for every edge (`Tf_delete_singleton`, PART 3). -/
theorem deletion_identity_of_local (f : ℝ → ℝ → ℝ) (hsym : ∀ a b, f a b = f b a)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : ∀ u v : V, G.Adj u v →
      Tf f (G.deleteEdges {s(u, v)}) = Tf f G - deltaOrd f G u v) :
    (1 / 2 : ℝ) * (∑ u, ∑ v ∈ G.neighborFinset u, Tf f (G.deleteEdges {s(u, v)}))
      = ((G.edgeFinset.card : ℝ) - 1) * Tf f G - Cf f G := by
  have h1 : ∀ u : V, ∀ v ∈ G.neighborFinset u,
      Tf f (G.deleteEdges {s(u, v)}) = Tf f G - deltaOrd f G u v := by
    intro u v hv
    exact hcard u v ((G.mem_neighborFinset u v).mp hv)
  have hsum_deg : (∑ u, (G.degree u : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    have := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast this
  have hinner : (∑ u, ∑ _v ∈ G.neighborFinset u, Tf f G)
      = 2 * (G.edgeFinset.card : ℝ) * Tf f G := by
    simp only [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
    rw [← Finset.sum_mul, hsum_deg]
  calc (1 / 2 : ℝ) * (∑ u, ∑ v ∈ G.neighborFinset u, Tf f (G.deleteEdges {s(u, v)}))
      = (1 / 2 : ℝ) * (∑ u, ∑ v ∈ G.neighborFinset u, (Tf f G - deltaOrd f G u v)) := by
        congr 1
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v hv => h1 u v hv
    _ = (1 / 2 : ℝ) * ((∑ u, ∑ _v ∈ G.neighborFinset u, Tf f G)
          - ∑ u, ∑ v ∈ G.neighborFinset u, deltaOrd f G u v) := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ =>
          Finset.sum_sub_distrib (f := fun _ : V => Tf f G)
            (g := fun v => deltaOrd f G u v)
    _ = ((G.edgeFinset.card : ℝ) - 1) * Tf f G - Cf f G := by
        rw [hinner, sum_deltaOrd f hsym G]
        ring

/-- **THEOREM (general edge-deletion identity).** For a symmetric kernel `f`,
`Σ_{e ∈ E} T_f(G - e) = (m - 1) T_f(G) - C_f(G)`, where the sum runs over the
edges (written here in ordered-pair form). -/
theorem deletion_identity (f : ℝ → ℝ → ℝ) (hsym : ∀ a b, f a b = f b a)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (1 / 2 : ℝ) * (∑ u, ∑ v ∈ G.neighborFinset u, Tf f (G.deleteEdges {s(u, v)}))
      = ((G.edgeFinset.card : ℝ) - 1) * Tf f G - Cf f G :=
  deletion_identity_of_local f hsym G fun _ _ huv => Tf_delete_singleton f hsym huv

end StarTheorem
