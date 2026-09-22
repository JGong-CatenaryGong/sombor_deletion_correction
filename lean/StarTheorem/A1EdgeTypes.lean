/-
  StarTheorem/A1EdgeTypes.lean -- exploration A1: the edge-type deletion identity.

  THEOREM (edge-type deletion identity).  With `edgeTypeCount G x y = N_xy(G)`
  the number of ORDERED adjacent pairs (u,v) with (d_u, d_v) = (x, y):

      sum_{e in E} N_xy(G - e) = (m - x - y + 1) * N_xy + x * N_{x+1,y} + y * N_{x,y+1}

  stated here in ordered-pair form (sum over u, v in N(u), halved), mirroring
  `deletion_identity`.

  The proof instantiates the already-formalised general deletion identity with
  the symmetric indicator kernel f_xy(a,b) = 1[{a,b} = {x,y}] and computes
  T_f and C_f exactly:

      x ≠ y:  T_f = N_xy,            C_f = (x+y-2) N_xy - x N_{x+1,y} - y N_{x,y+1}
      x = y:  T_f = N_xx / 2,        C_f = (x-1) N_xx   - x N_{x+1,x}

  Substituting into `sum_e T_f(G-e) = (m-1) T_f - C_f` and simplifying gives the
  identity (this is the "f = 1_(x,y) component" of the general identity, made
  explicit in the edge-type counting interpretation).

  Consequence (informal; see explorations/A1_proof.md): back-substitution in
  decreasing x+y recovers every N_xy from the edge deck whenever 2*Delta <= m,
  so on that class the deck determines every edge-additive degree index
  (Sombor included) -- report section 7.2 closed for the class.  The
  back-substitution itself is not formalised here.
-/

import StarTheorem.DeletionIdentity
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Ordered edge-type counts -/

/-- `N_xy(G)`: the number of ordered adjacent pairs `(u,v)` with degrees `(x,y)`. -/
noncomputable def edgeTypeCount (G : SimpleGraph V) [DecidableRel G.Adj] (x y : ℕ) : ℕ :=
  ((univ : Finset (V × V)).filter
    (fun p => G.Adj p.1 p.2 ∧ G.degree p.1 = x ∧ G.degree p.2 = y)).card

/-- `N_xy = N_yx` (swapping the ordered pair). -/
theorem edgeTypeCount_symm (G : SimpleGraph V) [DecidableRel G.Adj] (x y : ℕ) :
    edgeTypeCount G x y = edgeTypeCount G y x := by
  have h1 : (univ : Finset (V × V)).filter
        (fun p => G.Adj p.1 p.2 ∧ G.degree p.1 = y ∧ G.degree p.2 = x)
      = Finset.image Prod.swap
          ((univ : Finset (V × V)).filter
            (fun p => G.Adj p.1 p.2 ∧ G.degree p.1 = x ∧ G.degree p.2 = y)) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      exact ⟨Prod.swap p, ⟨h.1.symm, h.2.2, h.2.1⟩, by simp⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1.symm, hq.2.2, hq.2.1⟩
  calc edgeTypeCount G x y
      = ((univ : Finset (V × V)).filter
          (fun p => G.Adj p.1 p.2 ∧ G.degree p.1 = x ∧ G.degree p.2 = y)).card := rfl
    _ = ((univ : Finset (V × V)).filter
          (fun p => G.Adj p.1 p.2 ∧ G.degree p.1 = y ∧ G.degree p.2 = x)).card := by
        rw [h1, Finset.card_image_of_injective _ Prod.swap_injective]
    _ = edgeTypeCount G y x := rfl

/-! ### The symmetric indicator kernel of the degree pair {x,y} -/

/-- `f_xy(a,b) = 1` iff the unordered pair `{a,b}` of (real) degrees equals `{x,y}`. -/
noncomputable def fxy (x y : ℕ) : ℝ → ℝ → ℝ :=
  fun a b => if (a = (x : ℝ) ∧ b = (y : ℝ)) ∨ (a = (y : ℝ) ∧ b = (x : ℝ)) then 1 else 0

theorem fxy_symm (x y : ℕ) (a b : ℝ) : fxy x y a b = fxy x y b a := by
  have key : ((a = (x : ℝ) ∧ b = (y : ℝ)) ∨ (a = (y : ℝ) ∧ b = (x : ℝ)))
      ↔ ((b = (x : ℝ) ∧ a = (y : ℝ)) ∨ (b = (y : ℝ) ∧ a = (x : ℝ))) := by
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
  simp only [fxy, key]

/-! ### Bridging sums over `neighborFinset` to filter-sums over ordered pairs -/

private theorem sum_adj_pairs (G : SimpleGraph V) [DecidableRel G.Adj] (φ : V → V → ℝ) :
    (∑ u : V, ∑ v ∈ G.neighborFinset u, φ u v)
      = ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2), φ p.1 p.2 := by
  let ψ : V × V → ℝ := fun p => ite (G.Adj p.1 p.2) (φ p.1 p.2) 0
  calc (∑ u : V, ∑ v ∈ G.neighborFinset u, φ u v)
      = ∑ u : V, ∑ v ∈ (univ : Finset V).filter (G.Adj u), φ u v := by
        apply Finset.sum_congr rfl
        intro u _
        congr 1
        ext v
        simp only [mem_filter, mem_univ, true_and, G.mem_neighborFinset]
    _ = ∑ u ∈ (univ : Finset V), ∑ v ∈ (univ : Finset V), ψ (u, v) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_filter]
    _ = ∑ p ∈ (univ : Finset V) ×ˢ (univ : Finset V), ψ p := by
        rw [Finset.sum_product]
    _ = ∑ p ∈ (univ : Finset (V × V)), ψ p := by
        rw [Finset.univ_product_univ]
    _ = ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2), φ p.1 p.2 := by
        dsimp only [ψ]
        rw [← Finset.sum_filter]

/-! ### Pointwise values of the kernel -/

private theorem cast_key : ∀ a b : ℕ, ((a : ℝ) - 1 = (b : ℝ)) ↔ a = b + 1 := by
  intro a b
  have h1 : ((b + 1 : ℕ) : ℝ) = (b : ℝ) + 1 := by push_cast; ring
  rw [sub_eq_iff_eq_add, ← h1, Nat.cast_inj]

/-- Splitting an indicator of a disjoint union into a sum of indicators. -/
private theorem ite_or_add (P Q : Prop) [Decidable P] [Decidable Q]
    (hne : ¬(P ∧ Q)) :
    (ite (P ∨ Q) (1 : ℝ) 0) = ite P (1 : ℝ) 0 + ite Q (1 : ℝ) 0 := by
  by_cases hP : P
  · by_cases hQ : Q
    · exfalso
      exact hne ⟨hP, hQ⟩
    · simp [hP, hQ]
  · by_cases hQ : Q
    · simp [hP, hQ]
    · simp [hP, hQ]

private theorem fxy_nat_ne {x y : ℕ} (hxy : x ≠ y) (r s : ℕ) :
    fxy x y (r : ℝ) (s : ℝ)
      = ite (r = x ∧ s = y) (1 : ℝ) 0 + ite (r = y ∧ s = x) (1 : ℝ) 0 := by
  have cx : ((r : ℝ) = (x : ℝ)) ↔ r = x := Nat.cast_inj
  have cy : ((s : ℝ) = (y : ℝ)) ↔ s = y := Nat.cast_inj
  have cx' : ((r : ℝ) = (y : ℝ)) ↔ r = y := Nat.cast_inj
  have cy' : ((s : ℝ) = (x : ℝ)) ↔ s = x := Nat.cast_inj
  simp only [fxy, cx, cy, cx', cy']
  exact ite_or_add _ _ (by rintro ⟨⟨r1, _⟩, ⟨r2, _⟩⟩; exact hxy (r1.symm.trans r2))

private theorem fxy_nat_sub_ne {x y : ℕ} (hxy : x ≠ y) (r s : ℕ) :
    fxy x y ((r : ℝ) - 1) (s : ℝ)
      = ite (r = x + 1 ∧ s = y) (1 : ℝ) 0 + ite (r = y + 1 ∧ s = x) (1 : ℝ) 0 := by
  have cy : ((s : ℝ) = (y : ℝ)) ↔ s = y := Nat.cast_inj
  have cx : ((s : ℝ) = (x : ℝ)) ↔ s = x := Nat.cast_inj
  simp only [fxy, cast_key, cy, cx]
  exact ite_or_add _ _ (by rintro ⟨⟨r1, _⟩, ⟨r2, _⟩⟩; omega)

/-- The pointwise decomposition of the `C_f` summand for the indicator kernel, x ≠ y. -/
private theorem psi_decomp_ne {x y : ℕ} (hxy : x ≠ y) (r s : ℕ) :
    ((r : ℝ) - 1) * (fxy x y (r : ℝ) (s : ℝ) - fxy x y ((r : ℝ) - 1) (s : ℝ))
    = ite (r = x ∧ s = y) ((x : ℝ) - 1) 0
      + ite (r = y ∧ s = x) ((y : ℝ) - 1) 0
      - ite (r = x + 1 ∧ s = y) (x : ℝ) 0
      - ite (r = y + 1 ∧ s = x) (y : ℝ) 0 := by
  rw [fxy_nat_ne hxy r s, fxy_nat_sub_ne hxy r s]
  split_ifs with hA hB hC hD
  all_goals first
    | omega
    | simp_all
      try ring

private theorem psi_decomp_eq (x : ℕ) (r s : ℕ) :
    ((r : ℝ) - 1) * (fxy x x (r : ℝ) (s : ℝ) - fxy x x ((r : ℝ) - 1) (s : ℝ))
    = ite (r = x ∧ s = x) ((x : ℝ) - 1) 0 - ite (r = x + 1 ∧ s = x) (x : ℝ) 0 := by
  have f1 : fxy x x (r : ℝ) (s : ℝ) = ite (r = x ∧ s = x) (1 : ℝ) 0 := by
    have cx : ((r : ℝ) = (x : ℝ)) ↔ r = x := Nat.cast_inj
    have cy : ((s : ℝ) = (x : ℝ)) ↔ s = x := Nat.cast_inj
    simp only [fxy, cx, cy, or_self]
  have f2 : fxy x x ((r : ℝ) - 1) (s : ℝ) = ite (r = x + 1 ∧ s = x) (1 : ℝ) 0 := by
    have cx : ((s : ℝ) = (x : ℝ)) ↔ s = x := Nat.cast_inj
    simp only [fxy, cast_key, cx, or_self]
  rw [f1, f2]
  split_ifs with hA hB
  all_goals first
    | omega
    | simp_all
      try ring

/-! ### `T_f` and `C_f` for the indicator kernel -/

/-- Cell-sum helper: summing the indicator of one degree cell over ordered adjacent
pairs gives the edge-type count of that cell. -/
private theorem card_cell (G : SimpleGraph V) [DecidableRel G.Adj] (a b : ℕ) :
    ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
        ite (G.degree p.1 = a ∧ G.degree p.2 = b) (1 : ℝ) 0
      = (edgeTypeCount G a b : ℝ) := by
  rw [Finset.sum_boole, Nat.cast_inj, Finset.filter_filter, edgeTypeCount]

/-- Cell-sum helper with a general value. -/
private theorem sum_ite_cell (G : SimpleGraph V) [DecidableRel G.Adj] (val : ℝ) (a b : ℕ) :
    ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
        ite (G.degree p.1 = a ∧ G.degree p.2 = b) val 0
      = val * (edgeTypeCount G a b : ℝ) := by
  have hsum : ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
          ite (G.degree p.1 = a ∧ G.degree p.2 = b) val 0
        = (∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
            ite (G.degree p.1 = a ∧ G.degree p.2 = b) (1 : ℝ) 0) * val := by
    rw [Finset.sum_congr rfl (fun p _ => show
          ite (G.degree p.1 = a ∧ G.degree p.2 = b) val 0
            = ite (G.degree p.1 = a ∧ G.degree p.2 = b) (1 : ℝ) 0 * val from by
          by_cases h : G.degree p.1 = a ∧ G.degree p.2 = b
          · rw [if_pos h, if_pos h]
            ring
          · rw [if_neg h, if_neg h]
            ring),
        ← Finset.sum_mul]
  rw [hsum, card_cell G a b]
  ring

theorem Tf_fxy_ne (G : SimpleGraph V) [DecidableRel G.Adj] {x y : ℕ} (hxy : x ≠ y) :
    Tf (fxy x y) G = (edgeTypeCount G x y : ℝ) := by
  have hpoint : ∀ p : V × V,
      fxy x y (G.degree p.1) (G.degree p.2)
      = ite (G.degree p.1 = x ∧ G.degree p.2 = y) (1 : ℝ) 0
        + ite (G.degree p.1 = y ∧ G.degree p.2 = x) (1 : ℝ) 0 :=
    fun p => fxy_nat_ne hxy _ _
  calc Tf (fxy x y) G
      = (1 / 2 : ℝ) * ∑ u : V, ∑ v ∈ G.neighborFinset u,
            fxy x y (G.degree u) (G.degree v) := by rw [Tf]
    _ = (1 / 2 : ℝ) * ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
            fxy x y (G.degree p.1) (G.degree p.2) := by
        congr 1
        exact sum_adj_pairs G _
    _ = (1 / 2 : ℝ) * ((edgeTypeCount G x y : ℝ) + (edgeTypeCount G y x : ℝ)) := by
        congr 1
        rw [Finset.sum_congr rfl (fun p _ => hpoint p), Finset.sum_add_distrib,
          card_cell G x y, card_cell G y x]
    _ = (edgeTypeCount G x y : ℝ) := by
        rw [edgeTypeCount_symm]
        ring

theorem Tf_fxy_eq (G : SimpleGraph V) [DecidableRel G.Adj] (x : ℕ) :
    Tf (fxy x x) G = (edgeTypeCount G x x : ℝ) / 2 := by
  have hpoint : ∀ p : V × V,
      fxy x x (G.degree p.1) (G.degree p.2)
      = ite (G.degree p.1 = x ∧ G.degree p.2 = x) (1 : ℝ) 0 := by
    intro p
    have cx : ((G.degree p.1 : ℕ) : ℝ) = (x : ℝ) ↔ G.degree p.1 = x := Nat.cast_inj
    have cy : ((G.degree p.2 : ℕ) : ℝ) = (x : ℝ) ↔ G.degree p.2 = x := Nat.cast_inj
    simp only [fxy, cx, cy, or_self]
  calc Tf (fxy x x) G
      = (1 / 2 : ℝ) * ∑ u : V, ∑ v ∈ G.neighborFinset u,
            fxy x x (G.degree u) (G.degree v) := by rw [Tf]
    _ = (1 / 2 : ℝ) * ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
            fxy x x (G.degree p.1) (G.degree p.2) := by
        congr 1
        exact sum_adj_pairs G _
    _ = (1 / 2 : ℝ) * (edgeTypeCount G x x : ℝ) := by
        congr 1
        rw [Finset.sum_congr rfl (fun p _ => hpoint p), card_cell G x x]
    _ = (edgeTypeCount G x x : ℝ) / 2 := by ring

theorem Cf_fxy_ne (G : SimpleGraph V) [DecidableRel G.Adj] {x y : ℕ} (hxy : x ≠ y) :
    Cf (fxy x y) G
      = ((x : ℝ) + (y : ℝ) - 2) * (edgeTypeCount G x y : ℝ)
        - (x : ℝ) * (edgeTypeCount G (x + 1) y : ℝ)
        - (y : ℝ) * (edgeTypeCount G x (y + 1) : ℝ) := by
  have hbridge : Cf (fxy x y) G
      = ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
          ((G.degree p.1 : ℝ) - 1)
            * (fxy x y (G.degree p.1) (G.degree p.2)
              - fxy x y ((G.degree p.1 : ℝ) - 1) (G.degree p.2)) := by
    simp only [Cf, Finset.mul_sum, sum_adj_pairs]
  rw [hbridge]
  rw [Finset.sum_congr rfl (fun p _ => psi_decomp_ne hxy _ _)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_ite_cell G ((x : ℝ) - 1) x y, sum_ite_cell G ((y : ℝ) - 1) y x,
    sum_ite_cell G (x : ℝ) (x + 1) y, sum_ite_cell G (y : ℝ) (y + 1) x]
  have s1 : (edgeTypeCount G y x : ℝ) = (edgeTypeCount G x y : ℝ) := by
    rw [edgeTypeCount_symm]
  have s2 : (edgeTypeCount G (y + 1) x : ℝ) = (edgeTypeCount G x (y + 1) : ℝ) := by
    rw [edgeTypeCount_symm]
  rw [s1, s2]
  ring

theorem Cf_fxy_eq (G : SimpleGraph V) [DecidableRel G.Adj] (x : ℕ) :
    Cf (fxy x x) G
      = ((x : ℝ) - 1) * (edgeTypeCount G x x : ℝ)
        - (x : ℝ) * (edgeTypeCount G (x + 1) x : ℝ) := by
  have hbridge : Cf (fxy x x) G
      = ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
          ((G.degree p.1 : ℝ) - 1)
            * (fxy x x (G.degree p.1) (G.degree p.2)
              - fxy x x ((G.degree p.1 : ℝ) - 1) (G.degree p.2)) := by
    simp only [Cf, Finset.mul_sum, sum_adj_pairs]
  rw [hbridge]
  rw [Finset.sum_congr rfl (fun p _ => psi_decomp_eq x _ _)]
  rw [Finset.sum_sub_distrib]
  rw [sum_ite_cell G ((x : ℝ) - 1) x x, sum_ite_cell G (x : ℝ) (x + 1) x]

/-! ### The edge-type deletion identity -/

/-- **THEOREM (edge-type deletion identity)**, ordered-pair form:

      (1/2) * sum_{u} sum_{v in N(u)} N_xy(G - uv)
        = (m - x - y + 1) * N_xy(G) + x * N_{x+1,y}(G) + y * N_{x,y+1}(G).

The left side counts each edge deletion once, so this is exactly
`sum_e N_xy(G - e) = (m-x-y+1) N_xy + x N_{x+1,y} + y N_{x,y+1}`. -/
theorem edgeType_deletion_identity (G : SimpleGraph V) [DecidableRel G.Adj] (x y : ℕ) :
    (1 / 2 : ℝ) * (∑ u : V, ∑ v ∈ G.neighborFinset u,
        (edgeTypeCount (G.deleteEdges {s(u, v)}) x y : ℝ))
      = ((G.edgeFinset.card : ℝ) - (x : ℝ) - (y : ℝ) + 1) * (edgeTypeCount G x y : ℝ)
        + (x : ℝ) * (edgeTypeCount G (x + 1) y : ℝ)
        + (y : ℝ) * (edgeTypeCount G x (y + 1) : ℝ) := by
  have hsymm : ∀ a b : ℝ, fxy x y a b = fxy x y b a := fun a b => fxy_symm x y a b
  have hDI := deletion_identity (f := fxy x y) hsymm (G := G)
  by_cases hxy : x = y
  · subst hxy
    have hT : ∀ u v : V,
        Tf (fxy x x) (G.deleteEdges {s(u, v)})
          = (edgeTypeCount (G.deleteEdges {s(u, v)}) x x : ℝ) / 2 :=
      fun u v => Tf_fxy_eq _ x
    simp only [hT, Tf_fxy_eq, Cf_fxy_eq] at hDI
    have hsum : (∑ u : V, ∑ v ∈ G.neighborFinset u,
          ((edgeTypeCount (G.deleteEdges {s(u, v)}) x x : ℝ) / 2))
        = (1 / 2 : ℝ) * ∑ u : V, ∑ v ∈ G.neighborFinset u,
          (edgeTypeCount (G.deleteEdges {s(u, v)}) x x : ℝ) := by
      calc (∑ u : V, ∑ v ∈ G.neighborFinset u,
            ((edgeTypeCount (G.deleteEdges {s(u, v)}) x x : ℝ) / 2))
          = ∑ u : V, ∑ v ∈ G.neighborFinset u,
              ((1 / 2 : ℝ) * (edgeTypeCount (G.deleteEdges {s(u, v)}) x x : ℝ)) := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro v _
            ring
        _ = ∑ u : V, (1 / 2 : ℝ) * ∑ v ∈ G.neighborFinset u,
              (edgeTypeCount (G.deleteEdges {s(u, v)}) x x : ℝ) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.mul_sum]
        _ = (1 / 2 : ℝ) * ∑ u : V, ∑ v ∈ G.neighborFinset u,
              (edgeTypeCount (G.deleteEdges {s(u, v)}) x x : ℝ) := by
            rw [← Finset.mul_sum]
    rw [hsum] at hDI
    have hs : (edgeTypeCount G x (x + 1) : ℝ) = (edgeTypeCount G (x + 1) x : ℝ) := by
      rw [edgeTypeCount_symm]
    rw [hs]
    linear_combination 2 * hDI
  · have hT : ∀ u v : V,
        Tf (fxy x y) (G.deleteEdges {s(u, v)})
          = (edgeTypeCount (G.deleteEdges {s(u, v)}) x y : ℝ) :=
      fun u v => Tf_fxy_ne _ hxy
    have hfT := Tf_fxy_ne G hxy
    have hfC := Cf_fxy_ne G hxy
    simp only [hT, hfT, hfC] at hDI
    linear_combination hDI

end StarTheorem
