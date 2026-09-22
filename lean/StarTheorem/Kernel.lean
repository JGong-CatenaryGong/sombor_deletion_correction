/-
  StarTheorem/Kernel.lean -- the analytic core: monotonicity of the Sombor
  deletion kernel `c`.

  Human proof (report.md §8.3, ingredient L1):

      c(a,b) = sqrt(a^2+b^2) - sqrt((a-1)^2+b^2)

  is strictly increasing in `a` and strictly decreasing in `b` (for b >= 1).
  Both statements are proved here by elementary algebra (two squarings), using

      c(a,b) = (2a-1) / (sqrt(a^2+b^2) + sqrt((a-1)^2+b^2))            (rationalisation)
      sqrt(x) <= sqrt(y)  for x <= y                                    (monotonicity of sqrt)
      x <= y  for x,y >= 0 and x^2 <= y^2                               (squaring)

  The results are stated for natural-number arguments, since degrees are natural
  numbers; the combined corollary `c_le_c_m_one` is what the main theorem uses.
-/

import StarTheorem.Defs

open Finset
open scoped BigOperators

namespace StarTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Rationalisation of the kernel -/

/-- `c(a,b) * (sqrt(a^2+b^2) + sqrt((a-1)^2+b^2)) = 2a - 1`. -/
theorem c_mul_denom (a b : ℝ) :
    c a b * (Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt ((a - 1) ^ 2 + b ^ 2)) = 2 * a - 1 := by
  have hX : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hY : 0 ≤ (a - 1) ^ 2 + b ^ 2 := by positivity
  have h1 : Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (a ^ 2 + b ^ 2) = a ^ 2 + b ^ 2 := by
    rw [← sq, Real.sq_sqrt hX]
  have h2 : Real.sqrt ((a - 1) ^ 2 + b ^ 2) * Real.sqrt ((a - 1) ^ 2 + b ^ 2)
      = (a - 1) ^ 2 + b ^ 2 := by
    rw [← sq, Real.sq_sqrt hY]
  rw [c]
  nlinarith [h1, h2]

/-- The denominator is positive, so the rationalised form is a genuine quotient. -/
theorem denom_pos (a b : ℝ) :
    0 < Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt ((a - 1) ^ 2 + b ^ 2) := by
  have hX : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hY : 0 ≤ (a - 1) ^ 2 + b ^ 2 := by positivity
  have hsum : 0 < (a ^ 2 + b ^ 2) + ((a - 1) ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (2 * a - 1), sq_nonneg b]
  have h1 : Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (a ^ 2 + b ^ 2) = a ^ 2 + b ^ 2 := by
    rw [← sq, Real.sq_sqrt hX]
  have h2 : Real.sqrt ((a - 1) ^ 2 + b ^ 2) * Real.sqrt ((a - 1) ^ 2 + b ^ 2)
      = (a - 1) ^ 2 + b ^ 2 := by
    rw [← sq, Real.sq_sqrt hY]
  nlinarith [Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sqrt_nonneg ((a - 1) ^ 2 + b ^ 2),
    mul_nonneg (Real.sqrt_nonneg (a ^ 2 + b ^ 2)) (Real.sqrt_nonneg ((a - 1) ^ 2 + b ^ 2))]

/-- Rationalised form of the kernel. -/
theorem c_eq_div (a b : ℝ) :
    c a b = (2 * a - 1) /
      (Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt ((a - 1) ^ 2 + b ^ 2)) := by
  rw [eq_div_iff (ne_of_gt (denom_pos a b))]
  exact c_mul_denom a b


/-- A vertex adjacent to another one has positive degree (helper, not in this Mathlib). -/
theorem degree_pos_of_adj {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    0 < G.degree v :=
  (G.degree_pos_iff_exists_adj v).mpr ⟨u, h.symm⟩

/-- Same, in the `1 ≤ ·` form used by the degree arguments. -/
theorem one_le_degree_of_adj {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    1 ≤ G.degree v :=
  degree_pos_of_adj h


/-- Membership in `incidenceFinset`, in filter form. -/
theorem mem_incidenceFinset_iff (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) (e : Sym2 V) :
    e ∈ G.incidenceFinset w ↔ e ∈ G.edgeFinset ∧ w ∈ e := by
  rw [G.incidenceFinset_eq_filter, Finset.mem_filter]

/-! ### Positivity -/

/-- `c(a,b) > 0` whenever `a ≥ 1`, `b ≥ 1`. -/
theorem c_pos {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 0 < c a b := by
  have hX : 0 ≤ (a - 1) ^ 2 + b ^ 2 := by positivity
  have hlt : (a - 1) ^ 2 + b ^ 2 < a ^ 2 + b ^ 2 := by nlinarith
  have := Real.sqrt_lt_sqrt hX hlt
  rw [c]
  linarith

/-- For natural arguments with `1 ≤ a`, `1 ≤ b`: `c a b > 0`. -/
theorem c_pos_nat {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 0 < c (a : ℝ) (b : ℝ) := by
  refine c_pos ?_ ?_ <;> exact_mod_cast ‹_›

/-! ### Monotonicity in the second argument (decreasing) -/

/-- `c` is antitone in its second argument (natural arguments, `1 ≤ a`). -/
theorem c_antitone_right_nat {a b b' : ℕ} (ha : 1 ≤ a) (hbb' : b ≤ b') :
    c (a : ℝ) (b' : ℝ) ≤ c (a : ℝ) (b : ℝ) := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ (b' : ℝ) := by exact_mod_cast hbb'
  set X : ℝ := (a : ℝ) ^ 2 + (b : ℝ) ^ 2
  set X' : ℝ := (a : ℝ) ^ 2 + (b' : ℝ) ^ 2
  set Y : ℝ := ((a : ℝ) - 1) ^ 2 + (b : ℝ) ^ 2
  set Y' : ℝ := ((a : ℝ) - 1) ^ 2 + (b' : ℝ) ^ 2
  have hX : 0 ≤ X := by positivity
  have hX' : 0 ≤ X' := by positivity
  have hY : 0 ≤ Y := by positivity
  have hY' : 0 ≤ Y' := by positivity
  -- the polynomial inequality X' * Y ≤ X * Y'
  have hpoly : X' * Y ≤ X * Y' := by
    have h1 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have h2 : (b : ℝ) ^ 2 ≤ (b' : ℝ) ^ 2 := by nlinarith
    have h3 : (0 : ℝ) ≤ 2 * (a : ℝ) - 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) h3]
  have hsqrt : Real.sqrt (X' * Y) ≤ Real.sqrt (X * Y') := Real.sqrt_le_sqrt hpoly
  have hsqX' : Real.sqrt X' * Real.sqrt X' = X' := by rw [← sq, Real.sq_sqrt hX']
  have hsqX : Real.sqrt X * Real.sqrt X = X := by rw [← sq, Real.sq_sqrt hX]
  have hsqY : Real.sqrt Y * Real.sqrt Y = Y := by rw [← sq, Real.sq_sqrt hY]
  have hsqY' : Real.sqrt Y' * Real.sqrt Y' = Y' := by rw [← sq, Real.sq_sqrt hY']
  have hXY : X' + Y = X + Y' := by
    simp only [X, X', Y, Y']
    ring
  -- from sqrt(X'*Y) ≤ sqrt(X*Y') get the squared comparison of the sums
  have hsquare : (Real.sqrt X' + Real.sqrt Y) ^ 2 ≤ (Real.sqrt X + Real.sqrt Y') ^ 2 := by
    have h1 : Real.sqrt X' * Real.sqrt Y ≤ Real.sqrt X * Real.sqrt Y' := by
      have h := Real.sqrt_le_sqrt (show X' * Y ≤ X * Y' from hpoly)
      -- sqrt(X'*Y) = sqrt X' * sqrt Y  and  sqrt(X*Y') = sqrt X * sqrt Y'
      rwa [Real.sqrt_mul hX' , Real.sqrt_mul hX] at h
    nlinarith [hsqX', hsqX, hsqY, hsqY', h1, hXY]
  have hle : Real.sqrt X' + Real.sqrt Y ≤ Real.sqrt X + Real.sqrt Y' := by
    have h1 := sq_le_sq.mp hsquare
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h1
  simp only [c, X, X', Y, Y'] at *
  linarith

/-! ### Monotonicity in the first argument (increasing) -/

/-- Successor step: `c n b ≤ c (n+1) b` for `1 ≤ n`. -/
theorem c_succ_left_nat (n b : ℕ) (hn : 1 ≤ n) :
    c (n : ℝ) (b : ℝ) ≤ c ((n + 1 : ℕ) : ℝ) (b : ℝ) := by
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- With a = n, the claim is sqrt((n+1)^2+b^2) + sqrt((n-1)^2+b^2) >= 2 sqrt(n^2+b^2).
  set Z : ℝ := (n : ℝ) ^ 2 + (b : ℝ) ^ 2
  set Xp : ℝ := ((n : ℝ) + 1) ^ 2 + (b : ℝ) ^ 2
  set Xm : ℝ := ((n : ℝ) - 1) ^ 2 + (b : ℝ) ^ 2
  have hZ : 0 ≤ Z := by positivity
  have hXp : 0 ≤ Xp := by positivity
  have hXm : 0 ≤ Xm := by positivity
  have hZ1 : (1 : ℝ) ≤ Z := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    simp only [Z]; nlinarith
  -- (Xp * Xm) ≥ (Z - 1)^2
  have hprod : (Z - 1) ^ 2 ≤ Xp * Xm := by
    have hb2 : (0 : ℝ) ≤ 4 * (b : ℝ) ^ 2 := by positivity
    have : Xp * Xm - (Z - 1) ^ 2 = 4 * (b : ℝ) ^ 2 := by
      simp only [Xp, Xm, Z]; ring
    linarith
  have hsq : Z - 1 ≤ Real.sqrt (Xp * Xm) := by
    have h1 : Real.sqrt ((Z - 1) ^ 2) ≤ Real.sqrt (Xp * Xm) := Real.sqrt_le_sqrt hprod
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)] at h1
  have hmul : Real.sqrt Xp * Real.sqrt Xm = Real.sqrt (Xp * Xm) := (Real.sqrt_mul hXp Xm).symm
  have hsqp : Real.sqrt Xp * Real.sqrt Xp = Xp := by rw [← sq, Real.sq_sqrt hXp]
  have hsqm : Real.sqrt Xm * Real.sqrt Xm = Xm := by rw [← sq, Real.sq_sqrt hXm]
  have hsqZ : Real.sqrt Z * Real.sqrt Z = Z := by rw [← sq, Real.sq_sqrt hZ]
  have hXY : Xp + Xm = 2 * Z + 2 := by simp only [Xp, Xm, Z]; ring
  have hsquare : (2 * Real.sqrt Z) ^ 2 ≤ (Real.sqrt Xp + Real.sqrt Xm) ^ 2 := by
    nlinarith [hsqp, hsqm, hsqZ, hmul, hsq, hXY]
  have hle : 2 * Real.sqrt Z ≤ Real.sqrt Xp + Real.sqrt Xm := by
    have h1 := sq_le_sq.mp hsquare
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h1
  -- convert to c
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hexp : c ((n + 1 : ℕ) : ℝ) (b : ℝ) - c (n : ℝ) (b : ℝ)
      = (Real.sqrt Xp + Real.sqrt Xm) - 2 * Real.sqrt Z := by
    rw [hcast]
    simp only [c, Xp, Xm, Z]
    rw [show ((n : ℝ) + 1 - 1) ^ 2 = (n : ℝ) ^ 2 by ring]
    ring
  linarith

/-- `c` is monotone in its first argument (natural arguments, iterated successor). -/
theorem c_monotone_left_nat {a m : ℕ} (ha : 1 ≤ a) (h : a ≤ m) (b : ℕ) :
    c (a : ℝ) (b : ℝ) ≤ c (m : ℝ) (b : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
      have hsucc := c_succ_left_nat (a + d) b (by omega)
      have hsucc' : c ((a + d : ℕ) : ℝ) (b : ℝ) ≤ c ((a + (d + 1) : ℕ) : ℝ) (b : ℝ) := by
        simpa [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using hsucc
      exact le_trans (ih (by omega)) hsucc'

/-- The neighbour set of a vertex of degree zero is empty. -/
theorem neighborFinset_eq_empty_of_degree_eq_zero {G : SimpleGraph V} [DecidableRel G.Adj]
    {u : V} (hu : G.degree u = 0) : G.neighborFinset u = ∅ :=
  Finset.card_eq_zero.mp (by rw [G.card_neighborFinset_eq_degree, hu])

/-- **Key corollary**: for an edge of a graph with `m` edges, `c(d_u,d_v) ≤ c(m,1)`. -/
theorem c_le_c_m_one {a b m : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) (hb : 1 ≤ b) :
    c (a : ℝ) (b : ℝ) ≤ c (m : ℝ) 1 := by
  have h1 : c (a : ℝ) (b : ℝ) ≤ c (m : ℝ) (b : ℝ) := c_monotone_left_nat ha ham b
  have h2 : c (m : ℝ) (b : ℝ) ≤ c (m : ℝ) (1 : ℝ) := by
    simpa using c_antitone_right_nat (le_trans ha ham) hb
  simpa using le_trans h1 h2

/-! ### Strict monotonicity (needed for the equality characterisation) -/

/-- `c` is strictly antitone in its second argument (natural arguments, `1 ≤ a`). -/
theorem c_antitone_right_nat_lt {a b b' : ℕ} (ha : 1 ≤ a) (h : b < b') :
    c (a : ℝ) (b' : ℝ) < c (a : ℝ) (b : ℝ) := by
  have hb : (b : ℝ) < (b' : ℝ) := by exact_mod_cast h
  have hnum : 0 < 2 * (a : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hDpos := denom_pos (a : ℝ) (b : ℝ)
  have hD'pos := denom_pos (a : ℝ) (b' : ℝ)
  have hlt : Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) + Real.sqrt (((a : ℝ) - 1) ^ 2 + (b : ℝ) ^ 2)
      < Real.sqrt ((a : ℝ) ^ 2 + (b' : ℝ) ^ 2)
        + Real.sqrt (((a : ℝ) - 1) ^ 2 + (b' : ℝ) ^ 2) := by
    have h1 : Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)
        < Real.sqrt ((a : ℝ) ^ 2 + (b' : ℝ) ^ 2) :=
      Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
    have h2 : Real.sqrt (((a : ℝ) - 1) ^ 2 + (b : ℝ) ^ 2)
        ≤ Real.sqrt (((a : ℝ) - 1) ^ 2 + (b' : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    linarith
  rw [c_eq_div, c_eq_div]
  exact (div_lt_div_iff_of_pos_left hnum hD'pos hDpos).mpr hlt

/-- Strict successor step: `c n b < c (n+1) b` for `1 ≤ n`, `1 ≤ b`. -/
theorem c_succ_left_nat_lt (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) :
    c (n : ℝ) (b : ℝ) < c ((n + 1 : ℕ) : ℝ) (b : ℝ) := by
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set Z : ℝ := (n : ℝ) ^ 2 + (b : ℝ) ^ 2
  set Xp : ℝ := ((n : ℝ) + 1) ^ 2 + (b : ℝ) ^ 2
  set Xm : ℝ := ((n : ℝ) - 1) ^ 2 + (b : ℝ) ^ 2
  have hZ : 0 ≤ Z := by positivity
  have hXp : 0 ≤ Xp := by positivity
  have hXm : 0 ≤ Xm := by positivity
  have hZ1 : (1 : ℝ) ≤ Z := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    simp only [Z]; nlinarith
  have hprod : (Z - 1) ^ 2 < Xp * Xm := by
    have hb2 : 0 < 4 * (b : ℝ) ^ 2 := by positivity
    have hsplit : Xp * Xm - (Z - 1) ^ 2 = 4 * (b : ℝ) ^ 2 := by
      simp only [Xp, Xm, Z]; ring
    linarith
  have hsq : Z - 1 < Real.sqrt (Xp * Xm) := by
    have h1 : Real.sqrt ((Z - 1) ^ 2) < Real.sqrt (Xp * Xm) :=
      Real.sqrt_lt_sqrt (by positivity) hprod
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)] at h1
  have hmul : Real.sqrt Xp * Real.sqrt Xm = Real.sqrt (Xp * Xm) := (Real.sqrt_mul hXp Xm).symm
  have hsqp : Real.sqrt Xp * Real.sqrt Xp = Xp := by rw [← sq, Real.sq_sqrt hXp]
  have hsqm : Real.sqrt Xm * Real.sqrt Xm = Xm := by rw [← sq, Real.sq_sqrt hXm]
  have hsqZ : Real.sqrt Z * Real.sqrt Z = Z := by rw [← sq, Real.sq_sqrt hZ]
  have hXY : Xp + Xm = 2 * Z + 2 := by simp only [Xp, Xm, Z]; ring
  have hsquare : (2 * Real.sqrt Z) ^ 2 < (Real.sqrt Xp + Real.sqrt Xm) ^ 2 := by
    nlinarith [hsqp, hsqm, hsqZ, hmul, hsq, hXY]
  have hle : 2 * Real.sqrt Z < Real.sqrt Xp + Real.sqrt Xm := by
    have h1 := sq_lt_sq.mp hsquare
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h1
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hexp : c ((n + 1 : ℕ) : ℝ) (b : ℝ) - c (n : ℝ) (b : ℝ)
      = (Real.sqrt Xp + Real.sqrt Xm) - 2 * Real.sqrt Z := by
    rw [hcast]
    simp only [c, Xp, Xm, Z]
    rw [show ((n : ℝ) + 1 - 1) ^ 2 = (n : ℝ) ^ 2 by ring]
    ring
  linarith

/-- `c` is strictly monotone in its first argument (natural arguments). -/
theorem c_lt_left_nat {a m : ℕ} (ha : 1 ≤ a) (h : a < m) (b : ℕ) (hb : 1 ≤ b) :
    c (a : ℝ) (b : ℝ) < c (m : ℝ) (b : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  have h1 : c (a : ℝ) (b : ℝ) < c ((a + 1 : ℕ) : ℝ) (b : ℝ) := c_succ_left_nat_lt a b ha hb
  have h2 : c ((a + 1 : ℕ) : ℝ) (b : ℝ) ≤ c ((a + (d + 1) : ℕ) : ℝ) (b : ℝ) :=
    c_monotone_left_nat (by omega) (by omega) b
  exact lt_of_lt_of_le h1 h2

/-- **Key strict form**: `c a b = c m 1` with `1 ≤ a ≤ m`, `1 ≤ b` forces `a = m`, `b = 1`. -/
theorem c_eq_c_m_one_iff {a b m : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) (hb : 1 ≤ b) :
    c (a : ℝ) (b : ℝ) = c (m : ℝ) 1 ↔ a = m ∧ b = 1 := by
  constructor
  · intro h
    have ham' : a = m := by
      rcases lt_or_eq_of_le ham with hlt | heq
      · exfalso
        have h1 : c (a : ℝ) (b : ℝ) < c (m : ℝ) (b : ℝ) := c_lt_left_nat ha hlt b hb
        have h2 : c (m : ℝ) (b : ℝ) ≤ c (m : ℝ) 1 := by
          simpa using c_antitone_right_nat (a := m) (b := 1) (b' := b) (by omega) hb
        rw [h] at h1
        linarith
      · exact heq
    have hb1 : b = 1 := by
      rcases eq_or_lt_of_le hb with he | hlt
      · exact he.symm
      · exfalso
        have h1 : c (a : ℝ) (b : ℝ) < c (a : ℝ) 1 := by
          simpa using c_antitone_right_nat_lt (a := a) (b := 1) (b' := b) (by omega) hlt
        have h5 : c (a : ℝ) (b : ℝ) = c (a : ℝ) 1 := by rw [h, ham']
        exact absurd h5 (ne_of_lt h1)
    exact ⟨ham', hb1⟩
  · rintro ⟨rfl, rfl⟩
    simp

end StarTheorem
