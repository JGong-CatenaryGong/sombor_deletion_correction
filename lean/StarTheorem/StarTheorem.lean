/-
  StarTheorem -- formalisation of the main theorems of report.md §8.

  Import order follows the agreed priority:
    1. StarMax.lean          star maximisation  C(G) ≤ m(m-1)c(m,1)
    2. ZeroIff.lean          C(G) = 0 ↔ G is a matching
    3. Regular.lean          C(G) = N·r·(r-1)·c(r,r) for r-regular G
    4. Sandwich.lean         psiSum ≤ C ≤ √2·psiSum  (sharp sandwich)
    5. DeletionIdentity.lean Σ_e T_f(G-e) = (m-1)T_f(G) - C_f(G)
  plus the shared definitions (Defs.lean) and the analytic kernel lemmas (Kernel.lean).
-/
import StarTheorem.Defs
import StarTheorem.Kernel
import StarTheorem.StarMax
import StarTheorem.ZeroIff
import StarTheorem.Regular
import StarTheorem.Sandwich
import StarTheorem.DeletionIdentity
import StarTheorem.Zagreb
import StarTheorem.StarEquality
-- explorations A1/A3 (added after the frozen v4.0 baseline; existing files untouched)
import StarTheorem.A1EdgeTypes
import StarTheorem.A3Delta
