import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.RatHurewicz.Bridge.SimChainMap
import Submission.Work.SSSR.RatHurewicz.Bridge.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.RatHurewicz
open Work.RatHurewicz.Bridge
variable {R : Type} [CommRing R] [Nontrivial R]

open scoped unitInterval Topology Simplicial
open CategoryTheory AlgebraicTopology
open Work.SSSR.Stems.Cubical
namespace Work.SSSR.RatHurewicz.Bridge

noncomputable section

/-- The `y`-coordinate of `stdSimplex.map f z` vanishes when no `x` is mapped to `y`. -/
theorem stdSimplex_map_eq_zero_of_ne {a b : ℕ} (f : Fin a → Fin b)
    (z : stdSimplex ℝ (Fin a)) (y : Fin b) (hy : ∀ x, f x ≠ y) :
    (stdSimplex.map f z) y = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [if_neg]
  exact fun h => hy x h

/-- The `i`-th coordinate of the `i`-th coface vanishes. -/
theorem coface_apply_self (m : ℕ) (i : Fin (m + 2)) (z : stdSimplex ℝ (Fin (m + 1))) :
    coface m i z i = 0 := by
  rw [coface_apply]
  exact stdSimplex_map_eq_zero_of_ne _ _ _ fun k => Fin.succAbove_ne i k

end

end Work.SSSR.RatHurewicz.Bridge
