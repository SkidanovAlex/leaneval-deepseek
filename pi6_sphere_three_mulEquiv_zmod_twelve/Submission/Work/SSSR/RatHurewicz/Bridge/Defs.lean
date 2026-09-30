import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.SSSR.RatHurewicz.cubicalBridgeDefs
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.SSSR.Cohomology.Crux33.ezBridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.RatHurewicz
variable {R : Type} [CommRing R] [Nontrivial R]

open scoped unitInterval Topology Simplicial
open CategoryTheory AlgebraicTopology
namespace Work.SSSR.RatHurewicz.Bridge

open Work.SSSR.Stems.Cubical
noncomputable section

/-- The coface `Δⁿ → Δⁿ⁺¹` inserting a zero in position `i`. -/
def coface (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (Fin.succAbove i), stdSimplex.continuous_map _⟩

@[simp]
theorem coface_apply (n : ℕ) (i : Fin (n + 2)) (z : stdSimplex ℝ (Fin (n + 1))) :
    coface n i z = stdSimplex.map (Fin.succAbove i) z := rfl

end

end Work.SSSR.RatHurewicz.Bridge
