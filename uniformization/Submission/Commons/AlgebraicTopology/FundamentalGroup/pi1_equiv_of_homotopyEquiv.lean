import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

noncomputable section

open CategoryTheory FundamentalGroupoid
open scoped FundamentalGroupoid unitInterval ContinuousMap

namespace Commons.AlgebraicTopology.FundamentalGroup

/-- A homotopy equivalence of topological spaces induces an equivalence between their
fundamental groupoids. -/
def fundamentalGroupoidEquivOfHomotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (hequiv : X ≃ₕ Y) :
    FundamentalGroupoid X ≌ FundamentalGroupoid Y := by
  apply CategoryTheory.Equivalence.mk (FundamentalGroupoid.map hequiv.toFun)
    (FundamentalGroupoid.map hequiv.invFun)
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using (asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso hequiv.left_inv.some)).symm
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso hequiv.right_inv.some)

/-- A homotopy equivalence induces an isomorphism of fundamental groups. -/
theorem pi1_equiv_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y (e.toFun x)) := by
  let E : FundamentalGroupoid X ≌ FundamentalGroupoid Y :=
    fundamentalGroupoidEquivOfHomotopyEquiv e
  exact ⟨(Equivalence.fullyFaithfulFunctor E).mulEquivEnd (FundamentalGroupoid.mk x)⟩

end Commons.AlgebraicTopology.FundamentalGroup