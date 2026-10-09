import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_level_lift

/-!
# The canonical lift onto free generators is an epimorphism

For every `G`-representation `M` of the coefficient ring `Coeff = ℤ`, the representation
morphism

`Rep.freeLift Coeff G M (fun m : M.V => m) : Rep.free Coeff G M.V ⟶ M`

is surjective on the underlying types, hence an epimorphism of `Rep Coeff G`.  The generator
`Finsupp.single y (MonoidAlgebra.single 1 1)` of the free representation is mapped to
`1 • M.ρ 1 y = y`, so every `y : M.V` lies in the image.
-/

namespace Work.SSGRoute

open CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- The value of the canonical free lift `Rep.freeLift Coeff G M (fun m => m)` at the free
generator supported at `y` with coefficient `1`. -/
theorem freeLift_id_apply (G : Type) [Group G] (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (y : M.V) :
    (Rep.freeLift (k := SSGRoute.PTExt.Coeff) (G := G) M (fun m : M.V => m))
      (Finsupp.single y (MonoidAlgebra.single 1 1)) = y := by
  change (M.ρ.freeLift (fun m : M.V => m))
      (Finsupp.single y (MonoidAlgebra.single 1 1)) = y
  rw [Representation.freeLift_single_single]
  simp
  exact @one_smul SSGRoute.PTExt.Coeff M.V _ (M.hV2.toMulAction) y

theorem freeLift_id_epi (G : Type) [Group G] (M : Rep.{0} SSGRoute.PTExt.Coeff G) :
    CategoryTheory.Epi (Rep.freeLift SSGRoute.PTExt.Coeff G M (fun m : M.V => m)) := by
  rw [Rep.epi_iff_surjective]
  intro y
  exact ⟨Finsupp.single y (MonoidAlgebra.single 1 1), freeLift_id_apply G M y⟩

end Work.SSGRoute
