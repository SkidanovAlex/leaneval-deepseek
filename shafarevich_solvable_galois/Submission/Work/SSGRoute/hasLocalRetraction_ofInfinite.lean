import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.ext_idele_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

/-- **Every archimedean place admits a local retraction.**

At an infinite place `w` the local units `𝒪_wˣ` are, by definition, *all* of `K_wˣ`
(`NK.GlobalCFT.Place.localUnits_ofInfinite`), so the `D_w`-equivariant inclusion
`𝒪_wˣ ↪ K_wˣ` is an isomorphism of `Gal(K/k)`-representations and the required retraction is
its inverse. -/
theorem hasLocalRetraction_ofInfinite (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NumberField.InfinitePlace K) :
    Work.SSGRoute.HasLocalRetraction k K (NK.GlobalCFT.Place.ofInfinite w) := by
  let f : Additive (Place.localField K (Place.ofInfinite w))ˣ →ₗ[NK.HassePrinciple.CoeffInt]
      Additive ↥(Place.localUnits K (Place.ofInfinite w)) :=
    { toFun := fun u =>
        Additive.ofMul (⟨Additive.toMul u, trivial⟩ : ↥(Place.localUnits K (Place.ofInfinite w)))
      map_add' := by
        intro x y
        rw [toMul_add, ← ofMul_mul]
        congr 1
      map_smul' := by
        intro n x
        obtain ⟨z⟩ := n
        simp only [RingHom.id_apply, ULift.smul_def]
        rw [← ofMul_zpow]
        congr 1 }
  refine ⟨Rep.ofHom ⟨f, ?_⟩, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    rfl
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl

end Work.SSGRoute
