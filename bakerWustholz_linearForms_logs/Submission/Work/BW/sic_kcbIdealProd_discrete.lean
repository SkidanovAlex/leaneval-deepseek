import Mathlib
import Submission.Work.BW.kcb_lat_defs
import Submission.Work.BW.sieg2KernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Discreteness of the ideal-product lattice `kcbIdealProd`

For a number field `F` and a finite family `I : Fin M → (FractionalIdeal (𝓞 F)⁰ F)ˣ` of
fractional ideals, the product lattice

  `kcbIdealProd I = ∏ i, kcbIdealE (I i) ⊆ Fin M → KE F`

is discrete.

Each factor `kcbIdealE (I i)` is the pullback of the ideal lattice `idealLattice F (I i)`
(Mathlib's `NumberField.mixedEmbedding.idealLattice`, which is a full `ℤ`-lattice of the mixed
space, hence discrete) along the continuous linear equivalence
`NumberField.mixedEmbedding.euclidean.toMixed F`; by
`ZLattice.comap_discreteTopology` it is discrete as well.

A finite product of discrete lattices is discrete: the natural coordinate map from
`↥(kcbIdealProd I)` onto `∏ i, ↥(kcbIdealE (I i))` is continuous and injective, the latter is
discrete by `Pi.discreteTopology`, and a space admitting a continuous injective map into a
discrete space is discrete (`DiscreteTopology.of_continuous_injective`).
-/

set_option linter.style.haveILetI false

open scoped Classical
open NumberField MeasureTheory

namespace Work.BW

theorem sic_kcbIdealProd_discrete {F : Type*} [Field F] [NumberField F] {M : ℕ}
    (I : Fin M → (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)ˣ) :
    DiscreteTopology ↥(Work.BW.kcbIdealProd (F := F) I) := by
  -- Each factor of the product is a lattice, hence discrete.
  have hS : ∀ i, DiscreteTopology ↥(kcbIdealE (F := F) (I i)) := fun i =>
    ZLattice.comap_discreteTopology ℝ (NumberField.mixedEmbedding.idealLattice F (I i))
      (NumberField.mixedEmbedding.euclidean.toMixed F).continuous
      (NumberField.mixedEmbedding.euclidean.toMixed F).injective
  haveI := hS
  -- A finite product of discrete spaces is discrete.
  haveI hpi : DiscreteTopology (∀ i, ↥(kcbIdealE (F := F) (I i))) := inferInstance
  -- The coordinate map `↥(∏ i, kcbIdealE (I i)) → ∏ i, ↥(kcbIdealE (I i))`.
  let f : ↥(Work.BW.kcbIdealProd (F := F) I) → (∀ i, ↥(kcbIdealE (F := F) (I i))) :=
    fun x i => ⟨(x : Fin M → KE F) i, (Submodule.mem_pi.mp x.2) i (Set.mem_univ i)⟩
  have hc : Continuous f := by
    apply continuous_pi
    intro i
    exact Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val)
      (fun x => (Submodule.mem_pi.mp x.2) i (Set.mem_univ i))
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  exact DiscreteTopology.of_continuous_injective hc hinj

end Work.BW
