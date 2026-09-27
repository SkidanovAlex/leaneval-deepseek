import Mathlib
import Submission.Work.EKLRelCross.LeafMeasDefs

set_option linter.style.haveILetI false

namespace Work.EKLRelCross

open MeasureTheory Topology
open Work.EKLContract

/-- **The orbit image of a Borel set of group elements is Borel.**  If `U ≤ SL₃(ℝ)` is a closed
subgroup, `x ∈ X₃` is a point at which the orbit map `u ↦ u • x` is injective, and `B ⊆ SL₃(ℝ)`
is Borel, then `orbImg U x B = (u ↦ u • x) '' (B ∩ U)` is a Borel subset of `X₃`.

The orbit map restricts to a continuous injection on the closed (hence Polish) subgroup `U`, and
`X₃` is a standard Borel space, so the Lusin–Souslin theorem applies:
`MeasurableSet.image_of_measurable_injOn` (the version for a measurable injection from a
standard Borel space into a countably separated measurable space, which needs no topology on the
target beyond its Borel structure). -/
theorem measurableSet_orbImg {U : Subgroup Work.EKLContract.SL3}
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    [StandardBorelSpace Work.EKLContract.X3] {x : Work.EKLContract.X3}
    (hinj : Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x))
    {B : Set Work.EKLContract.SL3} (hB : MeasurableSet B) :
    MeasurableSet (Work.EKLRelCross.orbImg U x B) := by
  -- `SL₃(ℝ)` is Polish, hence so is its closed subgroup `U`, and the orbit map on `U` is
  -- continuous and injective.
  haveI : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : PolishSpace U := hUcl.polishSpace
  have hcont : Continuous (fun u : U => (u : SL3) • x) := by fun_prop
  -- the source `{u : U | (u : SL₃(ℝ)) ∈ B}` is measurable, being the preimage of `B` under the
  -- (measurable) inclusion `U ↪ SL₃(ℝ)`.
  have hs : MeasurableSet ((↑) ⁻¹' B : Set U) :=
    hB.preimage continuous_subtype_val.measurable
  -- Lusin–Souslin, in its standard-Borel-source / countably-separated-target form.
  have himg : MeasurableSet ((fun u : U => (u : SL3) • x) '' ((↑) ⁻¹' B : Set U)) :=
    hs.image_of_measurable_injOn hcont.measurable hinj.injOn
  -- the image is exactly the orbit image of `B`.
  have hset : (fun u : U => (u : SL3) • x) '' ((↑) ⁻¹' B : Set U)
      = Work.EKLRelCross.orbImg U x B := by
    ext y
    rw [mem_orbImg]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u : SL3), hu, u.2, rfl⟩
    · rintro ⟨g, hgB, hgU, rfl⟩
      exact ⟨⟨g, hgU⟩, hgB, rfl⟩
  rwa [hset] at himg

end Work.EKLRelCross
