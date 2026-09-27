import Mathlib
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLComp.X3Background

namespace Work.EKLRelCross

open MeasureTheory
open Work.EKLContract

set_option linter.style.haveILetI false

/-- For a closed subgroup `U ≤ SL₃(ℝ)` whose orbit map `u ↦ u • x` is injective on `U`, the
transport `pushOrbit U x ν` of a measure `ν` on `X₃` computes, on a measurable set `B`, as the
`ν`-measure of the `U`-orbit piece over `B`:
`pushOrbit U x ν B = ν ((u ↦ u • x) '' (B ∩ U))`.

The orbit map is a continuous injection on the Polish space `U` (a closed subspace of the Polish
group `SL₃(ℝ)`), hence a measurable embedding (Lusin–Souslin), so `Measure.comap` along it really
is the pushforward under the inverse map. -/
theorem pushOrbit_apply_of_injective {U : Subgroup Work.EKLContract.SL3}
    (hU : IsClosed (U : Set Work.EKLContract.SL3)) [StandardBorelSpace Work.EKLContract.X3]
    {x : Work.EKLContract.X3}
    (hinj : Function.Injective (fun u : U => ((u : Work.EKLContract.SL3) • x)))
    (ν : MeasureTheory.Measure Work.EKLContract.X3) {B : Set Work.EKLContract.SL3}
    (hB : MeasurableSet B) :
    Work.EKLRelCross.pushOrbit U x ν B
      = ν ((fun u : Work.EKLContract.SL3 => u • x) '' (B ∩ (U : Set Work.EKLContract.SL3))) := by
  haveI : PolishSpace Work.EKLContract.SL3 :=
    Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : PolishSpace U := hU.polishSpace
  rw [pushOrbit, Measure.map_apply continuous_subtype_val.measurable hB]
  have hcont : Continuous (fun u : U => (u : Work.EKLContract.SL3) • x) := by fun_prop
  have hφ : MeasurableEmbedding (fun u : U => (u : Work.EKLContract.SL3) • x) :=
    hcont.measurableEmbedding hinj
  have hcomap : (Measure.comap (fun u : U => (u : Work.EKLContract.SL3) • x) ν)
        (Subtype.val ⁻¹' B)
      = ν ((fun u : U => (u : Work.EKLContract.SL3) • x) '' (Subtype.val ⁻¹' B)) :=
    Measure.comap_apply _ hinj (fun s hs => hφ.measurableSet_image' hs) ν
      (hB.preimage continuous_subtype_val.measurable)
  rw [hcomap]
  have hset : (fun u : U => ((u : Work.EKLContract.SL3) • x)) '' (Subtype.val ⁻¹' B)
      = (fun u : Work.EKLContract.SL3 => u • x)
          '' (B ∩ (U : Set Work.EKLContract.SL3)) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u : Work.EKLContract.SL3), ⟨hu, u.2⟩, rfl⟩
    · rintro ⟨u, ⟨huB, huU⟩, rfl⟩
      exact ⟨⟨u, huU⟩, huB, rfl⟩
  rw [hset]

end Work.EKLRelCross
