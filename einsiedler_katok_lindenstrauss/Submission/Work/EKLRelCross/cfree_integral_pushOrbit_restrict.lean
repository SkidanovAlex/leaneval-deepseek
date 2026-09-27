import Mathlib
import Submission.Work.EKLRelCross.LeafMeasDefs
import Submission.Work.EKLRelCross.measurableSet_orbImg
import Submission.Work.EKLRelCross.pushOrbit_apply_of_injective
import Submission.Work.EKLRelCross.pushOrbit_lintegral_eq

namespace Work.EKLRelCross

set_option linter.style.haveILetI false

open MeasureTheory

/-- **Change of variables for the orbit transport `pushOrbit`.**

For a closed subgroup `U ≤ SL₃(ℝ)` acting freely at `x` (the orbit map `u ↦ u • x` is injective
on `U`), a finite measure `ρ` on `X₃`, a Borel set `A ⊆ SL₃(ℝ)` and a bounded measurable
`F : X₃ → ℝ`, the integral of `F (· • x)` over `A` against the transported measure
`pushOrbit U x ρ` equals the integral of `F` over the orbit image `orbImg U x A` against `ρ`.

Indeed, the orbit map `φ : u ↦ u • x` is a continuous injection from the Polish group `U` into
`X₃`, hence a measurable embedding; writing `ψ` for a measurable left inverse of `φ`
(`MeasurableEmbedding.exists_measurable_extend`), the transport is
`pushOrbit U x ρ = (ρ.restrict (φ '' U)).map ψ`, and restricting to `A` gives
`(pushOrbit U x ρ).restrict A = (ρ.restrict (orbImg U x A)).map ψ`.  The change-of-variables
formula `integral_map` for `ψ` then reduces both sides to the integral of `F` over
`orbImg U x A`, where `ψ y • x = y` for `y` in the orbit image. -/
theorem cfree_integral_pushOrbit_restrict {U : Subgroup Work.EKLContract.SL3}
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    {x : Work.EKLContract.X3}
    (hinj : Function.Injective (fun u : U => ((u : Work.EKLContract.SL3) • x)))
    {ρ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsFiniteMeasure ρ]
    {A : Set Work.EKLContract.SL3} (hA : MeasurableSet A)
    {F : Work.EKLContract.X3 → ℝ} (hF : Measurable F) (hFb : ∃ C, ∀ y, |F y| ≤ C) :
    (∫ u in A, F (u • x) ∂(Work.EKLRelCross.pushOrbit U x ρ))
      = ∫ y in Work.EKLRelCross.orbImg U x A, F y ∂ρ := by
  haveI hSB : StandardBorelSpace Work.EKLContract.X3 := Work.EKLComp.X3Background.2.2.2.2
  haveI : PolishSpace Work.EKLContract.SL3 :=
    Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : PolishSpace U := hUcl.polishSpace
  -- The orbit map on `U`, and a measurable left inverse `ψ` of it.
  set φ : U → Work.EKLContract.X3 := fun u => (u : Work.EKLContract.SL3) • x with hφdef
  have hφcont : Continuous φ := by fun_prop
  have hφ : MeasurableEmbedding φ := hφcont.measurableEmbedding hinj
  obtain ⟨ψ, hψmeas, hψeq⟩ :=
    hφ.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨1⟩)
  have hψ : ∀ u : U, ψ (φ u) = u := fun u => congr_fun hψeq u
  set Ψ : Work.EKLContract.X3 → Work.EKLContract.SL3 :=
    fun y => (ψ y : Work.EKLContract.SL3) with hΨdef
  have hΨmeas : Measurable Ψ := continuous_subtype_val.measurable.comp hψmeas
  have hBmeas : MeasurableSet (Work.EKLRelCross.orbImg U x A) :=
    Work.EKLRelCross.measurableSet_orbImg hUcl hinj hA
  have hΨφ : ∀ u : U, Ψ (φ u) = (u : Work.EKLContract.SL3) := fun u => by
    show ((ψ (φ u) : U) : Work.EKLContract.SL3) = (u : Work.EKLContract.SL3)
    rw [hψ u]
  have hΨsmul : ∀ (u : Work.EKLContract.SL3) (hu : u ∈ (U : Set Work.EKLContract.SL3)),
      Ψ (u • x) = u := fun u hu => hΨφ ⟨u, hu⟩
  -- On the orbit image of `A`, `Ψ` is a right inverse of the orbit map.
  have hψx : ∀ y ∈ Work.EKLRelCross.orbImg U x A, Ψ y • x = y := by
    intro y hy
    rw [Work.EKLRelCross.mem_orbImg] at hy
    obtain ⟨u, _huA, huU, huy⟩ := hy
    have h1 : Ψ y = u := by
      rw [← huy]
      exact hΨsmul u huU
    rw [h1, huy]
  -- The transport, restricted to `A`, is the pushforward under `Ψ` of `ρ` restricted to
  -- the orbit image of `A`.
  have hmeas_eq : (Work.EKLRelCross.pushOrbit U x ρ).restrict A
      = (ρ.restrict (Work.EKLRelCross.orbImg U x A)).map Ψ := by
    ext C hC
    have hkey : (fun u : Work.EKLContract.SL3 => u • x) ''
          (C ∩ A ∩ (U : Set Work.EKLContract.SL3))
        = Ψ ⁻¹' C ∩ Work.EKLRelCross.orbImg U x A := by
      rw [Work.EKLRelCross.orbImg]
      ext y
      constructor
      · rintro ⟨u, ⟨⟨huC, huA⟩, huU⟩, rfl⟩
        refine ⟨?_, ⟨u, ⟨huA, huU⟩, rfl⟩⟩
        show Ψ (u • x) ∈ C
        rw [hΨsmul u huU]
        exact huC
      · rintro ⟨hyC, ⟨u, ⟨huA, huU⟩, huy⟩⟩
        refine ⟨u, ⟨⟨?_, huA⟩, huU⟩, huy⟩
        have hΨu : Ψ y = u := by
          rw [← huy]
          exact hΨsmul u huU
        simpa [hΨu] using hyC
    rw [MeasureTheory.Measure.restrict_apply hC, MeasureTheory.Measure.map_apply hΨmeas hC,
        MeasureTheory.Measure.restrict_apply (hC.preimage hΨmeas),
        Work.EKLRelCross.pushOrbit_apply_of_injective hUcl hinj ρ (hC.inter hA), hkey]
  -- `F (Ψ y • x) = F y` for `ρ`-a.e. `y` in the orbit image of `A`.
  have hae : ∀ᵐ y ∂(ρ.restrict (Work.EKLRelCross.orbImg U x A)), F (Ψ y • x) = F y := by
    rw [MeasureTheory.ae_restrict_iff' hBmeas]
    exact Filter.Eventually.of_forall fun y hy => by rw [hψx y hy]
  have hFcomp : Measurable (fun u : Work.EKLContract.SL3 => F (u • x)) :=
    hF.comp (by fun_prop : Continuous (fun u : Work.EKLContract.SL3 => u • x)).measurable
  rw [hmeas_eq, MeasureTheory.integral_map hΨmeas.aemeasurable hFcomp.aestronglyMeasurable]
  exact MeasureTheory.integral_congr_ae hae

end Work.EKLRelCross
