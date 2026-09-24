import Mathlib
import Submission.Work.Kernel.GreenCover

/-!
# Chart-wise `C¹`-regularity of `χ * (Θ ∘ g)` for `g` harmonic and `χ` supported in the domain

Let `E` be a chart-ball cover of the surface, `gA` the Green function of `Ω` with pole `a`,
`χ` a weight whose (topological) support lies in `Ω` and which is `C¹` in every chart of the
cover, and `Θ` a `C¹` function of one real variable.

Then away from the pole `a` the product `χ · (Θ ∘ gA)` is `C¹` in every chart of the cover.

The substance is that `gA`, being harmonic off its pole, is `C²` in the *preferred* chart at
each point (`InnerProductSpace.HarmonicAt` *contains* `ContDiffAt ℝ 2`), so that chart
independence of harmonicity (`Submission.HarmonicOnXAt_iff_chart`) gives the `C²` (hence `C¹`)
regularity of the representative in any chart of the cover.  Off `Ω` the weight vanishes on a
neighbourhood of the point and the product is locally zero.
-/

open Set Filter

namespace Work.Kernel

/-- **Chart-wise `C¹`-regularity of `χ · (Θ ∘ gA)` off the pole.** -/
theorem contDiffAt_chartPullback_mul_comp_of_harmonic {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : Work.Kernel.GreenCover ι Ω K a b)
    {χ gA : X → ℝ} {Θ : ℝ → ℝ}
    (hχc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hχΩ : tsupport χ ⊆ Ω)
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA) (hΘ : ContDiff ℝ 1 Θ) :
    ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source, x ≠ a →
      ContDiffAt ℝ 1 ((fun y => χ y * Θ (gA y)) ∘ (chartAt ℂ (E.y k)).symm)
        ((chartAt ℂ (E.y k)) x) := by
  intro k x hx hxa
  by_cases hxχ : x ∈ tsupport χ
  · -- At a point of `Ω \ {a}` both factors are `C¹` in the chart: `χ` by hypothesis, and
    -- `Θ ∘ gA` because `gA` is harmonic (hence `C²`) there.
    have hxΩ : x ∈ Ω := hχΩ hxχ
    have hharmx : Submission.HarmonicOnXAt gA x :=
      hgA.2.1 x ⟨hxΩ, by simpa using hxa⟩
    have hgAc2 : ContDiffAt ℝ 2 (gA ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) :=
      ((Submission.HarmonicOnXAt_iff_chart (u := gA) (x := x) (y := E.y k) hx).mp hharmx).1
    have hgAc1 : ContDiffAt ℝ 1 (gA ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) :=
      hgAc2.of_le (by norm_num)
    have hΘc : ContDiffAt ℝ 1 Θ
        ((gA ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x)) := hΘ.contDiffAt
    have hcomp : ContDiffAt ℝ 1 (Θ ∘ (gA ∘ (chartAt ℂ (E.y k)).symm))
        ((chartAt ℂ (E.y k)) x) := hΘc.comp _ hgAc1
    exact (hχc1 k x hx).mul hcomp
  · -- Off the support of `χ` the product is identically zero near the point.
    have hχ0 : χ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxχ] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hxtgt : (chartAt ℂ (E.y k)) x ∈ (chartAt ℂ (E.y k)).target :=
      (chartAt ℂ (E.y k)).map_source hx
    have hcont : ContinuousAt (chartAt ℂ (E.y k)).symm ((chartAt ℂ (E.y k)) x) :=
      (chartAt ℂ (E.y k)).continuousAt_symm hxtgt
    have hEq : nhds ((chartAt ℂ (E.y k)).symm ((chartAt ℂ (E.y k)) x)) = nhds x :=
      congrArg nhds ((chartAt ℂ (E.y k)).left_inv hx)
    have hEv : ∀ᶠ w in nhds ((chartAt ℂ (E.y k)) x),
        χ ((chartAt ℂ (E.y k)).symm w) = 0 :=
      hcont.eventually (by rw [hEq]; exact hχ0)
    have hev : ((fun y => χ y * Θ (gA y)) ∘ (chartAt ℂ (E.y k)).symm)
        =ᶠ[nhds ((chartAt ℂ (E.y k)) x)] 0 := by
      filter_upwards [hEv] with w hw
      change χ ((chartAt ℂ (E.y k)).symm w) * Θ (gA ((chartAt ℂ (E.y k)).symm w)) = 0
      rw [hw, zero_mul]
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev

end Work.Kernel
