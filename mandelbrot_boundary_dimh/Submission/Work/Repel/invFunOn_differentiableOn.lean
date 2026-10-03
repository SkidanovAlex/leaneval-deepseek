import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

theorem invFunOn_differentiableOn {φ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hinj : Set.InjOn φ D) (hdiff : DifferentiableOn ℂ φ D) :
    DifferentiableOn ℂ (Function.invFunOn φ D) (φ '' D) := by
  intro w hw
  obtain ⟨z, hzD, rfl⟩ := hw
  -- φ is analytic at z and has nonvanishing derivative there (injectivity on an open set)
  have hφan : AnalyticAt ℂ φ z := hdiff.analyticAt (hD.mem_nhds hzD)
  obtain ⟨r₀, hr₀pos, hr₀sub⟩ := Metric.isOpen_iff.mp hD z hzD
  have hderiv : deriv φ z ≠ 0 :=
    Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr₀pos hφan (hinj.mono hr₀sub)
  -- the local inverse provided by the inverse function theorem
  let r : ℂ → ℂ := HasStrictDerivAt.localInverse φ (deriv φ z) z hφan.hasStrictDerivAt hderiv
  have hran : AnalyticAt ℂ r (φ z) := hφan.analyticAt_localInverse hderiv
  have hr_diff : DifferentiableAt ℂ r (φ z) := hran.differentiableAt
  have hright : ∀ᶠ y in 𝓝 (φ z), φ (r y) = y :=
    hφan.hasStrictDerivAt.eventually_right_inverse hderiv
  have hleft : ∀ᶠ x in 𝓝 z, r (φ x) = x :=
    hφan.hasStrictDerivAt.eventually_left_inverse hderiv
  have hrw : r (φ z) = z := hleft.self_of_nhds
  have hrwD : r (φ z) ∈ D := by rw [hrw]; exact hzD
  have hmem : ∀ᶠ y in 𝓝 (φ z), r y ∈ D :=
    hran.continuousAt.eventually (hD.mem_nhds hrwD)
  have hagree : (Function.invFunOn φ D) =ᶠ[𝓝[φ '' D] (φ z)] r := by
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds,
      hright.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hymem hyright hyimg
    obtain ⟨x, hxD, hxy⟩ := hyimg
    have hinv_mem : Function.invFunOn φ D y ∈ D := Function.invFunOn_mem ⟨x, hxD, hxy⟩
    have hinv_apply : φ (Function.invFunOn φ D y) = y := Function.invFunOn_eq ⟨x, hxD, hxy⟩
    exact hinj hinv_mem hymem (by rw [hinv_apply, hyright])
  exact (hagree.differentiableWithinAt_iff_of_mem (Set.mem_image_of_mem φ hzD)).mpr
    hr_diff.differentiableWithinAt

end Work.Repel
