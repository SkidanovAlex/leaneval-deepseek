import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open Filter Set
open scoped Topology

namespace Work.NN.Core

/-- A smooth function `η` which vanishes as soon as one coordinate modulus reaches `r j`, multiplied
by a function `u` that is `C¹` on the polydisc of multiradius `ρ > r`, is globally `C¹`. -/
theorem contDiff_one_mul_of_support {n : ℕ} {u : Cn n → ℂ} {η : Cn n → ℝ} {ρ r : Fin n → ℝ}
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hηr : ∀ z, (∃ j, r j ≤ ‖z j‖) → η z = 0)
    (hrρ : ∀ j, r j < ρ j) (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ)) :
    ContDiff ℝ 1 (fun z => (η z : ℂ) * u z) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Work.CR.Flat.polydisc 0 ρ
  · -- `x` is strictly inside the polydisc: both factors are `C¹` at `x`.
    have hux : ContDiffAt ℝ 1 u x :=
      hu.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hx)
    have hηC : ContDiffAt ℝ 1 (fun z : Cn n => (η z : ℂ)) x := by
      have h1 : ContDiff ℝ 1 η := hη.of_le (by simp)
      have h2 : ContDiff ℝ 1 (⇑Complex.ofRealCLM ∘ η) :=
        (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1) Complex.ofRealCLM).comp h1
      simpa [Function.comp_def, Complex.ofRealCLM_apply] using h2.contDiffAt
    exact hηC.mul hux
  · -- `x` lies at or beyond the boundary: some coordinate modulus is `≥ ρ j > r j`, and `η`
    -- vanishes on the whole open set where that coordinate modulus exceeds `r j`.
    simp only [Work.CR.Flat.mem_polydisc, Pi.zero_apply, sub_zero] at hx
    push Not at hx
    obtain ⟨j, hj⟩ := hx
    have hlt : r j < ‖x j‖ := lt_of_lt_of_le (hrρ j) hj
    have hopen : IsOpen {z : Cn n | r j < ‖z j‖} :=
      isOpen_Ioi.preimage (continuous_apply j).norm
    have hnhds : {z : Cn n | r j < ‖z j‖} ∈ 𝓝 x := hopen.mem_nhds hlt
    have hev : (fun z : Cn n => (η z : ℂ) * u z) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hnhds] with z hz
      rw [hηr z ⟨j, le_of_lt hz⟩, Complex.ofReal_zero, zero_mul]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

end Work.NN.Core
