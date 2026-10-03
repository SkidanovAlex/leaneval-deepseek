import Mathlib
import Submission.Work.FIArea6Road.TauHeartDefs

namespace Work.FIArea6Road

open MeasureTheory intervalIntegral Filter
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The `ℓ`-th Fourier summand `e^{iℓβ}` is `2π`-periodic in `β`. -/
lemma exp_int_mul_I_add_two_pi (ℓ : ℤ) (β : ℝ) :
    Complex.exp ((ℓ : ℂ) * Complex.I * ((β + 2 * Real.pi : ℝ) : ℂ)) =
      Complex.exp ((ℓ : ℂ) * Complex.I * (β : ℂ)) := by
  have hcast : ((β + 2 * Real.pi : ℝ) : ℂ) = (β : ℂ) + 2 * (Real.pi : ℂ) := by
    push_cast; ring
  rw [show (ℓ : ℂ) * Complex.I * ((β + 2 * Real.pi : ℝ) : ℂ)
      = (ℓ : ℂ) * Complex.I * (β : ℂ) + (ℓ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by
    rw [hcast]; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The series `fser q` is `2π`-periodic. -/
lemma fser_add_two_pi (q : ℝ → ℝ) (β : ℝ) :
    fser q (β + 2 * Real.pi) = fser q β := by
  rw [fser, fser]
  exact tsum_congr (fun ℓ => by rw [exp_int_mul_I_add_two_pi])

/-- **Pointwise Fourier inversion on the period.**  For a `C²` mollifier `q` supported in
`[0, 2πθ]` with `θ < 1`, and for every `α ∈ [0, 2π]`, the Fourier series
`Σ_ℓ q̂(ℓ) e^{iℓα}` sums to `q α`. -/
lemma hasSum_fser_of_mem_Icc (q : ℝ → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2)
    {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2 * Real.pi) :
    HasSum (fun ℓ : ℤ =>
        Work.FIArea5.S16.fcoef q ℓ * Complex.exp ((ℓ : ℂ) * Complex.I * α))
      ((q α : ℝ) : ℂ) := by
  have hθ1' : θ ≤ 1 := le_of_lt hθ1
  have h2πθ : 2 * Real.pi * θ ≤ 2 * Real.pi := by nlinarith [hθ, hθ1, Real.pi_pos]
  obtain ⟨hv1, hv2, _, _, _, _⟩ := Work.FIArea6.q_vanish_support q θ hqC hqsupp
  have hq_0 : q 0 = 0 := hv1 0 le_rfl
  have hq_2π : q (2 * Real.pi) = 0 := hv2 (2 * Real.pi) h2πθ
  -- the `2π`-periodic extension of `q`
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIoc (2 * Real.pi) 0 (fun x => (q x : ℂ)),
      AddCircle.liftIoc_zero_continuous (by simp [hq_0, hq_2π])
        (Complex.continuous_ofReal.comp hqC.continuous).continuousOn⟩
  have hFcoeff : ∀ ℓ : ℤ, fourierCoeff (⇑F) ℓ = Work.FIArea5.S16.fcoef q ℓ := by
    intro ℓ
    rw [Work.FIArea5.S16.fcoef]
    show fourierCoeff (AddCircle.liftIoc (2 * Real.pi) 0 (fun x => (q x : ℂ))) ℓ = _
    rw [fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral]
    simp only [zero_add, sub_zero, Complex.real_smul]
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) from by push_cast; ring]
    apply congrArg (fun z => ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
    apply intervalIntegral.integral_congr
    intro x _
    simp only [fourier_coe_apply, smul_eq_mul, zero_add, sub_zero]
    rw [show (2 * ↑Real.pi * Complex.I * ↑(-ℓ) * ↑x / ↑(2 * Real.pi))
        = -(ℓ : ℂ) * Complex.I * ↑x from by push_cast; field_simp]
    ring
  have hFsumm : Summable (fun ℓ : ℤ => fourierCoeff (⇑F) ℓ) := by
    have h := Work.FIArea5.S16.fcoef_summable q θ hθ hθ1' hqC hq0 hq1 hqsupp hd2
    exact h.congr (fun ℓ => (hFcoeff ℓ).symm)
  have hFx : F ((α : ℝ) : AddCircle (2 * Real.pi)) = (q α : ℂ) := by
    show (AddCircle.liftIoc (2 * Real.pi) 0 (fun x => (q x : ℂ)))
        ((α : ℝ) : AddCircle (2 * Real.pi)) = (q α : ℂ)
    exact Work.FIArea5.S16.liftIoc_eval q hq_0 hq_2π α hα hα2
  have hpt : HasSum (fun i => fourierCoeff (⇑F) i • fourier i ((α : ℝ) : AddCircle (2 * Real.pi)))
      (F ((α : ℝ) : AddCircle (2 * Real.pi))) :=
    has_pointwise_sum_fourier_series_of_summable hFsumm _
  rw [hFx] at hpt
  refine hpt.congr_fun (fun i => ?_)
  show Work.FIArea5.S16.fcoef q i * Complex.exp ((i : ℂ) * Complex.I * α)
    = fourierCoeff (⇑F) i • fourier i ((α : ℝ) : AddCircle (2 * Real.pi))
  rw [hFcoeff i, fourier_coe_apply, smul_eq_mul]
  congr 1
  rw [show (2 * ↑Real.pi * Complex.I * ↑i * ↑α / ↑(2 * Real.pi))
      = (i : ℂ) * Complex.I * ↑α from by push_cast; field_simp]

/-- The periodisation identity on the closed period `[0, 2π]`. -/
lemma fser_eq_of_mem_Icc (q : ℝ → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2)
    {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2 * Real.pi) :
    fser q α = (q α : ℂ) := by
  have h := hasSum_fser_of_mem_Icc q hθ hθ1 hqC hq0 hq1 hqsupp hd2 hα hα2
  rw [fser]
  exact h.tsum_eq

/-- **The periodisation of the angle mollifier `q` agrees with `q` on the range that occurs.**

For a `C²` mollifier `q` supported in `[0, 2πθ]` with `θ < 1`, and for every `β ∈ (−2π+2πθ, 2π]`,
the Fourier series `Σ_ℓ q̂(ℓ)e^{iℓβ}` (`Work.FIArea6Road.fser`, absolutely convergent by
`Work.FIArea5.S16.fcoef_summable`) converges to `q β`.

Route: on `[0,2π]` this is the pointwise Fourier inversion for the `2π`-periodic extension of `q`
(as in `Work.FIArea5.S16.fourier_truncation`, which builds `AddCircle.liftIoc (2*π) 0 (q ·)` and
proves `fourierCoeff F ℓ = fcoef q ℓ`, `Summable`, and `q 0 = q (2π) = 0` using `θ < 1`; conclude
with `has_pointwise_sum_fourier_series_of_summable`).  For `β ∈ (−2π+2πθ, 0)` use the `2π`-periodicity
of the series (`β + 2π ∈ (2πθ, 2π)`, where `q (β+2π) = 0 = q β` by the support condition). -/
theorem TauHeartFserEqQ (q : ℝ → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2)
    {β : ℝ} (hβ : β ∈ Set.Ioc (-(2 * Real.pi) + 2 * Real.pi * θ) (2 * Real.pi)) :
    Work.FIArea6Road.fser q β = (q β : ℂ) := by
  rw [Set.mem_Ioc] at hβ
  obtain ⟨hβlo, hβhi⟩ := hβ
  rcases le_or_gt (0 : ℝ) β with hβ0 | hβneg
  · exact fser_eq_of_mem_Icc q hθ hθ1 hqC hq0 hq1 hqsupp hd2 hβ0 hβhi
  · -- `β < 0`: the series is `2π`-periodic, and `q` vanishes at both `β` and `β + 2π`
    have hqβ : q β = 0 := by
      by_contra hc
      exact absurd (hqsupp β hc).1 (not_le.mpr hβneg)
    have hqβ2 : q (β + 2 * Real.pi) = 0 := by
      by_contra hc
      have hle : β + 2 * Real.pi ≤ 2 * Real.pi * θ := (hqsupp (β + 2 * Real.pi) hc).2
      linarith
    have hmem : 0 ≤ β + 2 * Real.pi ∧ β + 2 * Real.pi ≤ 2 * Real.pi := by
      have hpos : 0 < 2 * Real.pi * θ := mul_pos (by positivity) hθ
      exact ⟨by linarith, by linarith⟩
    have hpt : fser q (β + 2 * Real.pi) = (q (β + 2 * Real.pi) : ℂ) :=
      fser_eq_of_mem_Icc q hθ hθ1 hqC hq0 hq1 hqsupp hd2 hmem.1 hmem.2
    rw [← fser_add_two_pi q β, hpt, hqβ2, hqβ]

end

end Work.FIArea6Road
