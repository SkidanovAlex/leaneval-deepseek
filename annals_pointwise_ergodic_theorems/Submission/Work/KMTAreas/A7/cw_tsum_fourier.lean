import Mathlib
import Submission.Work.KMTAreas.A7.SmallKernMassBasics

namespace Work.KMTAreas.A7

open MeasureTheory

open scoped FourierTransform

/-- **Poisson summation for the coefficient kernel `cw`.**

`cw m j = ∫_ℝ m(θ) e(-jθ) dθ` is the Fourier transform of `m` at the integer frequency `j`
(`cw_eq_fourierTransform`), and Poisson summation identifies the sum of the Fourier transform
against the characters with the periodisation of `m`: for a `C²` compactly supported `m` and any
lift `x : ℝ` of a point of the circle,

`∑_j cw m j e(jx) = ∑_k m(x + k)`.

This is the statement of `cw_tsum_fourier` with the periodisation written out at a chosen lift. -/
theorem tsum_cw_mul_fourier_of_lift {m : ℝ → ℂ} (hm : ContDiff ℝ 2 m)
    (hcs : HasCompactSupport m) (x : ℝ) :
    ∑' j : ℤ, cw m j * fourier (T := 1) j (x : Work.Analysis.IonescuWainger.Circle)
      = ∑' k : ℤ, m (x + k) := by
  -- 1. Absolute summability of the coefficients
  have hsum_cw : Summable fun j : ℤ => ‖cw m j‖ :=
    summable_cw_of_contDiff_hasCompactSupport hm hcs
  have hsum : Summable fun j : ℤ => 𝓕 m (j : ℝ) := by
    refine Summable.of_norm ?_
    simpa only [cw_eq_fourierTransform] using hsum_cw
  -- 2. `m` decays at infinity, being compactly supported
  have hbig : m =O[Filter.cocompact ℝ] (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    have hme : m =ᶠ[Filter.cocompact ℝ] 0 := by
      simpa using (hasCompactSupport_iff_eventuallyEq.mp hcs)
    filter_upwards [hme] with y hy
    simp only [Pi.zero_apply] at hy
    rw [hy]
    simp only [norm_zero, one_mul]
    exact norm_nonneg _
  -- 3. Poisson summation
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (f := m) hm.continuous
    (b := 2) one_lt_two hbig hsum x
  rw [hp]
  refine tsum_congr fun j => ?_
  rw [cw_eq_fourierTransform]

theorem cw_tsum_fourier {m : ℝ → ℂ} (hm : ContDiff ℝ 2 m) (hcs : HasCompactSupport m)
    (θ : Work.Analysis.IonescuWainger.Circle) :
    ∑' j : ℤ, Work.KMTAreas.A7.cw m j * fourier (T := 1) j θ
      = Work.Analysis.IonescuWainger.periodize m θ := by
  rw [Work.Analysis.IonescuWainger.periodize]
  have h := tsum_cw_mul_fourier_of_lift hm hcs ((AddCircle.equivIco (1 : ℝ) 0 θ).val)
  rwa [AddCircle.coe_equivIco] at h

end Work.KMTAreas.A7
