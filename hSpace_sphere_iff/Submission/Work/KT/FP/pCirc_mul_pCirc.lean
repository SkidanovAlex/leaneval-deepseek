import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.Fund.SpectralAux
import Submission.Work.KT.Fund.circleIntegral_inv_sub_eq_zero_rev
import Submission.Work.KT.FP.pResA_mul_pResA
import Submission.Work.KT.FP.pCirc_mul_pCirc_iterated
import Submission.Work.KT.FP.swap_inv_sub_pResA

namespace Work.KT.FP

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-- **The two-circle computation for a linear pencil.**

With `F z = (z • A + B)⁻¹ * A = pResA A B z` and the pencil invertible on the closed annulus
`r ≤ ‖z‖ ≤ s` (`0 < r < s`),
`(∮_{|z|=r} F z) * (∮_{|w|=s} F w) = (2πi) • ∮_{|z|=r} F z`, i.e. the unnormalised product of the
Riesz projections at the two radii is `2πi` times the inner one (`P_r P_s = P_r` after dividing by
`2πi`).  This is the pencil analogue of `Work.KT.Fund.spectral_twoRadius`.

Route (verbatim adaptation of `Work.KT.Fund.spectral_twoRadius`,
`Work.KT.Fund.circA_mul_circB_iterated`, `Work.KT.Fund.swap_inv_sub_res` and
`Work.KT.Fund.circleIntegral_inv_sub_eq_zero_rev`, all in `Submission/Work/KT/Fund/`, with `ρ → r`,
`1 → s` and `Res b` replaced by `F`):

1. `pCirc A B r * pCirc A B s = ∮ z in C(0,r), ∮ w in C(0,s), F z * F w`
   (`circleIntegral_const_mul` / `circleIntegral_mul_const` + `circleIntegral.integral_congr`).
2. **Resolvent identity**: for units `z • A + B`, `w • A + B` with `z ≠ w`,
   `F z * F w = (w - z)⁻¹ • (F z - F w)`.  Proof: `(w - z) • (pRes z * A * pRes w) = pRes z - pRes w`
   from `pRes z * ((w • A + B) - (z • A + B)) * pRes w` (`Ring.mul_inverse_cancel`,
   `Ring.inverse_mul_cancel`), then multiply on the right by `A`.
3. For fixed `z` with `‖z‖ = r`, pointwise on `|w| = s`:
   `∮ w in C(0,s), F z * F w = (2πi) • F z - ∮ w in C(0,s), (w - z)⁻¹ • F w`
   (`circleIntegral.integral_sub_inv_of_mem_ball` for `z ∈ Metric.ball 0 s`, plus
   `circleIntegral.integral_smul_const`).
4. The correction term contributes `0`: Fubini (`Work.KT.Fund.circleIntegral_swap` for the
   continuous kernel `(w - z)⁻¹ • F w` on `Metric.sphere 0 r ×ˢ Metric.sphere 0 s`) turns it into
   `∮ w in C(0,s), (∮ z in C(0,r), (w - z)⁻¹) • F w`, and the inner integral vanishes by
   `Work.KT.Fund.circleIntegral_inv_sub_eq_zero_rev` since `r < ‖w‖ = s`.
5. Combine, using `circleIntegral.integral_sub`, `circleIntegral.integral_congr` and
   `circleIntegral.integral_smul`.

Continuity/integrability side conditions come from `hunit` (the pencil is a unit on the two circles)
and `ContinuousOn Ring.inverse {x | IsUnit x}` (`NormedRing.inverse_continuousAt`). -/
theorem pCirc_mul_pCirc {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hunit : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ s → IsUnit (z • A + B)) :
    pCirc A B r * pCirc A B s = (2 * Real.pi * Complex.I) • pCirc A B r := by
  have hrle : (0:ℝ) ≤ r := hr.le
  have hrsle : r ≤ s := hrs.le
  have h0s : (0:ℝ) ≤ s := hrle.trans hrsle
  -- membership description of the two circles
  have memr : ∀ z : ℂ, z ∈ Metric.sphere (0:ℂ) r → ‖z‖ = r := by
    intro z hz; simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have mems : ∀ w : ℂ, w ∈ Metric.sphere (0:ℂ) s → ‖w‖ = s := by
    intro w hw; simpa [Metric.mem_sphere, dist_eq_norm] using hw
  have hunitr : ∀ z ∈ Metric.sphere (0:ℂ) r, IsUnit (z • A + B) := by
    intro z hz
    have h := memr z hz
    exact hunit z (le_of_eq h.symm) (by rw [h]; exact hrsle)
  have hunits : ∀ w ∈ Metric.sphere (0:ℂ) s, IsUnit (w • A + B) := by
    intro w hw
    have h := mems w hw
    exact hunit w (by rw [h]; exact hrsle) (le_of_eq h)
  -- continuity and integrability of the pencil integrand on the two circles
  have hFr : ContinuousOn (fun z : ℂ => pResA A B z) (Metric.sphere (0:ℂ) r) :=
    pResA_continuousOn_sphere A B
      (fun z hz => hunit z (le_of_eq hz.symm) (by rw [hz]; exact hrsle))
  have hFs : ContinuousOn (fun w : ℂ => pResA A B w) (Metric.sphere (0:ℂ) s) :=
    pResA_continuousOn_sphere A B
      (fun w hw => hunit w (by rw [hw]; exact hrsle) (le_of_eq hw))
  have hInts : CircleIntegrable (fun w : ℂ => pResA A B w) 0 s := hFs.circleIntegrable h0s
  -- the two circles are disjoint
  have hzw : ∀ z ∈ Metric.sphere (0:ℂ) r, ∀ w ∈ Metric.sphere (0:ℂ) s, w ≠ z := by
    intro z hz w hw hcon
    have h1 := memr z hz
    have h2 := mems w hw
    rw [hcon, h1] at h2
    linarith
  -- integrability of the inner integrands, for each `z` on the inner circle
  have hinner1 : ∀ z ∈ Metric.sphere (0:ℂ) r,
      CircleIntegrable (fun w : ℂ => (w - z)⁻¹ • pResA A B z) 0 s := by
    intro z hz
    have hcont : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (Metric.sphere (0:ℂ) s) :=
      (continuousOn_id.sub continuousOn_const).inv₀
        (fun w hw => sub_ne_zero.mpr (hzw z hz w hw))
    exact (hcont.smul continuousOn_const).circleIntegrable h0s
  have hinner2 : ∀ z ∈ Metric.sphere (0:ℂ) r,
      CircleIntegrable (fun w : ℂ => (w - z)⁻¹ • pResA A B w) 0 s := by
    intro z hz
    have hcont : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (Metric.sphere (0:ℂ) s) :=
      (continuousOn_id.sub continuousOn_const).inv₀
        (fun w hw => sub_ne_zero.mpr (hzw z hz w hw))
    exact (hcont.smul hFs).circleIntegrable h0s
  -- the pointwise identity of integrands on the inner circle
  have hpoint : ∀ z ∈ Metric.sphere (0:ℂ) r,
      (∮ w in C(0, s), pResA A B z * pResA A B w) -
          ((2 * Real.pi * Complex.I) • pResA A B z)
        = -(∮ w in C(0, s), (w - z)⁻¹ • pResA A B w) := by
    intro z hz
    have h1 := hinner1 z hz
    have h2 := hinner2 z hz
    have hB : (∮ w in C(0, s), (w - z)⁻¹ • pResA A B z) =
        (2 * Real.pi * Complex.I) • pResA A B z := by
      have hball : z ∈ Metric.ball (0:ℂ) s := by
        rw [Metric.mem_ball, dist_zero_right, memr z hz]
        exact hrs
      rw [circleIntegral.integral_smul_const]
      rw [circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (R := s) (w := z) hball]
    have hA : (∮ w in C(0, s), pResA A B z * pResA A B w)
        = (2 * Real.pi * Complex.I) • pResA A B z
          - ∮ w in C(0, s), (w - z)⁻¹ • pResA A B w := by
      rw [← hB, ← circleIntegral.integral_sub h1 h2]
      refine circleIntegral.integral_congr h0s (fun w hw => ?_)
      rw [pResA_mul_pResA A B (hzw z hz w hw) (hunitr z hz) (hunits w hw), smul_sub]
    rw [hA]
    abel
  -- integrability of the two outer integrands
  have hF : CircleIntegrable
      (fun z : ℂ => ∮ w in C(0, s), pResA A B z * pResA A B w) 0 r := by
    have hF' : CircleIntegrable (fun z : ℂ => pResA A B z * pCirc A B s) 0 r :=
      (hFr.mul continuousOn_const).circleIntegrable hrle
    refine (circleIntegrable_congr (f₁ := fun z : ℂ => pResA A B z * pCirc A B s)
      (f₂ := fun z : ℂ => ∮ w in C(0, s), pResA A B z * pResA A B w) ?_).mp hF'
    intro z _
    exact (Work.KT.Fund.circleIntegral_const_mul (pResA A B z) (fun w : ℂ => pResA A B w) 0 s hInts).symm
  have hX : CircleIntegrable
      (fun z : ℂ => (2 * Real.pi * Complex.I) • pResA A B z) 0 r :=
    (continuousOn_const.smul hFr).circleIntegrable hrle
  -- the double integral of `(w - z)⁻¹ • pResA A B w` vanishes
  have hswap0 : (∮ z in C(0, r), ∮ w in C(0, s), (w - z)⁻¹ • pResA A B w) = 0 := by
    rw [swap_inv_sub_pResA A B hr hrs hunit]
    have hstep1 : (∮ w in C(0, s), ∮ z in C(0, r), (w - z)⁻¹ • pResA A B w)
        = ∮ w in C(0, s), (∮ z in C(0, r), (w - z)⁻¹) • pResA A B w := by
      refine circleIntegral.integral_congr h0s (fun w _ => ?_)
      exact circleIntegral.integral_smul_const (fun z : ℂ => (w - z)⁻¹) (pResA A B w) 0 r
    rw [hstep1]
    have hstep2 : (∮ w in C(0, s), (∮ z in C(0, r), (w - z)⁻¹) • pResA A B w)
        = ∮ w in C(0, s), (0:ℂ) • pResA A B w := by
      refine circleIntegral.integral_congr h0s (fun w hw => ?_)
      rw [Work.KT.Fund.circleIntegral_inv_sub_eq_zero_rev hr (by rw [mems w hw]; exact hrs)]
    rw [hstep2, circleIntegral.integral_smul]
    simp
  -- the difference of the two circle integrals vanishes
  have hdiff : (∮ z in C(0, r), ∮ w in C(0, s), pResA A B z * pResA A B w)
      - (∮ z in C(0, r), (2 * Real.pi * Complex.I) • pResA A B z) = 0 := by
    rw [← circleIntegral.integral_sub hF hX]
    rw [circleIntegral.integral_congr hrle (fun z hz => hpoint z hz)]
    have hz0 : (∮ z in C(0, r), -(∮ w in C(0, s), (w - z)⁻¹ • pResA A B w))
        = (-1:ℂ) • (∮ z in C(0, r), ∮ w in C(0, s), (w - z)⁻¹ • pResA A B w) := by
      rw [← circleIntegral.integral_smul]
      refine circleIntegral.integral_congr hrle (fun z _ => ?_)
      simp
    rw [hz0, hswap0, smul_zero]
  -- conclude
  have hfinal : (∮ z in C(0, r), ∮ w in C(0, s), pResA A B z * pResA A B w)
      = (2 * Real.pi * Complex.I) • pCirc A B r := by
    rw [sub_eq_zero.mp hdiff, circleIntegral.integral_smul]
    rfl
  rw [pCirc_mul_pCirc_iterated A B hr hrs hunit]
  exact hfinal

end

end Work.KT.FP
