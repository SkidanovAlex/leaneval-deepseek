import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Group.Integral
import Submission.Commons.Analysis.Calculus.norm_sub_le_intervalIntegral_norm_deriv

open MeasureTheory Set
open scoped Interval

namespace Commons.Analysis.Calculus

/-- The second finite difference of `m` with step `h` is the integral of the difference of the
first derivatives shifted by `h`:
`m x - 2 m (x+h) + m (x+2h) = ∫ t in 0..h, (m' (x+t+h) - m' (x+t))`. -/
lemma second_difference_eq_integral (m : ℝ → ℂ) (h x : ℝ)
    (hd1 : Differentiable ℝ m) (hd2 : Differentiable ℝ (deriv m)) :
    m x - 2 * m (x + h) + m (x + 2 * h)
      = ∫ t in (0:ℝ)..h, (deriv m (x + t + h) - deriv m (x + t)) := by
  have hcont_deriv : Continuous (deriv m) := hd2.continuous
  have ha_int : IntervalIntegrable (fun t : ℝ => deriv m (x + t + h)) volume 0 h := by
    apply Continuous.intervalIntegrable
    exact hcont_deriv.comp ((continuous_const.add continuous_id).add continuous_const)
  have hb_int : IntervalIntegrable (fun t : ℝ => deriv m (x + t)) volume 0 h := by
    apply Continuous.intervalIntegrable
    exact hcont_deriv.comp (continuous_const.add continuous_id)
  have hderiv_a : ∀ t ∈ Set.uIcc (0:ℝ) h,
      HasDerivAt (fun t : ℝ => m (x + t + h)) (deriv m (x + t + h)) t := by
    intro t ht
    have hid : HasDerivAt (fun t : ℝ => x + t + h) 1 t := by
      simpa using (((hasDerivAt_id t).const_add x).add_const h)
    have hcomp := HasDerivAt.scomp t ((hd1 (x + t + h)).hasDerivAt) hid
    simpa [Function.comp_def] using hcomp
  have hderiv_b : ∀ t ∈ Set.uIcc (0:ℝ) h,
      HasDerivAt (fun t : ℝ => m (x + t)) (deriv m (x + t)) t := by
    intro t ht
    have hid : HasDerivAt (fun t : ℝ => x + t) 1 t := by
      simpa using ((hasDerivAt_id t).const_add x)
    have hcomp := HasDerivAt.scomp t ((hd1 (x + t)).hasDerivAt) hid
    simpa [Function.comp_def] using hcomp
  have hla : ∫ t in (0:ℝ)..h, deriv m (x + t + h) = m (x + 2 * h) - m (x + h) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_a ha_int]
    ring_nf
  have hlb : ∫ t in (0:ℝ)..h, deriv m (x + t) = m (x + h) - m x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_b hb_int]
    ring_nf
  rw [intervalIntegral.integral_sub ha_int hb_int, hla, hlb]
  ring

/-- Pointwise `ENNReal` form of the second difference estimate: for `h ≥ 0`,
`‖m x - 2 m (x+h) + m (x+2h)‖ ≤ ∫⁻ t in (x,x+h] ... ` written as the double integral of
`‖m''‖` over `[0,h]²`, shifted by `x`. This is the pointwise input to the global `L¹` bound. -/
lemma ofReal_norm_second_difference_le (m : ℝ → ℂ) (h x : ℝ) (hh : 0 ≤ h)
    (hd1 : Differentiable ℝ m) (hd2 : Differentiable ℝ (deriv m))
    (hint2 : Integrable (deriv (deriv m))) :
    ENNReal.ofReal ‖m x - 2 * m (x + h) + m (x + 2 * h)‖
      ≤ ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h,
          ENNReal.ofReal ‖deriv (deriv m) (x + t + s)‖ := by
  have hrepr := second_difference_eq_integral m h x hd1 hd2
  have hcont_deriv : Continuous (deriv m) := hd2.continuous
  have hnorm : ENNReal.ofReal ‖m x - 2 * m (x + h) + m (x + 2 * h)‖
      ≤ ENNReal.ofReal (∫ t in (0:ℝ)..h, ‖deriv m (x + t + h) - deriv m (x + t)‖) := by
    rw [hrepr]
    exact ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm hh)
  have hcontab : Continuous (fun t : ℝ => ‖deriv m (x + t + h) - deriv m (x + t)‖) :=
    ((hcont_deriv.comp ((continuous_const.add continuous_id).add continuous_const)).sub
      (hcont_deriv.comp (continuous_const.add continuous_id))).norm
  have hintab : IntervalIntegrable
      (fun t : ℝ => ‖deriv m (x + t + h) - deriv m (x + t)‖) volume 0 h :=
    hcontab.intervalIntegrable 0 h
  have hconv1 : ENNReal.ofReal (∫ t in (0:ℝ)..h, ‖deriv m (x + t + h) - deriv m (x + t)‖)
      = ∫⁻ t in Set.Ioc (0:ℝ) h,
          ENNReal.ofReal ‖deriv m (x + t + h) - deriv m (x + t)‖ := by
    rw [intervalIntegral.integral_of_le hh]
    exact ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mp hintab)
      (ae_of_all _ fun t => norm_nonneg _)
  have hpt : ∀ t, ENNReal.ofReal ‖deriv m (x + t + h) - deriv m (x + t)‖
      ≤ ∫⁻ s in Set.Ioc (0:ℝ) h, ENNReal.ofReal ‖deriv (deriv m) (x + t + s)‖ := by
    intro t
    have hreal : ‖deriv m (x + t + h) - deriv m (x + t)‖
        ≤ ∫ s in (0:ℝ)..h, ‖deriv (deriv m) (x + t + s)‖ := by
      have h := Commons.Analysis.Calculus.norm_sub_le_intervalIntegral_norm_deriv
        (u := fun s : ℝ => deriv m (x + t + s))
        (u' := fun s : ℝ => deriv (deriv m) (x + t + s)) (a := 0) (b := h) hh
        (fun s hs => by
          have hid : HasDerivAt (fun s : ℝ => x + t + s) 1 s := by
            simpa using ((hasDerivAt_id s).const_add (x + t))
          have hcomp := HasDerivAt.scomp s ((hd2 (x + t + s)).hasDerivAt) hid
          simpa [Function.comp_def] using hcomp)
        ((hint2.comp_add_left (x + t)).intervalIntegrable)
      simpa using h
    have hint2t : IntegrableOn (fun s : ℝ => ‖deriv (deriv m) (x + t + s)‖)
        (Set.Ioc 0 h) volume :=
      (hint2.norm.comp_add_left (x + t)).integrableOn
    have hconv2 : ENNReal.ofReal (∫ s in (0:ℝ)..h, ‖deriv (deriv m) (x + t + s)‖)
        = ∫⁻ s in Set.Ioc (0:ℝ) h, ENNReal.ofReal ‖deriv (deriv m) (x + t + s)‖ := by
      rw [intervalIntegral.integral_of_le hh]
      exact ofReal_integral_eq_lintegral_ofReal hint2t (ae_of_all _ fun s => norm_nonneg _)
    calc ENNReal.ofReal ‖deriv m (x + t + h) - deriv m (x + t)‖
        ≤ ENNReal.ofReal (∫ s in (0:ℝ)..h, ‖deriv (deriv m) (x + t + s)‖) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ∫⁻ s in Set.Ioc (0:ℝ) h, ENNReal.ofReal ‖deriv (deriv m) (x + t + s)‖ := hconv2
  calc ENNReal.ofReal ‖m x - 2 * m (x + h) + m (x + 2 * h)‖
      ≤ ENNReal.ofReal (∫ t in (0:ℝ)..h, ‖deriv m (x + t + h) - deriv m (x + t)‖) := hnorm
    _ = ∫⁻ t in Set.Ioc (0:ℝ) h,
          ENNReal.ofReal ‖deriv m (x + t + h) - deriv m (x + t)‖ := hconv1
    _ ≤ ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h,
          ENNReal.ofReal ‖deriv (deriv m) (x + t + s)‖ := lintegral_mono hpt

/-- Double sliding-window / Tonelli estimate: for a measurable `F : ℝ → ℝ≥0∞` and `h ≥ 0`,
`∫⁻ x, ∫⁻ t in (0,h], ∫⁻ s in (0,h], F (x + t + s) = h * h * ∫⁻ x, F x`. -/
private lemma double_window_aux {h : ℝ} {F : ℝ → ENNReal} (hF : Measurable F) :
    ∫⁻ x, ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s)
      = ENNReal.ofReal h * (ENNReal.ofReal h * ∫⁻ x, F x) := by
  set I : Set ℝ := Set.Ioc (0:ℝ) h with hI
  have hImeas : MeasurableSet I := by rw [hI]; exact measurableSet_Ioc
  have hstep1 : ∀ x : ℝ, (∫⁻ t in I, ∫⁻ s in I, F (x + t + s))
      = ∫⁻ z in I ×ˢ I, F (x + z.1 + z.2) := by
    intro x
    have hmeas1 : AEMeasurable (fun z : ℝ × ℝ => F (x + z.1 + z.2))
        (volume.restrict (I ×ˢ I)) := by
      have h0 : Measurable (fun z : ℝ × ℝ => F (x + z.1 + z.2)) := by fun_prop
      exact h0.aemeasurable.mono_measure (Measure.restrict_le_self)
    exact (setLIntegral_prod (μ := volume) (ν := volume) (s := I) (t := I)
      (f := fun z : ℝ × ℝ => F (x + z.1 + z.2)) hmeas1).symm
  have hL1 : ∫⁻ x, ∫⁻ t in I, ∫⁻ s in I, F (x + t + s)
      = ∫⁻ x, ∫⁻ z in I ×ˢ I, F (x + z.1 + z.2) :=
    lintegral_congr (fun x => hstep1 x)
  have hmeas2 : AEMeasurable (fun p : ℝ × (ℝ × ℝ) => F (p.1 + p.2.1 + p.2.2))
      (volume.restrict (Set.univ ×ˢ (I ×ˢ I))) := by
    have h0 : Measurable (fun p : ℝ × (ℝ × ℝ) => F (p.1 + p.2.1 + p.2.2)) := by fun_prop
    exact h0.aemeasurable.mono_measure (Measure.restrict_le_self)
  have hswap : (∫⁻ x, ∫⁻ z in I ×ˢ I, F (x + z.1 + z.2))
      = ∫⁻ z in I ×ˢ I, ∫⁻ x, F (x + z.1 + z.2) := by
    have e1 : (∫⁻ x, ∫⁻ z in I ×ˢ I, F (x + z.1 + z.2))
        = ∫⁻ x in (Set.univ : Set ℝ), ∫⁻ z in I ×ˢ I, F (x + z.1 + z.2) := by
      rw [setLIntegral_univ]
    rw [e1, (setLIntegral_prod (μ := volume) (ν := volume) (s := Set.univ)
      (t := I ×ˢ I) (f := fun p : ℝ × (ℝ × ℝ) => F (p.1 + p.2.1 + p.2.2)) hmeas2).symm,
      setLIntegral_prod_symm (μ := volume) (ν := volume) (s := Set.univ)
      (t := I ×ˢ I) (f := fun p : ℝ × (ℝ × ℝ) => F (p.1 + p.2.1 + p.2.2)) hmeas2]
    simp only [setLIntegral_univ]
  have htrans : ∫⁻ z in I ×ˢ I, ∫⁻ x, F (x + z.1 + z.2)
      = ∫⁻ z in I ×ˢ I, ∫⁻ x, F x := by
    refine setLIntegral_congr_fun (hImeas.prod hImeas) (fun z hz => ?_)
    have : (fun x : ℝ => F (x + z.1 + z.2)) = (fun x : ℝ => F (x + (z.1 + z.2))) := by
      funext x; rw [add_assoc]
    rw [this, lintegral_add_right_eq_self F (z.1 + z.2)]
  have hconst : ∫⁻ z in I ×ˢ I, ∫⁻ x, F x
      = (∫⁻ x, F x) * (ENNReal.ofReal h * ENNReal.ofReal h) := by
    rw [setLIntegral_const]
    have hvol : (volume : Measure (ℝ × ℝ)) (I ×ˢ I)
        = ENNReal.ofReal h * ENNReal.ofReal h := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, hI, Real.volume_Ioc]
      norm_num
    rw [hvol]
  rw [hL1, hswap, htrans, hconst]
  ring

/-- **Second-difference `L¹` estimate.** For `h ≥ 0` and a twice differentiable `m : ℝ → ℂ`
with integrable second derivative,
`∫ x, ‖m x - 2 m (x+h) + m (x+2h)‖ ≤ 2 h² ∫ x, ‖m'' x‖`. -/
theorem integral_second_difference_le (m : ℝ → ℂ) (h : ℝ) (hh : 0 ≤ h)
    (hd1 : Differentiable ℝ m) (hd2 : Differentiable ℝ (deriv m))
    (hint2 : MeasureTheory.Integrable (deriv (deriv m))) :
    ∫ x, ‖m x - 2 * m (x + h) + m (x + 2 * h)‖
      ≤ 2 * h ^ 2 * ∫ x, ‖deriv (deriv m) x‖ := by
  classical
  let A : ℝ → ℂ := fun x => m x - 2 * m (x + h) + m (x + 2 * h)
  let F : ℝ → ENNReal := fun y => ENNReal.ofReal ‖deriv (deriv m) y‖
  change ∫ x, ‖A x‖ ≤ 2 * h ^ 2 * ∫ x, ‖deriv (deriv m) x‖
  have hFmeas : Measurable F :=
    ENNReal.measurable_ofReal.comp (measurable_deriv (deriv m)).norm
  have hcontA : Continuous A := by
    refine ((hd1.continuous.sub (continuous_const.mul
      (hd1.continuous.comp (continuous_id.add continuous_const)))).add ?_)
    exact hd1.continuous.comp (continuous_id.add continuous_const)
  have hpt : ∀ x, ENNReal.ofReal ‖A x‖
      ≤ ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s) :=
    fun x => ofReal_norm_second_difference_le m h x hh hd1 hd2 hint2
  have hstep1 : ENNReal.ofReal (∫ x, ‖A x‖) ≤ ∫⁻ x, ENNReal.ofReal ‖A x‖ := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => norm_nonneg _)
      hcontA.norm.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  have hstep2 : ∫⁻ x, ENNReal.ofReal ‖A x‖
      ≤ ∫⁻ x, ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s) :=
    lintegral_mono hpt
  have hwin : ∫⁻ x, ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s)
      = ENNReal.ofReal h * (ENNReal.ofReal h * ∫⁻ x, F x) :=
    double_window_aux hFmeas
  have hFin : ∫⁻ x, F x = ENNReal.ofReal (∫ x, ‖deriv (deriv m) x‖) :=
    (ofReal_integral_eq_lintegral_ofReal hint2.norm (ae_of_all _ fun x => norm_nonneg _)).symm
  have hchain : ENNReal.ofReal (∫ x, ‖A x‖)
      ≤ ENNReal.ofReal (h ^ 2 * ∫ x, ‖deriv (deriv m) x‖) := by
    calc ENNReal.ofReal (∫ x, ‖A x‖) ≤ ∫⁻ x, ENNReal.ofReal ‖A x‖ := hstep1
      _ ≤ ∫⁻ x, ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s) := hstep2
      _ = ENNReal.ofReal h * (ENNReal.ofReal h * ∫⁻ x, F x) := hwin
      _ = ENNReal.ofReal h
            * (ENNReal.ofReal h * ENNReal.ofReal (∫ x, ‖deriv (deriv m) x‖)) := by
            rw [hFin]
      _ = ENNReal.ofReal (h ^ 2 * ∫ x, ‖deriv (deriv m) x‖) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hh, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
  have hI2nn : 0 ≤ ∫ x, ‖deriv (deriv m) x‖ := integral_nonneg (fun x => norm_nonneg _)
  have hmain : ∫ x, ‖A x‖ ≤ h ^ 2 * ∫ x, ‖deriv (deriv m) x‖ :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg h) hI2nn)).mp hchain
  nlinarith [hmain, hI2nn, sq_nonneg h]

end Commons.Analysis.Calculus