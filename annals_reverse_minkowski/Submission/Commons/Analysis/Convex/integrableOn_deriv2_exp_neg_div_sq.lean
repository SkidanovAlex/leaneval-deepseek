import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Convex.deriv2_nonneg_of_convexOn_real

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Real Topology

/-- Improper integrability at `-∞` of `V'' e^{-V} / (V')²` when `V` is convex, `C²` and
`V' ≤ -c < 0` on the half-line. -/
theorem integrableOn_deriv2_exp_neg_div_sq (V : ℝ → ℝ) (hV : ContDiff ℝ 2 V)
    (hVc : ConvexOn ℝ Set.univ V) {a c : ℝ} (hc : 0 < c)
    (hVa : ∀ x, x ≤ a → deriv V x ≤ -c) :
    IntegrableOn (fun x => deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2)
      (Set.Iic a) volume := by
  set g : ℝ → ℝ := fun x => deriv (deriv V) x * Real.exp (-(V x)) / (deriv V x) ^ 2 with hg
  set F : ℝ → ℝ := fun x => -(Real.exp (-(V x)) / deriv V x) with hF
  have hVdiff : ∀ x, DifferentiableAt ℝ V x :=
    fun x => (hV.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hderiv2_nonneg : ∀ x, 0 ≤ deriv (deriv V) x :=
    deriv2_nonneg_of_convexOn_real hVc hVdiff
  have hderiv_lt : ∀ x, x ≤ a → deriv V x < 0 := fun x hx =>
    lt_of_le_of_lt (hVa x hx) (neg_neg_of_pos hc)
  have hcont_V : Continuous V := hV.continuous
  have hcont_dV : Continuous (deriv V) := hV.continuous_deriv (by norm_num)
  have hcont_ddV : Continuous (deriv (deriv V)) :=
    (hV.deriv' : ContDiff ℝ 1 (deriv V)).continuous_deriv (by norm_num)
  -- nonnegativity of `g` on `Iic a`
  have hg_nonneg : ∀ x, x ≤ a → 0 ≤ g x := by
    intro x hx
    have hlt : deriv V x < 0 := hderiv_lt x hx
    have hne : deriv V x ≠ 0 := ne_of_lt hlt
    have hsq : 0 < (deriv V x) ^ 2 := pow_two_pos_of_ne_zero hne
    rw [hg]
    exact div_nonneg (mul_nonneg (hderiv2_nonneg x) (Real.exp_pos _).le) hsq.le
  -- continuity of `g` on any `Icc b a`
  have hcont_g_on : ∀ b : ℝ, ContinuousOn g (Icc b a) := by
    intro b
    have hnum : ContinuousOn (fun x => deriv (deriv V) x * Real.exp (-(V x))) (Icc b a) :=
      (hcont_ddV.mul (Real.continuous_exp.comp hcont_V.neg)).continuousOn
    have hden : ContinuousOn (fun x => (deriv V x) ^ 2) (Icc b a) :=
      (hcont_dV.pow 2).continuousOn
    have hdiv : ContinuousOn
        (fun x => (deriv (deriv V) x * Real.exp (-(V x))) / (deriv V x) ^ 2) (Icc b a) :=
      ContinuousOn.div hnum hden (fun x hx =>
        pow_ne_zero 2 (ne_of_lt (hderiv_lt x hx.2)))
    rw [hg]
    exact hdiv
  -- derivative of `F`
  have hderivF : ∀ x, x ≤ a → HasDerivAt F (g x + Real.exp (-(V x))) x := by
    intro x hx
    have hne : deriv V x ≠ 0 := ne_of_lt (hderiv_lt x hx)
    have h1 : HasDerivAt (fun y => -(V y)) (-(deriv V x)) x :=
      (hVdiff x).hasDerivAt.neg
    have hA : HasDerivAt (fun y => Real.exp (-(V y)))
        (Real.exp (-(V x)) * (-(deriv V x))) x := by
      have := (Real.hasDerivAt_exp (-(V x))).comp x h1
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (deriv V) (deriv (deriv V) x) x :=
      hV.differentiable_deriv_two.differentiableAt.hasDerivAt
    have hAB := hA.div h2 hne
    have hval : -((Real.exp (-(V x)) * (-(deriv V x)) * deriv V x
                    - Real.exp (-(V x)) * deriv (deriv V) x) / (deriv V x) ^ 2)
                = g x + Real.exp (-(V x)) := by
      rw [hg]
      field_simp
      ring
    rw [hF]
    exact hAB.neg.congr_deriv hval
  -- bound on `∫_b^a g`
  have hbound : ∀ b : ℝ, b ≤ a → ∫ x in b..a, g x ≤ F a := by
    intro b hba
    have hcontF : ContinuousOn F (Icc b a) := by
      rw [hF]
      have hnum : ContinuousOn (fun x => Real.exp (-(V x))) (Icc b a) :=
        (Real.continuous_exp.comp hcont_V.neg).continuousOn
      have hden : ContinuousOn (fun x => deriv V x) (Icc b a) := hcont_dV.continuousOn
      have hdiv : ContinuousOn (fun x => Real.exp (-(V x)) / deriv V x) (Icc b a) :=
        ContinuousOn.div hnum hden (fun x hx => ne_of_lt (hderiv_lt x hx.2))
      exact hdiv.neg
    have hderiv_on : ∀ x ∈ Ioo b a, HasDerivAt F ((fun x => g x + Real.exp (-(V x))) x) x :=
      fun x hx => hderivF x (le_of_lt hx.2)
    have hint : IntervalIntegrable (fun x => g x + Real.exp (-(V x))) volume b a := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hba]
      exact ContinuousOn.add (hcont_g_on b)
        (Real.continuous_exp.comp hcont_V.neg).continuousOn
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hba hcontF hderiv_on hint
    have hintg : IntervalIntegrable g volume b a := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hba]
      exact hcont_g_on b
    have hinte : IntervalIntegrable (fun x => Real.exp (-(V x))) volume b a := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hba]
      exact (Real.continuous_exp.comp hcont_V.neg).continuousOn
    have hsplit : ∫ x in b..a, g x
        = (F a - F b) - ∫ x in b..a, Real.exp (-(V x)) := by
      rw [← hFTC, intervalIntegral.integral_add hintg hinte]
      ring
    have he_nn : 0 ≤ ∫ x in b..a, Real.exp (-(V x)) :=
      intervalIntegral.integral_nonneg hba (fun u _ => (Real.exp_pos _).le)
    have hFb : 0 ≤ F b := by
      rw [hF]
      have hquot : Real.exp (-(V b)) / deriv V b < 0 :=
        div_neg_of_pos_of_neg (Real.exp_pos _) (hderiv_lt b hba)
      exact neg_nonneg_of_nonpos hquot.le
    calc ∫ x in b..a, g x = (F a - F b) - ∫ x in b..a, Real.exp (-(V x)) := hsplit
      _ ≤ F a - F b := by linarith
      _ ≤ F a := by linarith
  -- final assembly
  have hfi : ∀ i : ℕ, IntegrableOn g (Ioc (-(i:ℝ)) a) volume := by
    intro i
    have hcomp : IntegrableOn g (Icc (-(i:ℝ)) a) volume :=
      ContinuousOn.integrableOn_compact isCompact_Icc (hcont_g_on (-(i:ℝ)))
    exact hcomp.mono_set Ioc_subset_Icc_self
  have ha : Tendsto (fun i : ℕ => -(i:ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have hbdd : ∀ᶠ i : ℕ in atTop, (∫ x in (-(i:ℝ))..a, ‖g x‖ ∂volume) ≤ F a := by
    filter_upwards [ha.eventually (eventually_le_atBot a)] with i hi
    have hcongr : ∫ x in (-(i:ℝ))..a, ‖g x‖ ∂volume = ∫ x in (-(i:ℝ))..a, g x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hi] at hx
      show ‖g x‖ = g x
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg x hx.2)]
    rw [hcongr]
    exact hbound (-(i:ℝ)) hi
  exact integrableOn_Iic_of_intervalIntegral_norm_bounded (f := g)
    (a := fun i : ℕ => -(i:ℝ)) (l := atTop) (F a) a hfi ha hbdd

end Commons.Analysis.Convex