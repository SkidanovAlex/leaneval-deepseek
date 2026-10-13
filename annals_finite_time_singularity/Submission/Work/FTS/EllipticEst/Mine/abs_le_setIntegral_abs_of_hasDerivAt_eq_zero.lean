import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

/-- If `f` is continuous on `[a,b]`, differentiable on `(a,b)` with derivative `g`, and
vanishes at some interior point `c`, then `|f θ| ≤ ∫_{[a,b]} |g|` for every `θ ∈ [a,b]`.
This is the fundamental theorem of calculus together with the monotonicity of the integral
over a subinterval. -/
theorem abs_le_setIntegral_abs_of_hasDerivAt_eq_zero
    {f g : ℝ → ℝ} {a b c θ : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (g x) x)
    (hc : c ∈ Set.Ioo a b) (hc0 : f c = 0) (hθ : θ ∈ Set.Icc a b)
    (hint : IntervalIntegrable g MeasureTheory.volume a b) :
    |f θ| ≤ ∫ x in Set.Icc a b, |g x| := by
  have hset : ∫ x in Set.Icc a b, |g x| = ∫ x in a..b, |g x| := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab.le]
  rw [hset]
  have habs : IntervalIntegrable (fun x => |g x|) MeasureTheory.volume a b := hint.abs
  have hmono : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b →
      ∫ x in p..q, |g x| ≤ ∫ x in a..b, |g x| := by
    intro p q hap hpq hqb
    exact intervalIntegral.integral_mono_interval hap hpq hqb
      (Filter.Eventually.of_forall fun x => abs_nonneg (g x)) habs
  rcases le_total c θ with hcθ | hθc
  · -- `c ≤ θ`: `f θ = f c + ∫_c^θ g`
    have hderiv' : ∀ x ∈ Set.Ioo c θ, HasDerivAt f (g x) x :=
      fun x hx => hderiv x ⟨lt_trans hc.1 hx.1, lt_of_lt_of_le hx.2 hθ.2⟩
    have hcont' : ContinuousOn f (Set.Icc c θ) :=
      hcont.mono (Set.Icc_subset_Icc hc.1.le hθ.2)
    have hint' : IntervalIntegrable g MeasureTheory.volume c θ :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hcθ, Set.uIcc_of_le hab.le]
        exact Set.Icc_subset_Icc hc.1.le hθ.2)
    have hftc : ∫ x in c..θ, g x = f θ - f c :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcθ hcont' hderiv' hint'
    calc |f θ| = |∫ x in c..θ, g x| := by rw [hftc, hc0, sub_zero]
      _ ≤ ∫ x in c..θ, |g x| := intervalIntegral.abs_integral_le_integral_abs hcθ
      _ ≤ ∫ x in a..b, |g x| := hmono hc.1.le hcθ hθ.2
  · -- `θ ≤ c`: `f θ = -∫_θ^c g`
    have hderiv' : ∀ x ∈ Set.Ioo θ c, HasDerivAt f (g x) x :=
      fun x hx => hderiv x ⟨lt_of_le_of_lt hθ.1 hx.1, lt_trans hx.2 hc.2⟩
    have hcont' : ContinuousOn f (Set.Icc θ c) :=
      hcont.mono (Set.Icc_subset_Icc hθ.1 hc.2.le)
    have hint' : IntervalIntegrable g MeasureTheory.volume θ c :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hθc, Set.uIcc_of_le hab.le]
        exact Set.Icc_subset_Icc hθ.1 hc.2.le)
    have hftc : ∫ x in θ..c, g x = f c - f θ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθc hcont' hderiv' hint'
    calc |f θ| = |∫ x in θ..c, g x| := by rw [hftc, hc0, zero_sub, abs_neg]
      _ ≤ ∫ x in θ..c, |g x| := intervalIntegral.abs_integral_le_integral_abs hθc
      _ ≤ ∫ x in a..b, |g x| := hmono hθ.1 hθc hc.2.le

end Work.FTS.EllipticEst.Mine
