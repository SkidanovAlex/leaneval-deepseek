/-
# ZeroFreeTables — tf71Fc_model

A continuous, `C¹` *model* of the test function `tf71f` of HB Lemma 7.1, and the
identification of the Laplace transform `tf71Fc` with the Laplace transform of that
model over the fixed interval `[0, 2γ]`.

Unlike `tf72f` (of HB Lemma 7.2), `tf71f` is not a polynomial: it is the trigonometric
closed form `tf71cf` on `[0, 2γ]` and `0` on `(-∞,0)`.  It therefore has a jump at `0`
and a kink at `2γ` in general, which makes it unsuitable for differentiating under the
integral sign.  On the interval of integration, however, it *is* the `C²` function
`tf71cf`, and that is all the parametric integral `tf71Fc` sees: this module records the
identification (`tf71Fc_eq_integral_cf`) together with the basic calculus facts
(continuity, differentiability, vanishing at the right endpoint) about the complexified
model `tf71cfC` and its derivative `tf71cfC'`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

lemma tf71_twoγ_pos {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    0 < 2 * tf71γ θ lam := by
  have := tf71γ_pos hθ0 hθ1 hlam
  linarith

lemma tf71_twoγ_nonneg {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    0 ≤ 2 * tf71γ θ lam :=
  le_of_lt (tf71_twoγ_pos hθ0 hθ1 hlam)

/-- The complexification of the trigonometric closed form `tf71cf`. -/
def tf71cfC (θ lam : ℝ) (t : ℝ) : ℂ := ((tf71cf θ lam t : ℝ) : ℂ)

/-- The derivative of the complexified model, as a complex-valued function of the real
variable `t`. -/
def tf71cfC' (θ lam : ℝ) (t : ℝ) : ℂ := ((deriv (tf71cf θ lam) t : ℝ) : ℂ)

lemma tf71cfC_cont (θ lam : ℝ) : Continuous (tf71cfC θ lam) :=
  Complex.continuous_ofReal.comp (tf71cf_cont θ lam)

lemma tf71cfC'_cont (θ lam : ℝ) : Continuous (tf71cfC' θ lam) :=
  Complex.continuous_ofReal.comp ((tf71cf_diff θ lam).continuous_deriv (by norm_num))

lemma tf71cfC_hasDerivAt (θ lam : ℝ) (t : ℝ) :
    HasDerivAt (tf71cfC θ lam) (tf71cfC' θ lam t) t := by
  have hd : DifferentiableAt ℝ (tf71cf θ lam) t := by unfold tf71cf; fun_prop
  exact (hd.hasDerivAt).ofReal_comp

lemma tf71cfC_at_twoγ {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    tf71cfC θ lam (2 * tf71γ θ lam) = 0 := by
  simp [tf71cfC, tf71cf_at_twoγ hθ0 hθ1 hlam]

/-- On the interval of integration `[0, 2γ]` the test function of HB Lemma 7.1 is the
trigonometric closed form `tf71cf`. -/
lemma tf71f_eq_cf (θ lam : ℝ) : ∀ t ∈ Set.Icc (0:ℝ) (2 * tf71γ θ lam),
    tf71f θ lam t = tf71cf θ lam t := by
  intro t ht
  unfold tf71f
  rw [if_pos ht.1, min_eq_left ht.2]

/-- **`tf71Fc` is the Laplace transform of the closed form over `[0, 2γ]`.**  On the
interval of integration the piecewise test function `tf71f` agrees with `tf71cf`, so the
two integrals coincide. -/
theorem tf71Fc_eq_integral_cf {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) (z : ℂ) :
    tf71Fc θ lam z = ∫ t in (0:ℝ)..(2 * tf71γ θ lam),
      Complex.exp (-(z * (t:ℂ))) * tf71cfC θ lam t := by
  unfold tf71Fc
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (tf71_twoγ_nonneg hθ0 hθ1 hlam)] at ht
  simp only [tf71cfC]
  rw [tf71f_eq_cf θ lam t ht]

end Work.ZeroFreeTables
