import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.tf71H_defs
import Submission.Work.ZeroFreeTables.tf71H_hasDerivAt
import Submission.Work.ZeroFreeTables.tf71H_value

/-!
# `tf71Fc_zero_re` — the value `F(0) = 2(1+tan²θ)(1 − θ cot θ)²` of HB's test-function transform

Heath-Brown (1992), Lemma 7.1: for the test function `f` of `testFn71_defs` the
Laplace transform `F z = ∫₀^{2γ} e^{−zt} f t dt` takes at the origin the value

`F 0 = ∫₀^{2γ} f t dt = 2(1+tan²θ)(1 − θ/tanθ)²`.

The real integral is evaluated with the explicit antiderivative `tf71H` of the
closed form `tf71cf` (`tf71H_defs`), and then transferred to the complex-valued
transform by `intervalIntegral.integral_ofReal`.
-/

noncomputable section
namespace Work.ZeroFreeTables

/-- `tf71Fc θ lam 0` is the complexification of the real integral of `f`. -/
theorem tf71Fc_zero (θ lam : ℝ) :
    tf71Fc θ lam 0 = ((∫ t in (0:ℝ)..(2 * tf71γ θ lam), tf71f θ lam t : ℝ) : ℂ) := by
  have hintegrand : (∫ t in (0:ℝ)..(2 * tf71γ θ lam),
        Complex.exp (-((0:ℂ) * (t:ℂ))) * ((tf71f θ lam t : ℝ) : ℂ))
      = ∫ t in (0:ℝ)..(2 * tf71γ θ lam), ((tf71f θ lam t : ℝ) : ℂ) :=
    intervalIntegral.integral_congr fun t _ => by simp
  rw [tf71Fc, hintegrand, intervalIntegral.integral_ofReal]

/-- `∫₀^{2γ} f t dt = 2(1+tan²θ)(1 − θ/tanθ)²` for HB's test function `f`
(Lemma 7.1 at `z = 0`). -/
theorem tf71f_intervalIntegral (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) :
    (∫ t in (0:ℝ)..(2 * tf71γ θ lam), tf71f θ lam t)
      = 2 * (1 + Real.tan θ ^ 2) * (1 - θ * (Real.tan θ)⁻¹) ^ 2 := by
  have hγ := tf71γ_pos hθ0 hθ1 hlam
  have hle : (0:ℝ) ≤ 2 * tf71γ θ lam := by linarith
  have hcongr : (∫ t in (0:ℝ)..(2 * tf71γ θ lam), tf71f θ lam t)
      = ∫ t in (0:ℝ)..(2 * tf71γ θ lam), tf71cf θ lam t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hle] at ht
    unfold tf71f
    rw [if_pos ht.1, min_eq_left ht.2]
  rw [hcongr]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := tf71H θ lam) (f' := tf71cf θ lam)
        (fun x _ => tf71H_hasDerivAt θ lam hθ0 hθ1 hlam x)
        ((tf71cf_cont θ lam).intervalIntegrable _ _)]
  exact tf71H_value θ lam hθ0 hθ1 hlam

theorem tf71Fc_zero_re (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    (Work.ZeroFreeTables.tf71Fc θ lam 0).re
      = 2 * (1 + Real.tan θ ^ 2) * (1 - θ * (Real.tan θ)⁻¹) ^ 2 := by
  rw [tf71Fc_zero θ lam, Complex.ofReal_re, tf71f_intervalIntegral θ lam hθ0 hθ1 hlam]

end Work.ZeroFreeTables
