import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.tf71Q_defs
import Submission.Work.ZeroFreeTables.tf71Q_hasDerivAt
import Submission.Work.ZeroFreeTables.tf71Q_sub

namespace Work.ZeroFreeTables

theorem tf71Fc_neglam_re (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    (Work.ZeroFreeTables.tf71Fc θ lam ((-(lam) : ℝ) : ℂ)).re
      = 2 * Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.tan θ)⁻¹ := by
  have hγ : 0 < tf71γ θ lam := tf71γ_pos hθ0 hθ1 hlam
  have hle : (0:ℝ) ≤ 2 * tf71γ θ lam := by linarith
  -- Step 1: the complex integrand at `z = -λ` is the coercion of the real integrand
  have hpoint : ∀ t : ℝ,
      Complex.exp (-(((-(lam) : ℝ) : ℂ) * (t:ℂ))) * ((tf71f θ lam t : ℝ) : ℂ)
        = ((Real.exp (lam * t) * tf71f θ lam t : ℝ) : ℂ) := by
    intro t
    have harg : -(((-(lam) : ℝ) : ℂ) * (t:ℂ)) = ((lam * t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  have h1 : (∫ t in (0:ℝ)..(2 * tf71γ θ lam),
        Complex.exp (-(((-(lam) : ℝ) : ℂ) * (t:ℂ))) * ((tf71f θ lam t : ℝ) : ℂ))
      = ((∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (lam * t) * tf71f θ lam t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal
      (f := fun t => Real.exp (lam * t) * tf71f θ lam t)]
    apply intervalIntegral.integral_congr
    intro t _
    exact hpoint t
  -- Step 2: replace `tf71f` by the closed form `tf71cf` on `[0, 2γ]`
  have hfc : ∀ t ∈ Set.Icc (0:ℝ) (2 * tf71γ θ lam), tf71f θ lam t = tf71cf θ lam t := by
    intro t ht
    unfold tf71f
    rw [if_pos ht.1, min_eq_left ht.2]
  have h2 : (∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (lam * t) * tf71f θ lam t)
      = ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (lam * t) * tf71cf θ lam t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) (2 * tf71γ θ lam) := by
      simpa [Set.uIcc_of_le hle] using ht
    show Real.exp (lam * t) * tf71f θ lam t = Real.exp (lam * t) * tf71cf θ lam t
    rw [hfc t ht']
  -- Step 3: fundamental theorem of calculus with the explicit antiderivative
  have hcont : Continuous (fun x : ℝ => Real.exp (lam * x) * tf71cf θ lam x) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (tf71cf_cont θ lam)
  have h3 : (∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (lam * t) * tf71cf θ lam t)
      = tf71Q θ lam (2 * tf71γ θ lam) - tf71Q θ lam 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => tf71Q_hasDerivAt θ lam hθ0 hθ1 hlam x) (hcont.intervalIntegrable _ _)
  unfold tf71Fc
  rw [h1, Complex.ofReal_re, h2, h3]
  exact tf71Q_sub θ lam hθ0 hθ1 hlam

end Work.ZeroFreeTables
