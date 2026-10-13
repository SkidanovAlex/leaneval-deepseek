import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory intervalIntegral

namespace Work.FTS.EllipticEst.remov.SourceBound

/-- Elementary domination of the integrand on `(0, π/4]`:
`1/(sin²t cos³t) ≤ 2π²/t²`.

Near `t = 0` the singularity is `1/t²`; we use `sin t ≥ 2t/π` (so `sin²t ≥ 4t²/π²`)
together with `cos t ≥ 1/2` on `[0, π/4]`, which follows from
`cos t ≥ 1 - t²/2` and `t ≤ π/4 < 1`. -/
private lemma inv_sinSq_cosCu_le (t : ℝ) (ht0 : 0 < t) (ht : t ≤ Real.pi / 4) :
    1 / (Real.sin t ^ 2 * Real.cos t ^ 3) ≤ 2 * Real.pi ^ 2 / t ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht_pi2 : t ≤ Real.pi / 2 := by linarith
  have hsin : 2 / Real.pi * t ≤ Real.sin t := Real.mul_le_sin (le_of_lt ht0) ht_pi2
  have hsin_sq : (2 / Real.pi * t) ^ 2 ≤ Real.sin t ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin 2
  have hcos : (1 : ℝ) / 2 ≤ Real.cos t := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := t)
    have ht1 : t < 1 := by linarith [ht, Real.pi_lt_four]
    have h2 : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
    linarith
  have hcos3 : ((1 : ℝ) / 2) ^ 3 ≤ Real.cos t ^ 3 := pow_le_pow_left₀ (by norm_num) hcos 3
  have hsin2 : 4 / Real.pi ^ 2 * t ^ 2 ≤ Real.sin t ^ 2 := by
    have h : (2 / Real.pi * t) ^ 2 = 4 / Real.pi ^ 2 * t ^ 2 := by ring
    linarith [hsin_sq, h]
  have hden : t ^ 2 / (2 * Real.pi ^ 2) ≤ Real.sin t ^ 2 * Real.cos t ^ 3 := by
    have h := mul_le_mul hsin2 hcos3 (by norm_num) (by positivity)
    have hr : 4 / Real.pi ^ 2 * t ^ 2 * ((1 : ℝ) / 2) ^ 3 = t ^ 2 / (2 * Real.pi ^ 2) := by ring
    linarith [h, hr]
  have hpos : 0 < t ^ 2 / (2 * Real.pi ^ 2) := by positivity
  calc 1 / (Real.sin t ^ 2 * Real.cos t ^ 3)
      ≤ 1 / (t ^ 2 / (2 * Real.pi ^ 2)) := one_div_le_one_div_of_le hpos hden
    _ = 2 * Real.pi ^ 2 / t ^ 2 := by rw [one_div_div]

/-- The integrand `1/(sin²t cos³t)` has an `1/a` singularity at the left endpoint
`t = 0` of the interval. -/
theorem integral_invSinSqCosCu_left :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 < a → a ≤ Real.pi / 4 →
      ∫ t in a..(Real.pi / 4), 1 / (Real.sin t ^ 2 * Real.cos t ^ 3) ≤ K / a := by
  refine ⟨2 * Real.pi ^ 2, by positivity, ?_⟩
  intro a ha ha4
  -- Integrability of the integrand on `a..π/4` (it is continuous there, `sin` and `cos`
  -- being positive and bounded away from `0`).
  have hfint : IntervalIntegrable
      (fun t : ℝ => 1 / (Real.sin t ^ 2 * Real.cos t ^ 3)) volume a (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ha4]
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (Real.continuous_sin.continuousOn.pow 2).mul (Real.continuous_cos.continuousOn.pow 3)
    · intro t ht
      obtain ⟨hat, htb⟩ := ht
      have hspos : 0 < Real.sin t :=
        Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le ha hat) (by linarith [Real.pi_pos])
      have hcpos : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith [Real.pi_pos]⟩
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hspos)) (pow_ne_zero 3 (ne_of_gt hcpos))
  -- Integrability of the dominating function `2π²/t²`.
  have hgint : IntervalIntegrable (fun t : ℝ => 2 * Real.pi ^ 2 / t ^ 2) volume a
      (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ha4]
    refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha ht.1))
  have hmono : ∫ t in a..(Real.pi / 4), 1 / (Real.sin t ^ 2 * Real.cos t ^ 3)
      ≤ ∫ t in a..(Real.pi / 4), 2 * Real.pi ^ 2 / t ^ 2 :=
    integral_mono_on ha4 hfint hgint
      (fun t ht => inv_sinSq_cosCu_le t (lt_of_lt_of_le ha ht.1) ht.2)
  -- The exact value, by the fundamental theorem of calculus.
  have hderiv : ∀ t ∈ Set.Ioo a (Real.pi / 4),
      HasDerivAt (fun s : ℝ => -(2 * Real.pi ^ 2 / s)) (2 * Real.pi ^ 2 / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha (le_of_lt ht.1))
    have h : HasDerivAt (-((fun x : ℝ => 2 * Real.pi ^ 2) / id))
        (-((0 * id t - 2 * Real.pi ^ 2 * 1) / id t ^ 2)) t :=
      ((hasDerivAt_const t (2 * Real.pi ^ 2)).div (hasDerivAt_id t) ht0).neg
    have hf : (fun s : ℝ => -(2 * Real.pi ^ 2 / s))
        = -((fun x : ℝ => 2 * Real.pi ^ 2) / id) := by
      funext s <;> simp only [Pi.div_apply, Pi.neg_apply, id_eq] <;> ring
    have hd : 2 * Real.pi ^ 2 / t ^ 2
        = -((0 * id t - 2 * Real.pi ^ 2 * 1) / id t ^ 2) := by
      simp only [id_eq] <;> ring
    rw [hf, hd]
    exact h
  have hcont : ContinuousOn (fun s : ℝ => -(2 * Real.pi ^ 2 / s)) (Set.Icc a (Real.pi / 4)) := by
    refine (ContinuousOn.div continuousOn_const continuousOn_id ?_).neg
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le ha ht.1)
  have hval : ∫ t in a..(Real.pi / 4), 2 * Real.pi ^ 2 / t ^ 2
      = 2 * Real.pi ^ 2 / a - 2 * Real.pi ^ 2 / (Real.pi / 4) := by
    have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha4 hcont hderiv hgint
    rw [h1]
    ring
  calc ∫ t in a..(Real.pi / 4), 1 / (Real.sin t ^ 2 * Real.cos t ^ 3)
      ≤ ∫ t in a..(Real.pi / 4), 2 * Real.pi ^ 2 / t ^ 2 := hmono
    _ = 2 * Real.pi ^ 2 / a - 2 * Real.pi ^ 2 / (Real.pi / 4) := hval
    _ ≤ 2 * Real.pi ^ 2 / a := by
        have : 0 ≤ 2 * Real.pi ^ 2 / (Real.pi / 4) := by positivity
        linarith

end Work.FTS.EllipticEst.remov.SourceBound
