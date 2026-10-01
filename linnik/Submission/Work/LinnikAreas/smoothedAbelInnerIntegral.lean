import Mathlib

namespace Work.LinnikAreas

open MeasureTheory

/-- Smoothed Abel inner integral used in Linnik's theorem.

For `1 ≤ n ≤ x` and any real `β`,
`∫_{n}^{x} ( ((1-β)/x) u^{-β} + β u^{-(β+1)} ) du = n^{-β} (1 - n/x)`.

The integrand is the derivative (with respect to `u`) of the primitive
`F u = u^{1-β}/x - u^{-β}`, whose value at `u = x` is `0` and at `u = n`
is `-(n^{-β}(1 - n/x))`. -/
theorem smoothedAbelInnerIntegral (β : ℝ) (x n : ℕ) (hn : 1 ≤ n) (hnx : n ≤ x) :
    ∫ u in (n:ℝ)..(x:ℝ),
      (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1)))
    = (n:ℂ) ^ (-(β:ℂ)) * (1 - (n:ℂ) / (x:ℂ)) := by
  have hxn : (n:ℝ) ≤ (x:ℝ) := by exact_mod_cast hnx
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hx1 : 1 ≤ x := le_trans hn hnx
  -- Complex power identity: `t ^ (1 - β) = t ^ (-β) * t` for `t ≥ 1`.
  have hkey : ∀ t : ℕ, 1 ≤ t → (t:ℂ)^(1 - (β:ℂ)) = (t:ℂ)^(-(β:ℂ)) * (t:ℂ) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by
      have ht0' : (t:ℝ) ≠ 0 := by
        have : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
        linarith
      exact_mod_cast ht0'
    have h1e : (1:ℂ) - (β:ℂ) = (-(β:ℂ)) + 1 := by ring
    rw [h1e, Complex.cpow_add _ _ ht0, Complex.cpow_one]
  -- The integrand is the derivative of the primitive `u ↦ u^{1-β}/x - u^{-β}`.
  have hderiv : ∀ u ∈ Set.uIcc (n:ℝ) (x:ℝ),
      HasDerivAt ((fun v : ℝ => (v:ℂ) ^ (1 - (β:ℂ)) / (x:ℂ)) - fun v : ℝ => (v:ℂ) ^ (-(β:ℂ)))
        (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))) u := by
    intro u hu
    rw [Set.uIcc_of_le hxn] at hu
    have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) (le_trans hn1 hu.1)
    have hmem : (u:ℂ) ∈ Complex.slitPlane := by
      simp only [Complex.slitPlane, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im]
      exact Or.inl hu0
    have h1 := (Complex.hasStrictDerivAt_cpow_const (x := (u:ℂ)) (c := 1 - (β:ℂ)) hmem).hasDerivAt.comp_ofReal
    have h2 := (Complex.hasStrictDerivAt_cpow_const (x := (u:ℂ)) (c := -(β:ℂ)) hmem).hasDerivAt.comp_ofReal
    have hF := (h1.div_const ((x:ℂ))).sub h2
    have key : ((1 - (β:ℂ)) * (u:ℂ) ^ ((1 - (β:ℂ)) - 1)) / (x:ℂ) - (-(β:ℂ)) * (u:ℂ) ^ ((-(β:ℂ)) - 1)
        = (1 - (β:ℂ)) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1)) := by
      have e1 : (1 - (β:ℂ)) - 1 = -(β:ℂ) := by ring
      have e2 : (-(β:ℂ)) - 1 = -((β:ℂ)+1) := by ring
      rw [e1, e2]; ring
    rw [key] at hF
    exact hF
  -- The integrand is continuous on the (positive) interval, hence integrable.
  have hint : IntervalIntegrable (fun u : ℝ => ((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))) volume (n:ℝ) (x:ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxn]
    intro u hu
    have hu1 : 1 ≤ u := le_trans hn1 hu.1
    have hune : u ≠ 0 := by linarith
    have hcont1 : ContinuousWithinAt (fun u : ℝ => (u:ℂ) ^ (-(β:ℂ))) (Set.Icc (n:ℝ) (x:ℝ)) u :=
      (Complex.continuousAt_ofReal_cpow_const u _ (Or.inr hune)).continuousWithinAt
    have hcont2 : ContinuousWithinAt (fun u : ℝ => (u:ℂ) ^ (-((β:ℂ) + 1))) (Set.Icc (n:ℝ) (x:ℝ)) u :=
      (Complex.continuousAt_ofReal_cpow_const u _ (Or.inr hune)).continuousWithinAt
    have hA : ContinuousWithinAt (fun u : ℝ => ((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ)) (Set.Icc (n:ℝ) (x:ℝ)) u :=
      (continuousWithinAt_const.mul hcont1).div_const _
    exact hA.add (continuousWithinAt_const.mul hcont2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hx0 : (x:ℂ) ≠ 0 := by
    have : (x:ℝ) ≠ 0 := by
      have : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
      linarith
    exact_mod_cast this
  simp only [Pi.sub_apply, Complex.ofReal_natCast]
  rw [hkey x hx1, hkey n hn, mul_div_cancel_right₀ _ hx0]
  ring

end Work.LinnikAreas
