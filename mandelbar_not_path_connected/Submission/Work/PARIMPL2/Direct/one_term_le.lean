import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- For `0 ≤ a ≤ π` we have `a * cos a ≤ sin a`.  Equivalently `sin` lies above
its tangent line at `0` in the sense that `t ↦ sin t - t * cos t` is monotone
on `[0, π]` (its derivative is `t * sin t ≥ 0` there). -/
private lemma mul_cos_le_sin (a : ℝ) (ha0 : 0 ≤ a) (haπ : a ≤ Real.pi) :
    a * Real.cos a ≤ Real.sin a := by
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) Real.pi,
      deriv (fun t : ℝ => Real.sin t - t * Real.cos t) x = x * Real.sin x := by
    intro x hx
    change deriv ((fun t : ℝ => Real.sin t) - fun t : ℝ => t * Real.cos t) x = x * Real.sin x
    rw [deriv_sub (Real.differentiableAt_sin) (by fun_prop)]
    rw [show deriv (fun t : ℝ => t * Real.cos t) x = Real.cos x - x * Real.sin x from by
      change deriv ((fun t : ℝ => t) * Real.cos) x = Real.cos x - x * Real.sin x
      rw [deriv_mul (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => t) x) (Real.differentiableAt_cos)]
      rw [deriv_id'', Real.deriv_cos]
      ring]
    rw [Real.deriv_sin]
    ring
  have hmono : MonotoneOn (fun t : ℝ => Real.sin t - t * Real.cos t) (Set.Icc 0 Real.pi) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).continuousOn
    · intro x hx
      exact ((Real.differentiableAt_sin).sub
        (differentiableAt_id.mul Real.differentiableAt_cos)).differentiableWithinAt
    · intro x hx
      rw [interior_Icc, Set.mem_Ioo] at hx
      rw [hderiv x hx]
      exact mul_nonneg hx.1.le (Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2.le)
  have h := hmono (Set.mem_Icc.mpr ⟨le_rfl, Real.pi_pos.le⟩) (Set.mem_Icc.mpr ⟨ha0, haπ⟩) ha0
  simp only [Real.sin_zero, zero_mul, sub_zero] at h
  linarith

/-- For `0 < a < π`, `1 / sin(a)^2 ≤ 1 / a^2 + 1 / (π - a)^2 + 1`.
The two correction terms account for `a` near `0` and for `π - a` near `0`
respectively; the constant `1` is the (small) amount by which these two
estimates have to be loosened in the middle of the interval. -/
private lemma one_div_sin_sq_le (a : ℝ) (h0 : 0 < a) (hπ : a < Real.pi) :
    1 / Real.sin a ^ 2 ≤ 1 / a ^ 2 + 1 / (Real.pi - a) ^ 2 + 1 := by
  have hcase1 : ∀ b : ℝ, 0 < b → b ≤ Real.pi / 2 → (Real.cos b / Real.sin b) ^ 2 ≤ 1 / b ^ 2 := by
    intro b hb0 hb2
    have hbπ : b < Real.pi := by linarith [Real.pi_pos]
    have hsin_pos : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hbπ
    have hcos_nn : 0 ≤ Real.cos b :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hb2
    have hmul : b * Real.cos b ≤ Real.sin b := mul_cos_le_sin b hb0.le (le_of_lt hbπ)
    have hdiv : Real.cos b / Real.sin b ≤ 1 / b := by
      rw [div_le_div_iff₀ hsin_pos hb0]
      linarith [hmul]
    have hnn : 0 ≤ Real.cos b / Real.sin b := div_nonneg hcos_nn hsin_pos.le
    calc (Real.cos b / Real.sin b) ^ 2 ≤ (1 / b) ^ 2 := pow_le_pow_left₀ hnn hdiv 2
      _ = 1 / b ^ 2 := by rw [div_pow, one_pow]
  have hsin_pos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hident : 1 / Real.sin a ^ 2 = 1 + (Real.cos a / Real.sin a) ^ 2 := by
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq a]
  rw [hident]
  have hsq : (Real.cos a / Real.sin a) ^ 2 ≤ 1 / a ^ 2 + 1 / (Real.pi - a) ^ 2 := by
    by_cases ha2 : a ≤ Real.pi / 2
    · have hc := hcase1 a h0 ha2
      have : 0 ≤ 1 / (Real.pi - a) ^ 2 := by positivity
      linarith
    · have hpa0 : 0 < Real.pi - a := by linarith
      have hpa2 : Real.pi - a ≤ Real.pi / 2 := by linarith
      have hc := hcase1 (Real.pi - a) hpa0 hpa2
      have heq : (Real.cos a / Real.sin a) ^ 2 =
          (Real.cos (Real.pi - a) / Real.sin (Real.pi - a)) ^ 2 := by
        rw [Real.cos_pi_sub, Real.sin_pi_sub, neg_div, neg_sq]
      rw [heq]
      have : 0 ≤ 1 / a ^ 2 := by positivity
      linarith
  linarith

theorem one_term_le (lam R x y : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hx1 : R / 4 + 2 ≤ x) (hx2 : x ≤ Real.pi / lam - R / 4) :
    lam ^ 2 / (Real.sin (lam * x) ^ 2 + Real.sinh (lam * y) ^ 2)
      ≤ 1 / x ^ 2 + 1 / (Real.pi / lam - x) ^ 2 + lam ^ 2 := by
  have hx_pos : 0 < x := by linarith
  have ha0 : 0 < lam * x := mul_pos hlam hx_pos
  have hamul : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by
    field_simp
  have haπ : lam * x < Real.pi := by
    have h1 : lam * x ≤ lam * (Real.pi / lam - R / 4) := mul_le_mul_of_nonneg_left hx2 hlam.le
    have h2 : 0 < lam * R / 4 := by positivity
    rw [hamul] at h1
    linarith
  have hsin_pos : 0 < Real.sin (lam * x) := Real.sin_pos_of_pos_of_lt_pi ha0 haπ
  have hSpos : 0 < Real.sin (lam * x) ^ 2 := pow_pos hsin_pos 2
  have hDpos : 0 < Real.sin (lam * x) ^ 2 + Real.sinh (lam * y) ^ 2 := by
    have := sq_nonneg (Real.sinh (lam * y)); linarith
  have hstep1 : lam ^ 2 / (Real.sin (lam * x) ^ 2 + Real.sinh (lam * y) ^ 2)
      ≤ lam ^ 2 / Real.sin (lam * x) ^ 2 := by
    rw [div_le_div_iff₀ hDpos hSpos]
    have hle : Real.sin (lam * x) ^ 2 ≤ Real.sin (lam * x) ^ 2 + Real.sinh (lam * y) ^ 2 := by
      have := sq_nonneg (Real.sinh (lam * y)); linarith
    nlinarith [sq_nonneg lam, hle]
  have hkey := one_div_sin_sq_le (lam * x) ha0 haπ
  have e2 : lam ^ 2 * (1 / (lam * x) ^ 2) = 1 / x ^ 2 := by
    field_simp
  have e3 : lam ^ 2 * (1 / (Real.pi - lam * x) ^ 2) = 1 / (Real.pi / lam - x) ^ 2 := by
    have hpi : Real.pi - lam * x = lam * (Real.pi / lam - x) := by field_simp
    rw [hpi]
    field_simp
  have hmain : lam ^ 2 / Real.sin (lam * x) ^ 2
      ≤ 1 / x ^ 2 + 1 / (Real.pi / lam - x) ^ 2 + lam ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hkey (sq_nonneg lam)
    rw [mul_add, mul_add, mul_one] at h
    have e1 : lam ^ 2 * (1 / Real.sin (lam * x) ^ 2) = lam ^ 2 / Real.sin (lam * x) ^ 2 := by ring
    rw [e1, e2, e3] at h
    exact h
  exact le_trans hstep1 hmain

end Work.PARIMPL2.Direct
