import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EllipticEst

/-- **Wirtinger-style sine domination.**  If `a < b`, `r > 0` with `r * (b - a) = π`, and
`u` is `C²` on `[a, b]` with `u a = u b = 0`, then `|u|` is dominated by `|sin (r · - a)|`:
there is `C ≥ 0` with `|u x| ≤ C * |sin (r * (x - a))|` for all `x ∈ [a, b]`.

Both `u` and `sin (r · - a)` vanish at the two endpoints of `[a, b]`, and the zeros of the sine
at `a` and `b` are simple (its derivative there is `± r ≠ 0`); since `u` is `C²`, its zeros at
`a`, `b` have order at least one, so the quotient extends continuously.  Formally the
mean-value/Lipschitz bound `|u x| ≤ M' · dist(x, {a, b})` (obtained through `derivWithin` and
`ContDiffOn.continuousOn_derivWithin`) is compared with Jordan's inequality `Real.mul_le_sin`,
`(2/π) t ≤ sin t` on `[0, π/2]`, applied on each half of the interval: with
`t = r (x - a) ∈ [0, π]` one has `min (x - a) (b - x) = min t (π - t) / r` and
`sin t ≥ (2/π) min t (π - t)`. -/
theorem wirt_sin_bound {a b r : ℝ} (hab : a < b) (hr : 0 < r) (hrb : r * (b - a) = π)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) (ha : u a = 0) (hb : u b = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc a b, |u x| ≤ C * |Real.sin (r * (x - a))| := by
  have hU : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hdiff : DifferentiableOn ℝ u (Set.Icc a b) := hu.differentiableOn (by norm_num)
  have hcont : ContinuousOn (derivWithin u (Set.Icc a b)) (Set.Icc a b) :=
    hu.continuousOn_derivWithin hU (by norm_num)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let M' : ℝ := max M 0
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hM'b : ∀ x ∈ Set.Icc a b, ‖derivWithin u (Set.Icc a b) x‖ ≤ M' :=
    fun x hx => le_trans (hM x hx) (le_max_left _ _)
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc _ _
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hrad : r * ((b - a) / 2) = π / 2 := by
    rw [← mul_div_assoc, hrb]
  -- Mean-value bound of `|u x|` by the distance to each endpoint.
  have hmvt_a : ∀ x ∈ Set.Icc a b, |u x| ≤ M' * (x - a) := by
    intro x hx
    have h := Convex.norm_image_sub_le_of_norm_derivWithin_le hdiff hM'b hconv ha_mem hx
    rw [ha, sub_zero] at h
    have hnorm : ‖x - a‖ = x - a := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
    rw [hnorm] at h
    simpa only [Real.norm_eq_abs] using h
  have hmvt_b : ∀ x ∈ Set.Icc a b, |u x| ≤ M' * (b - x) := by
    intro x hx
    have h := Convex.norm_image_sub_le_of_norm_derivWithin_le hdiff hM'b hconv hb_mem hx
    rw [hb, sub_zero] at h
    have hnorm : ‖x - b‖ = b - x := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.2])]
      ring
    rw [hnorm] at h
    simpa only [Real.norm_eq_abs] using h
  -- Jordan's inequality, multiplied through by `π/2`.
  have hsin_le : ∀ t : ℝ, 0 ≤ t → t ≤ π / 2 → t ≤ π / 2 * Real.sin t := by
    intro t h0 h1
    have hj := Real.mul_le_sin h0 h1
    have h2 : π / 2 * (2 / π * t) = t := by
      have hp : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      field_simp
    calc t = π / 2 * (2 / π * t) := h2.symm
      _ ≤ π / 2 * Real.sin t := mul_le_mul_of_nonneg_left hj (by positivity)
  refine ⟨M' * (1 / r) * (π / 2), ?_, fun x hx => ?_⟩
  · exact mul_nonneg (mul_nonneg hM'0 (div_nonneg zero_le_one hr.le))
      (div_nonneg Real.pi_pos.le (by norm_num))
  rcases le_total x ((a + b) / 2) with hxle | hxge
  · -- left half: compare against the zero of the sine at `a`
    have hxa0 : 0 ≤ x - a := by linarith [hx.1]
    have hxa_le : x - a ≤ (b - a) / 2 := by linarith
    have ht_le : r * (x - a) ≤ π / 2 := by
      have h := mul_le_mul_of_nonneg_left hxa_le hr.le
      rw [hrad] at h
      exact h
    have ht0 : 0 ≤ r * (x - a) := mul_nonneg hr.le hxa0
    have hsinpos : 0 ≤ Real.sin (r * (x - a)) :=
      Real.sin_nonneg_of_mem_Icc ⟨ht0, by linarith [ht_le, Real.pi_pos]⟩
    have hsinabs : |Real.sin (r * (x - a))| = Real.sin (r * (x - a)) :=
      abs_of_nonneg hsinpos
    have hmu : r * (x - a) ≤ (π / 2) * Real.sin (r * (x - a)) := hsin_le _ ht0 ht_le
    rw [hsinabs]
    calc |u x| ≤ M' * (x - a) := hmvt_a x hx
      _ = M' * (1 / r) * (r * (x - a)) := by
            have hr0 : r ≠ 0 := hr.ne'
            field_simp
      _ ≤ M' * (1 / r) * ((π / 2) * Real.sin (r * (x - a))) :=
            mul_le_mul_of_nonneg_left hmu (mul_nonneg hM'0 (div_nonneg zero_le_one hr.le))
      _ = M' * (1 / r) * (π / 2) * Real.sin (r * (x - a)) := by ring
  · -- right half: compare against the zero of the sine at `b`
    have hbx0 : 0 ≤ b - x := by linarith [hx.2]
    have hbx_le : b - x ≤ (b - a) / 2 := by linarith
    have ht_le : r * (b - x) ≤ π / 2 := by
      have h := mul_le_mul_of_nonneg_left hbx_le hr.le
      rw [hrad] at h
      exact h
    have ht0 : 0 ≤ r * (b - x) := mul_nonneg hr.le hbx0
    have hsinpos : 0 ≤ Real.sin (r * (b - x)) :=
      Real.sin_nonneg_of_mem_Icc ⟨ht0, by linarith [ht_le, Real.pi_pos]⟩
    have hmu : r * (b - x) ≤ (π / 2) * Real.sin (r * (b - x)) := hsin_le _ ht0 ht_le
    have harg : r * (x - a) = π - r * (b - x) := by
      have h : r * (x - a) = r * (b - a) - r * (b - x) := by ring
      rw [h, hrb]
    have hsinabs : |Real.sin (r * (x - a))| = Real.sin (r * (b - x)) := by
      rw [harg, Real.sin_pi_sub, abs_of_nonneg hsinpos]
    rw [hsinabs]
    calc |u x| ≤ M' * (b - x) := hmvt_b x hx
      _ = M' * (1 / r) * (r * (b - x)) := by
            have hr0 : r ≠ 0 := hr.ne'
            field_simp
      _ ≤ M' * (1 / r) * ((π / 2) * Real.sin (r * (b - x))) :=
            mul_le_mul_of_nonneg_left hmu (mul_nonneg hM'0 (div_nonneg zero_le_one hr.le))
      _ = M' * (1 / r) * (π / 2) * Real.sin (r * (b - x)) := by ring

end Work.FTS.EllipticEst
