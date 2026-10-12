import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxA0.SinParsevalDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory

/-- The square of the odd extension `oddExt F` satisfies
`(oddExt F v)^2 = (F (|v| - 1/2))^2`, i.e. it is the even function
`v ↦ (F (|v| - 1/2))^2`. Consequently its integral over `[-1,1]` is twice the
integral of `F^2` over `[-1/2,1/2]`. -/
lemma oddExt_sq_integral {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ v in (-1)..1, (Work.SmallBoxA0.oddExt F v) ^ 2)
      = 2 * ∫ x in (-(1 / 2))..(1 / 2), (F x) ^ 2 := by
  let φ : ℝ → ℝ := fun y => (F (y - 1 / 2)) ^ 2
  let ψ : ℝ → ℝ := fun x => (F x) ^ 2
  let G : ℝ → ℝ := fun v => (Work.SmallBoxA0.oddExt F v) ^ 2
  have hGval : ∀ v : ℝ, G v = (F (|v| - 1 / 2)) ^ 2 := by
    intro v
    change (Work.SmallBoxA0.oddExt F v) ^ 2 = (F (|v| - 1 / 2)) ^ 2
    rcases le_or_gt v 0 with hv | hv
    · rw [Work.SmallBoxA0.oddExt, if_pos hv, abs_of_nonpos hv, neg_sq]
    · rw [Work.SmallBoxA0.oddExt, if_neg (not_le.mpr hv), abs_of_pos hv]
  have hGcont : Continuous G := by
    have h1 : G = fun v : ℝ => (F (|v| - 1 / 2)) ^ 2 := by
      funext v; exact hGval v
    rw [h1]
    exact (hF.comp (continuous_abs.sub continuous_const)).pow 2
  have hint : ∀ a b : ℝ, IntervalIntegrable G volume a b := fun a b =>
    hGcont.intervalIntegrable a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint (-1) 0) (hint 0 1)
  -- Left half: substitute `v ↦ -v`.
  have hL : (∫ v in (-1 : ℝ)..0, G v) = ∫ y in (0 : ℝ)..1, φ y := by
    have s1 : (∫ v in (-1 : ℝ)..0, G v) = ∫ v in (-1 : ℝ)..0, φ (-v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
      beta_reduce
      rw [hGval v, abs_of_nonpos hv.2]
    have s2 : (∫ v in (-1 : ℝ)..0, φ (-v)) = ∫ y in (0 : ℝ)..1, φ y := by
      simp only [intervalIntegral.integral_comp_neg, neg_zero, neg_neg]
    rw [s1, s2]
  -- Right half: `|v| = v` on `[0,1]`.
  have hR : (∫ v in (0 : ℝ)..1, G v) = ∫ y in (0 : ℝ)..1, φ y := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    rw [hGval v, abs_of_nonneg hv.1]
  -- Shift the remaining integral `∫_0^1 (F (y - 1/2))^2` to `[-1/2,1/2]`.
  have hD : (∫ y in (0 : ℝ)..1, φ y) = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), ψ x := by
    have e : (∫ y in (0 : ℝ)..1, φ y) = ∫ y in (0 : ℝ)..1, ψ (y - 1 / 2) := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only [φ, ψ]
    rw [e, intervalIntegral.integral_comp_sub_right]
    norm_num
  change (∫ v in (-1)..1, G v) = 2 * ∫ x in (-(1 / 2) : ℝ)..(1 / 2), ψ x
  rw [← hsplit, hL, hR, hD]
  ring

end Work.SmallBoxA0
