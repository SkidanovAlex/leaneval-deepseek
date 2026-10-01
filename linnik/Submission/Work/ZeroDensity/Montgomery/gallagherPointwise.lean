import Mathlib

namespace Work.ZeroDensity.Montgomery

open scoped RealInnerProductSpace
open MeasureTheory

lemma gallagherPointwise {g g' : ℝ → ℂ} (hderiv : ∀ x, HasDerivAt g (g' x) x)
    (hcont : Continuous g') {h s x : ℝ} (hh : 0 < h) (hx : x ∈ Set.Icc (s - h) (s + h)) :
    ‖g s‖ ^ 2 ≤ ‖g x‖ ^ 2 + 2 * ∫ y in (s - h)..(s + h), ‖g y‖ * ‖g' y‖ := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hderiv t).continuousAt)
  have hF'cont : Continuous (fun y => (2:ℝ) * inner ℝ (g y) (g' y)) :=
    continuous_const.mul (hgc.inner hcont)
  -- Fundamental theorem of calculus: the derivative of ‖g ·‖² integrated from x to s
  have hFTC : ∫ y in x..s, (2:ℝ) * inner ℝ (g y) (g' y) = ‖g s‖ ^ 2 - ‖g x‖ ^ 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => (hderiv y).norm_sq) (hF'cont.intervalIntegrable x s)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (s - h) (s + h))]
      fun y => |(2:ℝ) * inner ℝ (g y) (g' y)| :=
    Filter.Eventually.of_forall (fun y => abs_nonneg _)
  have hIabs : IntervalIntegrable (fun y => |(2:ℝ) * inner ℝ (g y) (g' y)|)
      volume (s - h) (s + h) := hF'cont.abs.intervalIntegrable _ _
  -- Step 1: ∫_x^s F' ≤ ∫_{s-h}^{s+h} |F'|
  have key : ∫ y in x..s, (2:ℝ) * inner ℝ (g y) (g' y)
      ≤ ∫ y in (s - h)..(s + h), |(2:ℝ) * inner ℝ (g y) (g' y)| := by
    rcases le_total x s with hxs | hsx
    · calc ∫ y in x..s, (2:ℝ) * inner ℝ (g y) (g' y)
          ≤ ∫ y in x..s, |(2:ℝ) * inner ℝ (g y) (g' y)| :=
            intervalIntegral.integral_mono_on hxs (hF'cont.intervalIntegrable x s)
              (hF'cont.abs.intervalIntegrable x s) (fun y _ => le_abs_self _)
        _ ≤ ∫ y in (s - h)..(s + h), |(2:ℝ) * inner ℝ (g y) (g' y)| :=
            intervalIntegral.integral_mono_interval hx.1 hxs (by linarith) hnn hIabs
    · have hsymm : ∫ y in x..s, (2:ℝ) * inner ℝ (g y) (g' y)
            = - ∫ y in s..x, (2:ℝ) * inner ℝ (g y) (g' y) :=
        intervalIntegral.integral_symm s x
      rw [hsymm]
      calc -∫ y in s..x, (2:ℝ) * inner ℝ (g y) (g' y)
          ≤ |∫ y in s..x, (2:ℝ) * inner ℝ (g y) (g' y)| := neg_le_abs _
        _ ≤ ∫ y in s..x, |(2:ℝ) * inner ℝ (g y) (g' y)| :=
            intervalIntegral.abs_integral_le_integral_abs hsx
        _ ≤ ∫ y in (s - h)..(s + h), |(2:ℝ) * inner ℝ (g y) (g' y)| :=
            intervalIntegral.integral_mono_interval (by linarith) hsx hx.2 hnn hIabs
  -- Step 2: ∫_{s-h}^{s+h} |F'| ≤ 2 * ∫_{s-h}^{s+h} ‖g‖‖g'‖
  have hstep2 : ∫ y in (s - h)..(s + h), |(2:ℝ) * inner ℝ (g y) (g' y)|
      ≤ 2 * ∫ y in (s - h)..(s + h), ‖g y‖ * ‖g' y‖ := by
    have hle1 : s - h ≤ s + h := by linarith
    have hIrhs : IntervalIntegrable (fun y => (2:ℝ) * (‖g y‖ * ‖g' y‖))
        volume (s - h) (s + h) :=
      (continuous_const.mul (hgc.norm.mul hcont.norm)).intervalIntegrable _ _
    calc ∫ y in (s - h)..(s + h), |(2:ℝ) * inner ℝ (g y) (g' y)|
        ≤ ∫ y in (s - h)..(s + h), (2:ℝ) * (‖g y‖ * ‖g' y‖) :=
          intervalIntegral.integral_mono_on hle1 hIabs hIrhs (fun y _ => by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
            exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num))
      _ = 2 * ∫ y in (s - h)..(s + h), ‖g y‖ * ‖g' y‖ :=
          intervalIntegral.integral_const_mul 2 _
  have hmain : ‖g s‖ ^ 2 - ‖g x‖ ^ 2 ≤ 2 * ∫ y in (s - h)..(s + h), ‖g y‖ * ‖g' y‖ := by
    rw [← hFTC]
    exact le_trans key hstep2
  linarith

end Work.ZeroDensity.Montgomery
