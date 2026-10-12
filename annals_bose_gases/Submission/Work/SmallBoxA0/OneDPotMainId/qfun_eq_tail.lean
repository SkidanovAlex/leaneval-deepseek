import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxA0.OneDPotMainId.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.SmallBoxA0.OneDPotMainId

/-- Since `p` vanishes on `[R, ∞)`, the tail flux `qfun p r = ∫_r^∞ (s^2 p s)/s ds`
agrees, for `0 < r ≤ R`, with the honest interval integral `TailI p R r = ∫_r^R s p s ds`. -/
theorem qfun_eq_tail {R : ℝ} (p : ℝ → ℝ)
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    Work.SmallBoxA0.qfun p r = Work.SmallBoxA0.TailI p R r := by
  rw [Work.SmallBoxA0.qfun, Work.SmallBoxA0.TailI,
    ← Work.SmallBoxA0.integral_Ioo_eq_intervalIntegral hrR (f := fun s => s * p s)]
  -- The integrand `(s^2 * p s)/s` equals `s * p s` on `Ioi r` (where `s > 0`).
  have h1 : ∫ s in Set.Ioi r, (s ^ 2 * p s) / s = ∫ s in Set.Ioi r, s * p s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt (lt_trans hr hs)
    show s ^ 2 * p s / s = s * p s
    rw [show s ^ 2 * p s = (s * p s) * s by ring, mul_div_cancel_right₀ _ hs0]
  rw [h1]
  -- `s * p s` vanishes on `Ioi r \ Ioo r R ⊆ [R, ∞)`, so the integrals agree.
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun x hx => hx.1) (fun x hx => by
      have hxR : R ≤ x := le_of_not_gt (fun h => hx.2 ⟨hx.1, h⟩)
      rw [hp0 x hxR, mul_zero])

end Work.SmallBoxA0.OneDPotMainId
