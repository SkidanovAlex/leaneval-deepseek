import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germCHelpers

/-! The backward branch `invBranch a s` is holomorphic where the radicand has positive real
part (hence lies in the principal slit plane). -/

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

theorem analytic_invBranch {a : ℝ} {s : Bool} {Q : ℂ × ℂ}
    (h : 0 < (((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2)).re) :
    AnalyticAt ℂ (invBranch a s) Q := by
  have hΔ : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ∈ Complex.slitPlane :=
    Or.inl h
  have hD : AnalyticAt ℂ (fun Q : ℂ × ℂ => (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) Q :=
    (((analyticAt_fst : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.1) Q).add
      analyticAt_const).pow 2).add
      ((analyticAt_snd : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.2) Q).pow 2)
  have hroot : AnalyticAt ℂ
      (fun Q : ℂ × ℂ => ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) Q :=
    hD.cpow analyticAt_const hΔ
  have hne : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ≠ 0 := Complex.slitPlane_ne_zero hΔ
  have hrootne : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h0
    have h2 := Work.EQ.cpow_half_sq ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2)
    rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h2
    exact hne h2.symm
  have hfst : AnalyticAt ℂ (fun Q : ℂ × ℂ =>
      -Q.1 + (if s then (1 : ℂ) else -1) * (Q.1 + ((a / 2 : ℝ) : ℂ))
        / ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) Q :=
    ((analyticAt_fst : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.1) Q).neg).add
      ((analyticAt_const.mul
        (((analyticAt_fst : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.1) Q).add
          analyticAt_const))).div hroot hrootne)
  have hsnd : AnalyticAt ℂ (fun Q : ℂ × ℂ =>
      -Q.2 + (if s then (1 : ℂ) else -1) * Q.2
        / ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) Q :=
    ((analyticAt_snd : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.2) Q).neg).add
      ((analyticAt_const.mul
        ((analyticAt_snd : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.2) Q))).div hroot hrootne)
  have hiff : invBranch a s = fun Q : ℂ × ℂ =>
      (-Q.1 + (if s then (1 : ℂ) else -1) * (Q.1 + ((a / 2 : ℝ) : ℂ))
        / ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ),
       -Q.2 + (if s then (1 : ℂ) else -1) * Q.2
        / ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) := rfl
  rw [hiff]
  exact hfst.prod hsnd

end

end Work.EQ.FanTri
