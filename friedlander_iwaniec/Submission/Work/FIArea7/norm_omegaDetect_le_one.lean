import Mathlib
import Submission.Work.FIArea7.WBOmega
import Submission.Work.FIArea7.Section16Detection
import Submission.Work.FIArea7.norm_ratWeight_charSum_le

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem norm_omegaDetect_le_one (Q e : ℕ) [NeZero Q] (z1 z2 : GaussianInt)
    (h1 : Nat.Coprime (Work.FIPlan.gnorm z1) Q) (h2 : Nat.Coprime (Work.FIPlan.gnorm z2) Q) :
    ‖Work.FIArea7.omegaDetect Q e z1 z2‖ ≤ 1 := by
  rw [omegaDetect, dif_neg (NeZero.ne Q)]
  rw [sum_omegaDetect_eq_ratWeight Q e z1 z2 h1 h2]
  set p0 : GaussUnit Q := gaussUnitOf Q z1 h1 * (gaussUnitOf Q z2 h2)⁻¹ with hp0
  have hiff : ∀ p : GaussUnit Q, (gaussUnitOf Q z1 h1 = p * gaussUnitOf Q z2 h2) ↔ p = p0 := by
    intro p
    constructor
    · intro h
      have h' := congrArg (fun x => x * (gaussUnitOf Q z2 h2)⁻¹) h
      rw [mul_assoc, mul_inv_cancel, mul_one] at h'
      rw [← h', ← hp0]
    · intro h
      rw [h, hp0, mul_assoc, inv_mul_cancel, mul_one]
  have hterm : ∀ p : GaussUnit Q,
      (if gaussUnitOf Q z1 h1 = p * gaussUnitOf Q z2 h2 then ratWeight Q e p else 0)
        = (if p = p0 then ratWeight Q e p else 0) := by
    intro p
    by_cases h : p = p0
    · rw [if_pos ((hiff p).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((hiff p).mp hc)), if_neg h]
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  exact norm_ratWeight_le_one Q e p0

end

end Work.FIArea7
