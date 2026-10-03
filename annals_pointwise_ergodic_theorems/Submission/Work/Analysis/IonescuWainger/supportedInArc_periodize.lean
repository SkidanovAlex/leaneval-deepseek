import Submission.Work.Analysis.IonescuWainger.Symbol

/-!
# Support of the periodised symbol
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

open AddCircle

theorem supportedInArc_periodize {k : ℤ} {φ : ℝ → ℂ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ realArc k) (hsum : ∀ x : ℝ, Summable fun j : ℤ => φ (x + j)) :
    SupportedInArc k (periodize φ) := by
  intro ξ hξ
  obtain ⟨j, hj⟩ : ∃ j : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hξ ?_
    unfold periodize
    have h0 : (fun k : ℤ => φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k))
        = fun _ : ℤ => (0 : ℂ) := funext fun k => hcon k
    rw [h0, tsum_zero]
  refine ⟨(AddCircle.equivIco (1 : ℝ) 0 ξ).val + j, hφ _ hj, ?_⟩
  have hxc : ((AddCircle.equivIco (1 : ℝ) 0 ξ).val : Circle) = ξ := by simp
  have hjc : ((j : ℝ) : Circle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨j, by simp⟩
  rw [AddCircle.coe_add, hxc, hjc, add_zero]
