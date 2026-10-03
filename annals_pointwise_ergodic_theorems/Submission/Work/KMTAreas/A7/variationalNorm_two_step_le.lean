import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- The variational norm of a constant sequence `n ↦ c` is at most `‖c‖ₑ`: the supremum part is
`‖c‖ₑ` and the variation part vanishes because all increments are zero. -/
lemma variationalNorm_const_le {r : ℝ≥0} (hr : 1 ≤ r) (c : ℂ) :
    variationalNorm r (fun _ : ℕ => c) ≤ ‖c‖ₑ := by
  rw [variationalNorm_eq_add]
  have hsup : (⨆ n, ‖(fun _ : ℕ => c) n‖ₑ) = ‖c‖ₑ := by simp
  have hvar : varPart r (fun _ : ℕ => c) ≤ 0 := by
    refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
    have h := norm_toLp_le_sum_norm hr (fun i : Fin J => c - c)
    have h0 : ‖WithLp.toLp r (fun i : Fin J => c - c)‖ ≤ 0 := by simpa using h
    simpa using ENNReal.ofReal_le_ofReal h0
  rw [hsup]
  calc ‖c‖ₑ + varPart r (fun _ : ℕ => c) ≤ ‖c‖ₑ + 0 := add_le_add le_rfl hvar
    _ = ‖c‖ₑ := add_zero _

/-- A sequence which is `1` everywhere except at the single index `1`, where it takes the value
`b`, has variational norm at most `1 + 4‖b - 1‖`. -/
theorem variationalNorm_two_step_le (r : NNReal) (hr : 1 ≤ r) (b : ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n = 1 then b else 1) ≤ 1 + 4 * ‖b - 1‖ₑ := by
  have hdecomp : (fun n : ℕ => if n = 1 then b else 1)
      = (fun _ : ℕ => (1:ℂ)) + (fun n : ℕ => if n = 1 then b - 1 else 0) := by
    funext n
    by_cases h : n = 1 <;> simp [h]
  rw [hdecomp]
  calc variationalNorm r ((fun _ : ℕ => (1:ℂ)) + (fun n : ℕ => if n = 1 then b - 1 else 0))
      ≤ variationalNorm r (fun _ : ℕ => (1:ℂ))
        + variationalNorm r (fun n : ℕ => if n = 1 then b - 1 else 0) :=
        variationalNorm_add_le hr _ _
    _ ≤ 1 + 4 * ‖b - 1‖ₑ := by
        have h1 : variationalNorm r (fun _ : ℕ => (1:ℂ)) ≤ (1:ℝ≥0∞) := by
          simpa using variationalNorm_const_le (r := r) hr (1 : ℂ)
        exact add_le_add h1 (variationalNorm_spike_le hr 1 (b - 1))

end Work.KMTAreas.A7
