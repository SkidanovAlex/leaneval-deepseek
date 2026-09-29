import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.DnA` — cheap chunk of the tabulated certificate (lower bound for gvT) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `gvT` values on arcs 0–127 are above `LOG1E13LB`. -/
theorem DnA_p0 : ∀ j < 16, 0 ≤ j → decide (LOG1E13LB ≤ gvT (0 + j)) = true := by decide +kernel
theorem DnA_p1 : ∀ j < 32, 16 ≤ j → decide (LOG1E13LB ≤ gvT (0 + j)) = true := by decide +kernel
theorem DnA_p2 : ∀ j < 48, 32 ≤ j → decide (LOG1E13LB ≤ gvT (0 + j)) = true := by decide +kernel
theorem DnA_p3 : ∀ j < 64, 48 ≤ j → decide (LOG1E13LB ≤ gvT (0 + j)) = true := by decide +kernel
theorem DnA_p4 : ∀ j < 80, 64 ≤ j → decide (LOG1E13LB ≤ gvT (0 + j)) = true := by decide +kernel
theorem DnA_p5 : ∀ j < 96, 80 ≤ j → decide (LOG1E13LB ≤ gvT (0 + j)) = true := by decide +kernel
theorem DnA_p6 : ∀ j < 112, 96 ≤ j → decide (LOG1E13LB ≤ gvT (0 + j)) = true := by decide +kernel
theorem DnA_p7 : ∀ j < 128, 112 ≤ j → decide (LOG1E13LB ≤ gvT (0 + j)) = true := by decide +kernel
theorem DnA : ((List.range 128).all (fun j => decide (LOG1E13LB ≤ gvT (0 + j)))) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases h0 : j < 16
  · exact DnA_p0 j h0 (by omega)
  by_cases h1 : j < 32
  · exact DnA_p1 j h1 (by omega)
  by_cases h2 : j < 48
  · exact DnA_p2 j h2 (by omega)
  by_cases h3 : j < 64
  · exact DnA_p3 j h3 (by omega)
  by_cases h4 : j < 80
  · exact DnA_p4 j h4 (by omega)
  by_cases h5 : j < 96
  · exact DnA_p5 j h5 (by omega)
  by_cases h6 : j < 112
  · exact DnA_p6 j h6 (by omega)
  exact DnA_p7 j hj' (by omega)

theorem DnAv (j : ℕ) (hj : j < 128) : LOG1E13LB ≤ gvT (0 + j) :=
  all_range_iff.mp DnA j hj

end Work.CNum
