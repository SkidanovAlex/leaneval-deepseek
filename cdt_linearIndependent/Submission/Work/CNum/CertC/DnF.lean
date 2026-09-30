import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.DnF` — cheap chunk of the tabulated certificate (lower bound for gvT) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `gvT` values on arcs 640–767 are above `LOG1E13LB`. -/
theorem DnF_p0 : ∀ j < 16, 0 ≤ j → decide (LOG1E13LB ≤ gvT (640 + j)) = true := by decide +kernel
theorem DnF_p1 : ∀ j < 32, 16 ≤ j → decide (LOG1E13LB ≤ gvT (640 + j)) = true := by decide +kernel
theorem DnF_p2 : ∀ j < 48, 32 ≤ j → decide (LOG1E13LB ≤ gvT (640 + j)) = true := by decide +kernel
theorem DnF_p3 : ∀ j < 64, 48 ≤ j → decide (LOG1E13LB ≤ gvT (640 + j)) = true := by decide +kernel
theorem DnF_p4 : ∀ j < 80, 64 ≤ j → decide (LOG1E13LB ≤ gvT (640 + j)) = true := by decide +kernel
theorem DnF_p5 : ∀ j < 96, 80 ≤ j → decide (LOG1E13LB ≤ gvT (640 + j)) = true := by decide +kernel
theorem DnF_p6 : ∀ j < 112, 96 ≤ j → decide (LOG1E13LB ≤ gvT (640 + j)) = true := by decide +kernel
theorem DnF_p7 : ∀ j < 128, 112 ≤ j → decide (LOG1E13LB ≤ gvT (640 + j)) = true := by decide +kernel
theorem DnF : ((List.range 128).all (fun j => decide (LOG1E13LB ≤ gvT (640 + j)))) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases h0 : j < 16
  · exact DnF_p0 j h0 (by omega)
  by_cases h1 : j < 32
  · exact DnF_p1 j h1 (by omega)
  by_cases h2 : j < 48
  · exact DnF_p2 j h2 (by omega)
  by_cases h3 : j < 64
  · exact DnF_p3 j h3 (by omega)
  by_cases h4 : j < 80
  · exact DnF_p4 j h4 (by omega)
  by_cases h5 : j < 96
  · exact DnF_p5 j h5 (by omega)
  by_cases h6 : j < 112
  · exact DnF_p6 j h6 (by omega)
  exact DnF_p7 j hj' (by omega)

theorem DnFv (j : ℕ) (hj : j < 128) : LOG1E13LB ≤ gvT (640 + j) :=
  all_range_iff.mp DnF j hj

end Work.CNum
