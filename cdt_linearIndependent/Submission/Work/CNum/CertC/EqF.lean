import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqF` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 640–767 equal the tabulated `Gv` literals. -/
theorem EqF_p0 : ∀ j < 16, 0 ≤ j → decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0) = true := by decide +kernel
theorem EqF_p1 : ∀ j < 32, 16 ≤ j → decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0) = true := by decide +kernel
theorem EqF_p2 : ∀ j < 48, 32 ≤ j → decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0) = true := by decide +kernel
theorem EqF_p3 : ∀ j < 64, 48 ≤ j → decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0) = true := by decide +kernel
theorem EqF_p4 : ∀ j < 80, 64 ≤ j → decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0) = true := by decide +kernel
theorem EqF_p5 : ∀ j < 96, 80 ≤ j → decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0) = true := by decide +kernel
theorem EqF_p6 : ∀ j < 112, 96 ≤ j → decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0) = true := by decide +kernel
theorem EqF_p7 : ∀ j < 128, 112 ≤ j → decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0) = true := by decide +kernel
theorem EqF : ((List.range 128).all (fun j => decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0))) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases h0 : j < 16
  · exact EqF_p0 j h0 (by omega)
  by_cases h1 : j < 32
  · exact EqF_p1 j h1 (by omega)
  by_cases h2 : j < 48
  · exact EqF_p2 j h2 (by omega)
  by_cases h3 : j < 64
  · exact EqF_p3 j h3 (by omega)
  by_cases h4 : j < 80
  · exact EqF_p4 j h4 (by omega)
  by_cases h5 : j < 96
  · exact EqF_p5 j h5 (by omega)
  by_cases h6 : j < 112
  · exact EqF_p6 j h6 (by omega)
  exact EqF_p7 j hj' (by omega)

theorem EqFv (j : ℕ) (hj : j < 128) : GvT (640 + j) = gvLitL0.getD (640 + j) 0 :=
  all_range_iff.mp EqF j hj

end Work.CNum
