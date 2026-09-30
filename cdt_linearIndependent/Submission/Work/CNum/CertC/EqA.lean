import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqA` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 0–127 equal the tabulated `Gv` literals. -/
theorem EqA_p0 : ∀ j < 16, 0 ≤ j → decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0) = true := by decide +kernel
theorem EqA_p1 : ∀ j < 32, 16 ≤ j → decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0) = true := by decide +kernel
theorem EqA_p2 : ∀ j < 48, 32 ≤ j → decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0) = true := by decide +kernel
theorem EqA_p3 : ∀ j < 64, 48 ≤ j → decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0) = true := by decide +kernel
theorem EqA_p4 : ∀ j < 80, 64 ≤ j → decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0) = true := by decide +kernel
theorem EqA_p5 : ∀ j < 96, 80 ≤ j → decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0) = true := by decide +kernel
theorem EqA_p6 : ∀ j < 112, 96 ≤ j → decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0) = true := by decide +kernel
theorem EqA_p7 : ∀ j < 128, 112 ≤ j → decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0) = true := by decide +kernel
theorem EqA : ((List.range 128).all (fun j => decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0))) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases h0 : j < 16
  · exact EqA_p0 j h0 (by omega)
  by_cases h1 : j < 32
  · exact EqA_p1 j h1 (by omega)
  by_cases h2 : j < 48
  · exact EqA_p2 j h2 (by omega)
  by_cases h3 : j < 64
  · exact EqA_p3 j h3 (by omega)
  by_cases h4 : j < 80
  · exact EqA_p4 j h4 (by omega)
  by_cases h5 : j < 96
  · exact EqA_p5 j h5 (by omega)
  by_cases h6 : j < 112
  · exact EqA_p6 j h6 (by omega)
  exact EqA_p7 j hj' (by omega)

theorem EqAv (j : ℕ) (hj : j < 128) : GvT (0 + j) = gvLitL0.getD (0 + j) 0 :=
  all_range_iff.mp EqA j hj

end Work.CNum
