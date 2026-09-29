import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqD` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 384–511 equal the tabulated `Gv` literals. -/
theorem EqD_p0 : ∀ j < 16, 0 ≤ j → decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0) = true := by decide +kernel
theorem EqD_p1 : ∀ j < 32, 16 ≤ j → decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0) = true := by decide +kernel
theorem EqD_p2 : ∀ j < 48, 32 ≤ j → decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0) = true := by decide +kernel
theorem EqD_p3 : ∀ j < 64, 48 ≤ j → decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0) = true := by decide +kernel
theorem EqD_p4 : ∀ j < 80, 64 ≤ j → decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0) = true := by decide +kernel
theorem EqD_p5 : ∀ j < 96, 80 ≤ j → decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0) = true := by decide +kernel
theorem EqD_p6 : ∀ j < 112, 96 ≤ j → decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0) = true := by decide +kernel
theorem EqD_p7 : ∀ j < 128, 112 ≤ j → decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0) = true := by decide +kernel
theorem EqD : ((List.range 128).all (fun j => decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0))) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases h0 : j < 16
  · exact EqD_p0 j h0 (by omega)
  by_cases h1 : j < 32
  · exact EqD_p1 j h1 (by omega)
  by_cases h2 : j < 48
  · exact EqD_p2 j h2 (by omega)
  by_cases h3 : j < 64
  · exact EqD_p3 j h3 (by omega)
  by_cases h4 : j < 80
  · exact EqD_p4 j h4 (by omega)
  by_cases h5 : j < 96
  · exact EqD_p5 j h5 (by omega)
  by_cases h6 : j < 112
  · exact EqD_p6 j h6 (by omega)
  exact EqD_p7 j hj' (by omega)

theorem EqDv (j : ℕ) (hj : j < 128) : GvT (384 + j) = gvLitL0.getD (384 + j) 0 :=
  all_range_iff.mp EqD j hj

end Work.CNum
