import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqC` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 256–383 equal the tabulated `Gv` literals. -/
theorem EqC_p0 : ∀ j < 16, 0 ≤ j → decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0) = true := by decide +kernel
theorem EqC_p1 : ∀ j < 32, 16 ≤ j → decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0) = true := by decide +kernel
theorem EqC_p2 : ∀ j < 48, 32 ≤ j → decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0) = true := by decide +kernel
theorem EqC_p3 : ∀ j < 64, 48 ≤ j → decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0) = true := by decide +kernel
theorem EqC_p4 : ∀ j < 80, 64 ≤ j → decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0) = true := by decide +kernel
theorem EqC_p5 : ∀ j < 96, 80 ≤ j → decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0) = true := by decide +kernel
theorem EqC_p6 : ∀ j < 112, 96 ≤ j → decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0) = true := by decide +kernel
theorem EqC_p7 : ∀ j < 128, 112 ≤ j → decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0) = true := by decide +kernel
theorem EqC : ((List.range 128).all (fun j => decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0))) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases h0 : j < 16
  · exact EqC_p0 j h0 (by omega)
  by_cases h1 : j < 32
  · exact EqC_p1 j h1 (by omega)
  by_cases h2 : j < 48
  · exact EqC_p2 j h2 (by omega)
  by_cases h3 : j < 64
  · exact EqC_p3 j h3 (by omega)
  by_cases h4 : j < 80
  · exact EqC_p4 j h4 (by omega)
  by_cases h5 : j < 96
  · exact EqC_p5 j h5 (by omega)
  by_cases h6 : j < 112
  · exact EqC_p6 j h6 (by omega)
  exact EqC_p7 j hj' (by omega)

theorem EqCv (j : ℕ) (hj : j < 128) : GvT (256 + j) = gvLitL0.getD (256 + j) 0 :=
  all_range_iff.mp EqC j hj

end Work.CNum
