import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqE` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 512–639 equal the tabulated `Gv` literals. -/
theorem EqE_p0 : ∀ j < 16, 0 ≤ j → decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0) = true := by decide +kernel
theorem EqE_p1 : ∀ j < 32, 16 ≤ j → decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0) = true := by decide +kernel
theorem EqE_p2 : ∀ j < 48, 32 ≤ j → decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0) = true := by decide +kernel
theorem EqE_p3 : ∀ j < 64, 48 ≤ j → decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0) = true := by decide +kernel
theorem EqE_p4 : ∀ j < 80, 64 ≤ j → decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0) = true := by decide +kernel
theorem EqE_p5 : ∀ j < 96, 80 ≤ j → decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0) = true := by decide +kernel
theorem EqE_p6 : ∀ j < 112, 96 ≤ j → decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0) = true := by decide +kernel
theorem EqE_p7 : ∀ j < 128, 112 ≤ j → decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0) = true := by decide +kernel
theorem EqE : ((List.range 128).all (fun j => decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0))) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases h0 : j < 16
  · exact EqE_p0 j h0 (by omega)
  by_cases h1 : j < 32
  · exact EqE_p1 j h1 (by omega)
  by_cases h2 : j < 48
  · exact EqE_p2 j h2 (by omega)
  by_cases h3 : j < 64
  · exact EqE_p3 j h3 (by omega)
  by_cases h4 : j < 80
  · exact EqE_p4 j h4 (by omega)
  by_cases h5 : j < 96
  · exact EqE_p5 j h5 (by omega)
  by_cases h6 : j < 112
  · exact EqE_p6 j h6 (by omega)
  exact EqE_p7 j hj' (by omega)

theorem EqEv (j : ℕ) (hj : j < 128) : GvT (512 + j) = gvLitL0.getD (512 + j) 0 :=
  all_range_iff.mp EqE j hj

end Work.CNum
