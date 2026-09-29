import Mathlib

namespace Work.TMComp.RedProj

/-- The one-sided (natural-indexed) exponential decay series `∑ exp (-(η * n))` converges
for `η > 0`. -/
lemma summable_nat_exp_neg_mul (η : ℝ) (hη : 0 < η) :
    Summable (fun n : ℕ => Real.exp (-(η * (n : ℝ)))) := by
  have h := (Real.summable_exp_nat_mul_iff (a := -η)).mpr (by linarith : -η < 0)
  convert h using 1
  ext n
  ring_nf

theorem summable_int_exp_neg (η : ℝ) (hη : 0 < η) :
    Summable (fun k : ℤ => Real.exp (-(η * |(k : ℝ)|))) := by
  apply Summable.of_nat_of_neg (f := fun k : ℤ => Real.exp (-(η * |(k : ℝ)|)))
  · simpa using summable_nat_exp_neg_mul η hη
  · simpa using summable_nat_exp_neg_mul η hη

end Work.TMComp.RedProj
