import Mathlib
import Submission.Work.BMF.N4chain.linnik_newton_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N4chain

/-- If `p` divides the difference of the integer power sum `∑ i, ((a i).val) ^ j` and `H j`,
then the corresponding power sum of the residues of `a` in `ZMod p` equals `H j`. -/
theorem psumEval_eq_of_dvd {p k N : ℕ} (a : Fin k → Fin N) (H : ℕ → ℕ) (j : ℕ)
    (h : (p : ℤ) ∣ ((∑ i, ((a i).val : ℤ) ^ j) - (H j : ℤ))) :
    Work.BMF.N4chain.psumEval (fun i => ((a i).val : ZMod p)) j = ((H j : ℕ) : ZMod p) := by
  have hdiff : (((∑ i, ((a i).val : ℤ) ^ j) - (H j : ℤ) : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h
  rw [Int.cast_sub, sub_eq_zero] at hdiff
  have key : Work.BMF.N4chain.psumEval (fun i => ((a i).val : ZMod p)) j
      = ((∑ i, ((a i).val : ℤ) ^ j : ℤ) : ZMod p) := by
    simp only [psumEval]
    push_cast
    rfl
  rw [key, hdiff, Int.cast_natCast]

end Work.BMF.N4chain
