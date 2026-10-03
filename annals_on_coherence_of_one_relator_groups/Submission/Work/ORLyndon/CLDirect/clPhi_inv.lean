import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.clPhi_one
import Submission.Work.ORLyndon.CLDirect.clPhi_mul

namespace Work.ORLyndon.CLDirect

/-- `φ(n⁻¹) = −φ(n)`. Sketch: `clPhi_mul` at `(n, n⁻¹)` (`Subgroup.inv_mem hn` for the second membership, and `Subgroup.mul_mem` for the use below) gives `φ(n * n⁻¹) = φ n + φ n⁻¹`; rewrite `n * n⁻¹ = 1` and `clPhi_one` to get `φ n + φ n⁻¹ = 0`; conclude with `eq_neg_of_add_eq_zero_left`. -/
theorem clPhi_inv {X : Type*} [DecidableEq X] {K : Type*} [Field K] {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ) {n : FreeGroup X}
    (hn : n ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X))) :
    Work.ORLyndon.CLDirect.clPhi (K := K) D l n⁻¹ =
      - Work.ORLyndon.CLDirect.clPhi (K := K) D l n := by
  have hmul := clPhi_mul (K := K) D l hn
    ((Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X))).inv_mem hn)
  rw [mul_inv_cancel, clPhi_one] at hmul
  exact eq_neg_of_add_eq_zero_right hmul.symm

end Work.ORLyndon.CLDirect
