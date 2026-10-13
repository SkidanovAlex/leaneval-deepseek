import Mathlib
import Submission.Work.WilG0.Defs

set_option autoImplicit false
open Classical

namespace Work.WilG0

open WilkiesDesign

/-- The evaluation of `diagPoly` is the sum of squares `Σ_j (W_j - X_{ι j})²`. -/
theorem eval_diagPoly (n m : ℕ) (ι : Fin m → Fin n) (z : Fin (n + m) → ℝ) :
    MvPolynomial.eval z (diagPoly n m ι)
      = ∑ j : Fin m, (z (Fin.natAdd n j) - z (Fin.castAdd m (ι j)))^2 := by
  unfold diagPoly
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X]
  ring

theorem diagSet_eq (n m : ℕ) (ι : Fin m → Fin n) :
    diagSet n m ι = {z : Fin (n + m) → ℝ | MvPolynomial.eval z (diagPoly n m ι) = 0} := by
  ext z
  simp only [Set.mem_ofPred_eq]
  rw [eval_diagPoly]
  unfold diagSet
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    apply Finset.sum_eq_zero
    intro j _
    rw [h j]; ring
  · intro h j
    have hmem := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (z (Fin.natAdd n i) - z (Fin.castAdd m (ι i))))).mp h
    have hj := hmem j (Finset.mem_univ j)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hj)

end Work.WilG0
