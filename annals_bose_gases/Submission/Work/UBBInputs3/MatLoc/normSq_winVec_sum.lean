import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Int.SuccPred
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.UBBInputs3.MatLoc.prof_norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-- Squared norm of a complex scalar multiple: `‖(r : ℂ) * z‖² = r² ‖z‖²`. -/
lemma norm_sq_real_mul (r : ℝ) (z : ℂ) : ‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, show ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 from by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring]

/-- **Reflecting an interval sum.** `Σ_{m∈[A,B]} f (j - m) = Σ_{s∈[j-B, j-A]} f s`. -/
lemma sum_Icc_reflect (f : ℤ → ℝ) (A B j : ℤ) :
    ∑ m ∈ Finset.Icc A B, f (j - m) = ∑ s ∈ Finset.Icc (j - B) (j - A), f s := by
  refine Finset.sum_nbij' (fun m => j - m) (fun s => j - s) ?_ ?_ ?_ ?_ ?_
  · intro m hm; simp only [Finset.mem_Icc] at hm ⊢; omega
  · intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
  · intro m hm; ring
  · intro s hs; ring
  · intro m hm; rfl

/-- The profile vanishes (hence its square vanishes) outside `[-p, p]`. -/
lemma prof_sq_eq_zero_of_not_mem (p : ℕ) (t : ℤ)
    (ht : t ∉ Finset.Icc (-(p : ℤ)) (p : ℤ)) : (Work.UBBInputs3.prof p t) ^ 2 = 0 := by
  have hlt : (p : ℤ) < |t| := by
    rw [Finset.mem_Icc] at ht
    simp only [not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  have htri : Work.UBBInputs3.tri p t = 0 := by
    simp only [Work.UBBInputs3.tri]
    refine max_eq_left ?_
    have h1 : ((p : ℤ) : ℝ) + 1 ≤ ((|t| : ℤ) : ℝ) := by
      have : (p : ℤ) + 1 ≤ |t| := by omega
      exact_mod_cast this
    rw [Int.cast_abs] at h1
    push_cast at h1
    linarith
  simp [Work.UBBInputs3.prof, htri]

/-- For `j ∈ iRange n`, `Σ_{m ∈ mRange p n} prof (j - m)² = 1`. -/
lemma sum_prof_sq_mRange (n p : ℕ) (j : ℤ) (hj : j ∈ Work.UBBInputs3.iRange n) :
    ∑ m ∈ Work.UBBInputs3.mRange p n, (Work.UBBInputs3.prof p (j - m)) ^ 2 = 1 := by
  have hj' : (0 : ℤ) ≤ j ∧ j ≤ (n : ℤ) - 1 := by
    simpa [Work.UBBInputs3.iRange, Finset.mem_Icc] using hj
  rw [Work.UBBInputs3.mRange]
  rw [sum_Icc_reflect (fun s => (Work.UBBInputs3.prof p s) ^ 2)
        (-(p : ℤ)) ((n : ℤ) - 1 + (p : ℤ)) j]
  have hle := Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside
      (f := fun s => (Work.UBBInputs3.prof p s) ^ 2)
      (a := j - ((n : ℤ) - 1 + (p : ℤ))) (b := j - (-(p : ℤ)))
      (c := -(p : ℤ)) (d := (p : ℤ))
      (by omega) (by omega) (fun t ht => prof_sq_eq_zero_of_not_mem p t ht)
  rw [hle]
  exact prof_norm p

theorem normSq_winVec_sum (n p : ℕ) (ψ : ℤ → ℂ)
    (hψsupp : ∀ j, ψ j ≠ 0 → j ∈ Work.UBBInputs3.iRange n) :
    ∑ m ∈ Work.UBBInputs3.mRange p n,
        Work.UBBInputs3.normSq (Work.UBBInputs3.iRange n) (Work.UBBInputs3.winVec p ψ m)
      = Work.UBBInputs3.normSq (Work.UBBInputs3.iRange n) ψ := by
  have hstep : ∀ m ∈ Work.UBBInputs3.mRange p n,
      Work.UBBInputs3.normSq (Work.UBBInputs3.iRange n) (Work.UBBInputs3.winVec p ψ m)
        = ∑ j ∈ Work.UBBInputs3.iRange n,
            (Work.UBBInputs3.prof p (j - m)) ^ 2 * ‖ψ j‖ ^ 2 := by
    intro m _
    rw [Work.UBBInputs3.normSq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Work.UBBInputs3.winVec]
    exact norm_sq_real_mul (Work.UBBInputs3.prof p (j - m)) (ψ j)
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Work.UBBInputs3.normSq]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.sum_mul, sum_prof_sq_mRange n p j hj, one_mul]

end Work.UBBInputs3.MatLoc
