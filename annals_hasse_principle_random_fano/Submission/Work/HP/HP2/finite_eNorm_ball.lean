import Mathlib
import Submission.Work.HP.Defs

/-!
# Finiteness of Euclidean balls of integer vectors

For a finite index type `ι` and a real radius `R`, the set of integer vectors
`v : ι → ℤ` with Euclidean norm `Work.HP.eNorm v ≤ R` is finite.

The proof bounds each coordinate separately: every summand of `∑ i, (v i : ℝ)^2`
is nonnegative, so `|(v i : ℝ)| ≤ √(∑ j, (v j : ℝ)^2) = eNorm v ≤ R`, and hence each
coordinate lies in the finite interval `[-⌈R⌉₊, ⌈R⌉₊]`.  The set of such vectors is
therefore contained in the finite product of these intervals.

Note that the argument also covers `R < 0`: then `eNorm v ≤ R ≤ ⌈R⌉₊ = 0` forces
every coordinate to vanish, and the inclusion is the vacuous one.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.HP2

open Finset

/-- Each coordinate of an integer vector is bounded in absolute value by `eNorm`. -/
lemma abs_coord_le_eNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    |(v i : ℝ)| ≤ Work.HP.eNorm v := by
  have hterm : (v i : ℝ) ^ 2 ≤ ∑ j, (v j : ℝ) ^ 2 := by
    have h := Finset.single_le_sum (f := fun j => (v j : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    simpa using h
  calc |(v i : ℝ)| = Real.sqrt ((v i : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (v j : ℝ) ^ 2) := Real.sqrt_le_sqrt hterm
    _ = Work.HP.eNorm v := rfl

/-- The set of integer vectors of Euclidean norm at most `R` is finite. -/
lemma finite_eNorm_ball {ι : Type*} [Fintype ι] (R : ℝ) :
    {v : ι → ℤ | Work.HP.eNorm v ≤ R}.Finite := by
  classical
  refine (Finset.finite_toSet (Fintype.piFinset
    (fun _ : ι => Finset.Icc (-(⌈R⌉₊ : ℤ)) (⌈R⌉₊ : ℤ)))).subset ?_
  intro v hv
  simp only [Finset.mem_coe] at hv ⊢
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h2 : |(v i : ℝ)| ≤ (⌈R⌉₊ : ℝ) :=
    le_trans (le_trans (abs_coord_le_eNorm v i) hv) (Nat.le_ceil R)
  obtain ⟨h3, h4⟩ := abs_le.mp h2
  exact ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩

end Work.HP.HP2
