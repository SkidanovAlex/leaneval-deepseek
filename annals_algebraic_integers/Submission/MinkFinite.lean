import Mathlib

noncomputable section
open scoped BigOperators

/-!
# Finiteness of bounded integer points

`Submission.MinkFinite.finite_int_norm_le`: for `R ≥ 0`, there are only finitely many
integer-valued functions `z : Fin d → ℝ` (i.e. every coordinate `z j` is the image of
an integer) with sup-norm `‖z‖ ≤ R`.  This is the discreteness of the standard lattice
`ℤ^d ⊆ ℝ^d`.  (Used by `Submission.MinkGlue` in the greedy successive-minima recursion;
prove it e.g. with mathlib's `ZLattice`/`ZSpan` API applied to the standard basis of
`Fin d → ℝ`, or by a direct coordinate/injection argument into a finite product.)
-/

namespace Submission.MinkFinite

/-- The integers whose real casts lie in the interval `[-R, R]` form a finite set.

For every `R : ℝ` (no non-negativity assumption is needed) the integer `n` satisfies
`-⌈R⌉ ≤ n ≤ ⌈R⌉`, and a closed integer interval is finite. -/
lemma finite_int_abs_le (R : ℝ) : Set.Finite {n : ℤ | |(n : ℝ)| ≤ R} := by
  let M : ℤ := ⌈R⌉
  have hRM : R ≤ (M : ℝ) := by simpa [M] using (Int.le_ceil R)
  refine (Set.finite_Icc (-M) M).subset ?_
  intro n hn
  change |(n : ℝ)| ≤ R at hn
  rcases abs_le.mp hn with ⟨hneg, hpos⟩
  constructor
  · exact_mod_cast (le_trans (neg_le_neg hRM) hneg)
  · exact_mod_cast (le_trans hpos hRM)

lemma finite_int_norm_le (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Set.Finite {z : Fin d → ℝ | (∀ j : Fin d, ∃ n : ℤ, (n : ℝ) = z j) ∧ ‖z‖ ≤ R} := by
  have hR0 : 0 ≤ R := hR
  let B : Set ℤ := {n : ℤ | |(n : ℝ)| ≤ R}
  have hB : B.Finite := finite_int_abs_le R
  let T : Fin d → Set ℝ := fun _ => (fun n : ℤ => (n : ℝ)) '' B
  have hT : ∀ j : Fin d, (T j).Finite := by
    intro j
    exact Set.Finite.image (fun n : ℤ => (n : ℝ)) hB
  refine (Set.Finite.pi hT).subset ?_
  rintro z ⟨hint, hz⟩
  rw [Set.mem_univ_pi]
  intro j
  rcases hint j with ⟨n, hn⟩
  refine ⟨n, ?_, hn⟩
  have hzabs : |(n : ℝ)| ≤ R := by
    calc
      |(n : ℝ)| = ‖z j‖ := by rw [hn, Real.norm_eq_abs]
      _ ≤ ‖z‖ := norm_le_pi_norm z j
      _ ≤ R := hz
  exact hzabs

end Submission.MinkFinite
