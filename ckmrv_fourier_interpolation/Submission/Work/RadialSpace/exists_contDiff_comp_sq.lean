import Mathlib
import Submission.Work.RadialSpace.Basic
import Submission.Work.RadialSpace.EvenHalfDeriv
import Submission.Work.RadialSpace.evenHalfDeriv_eq
import Submission.Work.RadialSpace.contDiff_glue
import Submission.Work.RadialSpace.borel_lemma
import Submission.Work.RadialSpace.tendsto_iteratedDeriv_comp_sqrt

namespace Work.RadialSpace

/-- Every even smooth function `g : ℝ → ℂ` is a smooth function of `t ^ 2`:
there is a smooth `h : ℝ → ℂ` with `g t = h (t ^ 2)` for all `t`.

The construction writes `g (√s)` for `s > 0` and extends it across `s = 0` by
choosing `h` on `(-∞, 0]` to be the Borel sum with the prescribed one-sided
derivatives `(evenHalfDeriv^[m] g) 0` (`borel_lemma`); the result is smooth by
`contDiff_glue`. -/
theorem exists_contDiff_comp_sq {g : ℝ → ℂ} (hg : ContDiff ℝ Work.RadialSpace.Smooth g)
    (he : Function.Even g) :
    ∃ h : ℝ → ℂ, ContDiff ℝ Work.RadialSpace.Smooth h ∧ ∀ t : ℝ, g t = h (t ^ 2) := by
  obtain ⟨W, hW, hWderiv⟩ := borel_lemma (fun m : ℕ => (evenHalfDeriv^[m]) g 0)
  refine ⟨fun s => if 0 < s then g (Real.sqrt s) else W s, ?_, ?_⟩
  · refine contDiff_glue ?_ hW ?_
    · exact hg.comp_contDiffOn (ContDiffOn.sqrt contDiffOn_id (fun x hx => ne_of_gt hx))
    · intro m
      rw [hWderiv m]
      exact tendsto_iteratedDeriv_comp_sqrt hg he m
  · intro t
    rcases eq_or_ne t 0 with rfl | ht
    · simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), lt_self_iff_false, ↓reduceIte]
      have h0 := hWderiv 0
      simp only [iteratedDeriv_zero, Function.iterate_zero_apply] at h0
      exact h0.symm
    · have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
      change g t = (if 0 < t ^ 2 then g (Real.sqrt (t ^ 2)) else W (t ^ 2))
      rw [if_pos ht2, Real.sqrt_sq_eq_abs]
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, he t]

end Work.RadialSpace
