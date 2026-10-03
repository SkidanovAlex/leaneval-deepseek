import Mathlib
import Submission.Work.Peluse.SwapC.concatCore

namespace Work.Peluse.SwapC

open Work.Peluse

/-- `star` commutes with the iterates of `star` on `ℂ`: conjugating an iterated conjugate is the
iterated conjugate of the conjugate. -/
lemma star_iterate_star (n : ℕ) : ∀ z : ℂ, star ((star^[n]) z) = (star^[n]) (star z) := by
  induction n with
  | zero => intro z; simp
  | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [star_star, ih (star z), star_star]

/-- The `star` of `Rest` is `Rest` of the conjugated function. -/
theorem starRestEq {d : ℕ} (v : Fin d → ℤ) (f : ℤ → ℂ) (y : ℤ) :
    star (Rest v f y) = Rest v (fun x => star (f x)) y := by
  simp only [Rest]
  rw [star_prod]
  refine Finset.prod_congr rfl (fun ω _ => ?_)
  exact star_iterate_star (weight ω) (f (y + cornerShift v (fun _ => 0) ω))

end Work.Peluse.SwapC
