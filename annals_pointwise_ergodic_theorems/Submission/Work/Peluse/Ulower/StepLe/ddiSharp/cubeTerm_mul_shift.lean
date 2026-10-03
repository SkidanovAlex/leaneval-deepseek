import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.Defs

/-!
# Multiplicativity of the cube term under a pointwise product of shifted functions

The cube term `Work.Peluse.cubeTerm h h' f x = ∏_{ω : Fin σ → Bool} C^{|ω|} f (x + cornerShift h h' ω)`
(`C = star = complex conjugation`, `|ω| = weight ω`) is *multiplicative* in the function argument,
and the iterated conjugation commutes with `star`; together these give the "shifted product" rule

`cubeTerm h h' (fun y => f (y + c) * star (g (y + d))) x
   = cubeTerm h h' f (x + c) * star (cubeTerm h h' g (x + d))`.

This is the standard identity that turns the cube term of a `star`-twisted product into a product of
cube terms, one of which is conjugated — the algebraic core of the dual–difference interchange
(`cubeTerm u v F = star (cubeTerm v u F)` for odd `σ`, see `Submission/Work/Peluse/Ulower/lemma74_denseSet.lean`).

The three ingredients are proved in the `Work.Peluse.Ulower.StepLe.ddiSharp` namespace:
* `star_iterate_mul` : `(star^[n]) (a * b) = (star^[n]) a * (star^[n]) b`;
* `star_star_iterate` : `star ((star^[n]) z) = (star^[n]) (star z)`;
* `cubeTerm_mul`, `cubeTerm_comp_add`, `cubeTerm_star`.
-/

namespace Work.Peluse.Ulower.StepLe.ddiSharp

/-! ## Iterated conjugation -/

/-- Iterated conjugation is multiplicative (it is an iterate of the ring hom `star`). -/
lemma star_iterate_mul (n : ℕ) (a b : ℂ) :
    (star^[n]) (a * b) = (star^[n]) a * (star^[n]) b := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [show star (a * b) = star a * star b by rw [star_mul, mul_comm]]
      exact ih (star a) (star b)

/-- Iterated conjugation commutes with `star` (both are powers of the same involution). -/
lemma star_star_iterate (n : ℕ) (z : ℂ) :
    star ((star^[n]) z) = (star^[n]) (star z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (star z)

/-! ## The cube term -/

/-- The cube term is multiplicative in the function argument. -/
lemma cubeTerm_mul {σ : ℕ} (h h' : Fin σ → ℤ) (f g : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => f y * g y) x =
      Work.Peluse.cubeTerm h h' f x * Work.Peluse.cubeTerm h h' g x := by
  simp only [Work.Peluse.cubeTerm, star_iterate_mul, Finset.prod_mul_distrib]

/-- Shifting the function argument by `c` shifts the point of evaluation of the cube term by `c`. -/
lemma cubeTerm_comp_add {σ : ℕ} (h h' : Fin σ → ℤ) (f : ℤ → ℂ) (c x : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => f (y + c)) x = Work.Peluse.cubeTerm h h' f (x + c) := by
  simp only [Work.Peluse.cubeTerm]
  refine Finset.prod_congr rfl (fun ω _ => ?_)
  congr 2
  ring

/-- Conjugating the cube term conjugates the function argument. -/
lemma cubeTerm_star {σ : ℕ} (h h' : Fin σ → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    star (Work.Peluse.cubeTerm h h' f x) =
      Work.Peluse.cubeTerm h h' (fun y => star (f y)) x := by
  simp only [Work.Peluse.cubeTerm, star_prod, star_star_iterate]

theorem cubeTerm_mul_shift {σ : ℕ} (h h' : Fin σ → ℤ) (f g : ℤ → ℂ) (c d x : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => f (y + c) * star (g (y + d))) x =
      Work.Peluse.cubeTerm h h' f (x + c) * star (Work.Peluse.cubeTerm h h' g (x + d)) := by
  rw [cubeTerm_mul h h' (fun y => f (y + c)) (fun y => star (g (y + d))) x]
  rw [cubeTerm_comp_add h h' f c x]
  rw [← cubeTerm_star h h' (fun y => g (y + d)) x]
  rw [cubeTerm_comp_add h h' g d x]

end Work.Peluse.Ulower.StepLe.ddiSharp
