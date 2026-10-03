import Mathlib
import Submission.Work.Peluse.Ulower.iterDefs

/-!
# Peeling the outermost shift of the iterated `Δ'`-difference

`iterDelta' (t+1) sh f` is built by taking the `Δ'`-step with shift pair `sh 0` *outside* the
`t`-fold iterated difference over the remaining shifts `sh 1, …, sh t`.  The lemma
`iterDelta_peel` says that the same function is obtained by first taking the `Δ'`-step with
`sh 0` on `f` and then iterating the remaining shifts on the result:

`iterDelta' (t+1) sh f = iterDelta' t sh.tail (Δ'_{sh 0} f)`.

In other words the order in which the shifts are peeled off is irrelevant: `iterDelta'` is
symmetric in the shifts.  The proof is the elementary commutation of a single `Δ'`-step with an
iterated difference, which in turn is the commutation of two single `Δ'`-steps
(`peelStep_comm`), a computation in `ℤ`-translations and complex conjugation.
-/

namespace Work.Peluse.Ulower

noncomputable section

/-- One `Δ'`-step in the convention of `iterDelta'` (the `star` sits on the `(sh 0).1` factor):
`peelStep (a₁,a₂) F = fun x => star (F (x + a₁)) * F (x + a₂)`.  This is
`iterDelta' 1 (fun _ => a) F`. -/
def peelStep (a : ℤ × ℤ) (F : ℤ → ℂ) : ℤ → ℂ := fun x => star (F (x + a.1)) * F (x + a.2)

/-- The recursion of `iterDelta'`, read as a peel of the outermost shift pair. -/
lemma iterDelta'_succ (t : ℕ) (sh : Fin (t+1) → ℤ × ℤ) (F : ℤ → ℂ) :
    iterDelta' (t+1) sh F = peelStep (sh 0) (iterDelta' t (fun i => sh i.succ) F) := rfl

/-- Two single `Δ'`-steps commute (their order does not matter, because the corresponding
Boolean-cube product is commutative and the translations of `ℤ` commute). -/
lemma peelStep_comm (a b : ℤ × ℤ) (F : ℤ → ℂ) :
    peelStep b (peelStep a F) = peelStep a (peelStep b F) := by
  funext x
  simp only [peelStep]
  ring_nf
  simp only [star_mul, star_star]
  ring_nf

/-- A single `Δ'`-step commutes with an iterated `Δ'`-difference: the outermost shift pair of
`iterDelta'` may be moved to the innermost position. -/
lemma iterDelta'_peelStep_comm (t : ℕ) (sh : Fin t → ℤ × ℤ) (a : ℤ × ℤ) (F : ℤ → ℂ) :
    iterDelta' t sh (peelStep a F) = peelStep a (iterDelta' t sh F) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [iterDelta'_succ, iterDelta'_succ, ih (fun i => sh i.succ), peelStep_comm]

theorem iterDelta_peel (t : ℕ) (sh : Fin (t+1) → ℤ × ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.Ulower.iterDelta' (t+1) sh f x
      = Work.Peluse.Ulower.iterDelta' t (fun i => sh i.succ)
          (fun w : ℤ => star (f (w + (sh 0).1)) * f (w + (sh 0).2)) x := by
  rw [iterDelta'_succ, ← iterDelta'_peelStep_comm]
  rfl

end

end Work.Peluse.Ulower
