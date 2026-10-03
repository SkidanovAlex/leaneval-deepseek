import Mathlib
import Submission.Work.Peluse.Ulower.iterDefs

/-!
# Peeling the first coordinate of the cube term

`Work.Peluse.Ulower.cubeTerm_tail`: the level-`(t+1)` cube term at a shift pair is the level-`t`
cube term of the tails applied to the *pairing* of the two first coordinates.  This is the
recursion used by the induction on `σ` in the dual--difference interchange
(Peluse--Prendiville Lemma 6.3 / Peluse Lemma 7.4).
-/

namespace Work.Peluse.Ulower

section Helpers

open scoped BigOperators

private lemma starIterate_mul' (n : ℕ) (a b : ℂ) :
    (star^[n]) (a * b) = (star^[n]) a * (star^[n]) b := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
        Function.iterate_succ_apply', star_mul]
      ring

private lemma starIterate_star' : ∀ (n : ℕ) (z : ℂ), (star^[n]) (star z) = star ((star^[n]) z) := by
  intro n
  induction n with
  | zero => intro z; simp
  | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply, ih (star z)]
      rw [Function.iterate_succ_apply, ih z]

private lemma starIterate_succ' (n : ℕ) (z : ℂ) : (star^[n+1]) z = (star^[n]) (star z) :=
  Function.iterate_succ_apply star n z

/-- `cornerShift` splits off the first coordinate. -/
private lemma cornerShift_cons_first {t : ℕ} (h h' : Fin (t+1) → ℤ) (b : Bool)
    (ω : Fin t → Bool) :
    Work.Peluse.cornerShift h h' (Fin.cons b ω) =
      (if b then h 0 else h' 0) + Work.Peluse.cornerShift (Fin.tail h) (Fin.tail h') ω := by
  rw [Work.Peluse.cornerShift, Work.Peluse.cornerShift, Fin.sum_univ_succ, Fin.cons_zero]
  congr 1

/-- `weight` splits off the first coordinate. -/
private lemma weight_cons_first {t : ℕ} (b : Bool) (ω : Fin t → Bool) :
    Work.Peluse.weight (Fin.cons b ω) = Work.Peluse.weight ω + (if b then 1 else 0) := by
  have e : ∀ {n : ℕ} (ω : Fin n → Bool),
      Work.Peluse.weight ω = ∑ i, (if ω i = true then 1 else 0) := by
    intro n ω
    rw [Work.Peluse.weight, Finset.card_filter]
  rw [e (Fin.cons b ω), e ω, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, add_comm]

/-- **Peeling the first coordinate of the cube term.**  The cube term at a shift pair whose first
coordinates are `h 0`, `h' 0` and whose tails are `Fin.tail h`, `Fin.tail h'` equals the cube term
of the tails applied to the *pairing* `y ↦ f (y + h' 0) * conj (f (y + h 0))`.

This is the recursion `Δ'_{(c,t),(d,t')}(f) = Δ'_{(t,t')}(f(·+d)·conj(f(·+c)))` used by the
induction on `σ` in the dual--difference interchange. -/
theorem cubeTerm_tail {t : ℕ} (h h' : Fin (t+1) → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm h h' f x =
      Work.Peluse.cubeTerm (Fin.tail h) (Fin.tail h')
        (fun y => f (y + h' 0) * star (f (y + h 0))) x := by
  rw [Work.Peluse.cubeTerm, Work.Peluse.cubeTerm]
  rw [← Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (t+1) => Bool))
        (fun p : Bool × (Fin t → Bool) =>
          (star^[Work.Peluse.weight (Fin.cons p.1 p.2)])
            (f (x + Work.Peluse.cornerShift h h' (Fin.cons p.1 p.2))))
        (fun ω : Fin (t+1) → Bool => (star^[Work.Peluse.weight ω])
            (f (x + Work.Peluse.cornerShift h h' ω)))
        (by
          intro p
          rw [show (Fin.consEquiv (fun _ : Fin (t+1) => Bool)) p = Fin.cons p.1 p.2 from
            funext (fun i => by rw [Fin.consEquiv_apply])])]
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [cornerShift_cons_first, weight_cons_first, Bool.false_eq_true, if_true, if_false,
    add_zero]
  rw [show (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        ((fun y => f (y + h' 0) * star (f (y + h 0)))
          (x + Work.Peluse.cornerShift (Fin.tail h) (Fin.tail h') ω)))
      = (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (f (x + h' 0 + Work.Peluse.cornerShift (Fin.tail h) (Fin.tail h') ω)))
        * (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω + 1])
            (f (x + h 0 + Work.Peluse.cornerShift (Fin.tail h) (Fin.tail h') ω))) from by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ω _ => ?_
    rw [starIterate_mul', (starIterate_succ' (Work.Peluse.weight ω) _).symm]
    simp only [add_assoc, add_comm, add_left_comm]]
  simp only [add_assoc, add_comm, add_left_comm, Nat.add_comm]
  ring


end Helpers

end Work.Peluse.Ulower
