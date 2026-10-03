import Mathlib
import Submission.Work.Peluse.Ulower.iterDefs
import Submission.Work.Peluse.BoxNorm.cubeTerm_cons

namespace Work.Peluse.Ulower

open scoped BigOperators

/-!
# `iterDelta'` is the cube term of the shift pairs

`Work.Peluse.cubeTerm h h' f x` is the paper's cube term
`∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`, and `Work.Peluse.Ulower.iterDelta' t sh f`
is the `t`-fold iterated difference `Δ'_{(sh 0)} ⋯ Δ'_{(sh t-1)} f`.  The two agree when
`h = fun i => (sh i).1` and `h' = fun i => (sh i).2`:

`iterDelta' t sh f x = cubeTerm (fun i => (sh i).1) (fun i => (sh i).2) f x`.

This is the bridge between the `Δ'`-notation of the degree-lowering chapter (`Ulower/`) and the
cube-term notation of the box-norm chapter (`BoxNorm/`); it is the identity that lets the cube
average of `iterDelta'` be read as the box-norm power.

The proof is an induction on `t`.  The base case `t = 0` is the (unique) product over
`Fin 0 → Bool`; the step is exactly the first-coordinate splitting of the cube term,
`Work.Peluse.BoxNorm.cubeTerm_cons`, combined with the definition of `iterDelta'` at `t + 1`.
-/

/-- The cube term of order `0` is the function itself.  (`Fin 0 → Bool` is a singleton, its
element has weight `0` and corner shift `0`.) -/
private lemma cubeTerm_zero (h h' : Fin 0 → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm h h' f x = f x := by
  rw [Work.Peluse.cubeTerm]
  have hw : ∀ ω : Fin 0 → Bool, Work.Peluse.weight ω = 0 := by
    intro ω
    rw [Work.Peluse.weight, Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    intro i _
    exact Fin.elim0 i
  have hc : ∀ ω : Fin 0 → Bool, Work.Peluse.cornerShift h h' ω = 0 := by
    intro ω
    rw [Work.Peluse.cornerShift]
    simp
  calc ∏ ω : Fin 0 → Bool, (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift h h' ω))
      = ∏ _ω : Fin 0 → Bool, f x := by
        refine Finset.prod_congr rfl (fun ω _ => ?_)
        rw [hw ω, hc ω]
        simp
    _ = (f x) ^ (Finset.univ : Finset (Fin 0 → Bool)).card := Finset.prod_const (f x)
    _ = f x := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, pow_zero,
          pow_one]

/-- Splitting the cube term at the first coordinate, in the form of `Work.Peluse.cubeTerm`:
the cube term of the shift tuples `Fin.cons a h`, `Fin.cons b h'` is the cube term of the tails
evaluated at `x + b`, times the conjugate of the same at `x + a`. -/
private lemma cubeTerm_cons' {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm (Fin.cons a h) (Fin.cons b h') f x
      = Work.Peluse.cubeTerm h h' f (x + b) * star (Work.Peluse.cubeTerm h h' f (x + a)) := by
  simpa only [Work.Peluse.cubeTerm] using Work.Peluse.BoxNorm.cubeTerm_cons a b h h' f x

/-- The main identity, in the form of a universally quantified statement so that the induction
hypothesis stays general in the shift tuples. -/
private lemma iterDelta'_eq_cubeTerm : ∀ (t : ℕ) (sh : Fin t → ℤ × ℤ) (f : ℤ → ℂ) (x : ℤ),
    Work.Peluse.Ulower.iterDelta' t sh f x
      = Work.Peluse.cubeTerm (fun i => (sh i).1) (fun i => (sh i).2) f x := by
  intro t
  induction t with
  | zero =>
      intro sh f x
      exact (cubeTerm_zero (fun i : Fin 0 => (sh i).1) (fun i => (sh i).2) f x).symm
  | succ t ih =>
      intro sh f x
      rw [show Work.Peluse.Ulower.iterDelta' (t+1) sh f x
            = star (Work.Peluse.Ulower.iterDelta' t (fun i => sh i.succ) f (x + (sh 0).1))
              * Work.Peluse.Ulower.iterDelta' t (fun i => sh i.succ) f (x + (sh 0).2) from rfl]
      rw [ih (fun i => sh i.succ) f (x + (sh 0).1), ih (fun i => sh i.succ) f (x + (sh 0).2)]
      -- write the two `(t+1)`-tuples of first (resp. second) coordinates as a head and a tail
      have hq : (fun i : Fin (t+1) => (sh i).1)
          = Fin.cons (sh 0).1 (fun i : Fin t => (sh i.succ).1) := by
        funext i
        cases i using Fin.cases <;> simp
      have hq' : (fun i : Fin (t+1) => (sh i).2)
          = Fin.cons (sh 0).2 (fun i : Fin t => (sh i.succ).2) := by
        funext i
        cases i using Fin.cases <;> simp
      conv_rhs => rw [hq, hq']
      rw [cubeTerm_cons']
      ring

theorem lemma74_cubeTerm_iterDelta {t : ℕ} (sh : Fin t → ℤ × ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.Ulower.iterDelta' t sh f x
      = Work.Peluse.cubeTerm (fun i => (sh i).1) (fun i => (sh i).2) f x :=
  iterDelta'_eq_cubeTerm t sh f x

end Work.Peluse.Ulower
