/-
# The cube term peels at the first coordinate: the *column* form

`Work.Peluse.cubeTerm h h' f x = ∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`
is the `2^t`-vertex cube term of Peluse's box norm.  Peluse's recursion `t → t + 1` has two
equivalent readings:

* the **row** form (`Work.Peluse.Ulower.StepLe.cubeTerm_cons_pair`, and
  `Work.Peluse.Ulower.cubeTerm_tail`): the `(σ+1)`-fold cube term is the `σ`-fold cube term of the
  *pairing* `y ↦ f (y + b) * conj (f (y + a))`, where `a, b` are the two values at the peeled
  coordinate;
* the **column** form (this file, `cubeTerm_cons_one`): the `(σ+1)`-fold cube term is the
  *one*-fold cube term of the `σ`-fold cube term, i.e. the cube term is `(Δ')^{σ+1} f` and one may
  read the last difference first.

The two readings agree because the cube term is *multiplicative* in `f` and commutes with
translations and conjugation (each vertex contributes the corresponding operation):

  `cubeTerm h h' (y ↦ f (y+b) * conj (f (y+a))) x = cubeTerm h h' f (x+b) * conj (cubeTerm h h' f (x+a))`.

That identity, together with the `σ = 0` degeneration (`cubeTerm` over `Fin 0` is the identity
map), is what the proof below reduces to; both are proved from the definition.  The statement is
used in `Submission/Work/Peluse/Ulower/StepLe/dualDiffStep.lean`, where the *column* form is what
lets the one-dimensional base case of the dual--difference interchange be applied to the family
`z ↦ cubeTerm k̄.2.1 k̄.2.2 (G z)`.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.Defs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe.ddiSharp

/-- `star^[n]` is multiplicative (it is an iterate of the star ring anti-automorphism). -/
private lemma starIterate_mul {n : ℕ} (A B : ℂ) :
    (star^[n]) (A * B) = (star^[n]) A * (star^[n]) B := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
        Function.iterate_succ_apply', star_mul]
      ring

/-- `star^[n]` commutes with `star`. -/
private lemma starIterate_star : ∀ (n : ℕ) (z : ℂ), (star^[n]) (star z) = star ((star^[n]) z) := by
  intro n
  induction n with
  | zero => intro z; simp
  | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply, ih (star z)]
      rw [Function.iterate_succ_apply, ih z]

/-- The cube term commutes with translations of the argument. -/
private lemma cubeTerm_shift {t : ℕ} (h h' : Fin t → ℤ) (f : ℤ → ℂ) (x c : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => f (y + c)) x =
      Work.Peluse.cubeTerm h h' f (x + c) := by
  rw [Work.Peluse.cubeTerm, Work.Peluse.cubeTerm]
  refine Finset.prod_congr rfl fun ω _ => ?_
  ring_nf

/-- The cube term commutes with conjugation: `cubeTerm (conj ∘ f) = conj (cubeTerm f)`. -/
private lemma cubeTerm_star {t : ℕ} (h h' : Fin t → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => star (f y)) x = star (Work.Peluse.cubeTerm h h' f x) := by
  rw [Work.Peluse.cubeTerm, Work.Peluse.cubeTerm, star_prod]
  refine Finset.prod_congr rfl fun ω _ => ?_
  rw [starIterate_star]

/-- The cube term is multiplicative in the function: `Δ'(f·g) = Δ'f · Δ'g`. -/
private lemma cubeTerm_mul {t : ℕ} (h h' : Fin t → ℤ) (A B : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => A y * B y) x
      = Work.Peluse.cubeTerm h h' A x * Work.Peluse.cubeTerm h h' B x := by
  rw [Work.Peluse.cubeTerm, Work.Peluse.cubeTerm, Work.Peluse.cubeTerm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ω _ => ?_
  rw [starIterate_mul]

/-- The `0`-fold cube term is the function itself (the product over the single vertex
`Fin 0 → Bool`). -/
private lemma cubeTerm_fin_zero (u v : Fin 0 → ℤ) (g : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm u v g x = g x := by
  rw [Work.Peluse.cubeTerm, Fintype.prod_unique]
  simp [Work.Peluse.weight, Work.Peluse.cornerShift]

/-- **Peeling the first coordinate of the cube term, in the pairing form.**  The cube term of the
pairing `y ↦ f (y + b) * conj (f (y + a))` is the product of the two translated cube terms of `f`
(the second one conjugated).  This is the algebraic content of Peluse's recursion `t → t + 1`. -/
private lemma cubeTerm_pair_shift {t : ℕ} (a b : ℤ) (h h' : Fin t → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => f (y + b) * star (f (y + a))) x
      = Work.Peluse.cubeTerm h h' f (x + b) * star (Work.Peluse.cubeTerm h h' f (x + a)) := by
  rw [cubeTerm_mul, cubeTerm_shift]
  rw [cubeTerm_star, cubeTerm_shift]

/-- **The column form of the peel of the first coordinate.**  The `(σ+1)`-fold cube term equals
the one-fold cube term applied to the `σ`-fold cube term:

`Δ'_{(a::h, b::h')} f = Δ'_{(a,b)} (Δ'_{(h,h')} f)`.

Indeed both sides compute to `Δ'_{(h,h')} f (x + b) · conj (Δ'_{(h,h')} f (x + a))`: the left by
the peel (`Work.Peluse.Ulower.cubeTerm_tail`) preceded by `cubeTerm_pair_shift`, the right by the
peel at level `1` (whose tails are indexed by `Fin 0`, where the cube term is the identity). -/
theorem cubeTerm_cons_one {σ : ℕ} (a b : ℤ) (h h' : Fin σ → ℤ)
    (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm (Fin.cons a h) (Fin.cons b h') f x =
      Work.Peluse.cubeTerm (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
        (Work.Peluse.cubeTerm h h' f) x := by
  -- Peel the first coordinate of the `(σ+1)`-fold cube term.
  have hL := Work.Peluse.Ulower.cubeTerm_tail (h := Fin.cons a h) (h' := Fin.cons b h')
      (f := f) (x := x)
  rw [Fin.tail_cons, Fin.tail_cons, Fin.cons_zero, Fin.cons_zero] at hL
  rw [hL, cubeTerm_pair_shift]
  -- The one-fold cube term of the `σ`-fold cube term is the same product.
  have hR := Work.Peluse.Ulower.cubeTerm_tail (h := fun _ : Fin 1 => a)
      (h' := fun _ : Fin 1 => b) (f := Work.Peluse.cubeTerm h h' f) (x := x)
  rw [hR]
  rw [cubeTerm_fin_zero]

end Work.Peluse.Ulower.StepLe.ddiSharp
