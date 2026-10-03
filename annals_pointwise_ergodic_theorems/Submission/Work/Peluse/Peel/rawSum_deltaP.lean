import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow
import Submission.Work.Peluse.BoxNorm.WinDefs

/-!
# The raw box sum of a `Δ'`-difference

For a function `h : ℤ → ℂ` the raw box sum `rawSum t Q h` of `Work.Peluse.BoxNorm` is the
unnormalised cube average

`∑_{u, u' ∈ ∏ Q_i} ∑_x ∏_{ω : Fin t → Bool} C^{|ω|} h (x + ω·u + (1-ω)·u')`.

This file evaluates it on the `Δ'`-difference `h u = f (u + a) · conj (f (u + b))`, the object
that appears when Peluse's box norm is applied to the bilinear average of §2.  Because `C^{|ω|}`
is a ring homomorphism and commutes with conjugation, the cube term factorises as

`∏_ω C^{|ω|} (f (· + a) · conj (f (· + b)))
   = (∏_ω C^{|ω|} f (· + a)) · conj (∏_ω C^{|ω|} f (· + b))`,

which is exactly the statement below: the summand is the product of the cube terms of `f` shifted
by `a` and `b`, the second one conjugated.

## Main result

* `Work.Peluse.Peel.rawSum_deltaP`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Peel

/-- Decomposing `C^{|ω|}(A · conj B)`: iterated conjugation is multiplicative and commutes with
conjugation, so the product over `ω` splits into a product of `C^{|ω|} A` times the conjugate of the
product of `C^{|ω|} B`. -/
lemma prod_starIterate_mul_star {ι : Type*} [Fintype ι] (w : ι → ℕ) (A B : ι → ℂ) :
    (∏ i, (star^[w i]) (A i * star (B i)))
      = (∏ i, (star^[w i]) (A i)) * star (∏ i, (star^[w i]) (B i)) := by
  have h : ∀ i, (star^[w i]) (A i * star (B i))
      = (star^[w i]) (A i) * star ((star^[w i]) (B i)) :=
    fun i => by rw [Work.Peluse.BoxNorm.star_iterate_mul, Work.Peluse.BoxNorm.star_iterate_conj]
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_mul_distrib, star_prod]

theorem rawSum_deltaP (t : ℕ) (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) (a b : ℤ) :
    Work.Peluse.BoxNorm.rawSum t Q (fun u : ℤ => f (u + a) * star (f (u + b)))
      = ∑ hs : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑ hs' : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑' x : ℤ,
            (∏ τ : Fin t → Bool, (star^[Work.Peluse.weight τ])
              (f ((x + a) + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ)))
            * star (∏ τ : Fin t → Bool, (star^[Work.Peluse.weight τ])
              (f ((x + b) + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ))) := by
  simp only [Work.Peluse.BoxNorm.rawSum]
  refine Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ => ?_))
  refine tsum_congr (fun x => ?_)
  have key : ∀ ω : Fin t → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω + a)
          * star (f (x + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω + b)))
      = (star^[Work.Peluse.weight ω])
        (f ((x + a) + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω)
          * star (f ((x + b) + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω))) := by
    intro ω
    have e1 : x + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω + a
        = (x + a) + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω := by ring
    have e2 : x + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω + b
        = (x + b) + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω := by ring
    rw [e1, e2]
  rw [Finset.prod_congr rfl (fun ω _ => key ω)]
  exact prod_starIterate_mul_star (fun ω : Fin t → Bool => Work.Peluse.weight ω)
    (fun ω => f ((x + a) + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω))
    (fun ω => f ((x + b) + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) ω))

end Work.Peluse.Peel
