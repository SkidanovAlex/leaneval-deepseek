import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

/-! ### Auxiliary lemmas about ideals of a domain

`idealOfDiv` is a product of powers of the maximal ideals `placeIdeal C V z` of the places in the
support of `D`.  Each factor is nonzero: `placeIdeal` is the maximal ideal of a *height one*
prime of the Dedekind domain `Γ(C,V)` (`placeIdeal_eq_primeIdealOf`), and a product of nonzero
ideals of a domain is nonzero.  These two general facts are proved here. -/

/-- **In a domain the product of two nonzero ideals is nonzero.** -/
theorem mul_ne_bot_of_ne_bot {R : Type*} [CommRing R] [NoZeroDivisors R]
    {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I * J ≠ ⊥ := by
  intro h
  rcases (Ideal.mul_eq_bot).mp h with h' | h'
  · exact hI h'
  · exact hJ h'

/-- **In a nontrivial domain the power of a nonzero ideal is nonzero.** -/
theorem pow_ne_bot_of_ne_bot {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    {I : Ideal R} (hI : I ≠ ⊥) (n : ℕ) : I ^ n ≠ ⊥ := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact top_ne_bot
  | succ n ih => rw [pow_succ]; exact mul_ne_bot_of_ne_bot ih hI

/-- **In a nontrivial domain a finite product of nonzero ideals is nonzero.** -/
theorem finset_prod_ne_bot {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    {ι : Type*} (s : Finset ι) (f : ι → Ideal R) (h : ∀ i ∈ s, f i ≠ ⊥) :
    ∏ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top]; exact top_ne_bot
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mul_ne_bot_of_ne_bot (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### The ideal of a place in an affine open is nonzero -/

/-- **The maximal ideal `m_z` of a place `z` lying in an affine open `V` is nonzero**: it is the
prime ideal of a height one prime of the Dedekind domain `Γ(C,V)`, and hence is not the zero
ideal. -/
theorem placeIdeal_ne_bot {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (z : C.Place) (hz : z.point ∈ V) :
    Work.SymQuot.DivOf.placeIdeal C V z hz ≠ ⊥ := by
  rw [Work.SymQuot.DivOf.placeIdeal_eq_primeIdealOf hV z hz]
  exact Work.SymQuot.DivOf.heightOne_primeIdealOf_asIdeal_ne_bot_of_place hV z hz

/-! ### The target -/

open CategoryTheory Limits AlgebraicGeometry in
theorem idealOfDiv_ne_bot {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (D : C.Div) (hs : ∀ z ∈ D.support, z.point ∈ V) :
    idealOfDiv C V hV D hs ≠ ⊥ := by
  rw [idealOfDiv]
  refine finset_prod_ne_bot _ (fun z : {z // z ∈ D.support} =>
    Work.SymQuot.DivOf.placeIdeal C V ↑z (hs ↑z z.2) ^ (D ↑z).toNat) (fun z _ => ?_)
  exact pow_ne_bot_of_ne_bot (placeIdeal_ne_bot hV ↑z (hs ↑z z.2)) _

end Work.SymQuot.DivOf.Complete
