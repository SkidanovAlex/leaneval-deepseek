import Mathlib
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.heightOneSpectrum_equiv_place
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-! ### Auxiliary lemmas about multiplicities and about the monoid of ideals -/

section CountProd

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [DecidableEq (Associates M)] [∀ p : Associates M, Decidable (Irreducible p)]
  [Nontrivial M] [NoZeroDivisors M]

/-- **The multiplicity of an irreducible element in a finite product.**

For a unique factorization monoid `M`, a finite product of non-zero elements `f i`, and an
irreducible element `p`, the multiplicity of `p` in the factorization of the product is the sum
of its multiplicities in the factors. -/
theorem Associates.count_finset_prod {ι : Type*} (s : Finset ι) (f : ι → M)
    (hf : ∀ i ∈ s, f i ≠ 0) (p : Associates M) (hp : Irreducible p) :
    p.count (Associates.mk (∏ i ∈ s, f i)).factors =
      ∑ i ∈ s, p.count (Associates.mk (f i)).factors := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, Associates.mk_one, Associates.factors_one]
      exact Associates.count_zero hp
  | insert a s ha ih =>
      have hfs : ∏ i ∈ s, f i ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ← Associates.mk_mul_mk,
        Associates.count_mul (Associates.mk_ne_zero.mpr (hf a (Finset.mem_insert_self a s)))
          (Associates.mk_ne_zero.mpr hfs) hp,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

end CountProd

section IdealAssociates

/-- **Associated ideals are equal**: the units of the multiplicative monoid of ideals of a
commutative ring are the unit ideal, so `Associates.mk` is injective on ideals. -/
theorem Associates.mk_eq_mk_iff_eq {R : Type*} [CommSemiring R] {I J : Ideal R} :
    Associates.mk I = Associates.mk J ↔ I = J := by
  rw [Associates.mk_eq_mk_iff_associated]
  constructor
  · rintro ⟨u, hu⟩
    rw [← hu, Ideal.isUnit_iff.mp (Units.isUnit u), Ideal.mul_top]
  · rintro rfl
    exact Associated.refl _

end IdealAssociates

namespace Work.SymQuot.DivOf
open Work.CurveBasics

/-- **The order of vanishing of a product of place ideals: the number of factors equal to the
place.**  For a curve `C` over a field `F`, an affine open `V ⊆ C` with `Γ(C,V)` a Dedekind
domain, places `y m` (`m : Fin n`) and a place `z`, all lying in `V`, the multiplicity of the
maximal ideal of `z` in the factorization of `∏ m, m_{y m}` is the number of indices `m` with
`y m = z`. -/
theorem placeOrder_prod_placeIdeal {F : Type u} [Field F] {C : Curve F} {n : ℕ}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (y : Fin n → C.Place) (hy : ∀ m, (y m).point ∈ V)
    (z : C.Place) (hz : z.point ∈ V) :
    placeOrder C V (∏ m, placeIdeal C V (y m) (hy m)) z hz =
      (Finset.univ.filter (fun m => y m = z)).card := by
  classical
  -- the ideals `placeIdeal` are non-zero, being the height one primes attached to the places
  have hne : ∀ m, placeIdeal C V (y m) (hy m) ≠ ⊥ := by
    intro m
    rw [← heightOneEquiv_apply C V hV ⟨y m, hy m⟩]
    exact (heightOneEquiv C V hV ⟨y m, hy m⟩).ne_bot
  -- and irreducible as elements of the multiplicative monoid of associates
  have hirr : ∀ m, Irreducible (Associates.mk (placeIdeal C V (y m) (hy m))) := by
    intro m
    rw [← heightOneEquiv_apply C V hV ⟨y m, hy m⟩]
    exact (heightOneEquiv C V hV ⟨y m, hy m⟩).associates_irreducible
  have hpirr : Irreducible (Associates.mk (placeIdeal C V z hz)) := by
    rw [← heightOneEquiv_apply C V hV ⟨z, hz⟩]
    exact (heightOneEquiv C V hV ⟨z, hz⟩).associates_irreducible
  -- `placeIdeal` determines the place, hence the associate determines the index
  have hkey : ∀ m : Fin n, Associates.mk (placeIdeal C V (y m) (hy m)) =
      Associates.mk (placeIdeal C V z hz) ↔ y m = z := by
    intro m
    constructor
    · intro hmk
      have hI : placeIdeal C V (y m) (hy m) = placeIdeal C V z hz :=
        (Associates.mk_eq_mk_iff_eq).mp hmk
      exact placeIdeal_injective hV (hy m) hz hI
    · intro h
      rw [Associates.mk_eq_mk_iff_eq]
      subst h
      rfl
  -- the multiplicity of the prime of `z` in the prime of `y m`
  have hterm : ∀ m : Fin n,
      (Associates.mk (placeIdeal C V z hz)).count
          (Associates.mk (placeIdeal C V (y m) (hy m))).factors =
        if y m = z then 1 else 0 := by
    intro m
    by_cases h : y m = z
    · rw [ite_eq_left h, (hkey m).mpr h]
      exact Associates.count_self hpirr
    · rw [ite_eq_right h]
      exact Associates.count_eq_zero_of_ne hpirr (hirr m) fun heq => h ((hkey m).mp heq.symm)
  have hprod := Associates.count_finset_prod (s := (Finset.univ : Finset (Fin n)))
    (f := fun m => placeIdeal C V (y m) (hy m)) (fun m _ => hne m)
    (Associates.mk (placeIdeal C V z hz)) hpirr
  rw [show placeOrder C V (∏ m, placeIdeal C V (y m) (hy m)) z hz =
      (Associates.mk (placeIdeal C V z hz)).count
        (Associates.mk (∏ m, placeIdeal C V (y m) (hy m))).factors from rfl]
  rw [hprod, Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_boole]
  simp

end Work.SymQuot.DivOf

open Work.CurveBasics

/-- The statement as requested at the path of this file: the single-namespace form of
`Work.SymQuot.DivOf.Work.SymQuot.DivOf.placeOrder_prod_placeIdeal` (the declaration above, which
sits in the doubly opened namespace inherited from this file's original skeleton). -/
theorem placeOrder_prod_placeIdeal {F : Type u} [Field F] {C : Curve F} {n : ℕ}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (y : Fin n → C.Place) (hy : ∀ m, (y m).point ∈ V)
    (z : C.Place) (hz : z.point ∈ V) :
    placeOrder C V (∏ m, placeIdeal C V (y m) (hy m)) z hz =
      (Finset.univ.filter (fun m => y m = z)).card :=
  Work.SymQuot.DivOf.Work.SymQuot.DivOf.placeOrder_prod_placeIdeal V hV y hy z hz

end Work.SymQuot.DivOf
