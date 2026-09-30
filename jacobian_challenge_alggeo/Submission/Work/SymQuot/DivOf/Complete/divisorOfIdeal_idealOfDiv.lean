import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_placeIdeal
import Submission.Work.SymQuot.DivOf.placeOrder_prod_placeIdeal
import Submission.Work.SymQuot.DivOf.placeOrder_mono
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_mul
import Submission.Work.SymQuot.DivOf.placeIdeal_injective

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
open Work.CurveBasics

universe u

/-- **The order of vanishing of a product of powers of place ideals**: for places `y` ranging
over a finite set `s ⊆ V` with multiplicities `e`, the multiplicity of the maximal ideal `m_z` of
a place `z ∈ V` in the factorization of `∏_y m_y ^ (e y)` is `e z` if `z ∈ s` and `0`
otherwise. -/
theorem placeOrder_prod_placeIdeal_pow {F : Type u} [Field F] {C : Curve F}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (s : Finset C.Place) (e : C.Place → ℕ) (hs : ∀ y ∈ s, y.point ∈ V)
    (z : C.Place) (hz : z.point ∈ V) :
    placeOrder C V (∏ y ∈ s.attach, placeIdeal C V y.1 (hs y.1 y.2) ^ e y.1) z hz =
      if z ∈ s then e z else 0 := by
  classical
  -- the place ideals are non-zero, being the height one primes attached to the places
  have hne : ∀ y : {y // y ∈ s}, placeIdeal C V y.1 (hs y.1 y.2) ≠ ⊥ := by
    intro y
    rw [← heightOneEquiv_apply C V hV ⟨y.1, hs y.1 y.2⟩]
    exact (heightOneEquiv C V hV ⟨y.1, hs y.1 y.2⟩).ne_bot
  -- and irreducible as elements of the multiplicative monoid of associates
  have hirr : ∀ y : {y // y ∈ s},
      Irreducible (Associates.mk (placeIdeal C V y.1 (hs y.1 y.2))) := by
    intro y
    rw [← heightOneEquiv_apply C V hV ⟨y.1, hs y.1 y.2⟩]
    exact (heightOneEquiv C V hV ⟨y.1, hs y.1 y.2⟩).associates_irreducible
  have hpirr : Irreducible (Associates.mk (placeIdeal C V z hz)) := by
    rw [← heightOneEquiv_apply C V hV ⟨z, hz⟩]
    exact (heightOneEquiv C V hV ⟨z, hz⟩).associates_irreducible
  -- `placeIdeal` determines the place, hence the associate determines the index
  have hkey : ∀ y : {y // y ∈ s},
      Associates.mk (placeIdeal C V y.1 (hs y.1 y.2)) = Associates.mk (placeIdeal C V z hz) ↔
        y.1 = z := by
    intro y
    constructor
    · intro hmk
      have hI : placeIdeal C V y.1 (hs y.1 y.2) = placeIdeal C V z hz :=
        (Associates.mk_eq_mk_iff_eq).mp hmk
      exact placeIdeal_injective hV (hs y.1 y.2) hz hI
    · intro h
      rw [Associates.mk_eq_mk_iff_eq]
      subst h
      rfl
  -- the multiplicity of the prime of `z` in the power of the prime of `y`
  have hterm : ∀ y ∈ s.attach,
      (Associates.mk (placeIdeal C V z hz)).count
          (Associates.mk (placeIdeal C V y.1 (hs y.1 y.2) ^ e y.1)).factors =
        if y.1 = z then e y.1 else 0 := by
    intro y _
    rw [Associates.mk_pow,
      Associates.count_pow (Associates.mk_ne_zero.mpr (hne y)) hpirr (e y.1)]
    by_cases hyz : y.1 = z
    · rw [if_pos hyz, (hkey y).mpr hyz, Associates.count_self hpirr, mul_one]
    · rw [if_neg hyz,
        Associates.count_eq_zero_of_ne hpirr (hirr y) fun heq => hyz ((hkey y).mp heq.symm),
        mul_zero]
  -- the multiplicity of the prime of `z` in the whole product is the sum of the multiplicities
  have hprod := Work.SymQuot.DivOf.Associates.count_finset_prod (s := s.attach)
    (f := fun y => placeIdeal C V y.1 (hs y.1 y.2) ^ e y.1)
    (fun y _ => pow_ne_zero _ (hne y)) (Associates.mk (placeIdeal C V z hz)) hpirr
  rw [show placeOrder C V (∏ y ∈ s.attach, placeIdeal C V y.1 (hs y.1 y.2) ^ e y.1) z hz =
      (Associates.mk (placeIdeal C V z hz)).count
        (Associates.mk (∏ y ∈ s.attach,
          placeIdeal C V y.1 (hs y.1 y.2) ^ e y.1)).factors from rfl]
  rw [hprod, Finset.sum_congr rfl hterm,
    Finset.sum_attach (s := s) (f := fun y => if y = z then e y else 0),
    Finset.sum_ite_eq' s z e]

/-- **The order of vanishing of the ideal of definition of an effective divisor**: the
multiplicity of the maximal ideal of a place `z ∈ V` in the ideal `idealOfDiv C V hV D hs` of
definition of `D` is the coefficient of `D` at `z`. -/
theorem placeOrder_idealOfDiv {F : Type u} [Field F] {C : Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (D : C.Div) (hs : ∀ z ∈ D.support, z.point ∈ V) (z : C.Place) (hz : z.point ∈ V) :
    placeOrder C V (idealOfDiv C V hV D hs) z hz = (D z).toNat := by
  have hEq : idealOfDiv C V hV D hs =
      ∏ y ∈ D.support.attach, placeIdeal C V y.1 (hs y.1 y.2) ^ (D y.1).toNat := rfl
  rw [hEq,
    placeOrder_prod_placeIdeal_pow V hV D.support (fun y => (D y).toNat) hs z hz]
  by_cases hzS : z ∈ D.support
  · rw [if_pos hzS]
  · rw [if_neg hzS,
      show D z = 0 from by
        by_contra h
        exact hzS (Finsupp.mem_support_iff.mpr h),
      Int.toNat_zero]

open CategoryTheory Limits AlgebraicGeometry in
theorem divisorOfIdeal_idealOfDiv {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    {D : C.Div} (hD : D.IsEffective) (hs : ∀ z ∈ D.support, z.point ∈ V) :
    divisorOfIdeal C V hV (idealOfDiv C V hV D hs) = D := by
  ext w
  rw [divisorOfIdeal_apply]
  by_cases hw : w.point ∈ V
  · rw [dif_pos hw, placeOrder_idealOfDiv hV D hs w hw, Int.toNat_of_nonneg (hD w)]
  · rw [dif_neg hw]
    symm
    exact show D w = 0 from by
      by_contra h
      exact hw (hs w (Finsupp.mem_support_iff.mpr h))

end Work.SymQuot.DivOf.Complete
