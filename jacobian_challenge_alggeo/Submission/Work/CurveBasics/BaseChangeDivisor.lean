import Submission.Work.CurveBasics.BaseChangeFunctionField
import Submission.Work.CurveBasics.Place.ord_uniformizer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics
namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The place of `C` below a place of `C_F`, when it is again a place. -/
def under (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (Q' : (C.baseChange F).Place) (h : IsClosed ({(baseChangeFst C F) Q'.point} : Set C.left)) :
    C.Place := ⟨(baseChangeFst C F) Q'.point, h⟩

/-- The ramification index of a place of `C_F` over its image in `C`; `0` if the image is
the generic point. -/
noncomputable def ramIdx (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (Q' : (C.baseChange F).Place) : ℤ :=
  if h : IsClosed ({(baseChangeFst C F) Q'.point} : Set C.left) then
    (C.baseChange F).ordAt ((C.functionFieldMap F).hom (C.under F Q' h).uniformizer) Q'
  else 0

/-- The coefficient at a place of `C_F` of the base change of a divisor. -/
noncomputable def divMapCoeff (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (D : C.Div) (Q' : (C.baseChange F).Place) : ℤ :=
  if h : IsClosed ({(baseChangeFst C F) Q'.point} : Set C.left) then
    D (C.under F Q' h) * C.ramIdx F Q'
  else 0

/-- The support of `divMapCoeff` is finite: it is contained in the union, over the support of
`D`, of the supports of the principal divisors of the images of the uniformizers. -/
theorem finite_support_divMapCoeff (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (D : C.Div) : (Function.support (C.divMapCoeff F D)).Finite := by
  classical
  refine Set.Finite.subset (s := ⋃ Q ∈ D.support, {Q' : (C.baseChange F).Place |
      (C.baseChange F).ordAt ((C.functionFieldMap F).hom Q.uniformizer) Q' ≠ 0}) ?_
    (fun Q' hQ' => ?_)
  · refine Set.Finite.biUnion D.support.finite_toSet (fun Q _ => ?_)
    exact (C.baseChange F).finite_support_ordAt ((C.functionFieldMap F).hom Q.uniformizer)
  · simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe]
    by_cases h : IsClosed ({(baseChangeFst C F) Q'.point} : Set C.left)
    · have h1 : D (C.under F Q' h) * C.ramIdx F Q' ≠ 0 := by
        simpa only [Set.mem_setOf_eq, Function.mem_support, divMapCoeff, dif_pos h] using hQ'
      have h2 : D (C.under F Q' h) ≠ 0 := fun h0 => h1 (by rw [h0, zero_mul])
      refine ⟨C.under F Q' h, ?_, ?_⟩
      · simpa only [Finsupp.mem_support_iff] using h2
      · have h3 : C.ramIdx F Q' ≠ 0 := fun h0 => h1 (by rw [h0, mul_zero])
        have h4 : C.ramIdx F Q' = (C.baseChange F).ordAt
            ((C.functionFieldMap F).hom (C.under F Q' h).uniformizer) Q' := by
          simp only [ramIdx, dif_pos h]
        rw [← h4]
        simpa only [Function.mem_support] using h3
    · exact absurd (by rw [divMapCoeff, dite_eq_right h]) hQ'

/-- **Base change of divisors.**  The pullback of a divisor along `C_F ⟶ C`, with the
ramification weights: the coefficient of `[Q']` is `e(Q'/Q) · D(Q)`. -/
noncomputable def divMap (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    C.Div →+ (C.baseChange F).Div where
  toFun D := Finsupp.ofSupportFinite (C.divMapCoeff F D) (C.finite_support_divMapCoeff F D)
  map_zero' := by
    ext Q'
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.zero_apply, divMapCoeff]
    split <;> simp
  map_add' D E := by
    ext Q'
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.add_apply, divMapCoeff]
    split
    · ring
    · simp

@[simp]
theorem divMap_apply (C : Curve k) (F : Type u) [Field F] [Algebra k F] (D : C.Div)
    (Q' : (C.baseChange F).Place) :
    C.divMap F D Q' = C.divMapCoeff F D Q' :=
  congrFun (Finsupp.ofSupportFinite_coe (f := C.divMapCoeff F D)
    (hf := C.finite_support_divMapCoeff F D)) Q'

end

end Curve
end Work.CurveBasics
