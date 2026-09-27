import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.geom_glue
import Submission.Work.KT.Fund.Basic

/-!
# `Work.KT.Fund.Pullback` — `C(X × S², ℂ)` as the fibre product of the two disc algebras

The two-disc decomposition of `S²` (see `Work.KT.Fund.Geom`) identifies the algebra of continuous
functions on `X × S²` with the fibre product of two copies of `C(X × Ball ℂ, ℂ)` over
`C(X × Sph ℂ, ℂ)`:

* `pullAlg2 X` is that fibre product, as a `ℂ`-subalgebra of the product;
* `glueEquiv X` is the identification `C(X × S², ℂ) ≃ₐ[ℂ] pullAlg2 X`.

Consequently classes in `K₀(C(X × S², ℂ))` can be produced from "clutching data": a pair of
idempotent matrices over the two disc algebras whose boundary values agree.
-/

namespace Work.KT
namespace Fund

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The fibre product of two copies of `C(X × D, ℂ)` over `C(X × S¹, ℂ)`: the algebra of
clutching data for `X × S²`. -/
def pullAlg2 : Subalgebra ℂ (C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)) where
  carrier := {z | bdryRestrict X z.1 = bdryRestrict X z.2}
  mul_mem' := by
    intro a b ha hb
    show bdryRestrict X (a.1 * b.1) = bdryRestrict X (a.2 * b.2)
    rw [map_mul, map_mul, ha, hb]
  add_mem' := by
    intro a b ha hb
    show bdryRestrict X (a.1 + b.1) = bdryRestrict X (a.2 + b.2)
    rw [map_add, map_add, ha, hb]
  algebraMap_mem' := by
    intro c
    show bdryRestrict X
        ((algebraMap ℂ (C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ))) c).1
      = bdryRestrict X
        ((algebraMap ℂ (C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ))) c).2
    simp

/-- The map `C(X × S², ℂ) → pullAlg2 X` given by the two restrictions. -/
def pullAlg2Map : C(X × S2, ℂ) →ₐ[ℂ] pullAlg2 X where
  toFun g := ⟨(pullUp X g, pullDn X g), bdryRestrict_pullUp_eq_pullDn X g⟩
  map_one' := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;> exact map_one _
  map_mul' g h := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;> exact map_mul _ g h
  map_zero' := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;> exact map_zero _
  map_add' g h := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;> exact map_add _ g h
  commutes' c := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;>
      · ext p
        simp

@[simp] lemma pullAlg2Map_apply (g : C(X × S2, ℂ)) :
    ((pullAlg2Map X g : pullAlg2 X) : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ))
      = (pullUp X g, pullDn X g) := rfl

/-- **The two-disc decomposition**: `C(X × S², ℂ)` is the fibre product of the two disc algebras
over the circle algebra. -/
def glueEquiv : C(X × S2, ℂ) ≃ₐ[ℂ] pullAlg2 X where
  toFun := pullAlg2Map X
  invFun z := (geom_glue X (z : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)).1
    (z : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)).2 z.2).choose
  left_inv g := by
    have h := (geom_glue X _ _ (bdryRestrict_pullUp_eq_pullDn X g)).choose_spec.2 g
    exact (h ⟨rfl, rfl⟩).symm
  right_inv z := by
    refine Subtype.ext ?_
    have h := (geom_glue X _ _ z.2).choose_spec.1
    exact Prod.ext h.1 h.2
  map_mul' g h := by
    refine Subtype.ext ?_
    exact Prod.ext (map_mul _ _ _) (map_mul _ _ _)
  map_add' g h := by
    refine Subtype.ext ?_
    exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  commutes' c := by
    refine Subtype.ext ?_
    simp

@[simp] lemma glueEquiv_apply (g : C(X × S2, ℂ)) :
    ((glueEquiv X g : pullAlg2 X) : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ))
      = (pullUp X g, pullDn X g) := rfl

/-- `K₀` of `C(X × S², ℂ)` is `K₀` of the fibre product of the disc algebras over the circle
algebra. -/
def k0Glue : K0 C(X × S2, ℂ) ≃+ K0 (pullAlg2 X) where
  toFun := K0.map (glueEquiv X : C(X × S2, ℂ) →+* pullAlg2 X)
  invFun := K0.map ((glueEquiv X).symm : pullAlg2 X →+* C(X × S2, ℂ))
  map_add' x y := map_add (K0.map (glueEquiv X : C(X × S2, ℂ) →+* pullAlg2 X)) x y
  left_inv x := by
    have hcomp : (((glueEquiv X).symm : pullAlg2 X →+* C(X × S2, ℂ)).comp
        (glueEquiv X : C(X × S2, ℂ) →+* pullAlg2 X))
        = RingHom.id (C(X × S2, ℂ)) := by
      refine RingHom.ext fun g => ?_
      exact AlgEquiv.symm_apply_apply (glueEquiv X) g
    rw [← K0.map_comp_apply (glueEquiv X : C(X × S2, ℂ) →+* pullAlg2 X)
      ((glueEquiv X).symm : pullAlg2 X →+* C(X × S2, ℂ)) x, hcomp, K0.map_id_apply]
  right_inv x := by
    have hcomp : (((glueEquiv X : C(X × S2, ℂ) →+* pullAlg2 X)).comp
        ((glueEquiv X).symm : pullAlg2 X →+* C(X × S2, ℂ)))
        = RingHom.id (pullAlg2 X) := by
      refine RingHom.ext fun g => ?_
      exact AlgEquiv.apply_symm_apply (glueEquiv X) g
    rw [← K0.map_comp_apply ((glueEquiv X).symm : pullAlg2 X →+* C(X × S2, ℂ))
      (glueEquiv X : C(X × S2, ℂ) →+* pullAlg2 X) x, hcomp, K0.map_id_apply]

end

end Fund
end Work.KT
