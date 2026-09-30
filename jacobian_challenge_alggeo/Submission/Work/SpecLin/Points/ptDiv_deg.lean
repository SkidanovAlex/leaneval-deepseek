import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Work.SpecLin.Points

open CategoryTheory Limits AlgebraicGeometry

/-- If `ψ ∘ φ` is bijective for ring homs `φ : K →+* L`, `ψ : L →+* K'` between fields, then
`φ` is bijective: `φ` is injective since `ψ ∘ φ` is, and if `z ∈ L` then surjectivity of
`ψ ∘ φ` applied to `ψ z` produces `w` with `ψ (φ w) = ψ z`, whence `φ w = z` because a ring
homomorphism of fields `ψ` is injective. -/
theorem bijective_of_comp_bijective_ringHom {K L K' : Type*} [Field K] [Field L] [Field K']
    (φ : K →+* L) (ψ : L →+* K') (h : Function.Bijective (ψ.comp φ)) :
    Function.Bijective φ := by
  refine ⟨Function.Injective.of_comp h.1, fun z => ?_⟩
  obtain ⟨w, hw⟩ := h.2 (ψ z)
  refine ⟨w, ?_⟩
  have hw' : ψ (φ w) = ψ z := by simpa using hw
  have h1 : ψ (z - φ w) = 0 := by rw [map_sub, hw', sub_self]
  exact (sub_eq_zero.mp (RingHom.injective ψ (by rw [h1, map_zero]))).symm

/-- If `a : X ⟶ Y` is a section of `b : Y ⟶ X` (i.e. `a ≫ b = 𝟙 X`), then the residue degree
of `b` at the point `a x` is one.

Indeed `b.residueDegree (a x)` is the degree of the field extension
`κ(b (a x)) → κ(a x)` induced by `b.residueFieldMap (a x)`.  Composing with
`a.residueFieldMap x` gives the residue field map of `a ≫ b = 𝟙 X`, which is the identity
(`residueFieldMap_congr` supplies the transport along `(a ≫ b) x = x`); hence
`b.residueFieldMap (a x)` becomes bijective and the extension degree is `1`. -/
theorem residueDegree_of_section {X Y : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ X)
    (hab : a ≫ b = 𝟙 X) (x : X) : b.residueDegree (a x) = 1 := by
  letI : Algebra (X.residueField (b (a x))) (Y.residueField (a x)) :=
    (Scheme.Hom.residueFieldMap b (a x)).hom.toAlgebra
  rw [Scheme.Hom.residueDegree]
  apply Module.finrank_of_bijective_algebraMap
  have hcomp : Scheme.Hom.residueFieldMap b (a x) ≫ Scheme.Hom.residueFieldMap a x =
      Scheme.Hom.residueFieldMap (a ≫ b) x := (Scheme.residueFieldMap_comp a b x).symm
  have hcongr := Scheme.Hom.residueFieldMap_congr (X := X) (Y := X) (f := a ≫ b) (g := 𝟙 X) hab x
  have hid : Function.Bijective ⇑(Scheme.Hom.residueFieldMap (𝟙 X) x).hom := by
    rw [Scheme.residueFieldMap_id]
    exact ConcreteCategory.bijective_of_isIso (𝟙 (X.residueField x))
  have hbij : Function.Bijective ⇑(Scheme.Hom.residueFieldMap (a ≫ b) x).hom := by
    rw [hcongr, CommRingCat.hom_comp]
    change Function.Bijective ((⇑(CommRingCat.Hom.hom (Scheme.Hom.residueFieldMap (𝟙 X) x))) ∘
        (⇑(CommRingCat.Hom.hom (Scheme.residueFieldCongr _).hom)))
    exact Function.Bijective.comp hid
      (ConcreteCategory.bijective_of_isIso (Scheme.residueFieldCongr _).hom)
  rw [RingHom.algebraMap_toAlgebra]
  apply bijective_of_comp_bijective_ringHom (ψ := (Scheme.Hom.residueFieldMap a x).hom)
  have hcomp' : ((Scheme.Hom.residueFieldMap a x).hom).comp
        ((Scheme.Hom.residueFieldMap b (a x)).hom) =
      (Scheme.Hom.residueFieldMap (a ≫ b) x).hom := by
    have := congrArg CommRingCat.Hom.hom hcomp
    rwa [CommRingCat.hom_comp] at this
  rw [hcomp']
  exact hbij

/-- The point divisor `[p]` of an `F`-point `p` of a curve `C` has degree one: the residue
field of the corresponding closed point of `C_F` is `F` itself.

Route: `ptDiv p = Div.place (ptPlace p)`, `Div.deg_place` reduces this to
`(C.baseChange F).hom.residueDegree (ptToPoint p) = 1`; `ptLeft p` is a closed immersion
(hence induces an isomorphism of residue fields) whose composite with `(C.baseChange F).hom` is
the identity, and `Spec F` has a single point. -/
theorem ptDiv_deg {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u} [Field F]
    [Algebra K F] (p : Work.SpecLin.CurveFPt C F) :
    (C.baseChange F).deg (Work.SpecLin.ptDiv p) = 1 := by
  have hpt : Work.SpecLin.ptPlace p = ⟨Work.SpecLin.ptToPoint p,
      Work.SpecLin.Points.ptToPoint_isClosed p⟩ := rfl
  rw [Work.SpecLin.ptDiv, hpt, Work.CurveBasics.Curve.deg_place]
  have h : (C.baseChange F).hom.residueDegree (Work.SpecLin.ptToPoint p) = 1 :=
    residueDegree_of_section (Work.SpecLin.ptLeft p) (C.baseChange F).hom
      (Work.SpecLin.Points.ptLeft_comp_hom p) (IsLocalRing.closedPoint F)
  rw [h]
  norm_num

end Work.SpecLin.Points
