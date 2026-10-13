import Mathlib
import Submission.Work.DSG4a.SectionBaseChange

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG4a

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-- Naturality of the "pullback of sections" part of the comparison map: the pullback of a
restriction of a section of `X` along `V ≤ U` agrees with the restriction of its pullback to
`X_{A'}` along the induced inclusion `baseChangeOpen X f V ≤ baseChangeOpen X f U`. -/
theorem sectionBaseChange_naturality_fst (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {U V : X.Opens} (h : V ≤ U)
    (a : X.presheaf.obj (Opposite.op U)) :
    (CommRingCat.Hom.hom
        (Scheme.Hom.app (Work.DSG4a.baseChangeFst (A := A) (A' := A') X f) V))
        ((CommRingCat.Hom.hom (Work.DSG4a.resLE h)) a) =
      (CommRingCat.Hom.hom (Work.DSG4a.resLE
        (V := Work.DSG4a.baseChangeOpen X f V)
        (U := Work.DSG4a.baseChangeOpen X f U)
        (fun x hx => h hx)))
        (CommRingCat.Hom.hom
          (Scheme.Hom.app (Work.DSG4a.baseChangeFst (A := A) (A' := A') X f) U) a) := by
  have hnat := Scheme.Hom.naturality
    (f := Work.DSG4a.baseChangeFst (A := A) (A' := A') X f)
    (i := (homOfLE h : V ⟶ U).op)
  have hA' := ConcreteCategory.congr_hom hnat a
  simp only [CategoryTheory.comp_apply] at hA'
  simpa [Work.DSG4a.resLE] using hA'

/-- Naturality of the "structure section" part of the comparison map: restricting the
structure section of `b` from `baseChangeOpen X f U` to `baseChangeOpen X f V` is the
structure section of `b` over `baseChangeOpen X f V`. -/
theorem sectionBaseChange_naturality_snd (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {U V : X.Opens} (h : V ≤ U) (b : A') :
    (CommRingCat.Hom.hom (Work.DSG4a.resLE
        (V := Work.DSG4a.baseChangeOpen X f V)
        (U := Work.DSG4a.baseChangeOpen X f U)
        (fun x hx => h hx)))
        ((DSMap.phiU A' (Work.DSG4a.baseChangeScheme X f) (Work.DSG4a.baseChangeSnd X f)
            (Work.DSG4a.baseChangeOpen X f U)) b) =
      (DSMap.phiU A' (Work.DSG4a.baseChangeScheme X f) (Work.DSG4a.baseChangeSnd X f)
            (Work.DSG4a.baseChangeOpen X f V)) b := by
  exact DSMap.phiU_res (A := A') (X := Work.DSG4a.baseChangeScheme X f)
    (f := Work.DSG4a.baseChangeSnd X f) (i := homOfLE (fun x hx => h hx)) (a := b)

theorem sectionBaseChange_naturality {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {U V : X.Opens} (h : V ≤ U)
    (a : X.presheaf.obj (Opposite.op U)) (b : A') :
    Work.DSG4a.sectionBaseChange X f V
        (Work.DSG4a.tmulElem f V ((Work.DSG4a.resLE h).hom a) b) =
      (Work.DSG4a.resLE
        (V := Work.DSG4a.baseChangeOpen X f V)
        (U := Work.DSG4a.baseChangeOpen X f U)
        (fun x hx => h hx)).hom
        (Work.DSG4a.sectionBaseChange X f U
          (Work.DSG4a.tmulElem f U a b)) := by
  unfold Work.DSG4a.tmulElem
  simp only [Work.DSG4a.sectionBaseChange_tmul]
  rw [RingHom.map_mul]
  rw [sectionBaseChange_naturality_fst (A := A) (A' := A') X f h a,
    sectionBaseChange_naturality_snd (A := A) (A' := A') X f h b]

end Work.DSG4a
