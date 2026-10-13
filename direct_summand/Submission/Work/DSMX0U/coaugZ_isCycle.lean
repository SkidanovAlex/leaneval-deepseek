import Mathlib
import Submission.Work.DSMX0U.Basic
import Submission.Work.DSF1.Cech.exists_cechZ_lift

/-!
# The degree-`0` coaugmentation of the `ℤ`-indexed Čech complex is a cocycle

`DSMap.cechZ A X f U` is `(DSMap.cech A X f U).extend ComplexShape.embeddingUpNat`, the
Čech complex of `𝒪_X` (as a complex of `A`-modules) regraded from `ℕ` to `ℤ` by extending
by zero in negative degrees.  The degree-`0` coaugmentation `DSMap.coaug0` of the `ℕ`-indexed
complex transports to a cochain `A ⟶ (cechZ A X f U).X 0` of the `ℤ`-indexed complex via the
canonical identification `(cechZ).X 0 ≅ (cech).X 0`, and the content of this file is that this
transported cochain is a cocycle.

The mathematical input is `Work.DSF1.Cech.coaug0_cech_d` (the alternating sum of the cofaces
kills the constant section, in Čech degrees `0 → 1`) together with the computation
`HomologicalComplex.extend_d_eq` of the differential of an extended complex in degrees lying
in the image of the embedding.
-/

namespace Work.DSMX0U

open CategoryTheory AlgebraicGeometry

universe a

theorem coaugZ_isCycle {A : Type a} [CommRing A] {X : Scheme.{a}}
    (f : X ⟶ Spec (.of A)) {ι : Type a} (U : ι → X.Opens) :
    ∀ j : ℤ,
      (DSMap.coaug0 A X f U ≫
        ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv) ≫
          (DSMap.cechZ A X f U).d 0 j = 0 := by
  intro j
  -- `cechZ` is *definitionally* `(cech).extend embeddingUpNat`; we work with the latter so
  -- that the degrees occurring in the goal are the ones named by the embedding (`0` and `1`
  -- rather than `e.f 0` and `e.f 1`), which keeps the rewriting below at the default
  -- transparency level.
  by_cases hj : j = 1
  · subst hj
    show (DSMap.coaug0 A X f U ≫
          (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
            (i := 0) (i' := 0) rfl).inv) ≫
          ((DSMap.cech A X f U).extend ComplexShape.embeddingUpNat).d 0 1 = 0
    set g₀ := HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
        (i := 0) (i' := 0) rfl with hg₀
    set g₁ := HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
        (i := 1) (i' := 1) rfl with hg₁
    -- the differential of the extended complex between degrees lying in the image of `e`
    have hd : ((DSMap.cech A X f U).extend ComplexShape.embeddingUpNat).d 0 1 =
        g₀.hom ≫ (DSMap.cech A X f U).d 0 1 ≫ g₁.inv :=
      HomologicalComplex.extend_d_eq (DSMap.cech A X f U) ComplexShape.embeddingUpNat rfl rfl
    -- `g₀.inv` followed by `g₀.hom` is the identity, so the cochain is the transported
    -- degree-`0` coaugmentation followed by the Čech differential
    have h1 : (DSMap.coaug0 A X f U ≫ g₀.inv) ≫
          (g₀.hom ≫ ((DSMap.cech A X f U).d 0 1 ≫ g₁.inv))
        = DSMap.coaug0 A X f U ≫ ((DSMap.cech A X f U).d 0 1 ≫ g₁.inv) :=
      (Category.assoc _ _ _).trans (congrArg (fun m => DSMap.coaug0 A X f U ≫ m)
        (Iso.inv_hom_id_assoc g₀ ((DSMap.cech A X f U).d 0 1 ≫ g₁.inv)))
    rw [hd, h1, ← Category.assoc, Work.DSF1.Cech.coaug0_cech_d, Limits.zero_comp]
  · -- degrees which are not in the image of the shape embedding: the differential is zero
    show (DSMap.coaug0 A X f U ≫
          (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
            (i := 0) (i' := 0) rfl).inv) ≫
          ((DSMap.cech A X f U).extend ComplexShape.embeddingUpNat).d 0 j = 0
    rw [HomologicalComplex.shape _ 0 j (fun h => hj (by simpa using h.symm)), Limits.comp_zero]

end Work.DSMX0U
