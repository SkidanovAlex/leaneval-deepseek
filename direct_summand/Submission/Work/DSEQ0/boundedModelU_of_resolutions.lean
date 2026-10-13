import Mathlib
import Submission.Work.DSF1.Setup
import Submission.Work.DSEQ0.Coaug
import Submission.Work.DSEQ0.exists_lift_of_quasiIso
import Submission.Work.DSMap.Mix2
import Submission.Work.DSEQ0.termBddModel_cechZ_of_resolutions

/-!
# `Work.DSEQ0.boundedModelU_of_resolutions`

A **bounded** (both below and above) finite free model of the Čech complex `cechZ A X f U` of a
finite affine cover, carrying the coaugmentation, deduced from bounded finite free resolutions of
the cohomology modules `Hⁱ(Č)`.

This is the corrected form of the (refuted) node `Work.DSEQ0.boundedModel_of_resolutions`: the
refutation `Work.DSEQ0.not_boundedModel_concl` shows that requiring the model to vanish in
*negative* degrees is impossible in general (the trivial cover of `Spec 𝔽₂` over `ℤ` has
`H⁰(Č) ≅ 𝔽₂`, a non-zero torsion `ℤ`-module, and `H⁰(P) = ker (P.d 0 1) ↪ P.X 0` would embed it
into a free, hence torsion-free, module).  The trace functional of area `EQ0` needs only
boundedness on *both* sides, which is what is proved here.

The mathematical content is:

* `Work.DSEQ0.termBddModel_cechZ_of_resolutions` (the truncation + splicing input): the Čech
  complex, whose *cohomology* vanishes above `N` (`hhi`), admits a term-bounded finite free model
  `P` with a quasi-isomorphism `q : P ⟶ cechZ A X f U`.  This is
  `Work.DSEQ0.exists_bounded_free_model` applied to the good truncation `(cechZ).truncLE N`;
* the coaugmentation: `A[0]` is K-projective, so the Čech coaugmentation `Work.DSF1.ccZ` lifts
  along the quasi-isomorphism `q` to a chain map `c : A[0] ⟶ P`
  (`Work.DSEQ0.exists_lift_of_quasiIso`, in the derived category).  Since the source `A[0]` is
  concentrated in degree `0` and the target `cechZ` vanishes in degree `-1`, two chain maps
  `A[0] ⟶ cechZ` which are equal in the derived category are already *equal* in degree `0`
  (`Work.DSEQ0.f_zero_eq_of_Q_map_eq`): a homotopy realizing the derived equality has both its
  degree-`0` components zero.  Hence `(c ≫ q).f 0 = (ccZ).f 0` *strictly*, and the degree-`0`
  component of `Work.DSF1.ccZ_compat` gives the coaugmentation compatibility of
  `DSMap.Mix2.IsFinFreeModelU` for `ε := (singleObjXSelf (up ℤ) 0 A).inv ≫ c.f 0`.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQ0

universe a

section Helpers

variable {A : Type a} [CommRing A]

/-- Two homotopic chain maps out of `A[0]` into a complex which vanishes in degree `-1` agree in
degree `0`: the homotopy condition in degree `0`,
`f.f 0 = dNext 0 h.hom + prevD 0 h.hom + g.f 0`, has both extra terms zero because
`(A[0]).X 1 = 0` and `K.X (-1) = 0`. -/
lemma f_zero_eq_of_homotopic {K : CochainComplex (ModuleCat.{a} A) ℤ}
    (hK : CategoryTheory.Limits.IsZero (K.X (-1)))
    {f g : singleZ A ⟶ K} (h : Homotopy f g) : f.f 0 = g.f 0 := by
  have hcomm := h.comm 0
  have h1 : dNext (c := ComplexShape.up ℤ) (0 : ℤ) h.hom = 0 := by
    rw [dNext_eq h.hom (ComplexShape.up_mk (0 : ℤ) 1 (by norm_num))]
    have hz : (singleZ A).d 0 1 = 0 :=
      HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 (ModuleCat.of A A) 0 1
    rw [hz, zero_comp]
  have h2 : prevD (c := ComplexShape.up ℤ) (0 : ℤ) h.hom = 0 := by
    rw [prevD_eq h.hom (ComplexShape.up_mk (-1 : ℤ) 0 (by norm_num)),
      IsZero.eq_zero_of_tgt hK (h.hom 0 (-1)), zero_comp]
  rw [h1, h2] at hcomm
  simpa using hcomm

/-- Two chain maps `A[0] ⟶ K`, with `K` vanishing in degree `-1`, which are equal in the derived
category agree in degree `0`.  Since `A[0]` is K-projective, equality in `D(A)` means equality in
the homotopy category, i.e. the existence of a homotopy, and homotopic maps agree in degree `0`
by `Work.DSEQ0.f_zero_eq_of_homotopic`. -/
lemma f_zero_eq_of_Q_map_eq [HasDerivedCategory (ModuleCat.{a} A)]
    {K : CochainComplex (ModuleCat.{a} A) ℤ}
    (hK : CategoryTheory.Limits.IsZero (K.X (-1)))
    {f g : singleZ A ⟶ K}
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : f.f 0 = g.f 0 := by
  haveI : CochainComplex.IsKProjective (singleZ A) := singleZ_isKProjective
  refine f_zero_eq_of_homotopic hK (HomotopyCategory.homotopyOfEq f g ?_)
  refine (CochainComplex.IsKProjective.Qh_map_bijective (singleZ A)
    ((HomotopyCategory.quotient (ModuleCat.{a} A) (ComplexShape.up ℤ)).obj K)).injective ?_
  refine (cancel_mono ((DerivedCategory.quotientCompQhIso (ModuleCat.{a} A)).hom.app K)).mp ?_
  have h1 := DerivedCategory.quotientCompQhIso_hom_naturality f
  have h2 := DerivedCategory.quotientCompQhIso_hom_naturality g
  calc DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{a} A)
        (ComplexShape.up ℤ)).map f) ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{a} A)).hom.app K
      = (DerivedCategory.quotientCompQhIso (ModuleCat.{a} A)).hom.app (singleZ A) ≫
          DerivedCategory.Q.map f := h1
    _ = (DerivedCategory.quotientCompQhIso (ModuleCat.{a} A)).hom.app (singleZ A) ≫
          DerivedCategory.Q.map g := by rw [h]
    _ = DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{a} A)
          (ComplexShape.up ℤ)).map g) ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{a} A)).hom.app K := h2.symm

end Helpers

theorem boundedModelU_of_resolutions (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    [AlgebraicGeometry.IsProper f]
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) (N : ℤ)
    (hhi : ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology i))
    (G : ℤ → CochainComplex (ModuleCat.{a} A) ℤ)
    (hGfin : ∀ i j, Module.Finite A ((G i).X j))
    (hGfree : ∀ i j, Module.Free A ((G i).X j))
    (hGbdd : ∀ i, ∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero ((G i).X j))
    (hGres : ∀ i : ℤ, ∃ g : G i ⟶
      (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) i).obj
        ((DSMap.cechZ A X f U).homology i), QuasiIso g) :
    ∃ (a b : ℤ) (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0),
      DSMap.Mix2.IsFinFreeModelU A X f U P ε ∧
        (∀ i : ℤ, i < a ∨ b < i → CategoryTheory.Limits.IsZero (P.X i)) := by
  letI : HasDerivedCategory (ModuleCat.{a} A) := HasDerivedCategory.standard (ModuleCat.{a} A)
  -- (1) a term-bounded finite free model of the Čech complex, with a quasi-isomorphism
  obtain ⟨P, hPfin, hPfree, ⟨p₁, p₂, hPbdd⟩, q, hq⟩ :=
    termBddModel_cechZ_of_resolutions A X f U N hhi G hGfin hGfree hGbdd hGres
  -- (2) lift the Čech coaugmentation along the quasi-isomorphism
  obtain ⟨c, hc⟩ := exists_lift_of_quasiIso P (DSMap.cechZ A X f U) q hq (DSF1.ccZ A X f U)
  have hder : DerivedCategory.Q.map (c ≫ q) = DerivedCategory.Q.map (DSF1.ccZ A X f U) := by
    rw [Functor.map_comp, hc]
  -- (3) the lift is *strictly* compatible in degree `0`
  have hst : (c ≫ q).f 0 = (DSF1.ccZ A X f U).f 0 :=
    f_zero_eq_of_Q_map_eq (K := DSMap.cechZ A X f U)
      (isZero_cechZ_X_of_neg A X f U (by norm_num)) hder
  -- (4) assemble the model data
  refine ⟨p₁, p₂, P,
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫ c.f 0,
    ?_, hPbdd⟩
  refine ⟨⟨fun i => ⟨hPfree i, hPfin i⟩, p₂, fun i hi => hPbdd i (Or.inr hi)⟩, ?_, q, hq, ?_⟩
  · -- the coaugmentation is a cocycle (it is the degree-`0` component of a chain map)
    intro k
    rw [Category.assoc, HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d, zero_comp,
      comp_zero]
  · -- the coaugmentation compatibility `ε ≫ q.f 0 ≫ extendXIso.hom = coaug0`
    show (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫
        c.f 0 ≫ q.f 0 ≫
        (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
          DSF1.embeddingUpNat_f_zero).hom = DSMap.coaug0 A X f U
    have hεq : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫
        c.f 0) ≫ q.f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫
          (DSF1.ccZ A X f U).f 0 := by
      rw [Category.assoc, ← HomologicalComplex.comp_f, hst]
    calc (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫
          c.f 0 ≫ q.f 0 ≫
          (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
            DSF1.embeddingUpNat_f_zero).hom
        = (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫
            c.f 0) ≫ q.f 0) ≫
            (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
              DSF1.embeddingUpNat_f_zero).hom := (Category.assoc _ _ _).symm
      _ = ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫
            (DSF1.ccZ A X f U).f 0) ≫
            (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
              DSF1.embeddingUpNat_f_zero).hom := by
          rw [hεq]
      _ = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫
            ((DSF1.ccZ A X f U).f 0 ≫
              (HomologicalComplex.extendXIso (DSMap.cech A X f U) ComplexShape.embeddingUpNat
                DSF1.embeddingUpNat_f_zero).hom) := Category.assoc _ _ _
      _ = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv ≫
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (ModuleCat.of A A)).hom ≫ DSMap.coaug0 A X f U) := by
          rw [DSF1.ccZ_compat]
      _ = DSMap.coaug0 A X f U := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Work.DSEQ0
