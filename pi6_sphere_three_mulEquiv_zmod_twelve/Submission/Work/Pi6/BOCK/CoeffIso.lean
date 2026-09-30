import Mathlib
import Submission.Work.Pi6.BOCK.Defs
import Submission.Work.Pi6.BOCK.ExpTensBasic
import Submission.Work.Pi6.BOCK.FcHomologyNatural
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# AREA BOCK — the identification of `H_n(C_*(X;ℤ) ⊗ ℤ/p)` with `H_n(X;ℤ/p)`

The Bockstein short complex `0 → C_*(X;ℤ) --·p--> C_*(X;ℤ) --red--> C_*(X;ℤ) ⊗ ℤ/p → 0`
(`Work.Pi6.EMZ.bockSES`) has its third term computed with coefficients read over `ℤ`.  This file
identifies its homology with the mod-`p` homology `H_n(X;ℤ/p) = Work.Pi6.HR (ZMod p) X n`, by the
chain of natural isomorphisms

* `expTens K M ≅ K ⊗ M` (`Work.SSS.tensorRightMapHomIsoExpTens`),
* `F(C_*(X;ℤ)) ≅ C_*(X; F ℤ/p)` (`Work.Pi6.BOCK.baseChangeNatIso`),
* two changes of coefficients `(ℤ/p) ≅ F(ℤ/p)`, and
* `H_n(F(K)) ≅ F(H_n(K))` (`Work.Pi6.BOCK.fcHomologyIso`).

Every factor is an isomorphism of **functors** of the simplicial set, so the resulting isomorphism is
natural in `X`; this is the input to the naturality of the Bockstein sequence.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.BOCK

noncomputable section

/-! ## Coefficient rings and the restriction of scalars -/

/-- `ℤ/p` as a module over itself. -/
abbrev M0 (p : ℕ) : ModuleCat (ZMod p) := ModuleCat.of (ZMod p) (ZMod p)

/-- Restriction of scalars `ℤ/p`-modules → `ℤ`-modules. -/
abbrev Fp (p : ℕ) : ModuleCat (ZMod p) ⥤ ModuleCat ℤ :=
  ModuleCat.restrictScalars (Int.castRingHom (ZMod p))

/-! ## Changing coefficients at the level of the singular chain complex -/

/-- **Change of coefficients of the singular chain complex of a simplicial set.**  For an
isomorphism of coefficient modules `e : R ≅ R'`, the singular chain complex with coefficients in
`R` is that with coefficients in `R'`; the isomorphism is induced by the functoriality of the chain
functor in its coefficients, hence natural in the simplicial set. -/
def coeffIsoChain {R R' : ModuleCat ℤ} (e : R ≅ R') (X : SSet) :
    X.chainComplex R ≅ X.chainComplex R' :=
  ((SSet.chainComplexFunctor (ModuleCat ℤ)).mapIso e).app X

/-- Naturality of the change of coefficients in the simplicial set. -/
theorem coeffIsoChain_natural {R R' : ModuleCat ℤ} (e : R ≅ R') {X Y : SSet} (g : X ⟶ Y) :
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj R).map g ≫ (coeffIsoChain e Y).hom =
      (coeffIsoChain e X).hom ≫
        ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj R').map g :=
  NatTrans.naturality ((SSet.chainComplexFunctor (ModuleCat ℤ)).map e.hom) g

/-! ## The identification -/

/-- The coefficient isomorphism `(ℤ/p) ⊗ ℤ ≅ ℤ/p`. -/
def unitCoeffIso (p : ℕ) : (MonoidalCategory.tensorRight (Mp p)).obj zZ ≅ Mp p :=
  λ_ (Mp p)

/-- The coefficient isomorphism `ℤ/p ≅ (restrictScalars ℤ/p)(ℤ/p)`. -/
def coeffIsoMp (p : ℕ) (hp : p.Prime) : Mp p ≅ (Fp p).obj (M0 p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (Work.Pi6.EMZ.restrictScalarsObjIntIso (ZMod p)).symm

/-- **The identification of the coefficient-extended singular chains with the mod-`p` singular
chains, on homology.**  The composite of the functor `- ⊗ ℤ/p`, base change along
`restrictScalars (ℤ → ℤ/p)` and the two coefficient isomorphisms. -/
def eCIso (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    (Work.SSS.expTens (Work.Pi6.EMZ.chZ X) (Mp p)).homology n ≅
      (Fp p).obj (Work.Pi6.HR (ZMod p) X n) :=
  (HomologicalComplex.homologyMapIso (expTensIsoNat (Mp p) (Work.Pi6.EMZ.chZ X)) n) ≪≫
  (HomologicalComplex.homologyMapIso
    ((baseChangeNatIso (MonoidalCategory.tensorRight (Mp p)) zZ).app
      (Work.Pi6.EMZ.sing X)) n) ≪≫
  (HomologicalComplex.homologyMapIso (coeffIsoChain (unitCoeffIso p) (Work.Pi6.EMZ.sing X)) n) ≪≫
  (HomologicalComplex.homologyMapIso (coeffIsoChain (coeffIsoMp p hp) (Work.Pi6.EMZ.sing X)) n) ≪≫
  (HomologicalComplex.homologyMapIso
    ((baseChangeNatIso (Fp p) (M0 p)).app (Work.Pi6.EMZ.sing X)) n).symm ≪≫
  (fcHomologyIso (Fp p) ((Work.Pi6.EMZ.sing X).chainComplex (M0 p)) n)

/-! ## The six factors of the identification -/

section Factors

variable (p : ℕ)

/-- The `ℤ`-coefficient chain complex with the coefficient extension `- ⊗ ℤ/p` undone. -/
abbrev FcTens (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  ((MonoidalCategory.tensorRight (Mp p)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (Work.Pi6.EMZ.chZ X)

/-- Restriction of scalars applied to the mod-`p` singular chains. -/
abbrev chRestr (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  ((Fp p).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    ((Work.Pi6.EMZ.sing X).chainComplex (M0 p))

/-- Factor 1: the naive tensor complex is the coefficient extension. -/
def eC1 (X : Type) [TopologicalSpace X] :
    Work.SSS.expTens (Work.Pi6.EMZ.chZ X) (Mp p) ≅ FcTens p X :=
  expTensIsoNat (Mp p) (Work.Pi6.EMZ.chZ X)

/-- Factor 2: base change of the chain complex. -/
def eC2 (X : Type) [TopologicalSpace X] :
    FcTens p X ≅ (Work.Pi6.EMZ.sing X).chainComplex
      ((MonoidalCategory.tensorRight (Mp p)).obj zZ) :=
  (baseChangeNatIso (MonoidalCategory.tensorRight (Mp p)) zZ).app (Work.Pi6.EMZ.sing X)

/-- Factor 3: the unit isomorphism of the monoidal structure. -/
def eC3 (X : Type) [TopologicalSpace X] :
    (Work.Pi6.EMZ.sing X).chainComplex ((MonoidalCategory.tensorRight (Mp p)).obj zZ) ≅
      (Work.Pi6.EMZ.sing X).chainComplex (Mp p) :=
  coeffIsoChain (unitCoeffIso p) (Work.Pi6.EMZ.sing X)

/-- Factor 4: the identification of `ℤ/p` with the restriction of scalars of `ℤ/p`. -/
def eC4 (hp : p.Prime) (X : Type) [TopologicalSpace X] :
    (Work.Pi6.EMZ.sing X).chainComplex (Mp p) ≅
      (Work.Pi6.EMZ.sing X).chainComplex ((Fp p).obj (M0 p)) :=
  coeffIsoChain (coeffIsoMp p hp) (Work.Pi6.EMZ.sing X)

/-- Factor 5: base change of the chain complex, reversed. -/
def eC5 (X : Type) [TopologicalSpace X] :
    (Work.Pi6.EMZ.sing X).chainComplex ((Fp p).obj (M0 p)) ≅ chRestr p X :=
  ((baseChangeNatIso (Fp p) (M0 p)).app (Work.Pi6.EMZ.sing X)).symm

/-- Factor 6: restriction of scalars commutes with homology. -/
def eC6 (X : Type) [TopologicalSpace X] (n : ℕ) :
    (chRestr p X).homology n ≅
      (Fp p).obj (((Work.Pi6.EMZ.sing X).chainComplex (M0 p)).homology n) :=
  fcHomologyIso (Fp p) ((Work.Pi6.EMZ.sing X).chainComplex (M0 p)) n

/-- The identification, split into its six pieces. -/
def eCIso' (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    (Work.SSS.expTens (Work.Pi6.EMZ.chZ X) (Mp p)).homology n ≅
      (Fp p).obj (Work.Pi6.HR (ZMod p) X n) :=
  (HomologicalComplex.homologyMapIso (eC1 p X) n) ≪≫
    (HomologicalComplex.homologyMapIso (eC2 p X) n) ≪≫
    (HomologicalComplex.homologyMapIso (eC3 p X) n) ≪≫
    (HomologicalComplex.homologyMapIso (eC4 p hp X) n) ≪≫
    (HomologicalComplex.homologyMapIso (eC5 p X) n) ≪≫
    (eC6 p X n)

end Factors

/-! ## Naturality of the identification -/

section Naturality

variable (p : ℕ) (hp : p.Prime) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The chain map on the integral singular chains induced by a continuous map. -/
def chMapZ (f : C(X, Y)) : Work.Pi6.EMZ.chZ X ⟶ Work.Pi6.EMZ.chZ Y :=
  Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)

/-- The chain map on the mod-`p` singular chains induced by a continuous map. -/
def chMapK (f : C(X, Y)) :
    (Work.Pi6.EMZ.sing X).chainComplex (M0 p) ⟶
      (Work.Pi6.EMZ.sing Y).chainComplex (M0 p) :=
  Work.Cohomology.chainMap (ZMod p) (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)

/-- The map of singular simplicial sets induced by a continuous map. -/
def sMap (f : C(X, Y)) : Work.Pi6.EMZ.sing X ⟶ Work.Pi6.EMZ.sing Y :=
  TopCat.toSSet.map (TopCat.ofHom f)

/-- Naturality of the first factor of the identification. -/
theorem eC1_natural (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)) n ≫
      (HomologicalComplex.homologyMapIso (eC1 p Y) n).hom =
    (HomologicalComplex.homologyMapIso (eC1 p X) n).hom ≫
      HomologicalComplex.homologyMap
        (((MonoidalCategory.tensorRight (Mp p)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (chMapZ f)) n := by
  have h := expTensIsoNat_natural (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y)
    (chMapZ f) (Mp p)
  have h2 := congrArg (fun t => HomologicalComplex.homologyMap t n) h
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMapIso_hom,
    eC1] at h2 ⊢
  exact h2

/-- Naturality of the second factor of the identification. -/
theorem eC2_natural (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((MonoidalCategory.tensorRight (Mp p)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (chMapZ f)) n ≫
      (HomologicalComplex.homologyMapIso (eC2 p Y) n).hom =
    (HomologicalComplex.homologyMapIso (eC2 p X) n).hom ≫
      HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
          ((MonoidalCategory.tensorRight (Mp p)).obj zZ)).map (sMap f)) n := by
  have hmap : ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj zZ).map (sMap f) = chMapZ f := rfl
  have h := NatTrans.naturality
    ((baseChangeNatIso (MonoidalCategory.tensorRight (Mp p)) zZ).hom) (sMap f)
  have h2 := congrArg (fun t => HomologicalComplex.homologyMap t n) h
  simp only [Functor.comp_map, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMapIso_hom, eC2, hmap] at h2 ⊢
  exact h2

/-- Naturality of the third factor of the identification. -/
theorem eC3_natural (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
          ((MonoidalCategory.tensorRight (Mp p)).obj zZ)).map (sMap f)) n ≫
      (HomologicalComplex.homologyMapIso (eC3 p Y) n).hom =
    (HomologicalComplex.homologyMapIso (eC3 p X) n).hom ≫
      HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (Mp p)).map (sMap f)) n := by
  have h := coeffIsoChain_natural (unitCoeffIso p) (sMap f)
  have h2 := congrArg (fun t => HomologicalComplex.homologyMap t n) h
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMapIso_hom,
    eC3] at h2 ⊢
  exact h2

/-- Naturality of the fourth factor of the identification. -/
theorem eC4_natural (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (Mp p)).map (sMap f)) n ≫
      (HomologicalComplex.homologyMapIso (eC4 p hp Y) n).hom =
    (HomologicalComplex.homologyMapIso (eC4 p hp X) n).hom ≫
      HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj ((Fp p).obj (M0 p))).map
          (sMap f)) n := by
  have h := coeffIsoChain_natural (coeffIsoMp p hp) (sMap f)
  have h2 := congrArg (fun t => HomologicalComplex.homologyMap t n) h
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMapIso_hom,
    eC4] at h2 ⊢
  exact h2

/-- Naturality of the fifth factor of the identification. -/
theorem eC5_natural (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj ((Fp p).obj (M0 p))).map
          (sMap f)) n ≫
      (HomologicalComplex.homologyMapIso (eC5 p Y) n).hom =
    (HomologicalComplex.homologyMapIso (eC5 p X) n).hom ≫
      HomologicalComplex.homologyMap
        (((Fp p).mapHomologicalComplex (ComplexShape.down ℕ)).map (chMapK p f)) n := by
  have hmap : ((SSet.chainComplexFunctor (ModuleCat (ZMod p))).obj (M0 p)).map (sMap f) =
      chMapK p f := rfl
  have h := NatTrans.naturality ((baseChangeNatIso (Fp p) (M0 p)).inv) (sMap f)
  have h2 := congrArg (fun t => HomologicalComplex.homologyMap t n) h
  simp only [Functor.comp_map, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMapIso_inv, eC5, hmap] at h2 ⊢
  exact h2

/-- Naturality of the sixth factor of the identification. -/
theorem eC6_natural (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((Fp p).mapHomologicalComplex (ComplexShape.down ℕ)).map (chMapK p f)) n ≫
      (eC6 p Y n).hom =
    (eC6 p X n).hom ≫
      (Fp p).map (HomologicalComplex.homologyMap (chMapK p f) n) :=
  fcHomologyIsoNatural (Fp p) ((Work.Pi6.EMZ.sing X).chainComplex (M0 p))
    ((Work.Pi6.EMZ.sing Y).chainComplex (M0 p)) (chMapK p f) n

/-- **Naturality of the identification, as an equation of morphisms.** -/
theorem eCIso_natural_mor (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)) n ≫
      (eCIso' p hp Y n).hom =
    (eCIso' p hp X n).hom ≫
      (Fp p).map (HomologicalComplex.homologyMap (chMapK p f) n) :=
  comp_six_aux (S1 := HomologicalComplex.homologyMapIso (eC1 p X) n)
    (S2 := HomologicalComplex.homologyMapIso (eC2 p X) n)
    (S3 := HomologicalComplex.homologyMapIso (eC3 p X) n)
    (S4 := HomologicalComplex.homologyMapIso (eC4 p hp X) n)
    (S5 := HomologicalComplex.homologyMapIso (eC5 p X) n) (S6 := eC6 p X n)
    (T1 := HomologicalComplex.homologyMapIso (eC1 p Y) n)
    (T2 := HomologicalComplex.homologyMapIso (eC2 p Y) n)
    (T3 := HomologicalComplex.homologyMapIso (eC3 p Y) n)
    (T4 := HomologicalComplex.homologyMapIso (eC4 p hp Y) n)
    (T5 := HomologicalComplex.homologyMapIso (eC5 p Y) n) (T6 := eC6 p Y n)
    (m1 := HomologicalComplex.homologyMap
      (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)) n)
    (m2 := HomologicalComplex.homologyMap
      (((MonoidalCategory.tensorRight (Mp p)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (chMapZ f)) n)
    (m3 := HomologicalComplex.homologyMap
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        ((MonoidalCategory.tensorRight (Mp p)).obj zZ)).map (sMap f)) n)
    (m4 := HomologicalComplex.homologyMap
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (Mp p)).map (sMap f)) n)
    (m5 := HomologicalComplex.homologyMap
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj ((Fp p).obj (M0 p))).map (sMap f)) n)
    (m6 := HomologicalComplex.homologyMap
      (((Fp p).mapHomologicalComplex (ComplexShape.down ℕ)).map (chMapK p f)) n)
    (m7 := (Fp p).map (HomologicalComplex.homologyMap (chMapK p f) n))
    (h1 := eC1_natural p f n) (h2 := eC2_natural p f n) (h3 := eC3_natural p f n)
    (h4 := eC4_natural p hp f n) (h5 := eC5_natural p f n) (h6 := eC6_natural p f n)

end Naturality

end

end Work.Pi6.BOCK
