import Mathlib
import Submission.Work.SymQuot.DivOf.powMapAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

/-- **Membership in the place ideal is the vanishing of the value at the point.**

Let `U ⊆ X` be an affine open of a scheme, `σ : Spec F ⟶ X` a morphism whose (single) image
point lies in `U`, and `z = σ (closed point F)`.  Then a section `a ∈ Γ(X,U)` lies in the prime
ideal `𝔪_z` of `U` if and only if its pullback `σ^* a`, viewed in `F` through `Γ(Spec F) ≅ F`,
is zero. -/
theorem mem_primeIdealOf_iff_appLE_GammaSpecIso_eq_zero {F : Type u} [Field F] {X : Scheme.{u}}
    (U : X.Opens) (hU : IsAffineOpen U) (σ : Spec (CommRingCat.of F) ⟶ X)
    (hσ : ⊤ ≤ σ ⁻¹ᵁ U) (a : Γ(X, U)) :
    a ∈ (hU.primeIdealOf ⟨σ.base (IsLocalRing.closedPoint F), hσ trivial⟩).asIdeal ↔
      (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom a = 0 := by
  have hmap : Spec.map (CommRingCat.ofHom
        (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom)
      = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of F)).hom) ≫ Spec.map (σ.appLE U ⊤ hσ) := by
    rw [CommRingCat.ofHom_hom
      (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom), Spec.map_comp]
  have hcancel : Spec.map ((Scheme.ΓSpecIso (CommRingCat.of F)).hom) ≫
      (isAffineOpen_top (Spec (CommRingCat.of F))).fromSpec = 𝟙 (Spec (CommRingCat.of F)) := by
    rw [IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom, Iso.hom_inv_id]
  have hspec : Spec.map (σ.appLE U ⊤ hσ) ≫ hU.fromSpec
      = (isAffineOpen_top (Spec (CommRingCat.of F))).fromSpec ≫ σ :=
    IsAffineOpen.SpecMap_appLE_fromSpec σ hU (isAffineOpen_top _) hσ
  have hfrom : σ.base (IsLocalRing.closedPoint F)
      = hU.fromSpec (Spec.map (CommRingCat.ofHom
          (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom)
          (IsLocalRing.closedPoint F)) := by
    have h : Spec.map (CommRingCat.ofHom
          (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom) ≫ hU.fromSpec = σ := by
      rw [hmap, Category.assoc, hspec, ← Category.assoc, hcancel, Category.id_comp]
    calc σ.base (IsLocalRing.closedPoint F)
        = ((Spec.map (CommRingCat.ofHom
            (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom) ≫ hU.fromSpec)).base
            (IsLocalRing.closedPoint F) := by rw [h]
      _ = hU.fromSpec (Spec.map (CommRingCat.ofHom
            (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom)
            (IsLocalRing.closedPoint F)) := rfl
  have key := Work.SpecLin.Core.primeIdealOf_eq_of_fromSpec_eq hU
      (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom
      (IsLocalRing.closedPoint F) (hσ trivial) hfrom
  rw [key, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      Work.SpecLin.Core.closedPoint_asIdeal_eq_bot, Ideal.mem_bot]

/-- **The value of the constant section `s c` at a point of the fibre of `Spec F`.**

If `σ` is a section of the structure morphism `D ⟶ Spec F` (i.e. `σ ≫ D.hom = 𝟙`), then
pulling back the structure-map image `s c ∈ Γ(D,U)` of `c ∈ F` along `σ` (and reading the
result in `F` through `Γ(Spec F) ≅ F`) returns `c`. -/
theorem eval_sectionsAlgebraMap {F : Type u} [Field F] {D : Curve F} (U : D.left.Opens)
    (σ : Spec (CommRingCat.of F) ⟶ D.left) (hσ : ⊤ ≤ σ ⁻¹ᵁ U)
    (hsec : σ ≫ D.hom = 𝟙 (Spec (CommRingCat.of F))) (c : F) :
    (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom
      (sectionsAlgebraMap D U c) = c := by
  have hrestr : D.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ σ.appLE U ⊤ hσ
      = Scheme.Hom.appTop σ := by
    rw [Scheme.Hom.map_appLE]
    rw [Work.SymQuot.appLE_congr_le σ _ (le_rfl : ⊤ ≤ σ ⁻¹ᵁ ⊤)]
    exact Scheme.Hom.appLE_eq_app σ
  have hcomp2 : Scheme.Hom.appTop D.hom ≫ Scheme.Hom.appTop σ
      = 𝟙 Γ(Spec (CommRingCat.of F), ⊤) := by
    rw [← Scheme.Hom.comp_appTop σ D.hom, hsec]
    exact Scheme.Hom.id_app (⊤ : (Spec (CommRingCat.of F)).Opens)
  have hexp : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ Scheme.Hom.appTop D.hom
        ≫ D.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        ≫ σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      = 𝟙 (CommRingCat.of F) := by
    rw [← Category.assoc (D.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) (σ.appLE U ⊤ hσ)
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom]
    rw [hrestr]
    rw [← Category.assoc (Scheme.Hom.appTop D.hom) (Scheme.Hom.appTop σ)
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom]
    rw [hcomp2, Category.id_comp, Iso.inv_hom_id]
  rw [show sectionsAlgebraMap D U = ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
      D.hom.appTop ≫ D.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom from by
      rw [sectionsAlgebraMap]]
  calc (σ.appLE U ⊤ hσ ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom
        (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ D.hom.appTop ≫
          D.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom c)
      = ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ D.hom.appTop ≫
          D.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ σ.appLE U ⊤ hσ ≫
          (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom c := by
        repeat rw [CommRingCat.comp_apply]
    _ = c := by rw [hexp]; rfl

/-- `valAt` is the pullback of a chart section along the `F`-point `x m`. -/
lemma valAt_eq_GammaSpecIso_apply {K : Type u} [Field K] {C : Curve K} {n : ℕ} [NeZero n]
    [CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Sym C n) F} (d : ChartPt C n p) (x : Fin n → Work.SpecLin.CurveFPt C F)
    (h : LandsInChart d x) (m : Fin n)
    (hsle : ⊤ ≤ Over.Hom.left (x m) ⁻¹ᵁ d.V)
    (b : C.left.presheaf.obj (Opposite.op d.V)) :
    valAt d x h m b = (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      ((Scheme.Hom.appLE (Over.Hom.left (x m)) d.V ⊤ hsle).hom b) := by
  have hfac : Over.Hom.left (Limits.Pi.lift x) ≫ Over.Hom.left (proj C.toOver n m)
      = Over.Hom.left (x m) := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (Limits.Pi.lift_comp_π x m)
  have hcomp : Scheme.Hom.appLE (Over.Hom.left (proj C.toOver n m)) d.V (piOpen C.toOver d.V n)
        (by intro y hy; rw [Work.SymQuot.mem_piOpen] at hy; exact hy m)
      ≫ Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h
      = Scheme.Hom.appLE (Over.Hom.left (x m)) d.V ⊤ hsle := by
    calc Scheme.Hom.appLE (Over.Hom.left (proj C.toOver n m)) d.V (piOpen C.toOver d.V n) _
          ≫ Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h
        = Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x) ≫ Over.Hom.left (proj C.toOver n m))
            d.V ⊤ _ :=
          Scheme.Hom.appLE_comp_appLE (Over.Hom.left (Limits.Pi.lift x))
            (Over.Hom.left (proj C.toOver n m)) d.V d.openOf ⊤ _ h
      _ = Scheme.Hom.appLE (Over.Hom.left (x m)) d.V ⊤ hsle :=
          Work.SymQuot.appLE_congr_hom hfac _ _
  rw [valAt_apply, Work.SymQuot.DivOf.coordPullbackAt_apply]
  rw [show (d.evalMap x h) = ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom).comp
      ((Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h).hom) from rfl]
  rw [RingHom.comp_apply]
  congr 1
  calc (Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h).hom
        ((Scheme.Hom.appLE (Over.Hom.left (proj C.toOver n m)) d.V (piOpen C.toOver d.V n) _).hom b)
      = ((Scheme.Hom.appLE (Over.Hom.left (proj C.toOver n m)) d.V (piOpen C.toOver d.V n) _
          ≫ Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h).hom) b :=
        (CommRingCat.comp_apply _ _ b).symm
    _ = (Scheme.Hom.appLE (Over.Hom.left (x m)) d.V ⊤ hsle).hom b := by rw [hcomp]

/-- Pulling back `secAlpha b` along the section `ptLeft x` gives the value of `b` at `x`. -/
lemma eval_secAlpha_eq_GammaSpecIso_apply {K : Type u} [Field K] {C : Curve K} {F : Type u}
    [Field F] [Algebra K F] (W : C.left.Opens) (x : Work.SpecLin.CurveFPt C F)
    (hsle : ⊤ ≤ Over.Hom.left x ⁻¹ᵁ W)
    (hσ : ⊤ ≤ Work.SpecLin.ptLeft x ⁻¹ᵁ C.bcOpens F W)
    (b : C.left.presheaf.obj (Opposite.op W)) :
    ((Work.SpecLin.ptLeft x).appLE (C.bcOpens F W) ⊤ hσ ≫
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom (secAlpha C F W b)
      = (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
          ((Scheme.Hom.appLE (Over.Hom.left x) W ⊤ hsle).hom b) := by
  have hcomp : (C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl
      ≫ (Work.SpecLin.ptLeft x).appLE (C.bcOpens F W) ⊤ hσ
      = Scheme.Hom.appLE (Over.Hom.left x) W ⊤ hsle := by
    calc (C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl
          ≫ (Work.SpecLin.ptLeft x).appLE (C.bcOpens F W) ⊤ hσ
        = Scheme.Hom.appLE ((Work.SpecLin.ptLeft x) ≫ C.baseChangeFst F) W ⊤ _ :=
          Scheme.Hom.appLE_comp_appLE (Work.SpecLin.ptLeft x) (C.baseChangeFst F) W
            (C.bcOpens F W) ⊤ le_rfl hσ
      _ = Scheme.Hom.appLE (Over.Hom.left x) W ⊤ hsle :=
          Work.SymQuot.appLE_congr_hom (Work.SpecLin.ptLeft_fst x) _ _
  rw [show secAlpha C F W b = ((C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl).hom b from rfl]
  rw [CommRingCat.comp_apply]
  congr 1
  calc ((Work.SpecLin.ptLeft x).appLE (C.bcOpens F W) ⊤ hσ).hom
        (((C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl).hom b)
      = (((C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl) ≫
          (Work.SpecLin.ptLeft x).appLE (C.bcOpens F W) ⊤ hσ).hom b :=
        (CommRingCat.comp_apply _ _ b).symm
    _ = (Scheme.Hom.appLE (Over.Hom.left x) W ⊤ hsle).hom b :=
        congrArg (fun (m : Γ(C.left, W) ⟶ Γ(Spec (CommRingCat.of F), ⊤)) => m.hom b) hcomp

theorem mem_placeIdeal_valAt_sub {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : Work.SymQuot.DivOf.ChartPt C n p) (x : Fin n → Work.SpecLin.CurveFPt C F)
    (h : Work.SymQuot.DivOf.LandsInChart d x) (m : Fin n)
    (hs : Set.range (x m).left.base ⊆ (d.V : Set C.left))
    (hmem : Work.SpecLin.ptToPoint (x m) ∈ C.bcOpens F d.V)
    (b : C.left.presheaf.obj (Opposite.op d.V)) :
    Work.SymQuot.DivOf.secAlpha C F d.V b -
        Work.SymQuot.DivOf.secConst C F d.V (Work.SymQuot.DivOf.valAt d x h m b) ∈
      Work.SymQuot.DivOf.placeIdeal (C.baseChange F) (C.bcOpens F d.V)
        ⟨Work.SpecLin.ptToPoint (x m), Work.SpecLin.Points.ptToPoint_isClosed (x m)⟩ hmem := by
  classical
  haveI hUne : Nonempty (C.bcOpens F d.V) := ⟨⟨Work.SpecLin.ptToPoint (x m), hmem⟩⟩
  haveI hsub : Subsingleton ↥(Spec (CommRingCat.of F)) := inferInstance
  have hsle : ⊤ ≤ Over.Hom.left (x m) ⁻¹ᵁ d.V := by
    intro y _
    exact hs ⟨y, rfl⟩
  have hσ : ⊤ ≤ Work.SpecLin.ptLeft (x m) ⁻¹ᵁ C.bcOpens F d.V := by
    intro y hy
    rw [show y = IsLocalRing.closedPoint F from Subsingleton.elim _ _]
    exact hmem
  have hpt_eq : (⟨Work.SpecLin.ptToPoint (x m), hmem⟩ : ↥(C.bcOpens F d.V)) =
      ⟨(Work.SpecLin.ptLeft (x m)) (IsLocalRing.closedPoint F), hσ trivial⟩ := Subtype.ext rfl
  rw [Work.SymQuot.DivOf.placeIdeal_eq_primeIdealOf
      (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F d.V d.isAffineOpen_V) _ hmem, hpt_eq]
  rw [mem_primeIdealOf_iff_appLE_GammaSpecIso_eq_zero]
  have h1 : ((Work.SpecLin.ptLeft (x m)).appLE (C.bcOpens F d.V) ⊤ hσ ≫
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom (secAlpha C F d.V b)
      = valAt d x h m b :=
    (eval_secAlpha_eq_GammaSpecIso_apply d.V (x m) hsle hσ b).trans
      (valAt_eq_GammaSpecIso_apply d x h m hsle b).symm
  have h2 : ((Work.SpecLin.ptLeft (x m)).appLE (C.bcOpens F d.V) ⊤ hσ ≫
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom
          (secConst C F d.V (valAt d x h m b)) = valAt d x h m b :=
    eval_sectionsAlgebraMap (C.bcOpens F d.V) (Work.SpecLin.ptLeft (x m)) hσ
      (Work.SpecLin.Points.ptLeft_comp_hom (x m)) (valAt d x h m b)
  rw [map_sub, h1, h2, sub_self]

end Work.SymQuot.DivOf
