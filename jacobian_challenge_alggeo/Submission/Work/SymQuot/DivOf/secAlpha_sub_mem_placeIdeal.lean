import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.SymQuot.DivOf.mem_placeIdeal_valAt_sub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
namespace Work.SymQuot.DivOf
open Work.CurveBasics

/-- **The value of a chart section at a lifted point, as a pullback.**  For a chart `d` of a
point of `Symⁿ C`, a lift `x` over a field extension `F''` and the `m`-th point `x m` (which
lands in `d.V`), the value `valAtLift d x h m b` of a chart section `b` at `x m` is the
pullback of `b` along `x m`, read in `F''` through `Γ(Spec F'') ≅ F''`.

This is the `F''`-version of `valAt_eq_GammaSpecIso_apply`; its proof only uses that the lift
`Π_m x_m` lands in `d.openOf = Vⁿ`. -/
lemma valAtLift_eq_GammaSpecIso_apply {K : Type u} [Field K] {C : Curve K} {n : ℕ} [NeZero n]
    [CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Sym C n) F} (d : ChartPt C n p)
    {F'' : Type u} [Field F''] [Algebra K F'']
    (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (h : (⊤ : (Work.SpecLin.specOf (K := K) F'').left.Opens) ≤
      ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F'' ⟶
        Work.SymQuot.prod C.toOver n)).left ⁻¹ᵁ d.openOf)
    (m : Fin n)
    (hsle : ⊤ ≤ Over.Hom.left (x m) ⁻¹ᵁ d.V)
    (b : C.left.presheaf.obj (Opposite.op d.V)) :
    valAtLift d x h m b = (Scheme.ΓSpecIso (CommRingCat.of F'')).hom.hom
      ((Scheme.Hom.appLE (Over.Hom.left (x m)) d.V ⊤ hsle).hom b) := by
  have hfac : Over.Hom.left (Limits.Pi.lift x) ≫
      Over.Hom.left (Work.SymQuot.proj C.toOver n m) = Over.Hom.left (x m) := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (Limits.Pi.lift_comp_π x m)
  have hcomp : Scheme.Hom.appLE (Over.Hom.left (Work.SymQuot.proj C.toOver n m)) d.V
        (Work.SymQuot.piOpen C.toOver d.V n)
        (by intro y hy; rw [Work.SymQuot.mem_piOpen] at hy; exact hy m)
      ≫ Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h
      = Scheme.Hom.appLE (Over.Hom.left (x m)) d.V ⊤ hsle := by
    calc Scheme.Hom.appLE (Over.Hom.left (Work.SymQuot.proj C.toOver n m)) d.V
            (Work.SymQuot.piOpen C.toOver d.V n) _
          ≫ Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h
        = Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)
            ≫ Over.Hom.left (Work.SymQuot.proj C.toOver n m)) d.V ⊤ _ :=
          Scheme.Hom.appLE_comp_appLE (Over.Hom.left (Limits.Pi.lift x))
            (Over.Hom.left (Work.SymQuot.proj C.toOver n m)) d.V d.openOf ⊤ _ h
      _ = Scheme.Hom.appLE (Over.Hom.left (x m)) d.V ⊤ hsle :=
          Work.SymQuot.appLE_congr_hom hfac _ _
  rw [Work.SymQuot.DivOf.valAtLift_apply, Work.SymQuot.DivOf.coordPullbackAt_apply]
  rw [show (d.evalMap x h) = ((Scheme.ΓSpecIso (CommRingCat.of F'')).hom.hom).comp
      ((Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h).hom) from rfl]
  rw [RingHom.comp_apply]
  congr 1
  calc (Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h).hom
        ((Scheme.Hom.appLE (Over.Hom.left (Work.SymQuot.proj C.toOver n m)) d.V
          (Work.SymQuot.piOpen C.toOver d.V n) _).hom b)
      = ((Scheme.Hom.appLE (Over.Hom.left (Work.SymQuot.proj C.toOver n m)) d.V
          (Work.SymQuot.piOpen C.toOver d.V n) _
          ≫ Scheme.Hom.appLE (Over.Hom.left (Limits.Pi.lift x)) d.openOf ⊤ h).hom) b :=
        (CommRingCat.comp_apply _ _ b).symm
    _ = (Scheme.Hom.appLE (Over.Hom.left (x m)) d.V ⊤ hsle).hom b := by rw [hcomp]

theorem secAlpha_sub_mem_placeIdeal {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) {F'' : Type u} [Field F''] [Algebra K F'']
    (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (h : (⊤ : (Work.SpecLin.specOf (K := K) F'').left.Opens) ≤
      ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F'' ⟶
        Work.SymQuot.prod C.toOver n)).left ⁻¹ᵁ d.openOf)
    (hmem : ∀ m, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' d.V)
    (m : Fin n) (b : C.left.presheaf.obj (Opposite.op d.V)) :
    secAlpha C F'' d.V b - secConst C F'' d.V (valAtLift d x h m b) ∈
      placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) (Work.SpecLin.ptPlace (x m)) (hmem m) := by
  classical
  haveI hUne : Nonempty (C.bcOpens F'' d.V) := ⟨⟨(Work.SpecLin.ptPlace (x m)).point, hmem m⟩⟩
  haveI hsub : Subsingleton ↥(Work.SpecLin.specOf (K := K) F'').left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of F'')))
  have hsle : ⊤ ≤ Over.Hom.left (x m) ⁻¹ᵁ d.V := by
    intro z _
    have hfac : Over.Hom.left (Limits.Pi.lift x) ≫
        Over.Hom.left (Work.SymQuot.proj C.toOver n m) = Over.Hom.left (x m) := by
      simpa only [Over.comp_left] using congrArg Over.Hom.left (Limits.Pi.lift_comp_π x m)
    have hz : (Limits.Pi.lift x).left z ∈ d.openOf := h trivial
    have hz' : (Work.SymQuot.proj C.toOver n m).left ((Limits.Pi.lift x).left z) ∈ d.V :=
      Work.SymQuot.mem_piOpen.mp hz m
    have hcomp : (Work.SymQuot.proj C.toOver n m).left ((Limits.Pi.lift x).left z) =
        (x m).left z := by
      rw [← hfac, Scheme.Hom.comp_apply]
      rfl
    rwa [hcomp] at hz'
  have hσ : ⊤ ≤ Work.SpecLin.ptLeft (x m) ⁻¹ᵁ C.bcOpens F'' d.V := by
    intro y hy
    rw [show y = IsLocalRing.closedPoint F'' from Subsingleton.elim _ _]
    exact hmem m
  have hpt_eq : (⟨(Work.SpecLin.ptPlace (x m)).point, hmem m⟩ : ↥(C.bcOpens F'' d.V)) =
      ⟨(Work.SpecLin.ptLeft (x m)) (IsLocalRing.closedPoint F''), hσ trivial⟩ :=
    Subtype.ext rfl
  rw [placeIdeal_eq_primeIdealOf
      (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F'' d.V d.isAffineOpen_V)
      (Work.SpecLin.ptPlace (x m)) (hmem m), hpt_eq]
  rw [mem_primeIdealOf_iff_appLE_GammaSpecIso_eq_zero]
  have h1 : ((Work.SpecLin.ptLeft (x m)).appLE (C.bcOpens F'' d.V) ⊤ hσ ≫
        (Scheme.ΓSpecIso (CommRingCat.of F'')).hom).hom (secAlpha C F'' d.V b)
      = valAtLift d x h m b :=
    (eval_secAlpha_eq_GammaSpecIso_apply d.V (x m) hsle hσ b).trans
      (valAtLift_eq_GammaSpecIso_apply d x h m hsle b).symm
  have h2 : ((Work.SpecLin.ptLeft (x m)).appLE (C.bcOpens F'' d.V) ⊤ hσ ≫
        (Scheme.ΓSpecIso (CommRingCat.of F'')).hom).hom
          (secConst C F'' d.V (valAtLift d x h m b)) = valAtLift d x h m b :=
    eval_sectionsAlgebraMap (C.bcOpens F'' d.V) (Work.SpecLin.ptLeft (x m)) hσ
      (Work.SpecLin.Points.ptLeft_comp_hom (x m)) (valAtLift d x h m b)
  rw [map_sub, h1, h2, sub_self]

end Work.SymQuot.DivOf
