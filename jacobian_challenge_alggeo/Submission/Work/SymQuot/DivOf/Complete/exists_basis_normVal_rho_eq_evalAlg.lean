import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.RhoData
import Submission.Work.SymQuot.NormPoint.MapT
import Submission.Work.SymQuot.NormPoint.normVal_mapT
import Submission.Work.SymQuot.DivOf.Complete.EBasis.tensSingle
import Submission.Work.SymQuot.DivOf.Complete.EBasis.exists_tensorQuotEquiv_bcSec
import Submission.Work.SymQuot.DivOf.Complete.divIdeal_map_bcSec_eq_prod_placeIdeal
import Submission.Work.SymQuot.DivOf.divMap_divOfChart
import Submission.Work.SymQuot.DivOf.Complete.exists_ptDiv_sum_of_div
import Submission.Work.SymQuot.DivOf.Complete.divisorOfIdeal_idealOfDiv
import Submission.Work.SymQuot.DivOf.CharIdealGenMapDefs
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_injective
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_prod_placeIdeal
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_map_bcSec
import Submission.Work.SymQuot.NormPoint.exists_flagBasis
import Submission.Work.SymQuot.NormPoint.normVal_eq_evalT
import Submission.Work.SymQuot.NormPoint.normVal_basis_indep
import Submission.Work.SymQuot.NormPoint.normVal_bcT
import Submission.Work.SymQuot.NormPoint.bcT_mem_symTensors
import Submission.Work.SpecLin.Alt.isLocalization_chartTensorSectionsMap
import Submission.Work.CurveBasics.Curve.BCSquare.SectionsTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open Work.CurveBasics
open Work.SymQuot.NormPoint
open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.DivOf.Complete

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ} [NeZero n]
  [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
  {L : Type u} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [IsAlgClosed L]
  {V : C.left.Opens} [Nonempty V]

theorem top_le_preimage_ptLeft (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n) :
    ⊤ ≤ (Work.SpecLin.ptLeft (y m)) ⁻¹ᵁ (C.bcOpens L V) := by
  intro z _
  show (Work.SpecLin.ptLeft (y m)).base z ∈ C.bcOpens L V
  have hsub : Subsingleton ↥(Spec ↧L) := inferInstance
  rw [Subsingleton.elim z (IsLocalRing.closedPoint L)]
  exact hplace m

theorem top_le_preimage_left (y : Fin n → Work.SpecLin.CurveFPt C L)
    (h : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n) (m : Fin n) :
    ⊤ ≤ (y m).left ⁻¹ᵁ V := by
  intro z _
  have hfac : Over.Hom.left (Limits.Pi.lift y) ≫
      Over.Hom.left (Work.SymQuot.proj C.toOver n m) = Over.Hom.left (y m) := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (Limits.Pi.lift_comp_π y m)
  have hz : (Limits.Pi.lift y).left z ∈ Work.SymQuot.piOpen C.toOver V n := h trivial
  have hz' : (Work.SymQuot.proj C.toOver n m).left ((Limits.Pi.lift y).left z) ∈ V :=
    Work.SymQuot.mem_piOpen.mp hz m
  have hcomp : (Work.SymQuot.proj C.toOver n m).left ((Limits.Pi.lift y).left z) =
      (y m).left z := by
    rw [← hfac, Scheme.Hom.comp_apply]
    rfl
  rwa [hcomp] at hz'
noncomputable def ev (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n) :
    Γ((C.baseChange L).left, C.bcOpens L V) →+* L :=
  ((Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom).comp
    ((Work.SpecLin.ptLeft (y m)).appLE (C.bcOpens L V) ⊤
      (top_le_preimage_ptLeft (C := C) (L := L) y hplace m)).hom

theorem ev_secConst (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n) (c : L) :
    ev (C := C) (L := L) (V := V) y hplace m (Work.SymQuot.DivOf.secConst C L V c) = c :=
  Work.SymQuot.DivOf.eval_sectionsAlgebraMap (D := C.baseChange L) (C.bcOpens L V)
    (Work.SpecLin.ptLeft (y m)) (top_le_preimage_ptLeft (C := C) (L := L) y hplace m)
    (Work.SpecLin.Points.ptLeft_comp_hom (C := C) (y m)) c

noncomputable def evAlg (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n) :
    Γ((C.baseChange L).left, C.bcOpens L V) →ₐ[L] L :=
  { toRingHom := ev (C := C) (L := L) (V := V) y hplace m
    commutes' := fun c => ev_secConst (C := C) (L := L) (V := V) y hplace m c }

@[simp]
theorem evAlg_apply (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n)
    (x : Γ((C.baseChange L).left, C.bcOpens L V)) :
    evAlg (C := C) (L := L) (V := V) y hplace m x = ev (C := C) (L := L) (V := V) y hplace m x :=
  rfl

/-- The kernel of the evaluation hom is the place ideal. -/
theorem ev_ker (hV : IsAffineOpen V) (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n) :
    RingHom.ker (ev (C := C) (L := L) (V := V) y hplace m) =
      Work.SymQuot.DivOf.placeIdeal (C.baseChange L) (C.bcOpens L V)
        (Work.SpecLin.ptPlace (y m)) (hplace m) := by
  have hW : IsAffineOpen (C.bcOpens L V) := BaseChange.isAffineOpen_bcOpens L V hV
  rw [Work.SymQuot.DivOf.placeIdeal_eq_primeIdealOf (C := C.baseChange L) hW
    (Work.SpecLin.ptPlace (y m)) (hplace m)]
  have hpt : (⟨(Work.SpecLin.ptLeft (y m)).base (IsLocalRing.closedPoint L),
      (top_le_preimage_ptLeft (C := C) (L := L) y hplace m) trivial⟩ : ↥(C.bcOpens L V)) =
      ⟨(Work.SpecLin.ptPlace (y m)).point, hplace m⟩ := Subtype.ext rfl
  rw [show hW.primeIdealOf ⟨(Work.SpecLin.ptPlace (y m)).point, hplace m⟩ =
      hW.primeIdealOf ⟨(Work.SpecLin.ptLeft (y m)).base (IsLocalRing.closedPoint L),
        (top_le_preimage_ptLeft (C := C) (L := L) y hplace m) trivial⟩ from
    congrArg hW.primeIdealOf hpt]
  ext a
  rw [RingHom.mem_ker]
  rw [Work.SymQuot.DivOf.mem_primeIdealOf_iff_appLE_GammaSpecIso_eq_zero
    (X := (C.baseChange L).left) (C.bcOpens L V) hW (Work.SpecLin.ptLeft (y m))
    (top_le_preimage_ptLeft (C := C) (L := L) y hplace m) a]
  constructor
  · intro h; exact h
  · intro h; exact h

/-- The value of `bcSec (secAlpha b)` is `ptVal` of `b`. -/
theorem ev_bcSec_secAlpha (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V)
    (h : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n) (m : Fin n)
    (b : Γ(C.left, V)) :
    ev (C := C) (L := L) (V := V) y hplace m
        (Work.SymQuot.DivOf.bcSec (C := C) F L V (Work.SymQuot.DivOf.secAlpha C F V b))
      = Work.SymQuot.DivOf.ptVal C V (y m) (top_le_preimage_left (C := C) y h m) b := by
  rw [Work.SymQuot.DivOf.bcSec_secAlpha]
  have hσ := top_le_preimage_ptLeft (C := C) (L := L) y hplace m
  have h1 : ev (C := C) (L := L) (V := V) y hplace m (Work.SymQuot.DivOf.secAlpha C L V b) =
      ((Work.SpecLin.ptLeft (y m)).appLE (C.bcOpens L V) ⊤ hσ ≫
        (Scheme.ΓSpecIso (CommRingCat.of L)).hom).hom (Work.SymQuot.DivOf.secAlpha C L V b) := rfl
  rw [h1, Work.SymQuot.DivOf.eval_secAlpha_eq_GammaSpecIso_apply (C := C) V (y m)
    (top_le_preimage_left (C := C) y h m) hσ b]
  rfl


/-- For an affine open `U ⊆ X` and `f : Spec R ⟶ X` whose image lies in `U`, the `Spec` of the
ring map obtained by pulling back sections along `f` and identifying `Γ(Spec R) ≅ R` is a
section of `f` along the canonical immersion `Spec Γ(X,U) ⟶ X`. -/
private theorem Spec_map_appLE_SpecIso_fromSpec {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : Spec R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ f ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso R).hom.hom.comp (f.appLE U ⊤ h).hom)) ≫
        hU.fromSpec = f := by
  have h1 : CommRingCat.ofHom ((Scheme.ΓSpecIso R).hom.hom.comp (f.appLE U ⊤ h).hom)
      = (f.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso R).hom := by
    rw [show (Scheme.ΓSpecIso R).hom.hom.comp (f.appLE U ⊤ h).hom
      = ((f.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso R).hom).hom from rfl, CommRingCat.ofHom_hom]
  rw [h1, Spec.map_comp, Category.assoc]
  rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU (isAffineOpen_top (Spec R)) h]
  rw [IsAffineOpen.fromSpec_top]
  rw [← Scheme.isoSpec_Spec_hom R]
  rw [Iso.hom_inv_id_assoc]

/-- **A point of the affine open `V ⊆ C` is determined by its value map.** -/
theorem ptOfAlgHom_eq_of_ptVal {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {V : C.left.Opens} (hV : IsAffineOpen V) {F : Type u} [Field F] [Algebra K F]
    (y : Work.SpecLin.RPt C.toOver F) (h : ⊤ ≤ y.left ⁻¹ᵁ V)
    (κ : Γ(C.left, V) →ₐ[K] F) (hκ : κ.toRingHom = Work.SymQuot.DivOf.ptVal C V y h) :
    Work.SymQuot.DivOf.ptOfAlgHom C hV κ = y := by
  apply Over.OverMorphism.ext
  have hspec := Spec_map_appLE_SpecIso_fromSpec (X := C.left) y.left hV h
  rw [show Work.SymQuot.DivOf.ptVal C V y h
      = (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (y.left.appLE V ⊤ h).hom from rfl] at hκ
  rw [← hκ] at hspec
  show Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ hV.fromSpec = y.left
  exact hspec

/-- The product of the kernels of the evaluation maps `evAlg y hplace m` on `Γ(C_L, V_L)`. -/
noncomputable def JJ (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) :
    Ideal Γ((C.baseChange L).left, C.bcOpens L V) :=
  ∏ m, RingHom.ker (evAlg (C := C) (L := L) (V := V) y hplace m)

theorem JJ_le_ker (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n) :
    JJ (C := C) (L := L) (V := V) y hplace ≤
      RingHom.ker (evAlg (C := C) (L := L) (V := V) y hplace m) := by
  rw [JJ, ← Finset.prod_erase_mul Finset.univ
    (fun k : Fin n => RingHom.ker (evAlg (C := C) (L := L) (V := V) y hplace k))
    (Finset.mem_univ m)]
  exact Ideal.mul_le_right

/-- The kernel of `evAlg y hplace m` is the maximal ideal of the point `ptPlace (y m)`. -/
theorem evAlg_ker_eq (hV : IsAffineOpen V) (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n) :
    RingHom.ker (evAlg (C := C) (L := L) (V := V) y hplace m) =
      Work.SymQuot.DivOf.placeIdeal (C.baseChange L) (C.bcOpens L V)
        (Work.SpecLin.ptPlace (y m)) (hplace m) :=
  ev_ker hV y hplace m

theorem evAlg_ker_ne_bot (hV : IsAffineOpen V) (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n) :
    RingHom.ker (evAlg (C := C) (L := L) (V := V) y hplace m) ≠ ⊥ := by
  haveI : Nonempty (C.bcOpens L V) := Curve.bcOpens_nonempty C L V
  haveI hDed : IsDedekindDomain Γ((C.baseChange L).left, C.bcOpens L V) :=
    Work.SymQuot.DivOf.isDedekindDomain_sections (BaseChange.isAffineOpen_bcOpens L V hV)
  rw [evAlg_ker_eq hV y hplace m]
  exact Work.SymQuot.DivOf.placeIdeal_ne_bot (BaseChange.isAffineOpen_bcOpens L V hV)
    (Work.SpecLin.ptPlace (y m)) (hplace m)

/-- The evaluation maps descend to the quotient by `JJ`. -/
noncomputable def psiBar (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n) :
    Γ((C.baseChange L).left, C.bcOpens L V) ⧸ JJ (C := C) (L := L) (V := V) y hplace →ₐ[L] L :=
  Ideal.Quotient.liftₐ (JJ (C := C) (L := L) (V := V) y hplace)
    (evAlg (C := C) (L := L) (V := V) y hplace m)
    (fun a ha => RingHom.mem_ker.mp (JJ_le_ker (C := C) (L := L) (V := V) y hplace m ha))

theorem psiBar_mk (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) (m : Fin n)
    (b : Γ((C.baseChange L).left, C.bcOpens L V)) :
    psiBar (C := C) (L := L) (V := V) y hplace m
        (Ideal.Quotient.mk (JJ (C := C) (L := L) (V := V) y hplace) b) =
      evAlg (C := C) (L := L) (V := V) y hplace m b := by
  rw [psiBar, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

/-- **A flag basis of `Γ(C_L,V_L) ⧸ JJ` adapted to the evaluation maps.** -/
theorem exists_flagBasis_evAlg (hV : IsAffineOpen V) (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) :
    ∃ u : Module.Basis (Fin n) L
        (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ JJ (C := C) (L := L) (V := V) y hplace),
      ∀ m (b : Γ((C.baseChange L).left, C.bcOpens L V)),
        Ideal.Quotient.mk (JJ (C := C) (L := L) (V := V) y hplace) b * u m
            - evAlg (C := C) (L := L) (V := V) y hplace m b • u m ∈
          Submodule.span L (u '' {k | m < k}) := by
  haveI : Nonempty (C.bcOpens L V) := Curve.bcOpens_nonempty C L V
  haveI hDed : IsDedekindDomain Γ((C.baseChange L).left, C.bcOpens L V) :=
    Work.SymQuot.DivOf.isDedekindDomain_sections
      (BaseChange.isAffineOpen_bcOpens L V hV)
  exact Work.SymQuot.NormPoint.exists_flagBasis
    (fun m : Fin n => evAlg (C := C) (L := L) (V := V) y hplace m)
    (fun m => evAlg_ker_ne_bot hV y hplace m)

/-- The quotient `Γ(C_L,V_L) ⧸ JJ` has `L`-dimension `n`. -/
theorem finrank_quot_evAlg (hV : IsAffineOpen V) (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) :
    Module.finrank L
        (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ JJ (C := C) (L := L) (V := V) y hplace) = n := by
  obtain ⟨u, -⟩ := exists_flagBasis_evAlg (C := C) (L := L) (V := V) hV y hplace
  rw [Module.finrank_eq_card_basis u, Fintype.card_fin]


/-- The defining formula of `kappa`. -/
theorem kappa_apply (hV : IsAffineOpen V)
    (I : Ideal Γ((C.baseChange F).left, C.bcOpens F V)) (m : Fin n) (b : Γ(C.left, V)) :
    kappa (C := C) (F := F) (n := n) V hV I m b =
      tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m
        (Ideal.Quotient.mk I (Work.SymQuot.DivOf.secAlpha C F V b)) := rfl

theorem top_le_preimage_RPt_map {S S' : Type u} [CommRing S] [Algebra K S] [CommRing S']
    [Algebra K S'] (f : S →ₐ[K] S') {W : C.left.Opens} (p : Work.SpecLin.RPt C.toOver S)
    (hp : ⊤ ≤ p.left ⁻¹ᵁ W) : ⊤ ≤ (Work.SpecLin.RPt.map f p).left ⁻¹ᵁ W := by
  intro z _
  exact hp trivial

theorem evalT_psi_mapT_bcT_kappa_apply (hV : IsAffineOpen V)
    {I : Ideal (Γ((C.baseChange F).left, C.bcOpens F V))}
    {J : Ideal (Γ((C.baseChange L).left, C.bcOpens L V))}
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V)
    (h : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    (ψ : Fin n → (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J) →ₐ[L] L)
    (hψ : ∀ m (b : Γ((C.baseChange L).left, C.bcOpens L V)),
      ψ m (Ideal.Quotient.mk J b) = evAlg (C := C) (L := L) (V := V) y hplace m b)
    (e : TensorProduct F L (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) ≃ₐ[L]
      (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J))
    (he : ∀ b : Γ((C.baseChange F).left, C.bcOpens F V),
      e ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk I b) = Ideal.Quotient.mk J
        (Work.SymQuot.DivOf.bcSec (C := C) F L V b))
    (m : Fin n) (b : Γ(C.left, V)) :
    evalT ψ (mapT e (bcT L (kappa (C := C) (F := F) (n := n) V hV I m b))) =
      Work.SymQuot.DivOf.ptVal C V (y m) (top_le_preimage_left (C := C) y h m) b := by
  rw [kappa_apply, bcT_tensSingle, mapT_tensSingle, evalT_tensSingle,
    he (Work.SymQuot.DivOf.secAlpha C F V b),
    hψ m (Work.SymQuot.DivOf.bcSec (C := C) F L V (Work.SymQuot.DivOf.secAlpha C F V b)),
    evAlg_apply]
  exact ev_bcSec_secAlpha (C := C) (F := F) (L := L) (V := V) y hplace h m b

/-- **The point defined by the composite value map is `y m`.** -/
theorem ptOfAlgHom_comp_kappa_eq_y (hV : IsAffineOpen V)
    {I : Ideal (Γ((C.baseChange F).left, C.bcOpens F V))}
    {J : Ideal (Γ((C.baseChange L).left, C.bcOpens L V))}
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V)
    (h : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    (ψ : Fin n → (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J) →ₐ[L] L)
    (hψ : ∀ m (b : Γ((C.baseChange L).left, C.bcOpens L V)),
      ψ m (Ideal.Quotient.mk J b) = evAlg (C := C) (L := L) (V := V) y hplace m b)
    (e : TensorProduct F L (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) ≃ₐ[L]
      (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J))
    (he : ∀ b : Γ((C.baseChange F).left, C.bcOpens F V),
      e ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk I b) = Ideal.Quotient.mk J
        (Work.SymQuot.DivOf.bcSec (C := C) F L V b))
    (m : Fin n) :
    Work.SymQuot.DivOf.ptOfAlgHom C hV
      (((evalT ψ).restrictScalars K).comp
        ((((mapT e).toAlgHom).restrictScalars K).comp
          ((((bcT (F := F) (Q := Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I)
              (n := n) L)).restrictScalars K).comp
            (kappa (C := C) (F := F) (n := n) V hV I m)))) = y m := by
  apply ptOfAlgHom_eq_of_ptVal hV (y m) (top_le_preimage_left (C := C) y h m)
  ext b
  exact evalT_psi_mapT_bcT_kappa_apply (C := C) (F := F) (L := L) (V := V)
    hV y hplace h ψ hψ e he m b


theorem algebraMap_normVal_eq_evalT (hV : IsAffineOpen V)
    {I : Ideal (Γ((C.baseChange F).left, C.bcOpens F V))}
    {J : Ideal (Γ((C.baseChange L).left, C.bcOpens L V))}
    (u : Module.Basis (Fin n) L (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J))
    (ψ : Fin n → (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J) →ₐ[L] L)
    (htri : ∀ m (b : Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J),
      b * u m - ψ m b • u m ∈ Submodule.span L (u '' {k | m < k}))
    (e : TensorProduct F L (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) ≃ₐ[L]
      (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J))
    (v : Module.Basis (Fin n) F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I))
    (a : ↥(Work.SymQuot.chartInvariants (C := C) (n := n)
      (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))) :
    algebraMap F L (normVal v (rho (C := C) (F := F) (n := n) V hV I ↑a)) =
      evalT ψ (mapT e (bcT L (rho (C := C) (F := F) (n := n) V hV I ↑a))) := by
  rw [← normVal_bcT L v (rho (C := C) (F := F) (n := n) V hV I ↑a)]
  have hsym : mapT e (bcT L (rho (C := C) (F := F) (n := n) V hV I ↑a)) ∈
      symTensors L (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J) n :=
    mapT_mem_symTensors e (bcT_mem_symTensors L
      (rho_mem_symTensors (C := C) (F := F) (n := n) V hV I a.2))
  calc normVal (Algebra.TensorProduct.basis L v) (bcT L (rho (C := C) (F := F) (n := n) V hV I ↑a))
      = normVal ((Algebra.TensorProduct.basis L v).map e.toLinearEquiv)
          (mapT e (bcT L (rho (C := C) (F := F) (n := n) V hV I ↑a))) :=
        (normVal_mapT e (Algebra.TensorProduct.basis L v)
          (bcT L (rho (C := C) (F := F) (n := n) V hV I ↑a))).symm
    _ = normVal u (mapT e (bcT L (rho (C := C) (F := F) (n := n) V hV I ↑a))) :=
        normVal_basis_indep _ _ hsym
    _ = evalT ψ (mapT e (bcT L (rho (C := C) (F := F) (n := n) V hV I ↑a))) :=
        normVal_eq_evalT u ψ htri _


theorem finrank_quot_eq_n (hV : IsAffineOpen V)
    {I : Ideal (Γ((C.baseChange F).left, C.bcOpens F V))}
    {J : Ideal (Γ((C.baseChange L).left, C.bcOpens L V))}
    (e : TensorProduct F L (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) ≃ₐ[L]
      (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J))
    (hJ : Module.finrank L (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J) = n) :
    Module.finrank F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) = n := by
  have h1 : Module.finrank L (TensorProduct F L (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I)) =
      Module.finrank F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) :=
    Module.finrank_baseChange (R := L) (S := F) (M' := Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I)
  have h2 : Module.finrank L (TensorProduct F L (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I)) =
      Module.finrank L (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J) :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  rw [← h1, h2, hJ]

theorem exists_basis_quot (hV : IsAffineOpen V)
    {I : Ideal (Γ((C.baseChange F).left, C.bcOpens F V))}
    {J : Ideal (Γ((C.baseChange L).left, C.bcOpens L V))}
    (e : TensorProduct F L (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) ≃ₐ[L]
      (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J))
    (hJ : Module.finrank L (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J) = n) :
    Nonempty (Module.Basis (Fin n) F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I)) := by
  have hfin := finrank_quot_eq_n (C := C) (F := F) (L := L) (V := V) hV e hJ
  haveI : Module.Finite F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) :=
    Module.finite_of_finrank_pos (by rw [hfin]; exact Nat.pos_of_ne_zero (NeZero.ne n))
  exact ⟨Module.finBasisOfFinrankEq F _ hfin⟩


theorem evalT_psi_mapT_bcT_rho_eq (hV : IsAffineOpen V)
    {I : Ideal (Γ((C.baseChange F).left, C.bcOpens F V))}
    {J : Ideal (Γ((C.baseChange L).left, C.bcOpens L V))}
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V)
    (h : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    (ψ : Fin n → (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J) →ₐ[L] L)
    (hψ : ∀ m (b : Γ((C.baseChange L).left, C.bcOpens L V)),
      ψ m (Ideal.Quotient.mk J b) = evAlg (C := C) (L := L) (V := V) y hplace m b)
    (e : TensorProduct F L (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) ≃ₐ[L]
      (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ J))
    (he : ∀ b : Γ((C.baseChange F).left, C.bcOpens F V),
      e ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk I b) = Ideal.Quotient.mk J
        (Work.SymQuot.DivOf.bcSec (C := C) F L V b))
    (a : ↥(Work.SymQuot.chartInvariants (C := C) (n := n)
      (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V))) :
    evalT ψ (mapT e (bcT L (rho (C := C) (F := F) (n := n) V hV I ↑a))) =
      evalAlg C V n y h ↑a := by
  classical
  set x : Fin n → Work.SpecLin.RPt C.toOver
      (Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n) :=
    fun m => Work.SymQuot.DivOf.ptOfAlgHom C hV
      (kappa (C := C) (F := F) (n := n) V hV I m) with hxdef
  have hxmem : ∀ m, ⊤ ≤ (x m).left ⁻¹ᵁ V :=
    fun m => ptOfAlgHom_mem (C := C) (V := V) hV
      (kappa (C := C) (F := F) (n := n) V hV I m)
  have hxlands : ⊤ ≤ (Limits.Pi.lift x).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n :=
    piOpen_landsIn (C := C) (n := n) x hxmem
  have hrho : rho (C := C) (F := F) (n := n) V hV I =
      evalAlg C V n x hxlands := rfl
  set g : Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n →ₐ[K] L :=
    ((evalT ψ).restrictScalars K).comp
      ((((mapT e).toAlgHom).restrictScalars K).comp
        (((bcT (F := F) (Q := Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I)
          (n := n) L)).restrictScalars K)) with hg
  set x' : Fin n → Work.SpecLin.RPt C.toOver L := fun m => Work.SpecLin.RPt.map g (x m) with hx'
  have hx'mem : ∀ m, ⊤ ≤ (x' m).left ⁻¹ᵁ V :=
    fun m => top_le_preimage_RPt_map g (x m) (hxmem m)
  have hx'lands : ⊤ ≤ (Limits.Pi.lift x').left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n :=
    piOpen_landsIn (C := C) (n := n) x' hx'mem
  have hcomp : g (evalAlg C V n x hxlands ↑a) = evalAlg C V n x' hx'lands ↑a :=
    congrArg (fun f => f ↑a) (evalAlg_comp (f := g) x hxlands hx'lands)
  have htuple : x' = y := by
    funext m
    simp only [hx', hxdef, Work.SymQuot.DivOf.Complete.RPt_map_ptOfAlgHom]
    apply ptOfAlgHom_eq_of_ptVal hV (y m) (top_le_preimage_left (C := C) y h m)
    ext b
    show g (kappa (C := C) (F := F) (n := n) V hV I m b) =
      Work.SymQuot.DivOf.ptVal C V (y m) (top_le_preimage_left (C := C) y h m) b
    exact evalT_psi_mapT_bcT_kappa_apply (C := C) (F := F) (L := L) (V := V)
      hV y hplace h ψ hψ e he m b
  show g (evalAlg C V n x hxlands ↑a) = evalAlg C V n y h ↑a
  rw [hcomp]
  exact congrArg (fun f => f ↑a) (evalAlg_congr htuple hx'lands h)


theorem map_bcSec_eq_JJ (hV : IsAffineOpen V)
    (D : Work.SpecLin.Dv C F) (hD : D.IsEffective)
    (hsupp : ∀ z ∈ D.support, z.point ∈ C.bcOpens F V)
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hy : Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) D = ∑ m, Work.SpecLin.ptDiv (y m))
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) :
    (divIdeal (C := C) (F := F) V hV D hsupp).map (Work.SymQuot.DivOf.bcSec F L V) =
      JJ (C := C) (L := L) (V := V) y hplace := by
  have hprodJ : (∏ m, Work.SymQuot.DivOf.placeIdeal (C.baseChange L) (C.bcOpens L V)
        (Work.SpecLin.ptPlace (y m)) (hplace m)) =
      JJ (C := C) (L := L) (V := V) y hplace := by
    rw [JJ]
    exact Finset.prod_congr rfl (fun m _ => (evAlg_ker_eq hV y hplace m).symm)
  exact (divIdeal_map_bcSec_eq_prod_placeIdeal (C := C) (F := F) (L := L) (V := V)
    D hD hV hsupp y hy hplace).trans hprodJ

theorem exists_algEquiv_tensor_JJ (hV : IsAffineOpen V)
    (D : Work.SpecLin.Dv C F) (hD : D.IsEffective)
    (hsupp : ∀ z ∈ D.support, z.point ∈ C.bcOpens F V)
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hy : Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) D = ∑ m, Work.SpecLin.ptDiv (y m))
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) :
    ∃ e : TensorProduct F L
        (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ divIdeal (C := C) (F := F) V hV D hsupp) ≃ₐ[L]
        (Γ((C.baseChange L).left, C.bcOpens L V) ⧸ JJ (C := C) (L := L) (V := V) y hplace),
      ∀ b : Γ((C.baseChange F).left, C.bcOpens F V),
        e ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk (divIdeal (C := C) (F := F) V hV D hsupp) b) =
          Ideal.Quotient.mk (JJ (C := C) (L := L) (V := V) y hplace)
            (Work.SymQuot.DivOf.bcSec (C := C) F L V b) := by
  obtain ⟨e₀, he₀⟩ := Work.SymQuot.DivOf.Complete.EBasis.exists_tensorQuotEquiv_bcSec
    (C := C) (F := F) (L := L) hV (divIdeal (C := C) (F := F) V hV D hsupp)
  have hIJ := map_bcSec_eq_JJ (C := C) (F := F) (L := L) (V := V) hV D hD hsupp y hy hplace
  have hJI : JJ (C := C) (L := L) (V := V) y hplace =
      (divIdeal (C := C) (F := F) V hV D hsupp).map
        (Work.SymQuot.DivOf.bcSec F L V) := hIJ.symm
  refine ⟨e₀.trans (Ideal.quotientEquivAlg
    ((divIdeal (C := C) (F := F) V hV D hsupp).map (Work.SymQuot.DivOf.bcSec F L V))
    (JJ (C := C) (L := L) (V := V) y hplace)
    AlgEquiv.refl ?_), ?_⟩
  · simpa [Ideal.map_id] using hJI
  · intro b
    rw [AlgEquiv.trans_apply, he₀ b, Ideal.quotientEquivAlg_mk]
    rfl


open CategoryTheory Limits AlgebraicGeometry in

theorem exists_basis_normVal_rho_eq_evalAlg {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} {n : ℕ} [NeZero n] [Work.SymQuot.CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F]
    {L : Type u} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [IsAlgClosed L]
    (D : Work.SpecLin.Dv C F) (hD : D.IsEffective) (hdeg : (C.baseChange F).deg D = n)
    {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V)
    (hsupp : ∀ z ∈ D.support, z.point ∈ C.bcOpens F V)
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hy : Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) D =
      ∑ m, Work.SpecLin.ptDiv (y m))
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V)
    (h : ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n) :
    ∃ v : Module.Basis (Fin n) F
        (Γ((C.baseChange F).left, C.bcOpens F V) ⧸
          Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp),
      ∀ a : ↥(Work.SymQuot.chartInvariants (C := C) (n := n)
          (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V)),
        algebraMap F L
          (Work.SymQuot.DivOf.Complete.phiD (C := C) (F := F) (n := n) V hV
            (Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp)
            v a)
        = Work.SymQuot.DivOf.evalAlg C V n y h ↑a := by
  classical
  obtain ⟨e, he⟩ := exists_algEquiv_tensor_JJ (C := C) (F := F) (L := L) (V := V)
    hV D hD hsupp y hy hplace
  obtain ⟨u, hu⟩ := exists_flagBasis_evAlg (C := C) (L := L) (V := V) hV y hplace
  have htri : ∀ m (b : Γ((C.baseChange L).left, C.bcOpens L V) ⧸
      JJ (C := C) (L := L) (V := V) y hplace),
      b * u m - psiBar (C := C) (L := L) (V := V) y hplace m b • u m ∈
        Submodule.span L (u '' {k | m < k}) := by
    intro m b
    obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [psiBar_mk]
    exact hu m b₀
  have hψ : ∀ m (b : Γ((C.baseChange L).left, C.bcOpens L V)),
      psiBar (C := C) (L := L) (V := V) y hplace m
        (Ideal.Quotient.mk (JJ (C := C) (L := L) (V := V) y hplace) b) =
      evAlg (C := C) (L := L) (V := V) y hplace m b :=
    fun m b => psiBar_mk (C := C) (L := L) (V := V) y hplace m b
  obtain ⟨v⟩ := exists_basis_quot (C := C) (F := F) (L := L) (V := V) hV e
    (finrank_quot_evAlg (C := C) (L := L) (V := V) hV y hplace)
  refine ⟨v, fun a => ?_⟩
  rw [phiD_apply]
  rw [algebraMap_normVal_eq_evalT (C := C) (F := F) (L := L) (V := V) hV u
    (psiBar (C := C) (L := L) (V := V) y hplace) htri e v a]
  exact evalT_psi_mapT_bcT_rho_eq (C := C) (F := F) (L := L) (V := V) hV y hplace h
    (psiBar (C := C) (L := L) (V := V) y hplace) hψ e he a


end Work.SymQuot.DivOf.Complete
