import Mathlib
import Submission.Work.Thom.localThomUnionAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Gluing the cup map over a two-piece cover

`Work.Thom.luThomGen` is the Mayer--Vietoris step of the transgression/Thom-isomorphism argument
in the generality of an arbitrary continuous map `π : Y → X` and an arbitrary set `A ⊆ Y`:

if `U, V ⊆ X` is an open cover, `c ∈ H^n(Y,A)` restricts to classes `cU`, `cV`, `cUV` over `U`, `V`
and the overlap for which the cup maps `x ↦ π^*(x) ⌣ c` are bijective, and the overlap's
`(n-1)`-st relative cohomology vanishes, then the cup map with `c` itself is bijective.

The proof is the five lemma for the two Mayer--Vietoris long exact sequences (of the cover `(U,V)`
of `X` with trivial coefficients, and of the preimage cover `(π⁻¹U, π⁻¹V)` of the pair `(Y,A)`),
the three ladder squares being the naturality of the cup product with respect to restriction, and
the naturality of the connecting homomorphism (`Work.Thom.transgressionNatural` together with
`Work.Thom.honestDelta_mixedCup`).
-/

open Work.TangentClasses
open CategoryTheory CategoryTheory.Limits

namespace Work.Thom

noncomputable section

/-! ## Auxiliary: equal maps induce the same pullback on cohomology -/

/-- Equal continuous maps induce the same pullback on singular cohomology. -/
theorem luCohMap_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f = g) (k : ℕ) : CohMap f ℤ k = CohMap g ℤ k := by
  subst h; rfl

/-! ## The global cup map and its piecewise versions -/

/-- The global cup map `x ↦ π^*(x) ⌣ c`, from the absolute cohomology of the base to the relative
cohomology of the pair `(Y,A)`. -/
noncomputable def luTM {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A) (k : ℕ) :
    Work.Cohomology.pdCoh (TopCat.of X) (∅ : Set X) k ⟶
      Work.Cohomology.pdCoh (TopCat.of Y) A (k + n) :=
  (pdCohIso X k).hom ≫ ModuleCat.ofHom
    (((LinearMap.applyₗ c).comp (mixedCupC ℤ A k n)).comp (CohMap π ℤ k).hom)

/-- The cup map over a piece `P` of the base. -/
noncomputable def luTU {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) {P : Set X}
    (cP : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' P) n) (k : ℕ) :
    Work.Cohomology.pdCohSub (TopCat.of X) (∅ : Set X) P k ⟶
      Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' P) (k + n) :=
  (pdCohIso ↥P k).hom ≫ ModuleCat.ofHom (Work.Cohomology.luCupMap π A n cP k)

/-- The cup map over a cover `{U,V}` of the base, on the biproduct of the two pieces. -/
noncomputable def luTP {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) {U V : Set X}
    (cU : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U) n)
    (cV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' V) n) (k : ℕ) :
    Work.Cohomology.pdCohBiprod (TopCat.of X) (∅ : Set X) U V k ⟶
      Work.Cohomology.pdCohBiprod (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) (k + n) :=
  biprod.map (luTU π A n cU k) (luTU π A n cV k)

/-- The cup map over the overlap of the cover, on the base cohomology of the overlap. -/
noncomputable def luCupMapOvl {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) {U V : Set X}
    (cUV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n) (k : ℕ) :
    Coh ℤ k ↥(U ∩ V) →ₗ[ℤ]
      Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) (k + n) :=
  ((LinearMap.applyₗ cUV).comp
      (mixedCupC ℤ (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V)) k n)).comp
    (CohMap (fPieceProj π U V) ℤ k).hom

/-- The cup map over the overlap of the cover, as a morphism. -/
noncomputable def luTQ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) {U V : Set X}
    (cUV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n) (k : ℕ) :
    Work.Cohomology.pdCohSub (TopCat.of X) (∅ : Set X) (U ∩ V) k ⟶
      Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) (k + n) :=
  (pdCohIso ↥(U ∩ V) k).hom ≫ ModuleCat.ofHom (luCupMapOvl π A n cUV k)

/-- The connecting homomorphism of the Mayer--Vietoris sequence of the preimage cover, with its
degree shifted to `(k+1)+n`. -/
noncomputable def luDelta2 {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) {U V : Set X}
    (hU : IsOpen (π ⁻¹' U)) (hV : IsOpen (π ⁻¹' V)) (hcov : π ⁻¹' U ∪ π ⁻¹' V = Set.univ)
    (k : ℕ) :
    Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) (k + n) ⟶
      Work.Cohomology.pdCoh (TopCat.of Y) A ((k + 1) + n) :=
  Work.Cohomology.honestDelta (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) hU hV hcov (k + n)
    ≫ eqToHom (congrArg (fun m => Work.Cohomology.pdCoh (TopCat.of Y) A m)
        (by omega : k + n + 1 = (k + 1) + n))

/-! ## Element-level naturality computations -/

/-- **The cup map over a piece is the restriction of the global cup map.**  For a base class `x`
on all of `X`, restricting `π^*(x) ⌣ c` to the piece over `W` is cupping the restriction of `x`
with the restriction `cW` of `c`. -/
theorem luRestrict_cup {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A)
    {W : Set X} (cW : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' W) n)
    (hcW : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' W) n).hom c = cW)
    (k : ℕ) (x : Coh ℤ k X) :
    (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' W) (k + n)).hom
        ((mixedCupC ℤ A k n) ((CohMap π ℤ k).hom x) c)
      = (Work.Cohomology.luCupMap π A n cW k) ((restrCoh W ℤ k).hom x) := by
  have hnat := mixedCupC_pairNatural (subtypeMap (π ⁻¹' W))
    (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' W)) A (fun _ hy => hy) k n
    ((CohMap π ℤ k).hom x) c
  have hCoh : (CohMap (subtypeMap (π ⁻¹' W)) ℤ k).hom ((CohMap π ℤ k).hom x)
      = (CohMap (Work.Cohomology.luFPiece π W) ℤ k).hom
        ((CohMap (subtypeMap W) ℤ k).hom x) := by
    have h1 := congrArg (fun m => (ModuleCat.Hom.hom m) x)
      (CohMap_comp (subtypeMap (π ⁻¹' W)) π ℤ k)
    have h2 := congrArg (fun m => (ModuleCat.Hom.hom m) x)
      (CohMap_comp (Work.Cohomology.luFPiece π W) (subtypeMap W) ℤ k)
    have h3 : π.comp (subtypeMap (π ⁻¹' W))
        = (subtypeMap W).comp (Work.Cohomology.luFPiece π W) := by
      ext p; rfl
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
    rw [← h1, ← h2, luCohMap_congr h3]
  have hcW' : (ModuleCat.Hom.hom (relCohMap (subtypeMap (π ⁻¹' W))
      (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' W)) A (fun _ hy => hy) ℤ n)) c
      = cW := hcW
  rw [hCoh, hcW'] at hnat
  exact hnat

/-- **The cup map over the overlap, restricted from a piece.**  For a piece `P` of the base
containing the overlap `U ∩ V`, the restriction to the preimage overlap of the cup map over `P`
is the overlap cup map applied to the restriction of the base class. -/
theorem luOvl_cup_restrict {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A)
    {U V P : Set X} (hPV : U ∩ V ⊆ P)
    (cP : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' P) n)
    (hcP : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' P) n).hom c = cP)
    (cUV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n)
    (hcUV : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n).hom c = cUV)
    (k : ℕ) (y : Coh ℤ k ↥P) :
    (Work.Cohomology.pdCohMap (TopCat.of Y) A (π ⁻¹' P) (π ⁻¹' U ∩ π ⁻¹' V)
        (fun _ hx => hPV ⟨hx.1, hx.2⟩) (k + n)).hom
        ((Work.Cohomology.luCupMap π A n cP k) y)
      = (mixedCupC ℤ (Work.Cohomology.interAU (X := TopCat.of Y)
            A (π ⁻¹' U ∩ π ⁻¹' V)) k n)
          ((CohMap (fPieceProj π U V) ℤ k).hom
            ((CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of X)
              P (U ∩ V) hPV)) ℤ k).hom y))
          cUV := by
  have hnat := mixedCupC_pairNatural (X := ↥(π ⁻¹' U ∩ π ⁻¹' V)) (Y := ↥(π ⁻¹' P))
    (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of Y) (π ⁻¹' P : Set Y)
      (π ⁻¹' U ∩ π ⁻¹' V : Set Y) (fun _ hx => hPV ⟨hx.1, hx.2⟩)))
    (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V))
    (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' P)) (fun _ hy => hy) k n
    ((CohMap (Work.Cohomology.luFPiece π P) ℤ k).hom y) cP
  have hcup : (ModuleCat.Hom.hom (relCohMap
      (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of Y) (π ⁻¹' P : Set Y)
        (π ⁻¹' U ∩ π ⁻¹' V : Set Y) (fun _ hx => hPV ⟨hx.1, hx.2⟩)))
      (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V))
      (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' P)) (fun _ hy => hy) ℤ n)) cP
      = cUV := by
    rw [show (ModuleCat.Hom.hom (relCohMap
        (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of Y) (π ⁻¹' P : Set Y)
          (π ⁻¹' U ∩ π ⁻¹' V : Set Y) (fun _ hx => hPV ⟨hx.1, hx.2⟩)))
        (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V))
        (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' P)) (fun _ hy => hy) ℤ n)) cP
        = (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Y) A (π ⁻¹' P)
            (π ⁻¹' U ∩ π ⁻¹' V) (fun _ hx => hPV ⟨hx.1, hx.2⟩) n)) cP from
      congrArg (fun m => (ModuleCat.Hom.hom m) cP)
        (Work.Cohomology.pdCohMap_eq_relCohMap (TopCat.of Y) A (π ⁻¹' P)
          (π ⁻¹' U ∩ π ⁻¹' V) (fun _ hx => hPV ⟨hx.1, hx.2⟩) n).symm]
    have hcomp := congrArg (fun m => (ModuleCat.Hom.hom m) c)
      (Work.Cohomology.pdCohRes_comp (TopCat.of Y) A (π ⁻¹' P) (π ⁻¹' U ∩ π ⁻¹' V)
        (fun _ hx => hPV ⟨hx.1, hx.2⟩) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
    rw [hcP] at hcomp
    rw [← hcomp]
    exact hcUV
  have hCoh : (CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of Y)
        (π ⁻¹' P : Set Y) (π ⁻¹' U ∩ π ⁻¹' V : Set Y) (fun x hx => hPV ⟨hx.1, hx.2⟩))) ℤ k).hom
        ((CohMap (Work.Cohomology.luFPiece π P) ℤ k).hom y)
      = (CohMap (fPieceProj π U V) ℤ k).hom
        ((CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of X)
          P (U ∩ V) hPV)) ℤ k).hom y) := by
    have h1 := congrArg (fun m => (ModuleCat.Hom.hom m) y)
      (CohMap_comp (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of Y)
          (π ⁻¹' P : Set Y) (π ⁻¹' U ∩ π ⁻¹' V : Set Y) (fun x hx => hPV ⟨hx.1, hx.2⟩)))
        (Work.Cohomology.luFPiece π P) ℤ k)
    have h2 := congrArg (fun m => (ModuleCat.Hom.hom m) y)
      (CohMap_comp (fPieceProj π U V)
        (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of X)
          P (U ∩ V) hPV)) ℤ k)
    have h3 : (Work.Cohomology.luFPiece π P).comp
          (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of Y)
            (π ⁻¹' P : Set Y) (π ⁻¹' U ∩ π ⁻¹' V : Set Y) (fun _ hx => hPV ⟨hx.1, hx.2⟩)))
        = (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of X) P (U ∩ V) hPV)).comp
            (fPieceProj π U V) := by
      ext p; rfl
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
    rw [← h1, ← h2]
    exact congrArg (fun m => (ModuleCat.Hom.hom m) y) (luCohMap_congr h3 k)
  rw [hcup, hCoh] at hnat
  exact hnat

/-- **The global cup map as pullback followed by cupping with the global class.** -/
theorem luTM_eq_relPb_Ttop {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A) (k : ℕ) :
    luTM π A n c k = relPb π k ≫ TsqH.Ttop (TopCat.of Y) A n c k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [luTM, TsqH.Ttop]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [Work.Cohomology.relPb_apply]
  rfl

/-- **The overlap cup map as pullback of the absolute cohomology followed by cupping with the
overlap class.** -/
theorem luTQ_eq_relPb_Tov {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A)
    {U V : Set X} (cUV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n)
    (hcUV : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n).hom c = cUV)
    (k : ℕ) :
    relPb (fPieceProj π U V) k ≫ TsqH.Tov (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) n c k
      = luTQ π A n cUV k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [luTQ, TsqH.Tov, luCupMapOvl]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [Work.Cohomology.relPb_apply]
  have h : (ModuleCat.Hom.hom (TsqH.relRestrOvl (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) n)) c = cUV :=
    hcUV
  rw [h]
  rfl

/-! ## The component identities -/

/-- **First component of the `F`-square**: the cup map over `P` is the restriction of the global
cup map. -/
theorem luF_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A)
    {P : Set X} (cP : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' P) n)
    (hcP : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' P) n).hom c = cP) (k : ℕ) :
    Work.Cohomology.pdCohRes (TopCat.of X) (∅ : Set X) P k ≫ luTU π A n cP k
      = luTM π A n c k ≫ Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' P) (k + n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [luTU, luTM]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  have h1 := congrArg (fun m => (ModuleCat.Hom.hom m) z)
    (Work.Thom.pdCohRes_pdCohIso X P k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1]
  exact (luRestrict_cup π A n c cP hcP k ((pdCohIso X k).hom z)).symm

/-- **The `G`-square component**: the overlap cup map applied to a restricted class is the
restriction of the piece cup map. -/
theorem luG_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A)
    {U V P : Set X} (hPV : U ∩ V ⊆ P)
    (cP : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' P) n)
    (hcP : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' P) n).hom c = cP)
    (cUV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n)
    (hcUV : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n).hom c = cUV)
    (k : ℕ) :
    Work.Cohomology.pdCohMap (TopCat.of X) (∅ : Set X) P (U ∩ V) hPV k ≫ luTQ π A n cUV k
      = luTU π A n cP k ≫ Work.Cohomology.pdCohMap (TopCat.of Y) A (π ⁻¹' P)
          (π ⁻¹' U ∩ π ⁻¹' V) (fun _ hx => hPV ⟨hx.1, hx.2⟩) (k + n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [luTU, luTQ]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  have h1 := congrArg (fun m => (ModuleCat.Hom.hom m) z)
    (Work.Thom.pdCohMap_pdCohIso X P (U ∩ V) hPV k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1]
  simp only [luCupMapOvl]
  exact (luOvl_cup_restrict π A n c hPV cP hcP cUV hcUV k ((pdCohIso ↥P k).hom z)).symm

/-! ## The three squares of the Mayer--Vietoris ladder -/

/-- **The `F`-square**: the two restrictions commute with the cup maps. -/
theorem luF_square {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A)
    {U V : Set X}
    (cU : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U) n)
    (cV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' V) n)
    (hcU : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' U) n).hom c = cU)
    (hcV : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' V) n).hom c = cV) :
    ∀ k, Work.Cohomology.honestF (TopCat.of X) (∅ : Set X) U V k ≫ luTP π A n cU cV k
      = luTM π A n c k ≫ Work.Cohomology.honestF (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V)
          (k + n) := by
  intro k
  rw [show luTP π A n cU cV k = biprod.map (luTU π A n cU k) (luTU π A n cV k) from rfl]
  apply biprod.hom_ext
  · simp only [Category.assoc]
    rw [biprod.map_fst, honestF_fst'_assoc, Work.Cohomology.honestF_fst']
    exact luF_comp π A n c cU hcU k
  · simp only [Category.assoc]
    rw [biprod.map_snd, honestF_snd'_assoc, Work.Cohomology.honestF_snd']
    exact luF_comp π A n c cV hcV k

/-- **The `G`-square**: the difference of the two restrictions commutes with the cup maps. -/
theorem luG_square {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A)
    {U V : Set X}
    (cU : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U) n)
    (cV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' V) n)
    (cUV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n)
    (hcU : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' U) n).hom c = cU)
    (hcV : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' V) n).hom c = cV)
    (hcUV : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n).hom c = cUV) :
    ∀ k, Work.Cohomology.honestG (TopCat.of X) (∅ : Set X) U V k ≫ luTQ π A n cUV k
      = luTP π A n cU cV k ≫ Work.Cohomology.honestG (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V)
          (k + n) := by
  intro k
  rw [show luTP π A n cU cV k = biprod.map (luTU π A n cU k) (luTU π A n cV k) from rfl]
  apply biprod.ext_from_iff.mpr
  constructor
  · rw [honestG_inl'_assoc, biprod.inl_map_assoc, Work.Cohomology.honestG_inl']
    exact luG_comp π A n c Set.inter_subset_left cU hcU cUV hcUV k
  · rw [honestG_inr'_assoc, biprod.inr_map_assoc, Work.Cohomology.honestG_inr',
      Preadditive.comp_neg, Preadditive.neg_comp, neg_inj]
    exact luG_comp π A n c Set.inter_subset_right cV hcV cUV hcUV k

/-- **The transgression square of the ladder**: the connecting homomorphisms commute with the cup
maps. -/
theorem luDelta_square {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A)
    {U V : Set X} (cUV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n)
    (hcUV : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n).hom c = cUV)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∀ k, Work.Cohomology.honestDelta (TopCat.of X) (∅ : Set X) U V hU hV hcov k
        ≫ luTM π A n c (k + 1)
      = luTQ π A n cUV k ≫ luDelta2 π A n (hU.preimage π.continuous)
          (hV.preimage π.continuous)
          (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) k := by
  intro k
  rw [luTM_eq_relPb_Ttop π A n c (k + 1)]
  rw [← Category.assoc]
  rw [Work.Thom.transgressionNatural π hU hV hcov k]
  rw [Category.assoc]
  rw [Work.Thom.honestDelta_mixedCup (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V)
    (hU.preimage π.continuous) (hV.preimage π.continuous)
    (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) n c k]
  rw [← Category.assoc]
  rw [luTQ_eq_relPb_Tov π A n c cUV hcUV k]
  rfl

/-- **Milnor's gluing step for the transgression.** -/
theorem luThomGen {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (hn : 1 ≤ n)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (c : Work.Thom.RelCoh ℤ n Y A)
    (cU : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U) n)
    (hcU : ∀ k, Function.Bijective (Work.Cohomology.luCupMap π A n cU k))
    (cV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' V) n)
    (hcV : ∀ k, Function.Bijective (Work.Cohomology.luCupMap π A n cV k))
    (cUV : Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) n)
    (hcUV : ∀ k, Function.Bijective (fun x : Work.Thom.Coh ℤ k ↥(U ∩ V) =>
      (Work.Thom.mixedCupC ℤ (Work.Cohomology.interAU (X := TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V)) k n)
        ((Work.Thom.CohMap (Work.Thom.fPieceProj π U V) ℤ k).hom x) cUV))
    (hUc : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' U) n).hom c = cU)
    (hVc : (Work.Cohomology.pdCohRes (TopCat.of Y) A (π ⁻¹' V) n).hom c = cV)
    (hUVc : (Work.Thom.TsqH.relRestrOvl (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) n).hom c = cUV)
    (hlow : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) (n - 1))) :
    ∀ k, Function.Bijective (fun x : Work.Thom.Coh ℤ k X =>
      (Work.Thom.mixedCupC ℤ A k n) ((Work.Thom.CohMap π ℤ k).hom x) c) := by
  have hcov' : π ⁻¹' U ∪ π ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, hcov, Set.preimage_univ]
  have hU' : IsOpen (π ⁻¹' U) := hU.preimage π.continuous
  have hV' : IsOpen (π ⁻¹' V) := hV.preimage π.continuous
  have hcUV' : ∀ k, Function.Bijective (luCupMapOvl π A n cUV k) := fun k => hcUV k
  have hmain := five_lemma_LES'
    (M₁ := fun k => Work.Cohomology.pdCoh (TopCat.of X) (∅ : Set X) k)
    (P₁ := fun k => Work.Cohomology.pdCohBiprod (TopCat.of X) (∅ : Set X) U V k)
    (Q₁ := fun k => Work.Cohomology.pdCohSub (TopCat.of X) (∅ : Set X) (U ∩ V) k)
    (M₂ := fun k => Work.Cohomology.pdCoh (TopCat.of Y) A (k + n))
    (P₂ := fun k => Work.Cohomology.pdCohBiprod (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) (k + n))
    (Q₂ := fun k => Work.Cohomology.pdCohSub (TopCat.of Y) A (π ⁻¹' U ∩ π ⁻¹' V) (k + n))
    (F₁ := fun k => Work.Cohomology.honestF (TopCat.of X) (∅ : Set X) U V k)
    (G₁ := fun k => Work.Cohomology.honestG (TopCat.of X) (∅ : Set X) U V k)
    (δ₁ := fun k => Work.Cohomology.honestDelta (TopCat.of X) (∅ : Set X) U V hU hV hcov k)
    (F₂ := fun k => Work.Cohomology.honestF (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) (k + n))
    (G₂ := fun k => Work.Cohomology.honestG (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) (k + n))
    (δ₂ := fun k => luDelta2 π A n hU' hV' hcov' k)
    (e₂₁ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.honest_exact₂ (TopCat.of X) (∅ : Set X) U V hU hV hcov k))
    (e₃₁ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.honest_exact₃ (TopCat.of X) (∅ : Set X) U V hU hV hcov k))
    (e₁₁ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.honest_exact₁ (TopCat.of X) (∅ : Set X) U V hU hV hcov k))
    (e₂₂ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.honest_exact₂ (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) hU' hV' hcov' (k + n)))
    (e₃₂ := fun k => by
      rw [luDelta2, ker_comp_iso]
      exact ShortComplex.Exact.moduleCat_range_eq_ker
        (Work.Cohomology.honest_exact₃ (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) hU' hV' hcov'
          (k + n)))
    (e₁₂ := fun k => by
      rw [luDelta2, ModuleCat.hom_comp, LinearMap.range_comp]
      have hr : (LinearMap.range (ModuleCat.Hom.hom (Work.Cohomology.honestDelta
            (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) hU' hV' hcov' (k + n))))
          = (LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestF
              (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) ((k + n) + 1)))) :=
        ShortComplex.Exact.moduleCat_range_eq_ker
          (Work.Cohomology.honest_exact₁ (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) hU' hV' hcov'
            (k + n))
      rw [hr]
      exact map_ker_eq_ker
        (congrArg (fun m => Work.Cohomology.pdCoh (TopCat.of Y) A m)
          (by omega : (k + n) + 1 = (k + 1) + n))
        (congrArg (fun m => Work.Cohomology.pdCohBiprod (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) m)
          (by omega : (k + n) + 1 = (k + 1) + n))
        (Work.Cohomology.honestF (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) ((k + n) + 1))
        (Work.Cohomology.honestF (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) ((k + 1) + n))
        (eqToHom_honestF (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V)
          (by omega : (k + n) + 1 = (k + 1) + n)))
    (TM := fun k => luTM π A n c k)
    (TP := fun k => luTP π A n cU cV k)
    (TQ := fun k => luTQ π A n cUV k)
    (f₁ := by
      haveI : Mono (Work.Cohomology.hmvF (TopCat.of X) (∅ : Set X) U V) :=
        (Work.Cohomology.hmv_shortExact (TopCat.of X) (∅ : Set X) U V).mono_f
      haveI : Mono (HomologicalComplex.homologyMap
          (Work.Cohomology.hmvF (TopCat.of X) (∅ : Set X) U V) 0) :=
        mono_homologyMap_f_zero _
      have heq : Work.Cohomology.honestF (TopCat.of X) (∅ : Set X) U V 0
          = (Work.Cohomology.cmpXIso (TopCat.of X) (∅ : Set X) U V hU hV hcov 0).hom
            ≫ HomologicalComplex.homologyMap
                (Work.Cohomology.hmvF (TopCat.of X) (∅ : Set X) U V) 0
            ≫ (Work.Cohomology.hmvMidIso (TopCat.of X) (∅ : Set X) U V 0).hom := by
        have hs := Work.Cohomology.honestSq₁ (TopCat.of X) (∅ : Set X) U V 0
        have h := congrArg
          (fun m => m ≫ (Work.Cohomology.hmvMidIso (TopCat.of X) (∅ : Set X) U V 0).hom) hs
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
        rw [← Work.Cohomology.cmpXIso_hom] at h
        exact h.symm
      have hmono : Mono (Work.Cohomology.honestF (TopCat.of X) (∅ : Set X) U V 0) := by
        rw [heq]; infer_instance
      rw [LinearMap.ker_eq_bot]
      exact (ModuleCat.mono_iff_injective _).mp hmono)
    (f₂ := by
      have hker_n : (LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestF
          (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) n))) = ⊥ := by
        have hr : (LinearMap.range (ModuleCat.Hom.hom (Work.Cohomology.honestDelta
              (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) hU' hV' hcov' (n - 1))))
            = (LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestF
                (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) ((n - 1) + 1)))) :=
          ShortComplex.Exact.moduleCat_range_eq_ker
            (Work.Cohomology.honest_exact₁ (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) hU' hV' hcov'
              (n - 1))
        haveI : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Y) A
            (π ⁻¹' U ∩ π ⁻¹' V) (n - 1)) := hlow
        have hbot : (LinearMap.range (ModuleCat.Hom.hom (Work.Cohomology.honestDelta
            (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) hU' hV' hcov' (n - 1)))) = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro y hy
          obtain ⟨x, rfl⟩ := hy
          rw [show x = 0 from Subsingleton.elim x 0, map_zero]
        have hk : (LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestF
            (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) ((n - 1) + 1)))) = ⊥ := by
          rw [← hr, hbot]
        rwa [show (n - 1) + 1 = n from Nat.sub_add_cancel hn] at hk
      have hker0 : (LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestF
          (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) (0 + n)))) = ⊥ := by
        refine eq_bot_of_map_eq_bot
          (congrArg (fun m => Work.Cohomology.pdCoh (TopCat.of Y) A m) (Nat.zero_add n)) _ ?_
        rw [map_ker_eq_ker
          (congrArg (fun m => Work.Cohomology.pdCoh (TopCat.of Y) A m) (Nat.zero_add n))
          (congrArg (fun m => Work.Cohomology.pdCohBiprod (TopCat.of Y) A (π ⁻¹' U)
            (π ⁻¹' V) m) (Nat.zero_add n))
          (Work.Cohomology.honestF (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) (0 + n))
          (Work.Cohomology.honestF (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) n)
          (eqToHom_honestF (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) (Nat.zero_add n)),
          hker_n]
      intro u hu
      have hu0 : u = 0 := by
        have hz := (Submodule.eq_bot_iff (LinearMap.ker (ModuleCat.Hom.hom
          (Work.Cohomology.honestF (TopCat.of Y) A (π ⁻¹' U) (π ⁻¹' V) (0 + n))))).mp hker0
        exact hz u (by
          show ModuleCat.Hom.hom (Work.Cohomology.honestF (TopCat.of Y) A (π ⁻¹' U)
            (π ⁻¹' V) (0 + n)) u = 0
          exact hu)
      exact ⟨0, by rw [map_zero, hu0]⟩)
    (hF := luF_square π A n c cU cV hUc hVc)
    (hG := luG_square π A n c cU cV cUV hUc hVc hUVc)
    (hδ := luDelta_square π A n c cUV hUVc hU hV hcov)
    (hP := by
      intro k
      haveI : IsIso (ModuleCat.ofHom (Work.Cohomology.luCupMap π A n cU k)) := by
        rw [isIso_iff_mono_and_epi]
        exact ⟨(ModuleCat.mono_iff_injective _).mpr (hcU k).1,
          (ModuleCat.epi_iff_surjective _).mpr (hcU k).2⟩
      haveI : IsIso (ModuleCat.ofHom (Work.Cohomology.luCupMap π A n cV k)) := by
        rw [isIso_iff_mono_and_epi]
        exact ⟨(ModuleCat.mono_iff_injective _).mpr (hcV k).1,
          (ModuleCat.epi_iff_surjective _).mpr (hcV k).2⟩
      haveI hiU : IsIso ((pdCohIso ↥U k).hom
          ≫ ModuleCat.ofHom (Work.Cohomology.luCupMap π A n cU k)) :=
        ((pdCohIso ↥U k).trans
          (asIso (ModuleCat.ofHom (Work.Cohomology.luCupMap π A n cU k)))).isIso_hom
      haveI hiV : IsIso ((pdCohIso ↥V k).hom
          ≫ ModuleCat.ofHom (Work.Cohomology.luCupMap π A n cV k)) :=
        ((pdCohIso ↥V k).trans
          (asIso (ModuleCat.ofHom (Work.Cohomology.luCupMap π A n cV k)))).isIso_hom
      exact (biprod.mapIso
        (asIso ((pdCohIso ↥U k).hom ≫ ModuleCat.ofHom (Work.Cohomology.luCupMap π A n cU k)))
        (asIso ((pdCohIso ↥V k).hom ≫ ModuleCat.ofHom (Work.Cohomology.luCupMap π A n cV k)))).isIso_hom)
    (hQ := by
      intro k
      haveI : IsIso (ModuleCat.ofHom (luCupMapOvl π A n cUV k)) := by
        rw [isIso_iff_mono_and_epi]
        exact ⟨(ModuleCat.mono_iff_injective _).mpr (hcUV' k).1,
          (ModuleCat.epi_iff_surjective _).mpr (hcUV' k).2⟩
      exact ((pdCohIso ↥(U ∩ V) k).trans
        (asIso (ModuleCat.ofHom (luCupMapOvl π A n cUV k)))).isIso_hom)
  intro k
  haveI hk : IsIso ((pdCohIso X k).hom ≫ ModuleCat.ofHom
      (((LinearMap.applyₗ c).comp (mixedCupC ℤ A k n)).comp (CohMap π ℤ k).hom)) := hmain k
  haveI hΦ : IsIso (ModuleCat.ofHom
      (((LinearMap.applyₗ c).comp (mixedCupC ℤ A k n)).comp (CohMap π ℤ k).hom)) :=
    IsIso.of_isIso_comp_left (pdCohIso X k).hom
      (ModuleCat.ofHom
        (((LinearMap.applyₗ c).comp (mixedCupC ℤ A k n)).comp (CohMap π ℤ k).hom))
  rw [isIso_iff_mono_and_epi] at hΦ
  exact ⟨(ModuleCat.mono_iff_injective _).mp hΦ.1, (ModuleCat.epi_iff_surjective _).mp hΦ.2⟩

end

end Work.Thom
