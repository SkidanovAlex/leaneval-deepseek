import Submission.Work.DSFinal.Mix
import Submission.Work.DSMap.Fix
import Submission.Work.DSMap.Fix2
import Submission.Work.DSG1.Main
import Submission.Work.DSG2.Main
import Submission.Work.DSG3.Main
import Submission.Work.DSG4a.Main
import Submission.Work.DSG4b.Main
import Submission.Work.DSG4c.Main
import Submission.Work.DSTRI.Main
import Submission.Work.DSEQ0.Main
import Submission.Work.DSEQP.Main

/-! # DSFinal.Main — LEAD-OWNED final wiring (curric-46, 10-14)

`main_dsplit_final` = `DSMap.main_dsplit` with every area replaced by its proved deliverable
(G1/G4a through the `Fix`/`Fix2` repairs; G4a via the clean `area_G4a_localGlobal_of_areas` fed
with F1 proved + COH frozen; MIX via `Work.DSFinal.area_MIX2pos1_final`), and the two challenge
theorems with types identical to `Submission.lean`'s. -/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

set_option linter.style.haveILetI false

namespace Work.DSFinal

open DSMap

universe u w₁ w₂

/-- G4aU from the clean `Work.DSG4a.area_G4a_localGlobal_of_areas`: F1 proved, COH frozen. -/
theorem area_G4a_final.{a, b, c} (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hp : IsProjOver A f)
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ (A' : Type a) (_ : CommRing A') (_ : IsLocalRing A')
      (ψ : A →+* A'), ψ.Flat ∧ (maximalIdeal A').comap ψ = m ∧
      DSplit.{a, a + 1, a + 1} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
        (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))) :
    DSplit.{a, b, c} A X f :=
  Work.DSG4a.area_G4a_localGlobal_of_areas.{a, b, c} A X f hp
    (fun (B : Type a) [CommRing B] {Y : Scheme.{a}} (g : Y ⟶ Spec (.of B)) [IsProper g]
      {κ : Type a} [Finite κ] [Nonempty κ] (W : κ → Y.Opens) (hW : ∀ i, IsAffineOpen (W i))
      (hcov : ⨆ i, W i = ⊤) (i : HasDerivedCategory.{b} (ModuleCat.{a} B))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} Y.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} Y.ringCatSheaf)) => by
        letI := i
        letI := j
        letI := k
        haveI : QuasiCompact g := Work.DSMX0bU.quasiCompact_of_isProper g
        exact DSMap.area_F1_cech_proved.{a, b, c} B Y g W hW hcov)
    (fun (B : Type a) [CommRing B] [IsNoetherianRing B] {Y : Scheme.{a}}
      (g : Y ⟶ Spec (.of B)) [IsProper g] (hp : IsProjOver B g)
      (i : HasDerivedCategory.{b} (ModuleCat.{a} B))
      (j : HasDerivedCategory.{c} (SheafOfModules.{a} Y.ringCatSheaf))
      (k : EnoughInjectives (SheafOfModules.{a} Y.ringCatSheaf)) => by
        letI := i
        letI := j
        letI := k
        exact DSMap.area_COH_proved.{a, b, c} B Y g hp)
    (fun (A' : Type a) [CommRing A'] (ψ : A →+* A') [Algebra A A'] {κ : Type a}
      [Finite κ] [Nonempty κ]
      (W : κ → (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f).Opens)
      (hW : ∀ i, IsAffineOpen (W i)) (hcov : ⨆ i, W i = ⊤)
      (i : HasDerivedCategory.{a + 1} (ModuleCat.{a} A'))
      (j : HasDerivedCategory.{a + 1}
        (SheafOfModules.{a} (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf))
      (k : EnoughInjectives
        (SheafOfModules.{a} (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f).ringCatSheaf)) => by
        letI := i
        letI := j
        letI := k
        haveI : IsProper (Work.DSG4a.baseChangeSnd (A := A) (A' := A') X f) := inferInstance
        haveI : QuasiCompact (Work.DSG4a.baseChangeSnd (A := A) (A' := A') X f) :=
          Work.DSMX0bU.quasiCompact_of_isProper _
        exact DSMap.area_F1_cech_proved.{a, a + 1, a + 1} A'
          (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f)
          (Work.DSG4a.baseChangeSnd (A := A) (A' := A') X f) W hW hcov)
    h

example : type_of% (@area_G4a_final.{u, w₁, w₂}) =
    type_of% (@DSMap.Fix2.area_G4a_localGlobalU.{u, w₁, w₂}) := rfl

/-- `DSMap.main_dsplit` rewired onto the proved areas. -/
theorem main_dsplit_final (A : Type u) [CommRing A] [IsRegularRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f) :
    DSplit.{u, w₁, w₂} A X f := by
  obtain ⟨X', g, hg, hprop, hproj⟩ := DSMap.area_G2_chow_proved A X f
  refine DSMap.Fix.area_G1_pullbackU_proved A f g ?_
  have hsf : Function.Surjective (g ≫ f) := by
    intro x
    obtain ⟨y, rfl⟩ := hs x
    obtain ⟨z, rfl⟩ := hg y
    exact ⟨z, by simp⟩
  refine area_G4a_final.{u, w₁, u + 1} A X' (g ≫ f) hproj ?_
  intro m hm
  obtain ⟨A', _, _, ψ, hcomp, hac, hflat, hcomap⟩ := DSMap.area_G4b_gonflement_proved A m hm
  refine ⟨A', inferInstance, inferInstance, ψ, hflat, hcomap, ?_⟩
  obtain ⟨hP, hS, hPr⟩ := DSMap.area_G4c_baseChange_proved A A' ψ X' (g ≫ f) hsf hproj
  have := DSMap.area_REG_proved A'
  obtain ⟨Z, ι, -, hZ, hsZ, hpZ, hgfZ, hprZ⟩ :=
    DSMap.area_G3_multisection_proved A' _ (pullback.snd (g ≫ f) (Spec.map (CommRingCat.ofHom ψ)))
      hS hPr
  refine DSMap.Fix.area_G1_pullbackU_proved A' _ ι ?_
  rcases DSMap.area_TRI_proved A' with h0 | ⟨p, hp, hcp⟩ | ⟨p, hp, hc0, hcr⟩
  · exact DSMap.area_EQ0_proved A' Z _ hsZ hgfZ hprZ
  · have := Fact.mk hp
    exact DSMap.area_EQP_proved A' p Z _ hsZ hgfZ hprZ
  · have := Fact.mk hp
    exact area_MIX2pos1_final A' p Z _ hsZ hgfZ hprZ

example : type_of% (@main_dsplit_final.{u, w₁, w₂}) = type_of% (@DSMap.main_dsplit.{u, w₁, w₂}) :=
  rfl

end Work.DSFinal

/-! ## The two challenge theorems (statements copied verbatim from `Submission.lean`) -/

namespace Work.DSFinal

open _root_.LeanEval
open _root_.LeanEval.AlgebraicGeometry
open _root_.LeanEval.AlgebraicGeometry.DirectSummand
open CategoryTheory AlgebraicGeometry

variable (A : Type*) [CommRing A] [IsRegularRing A]

theorem derived_direct_summand_final [HasDerivedCategory (ModuleCat A)]
    (X : Scheme) (f : X ⟶ Spec (.of A)) [IsProper f] (surj : Function.Surjective f)
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)] :
    let φ : A →+* Γ(X, ⊤) := ((ΓSpec.adjunction.homEquiv _ _).symm f).unop.hom
    let : Algebra A Γ(X, ⊤) := φ.toAlgebra
    ∀ _ : EnoughInjectives (SheafOfModules X.ringCatSheaf), IsSplitMono <|
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (ModuleCat.ofHom (Algebra.linearMap A Γ(X, ⊤))) ≫
      (rightDerivedFunctorPlusUnit' (SheafOfModules.evaluation X.ringCatSheaf ⟨⊤⟩ ⋙
        ModuleCat.restrictScalars φ) 0).app (SheafOfModules.unit X.ringCatSheaf) := by
  intro φ _ ei
  exact main_dsplit_final A X f surj _ _ ei

theorem direct_summand_final (B : Type*) [CommRing B] [Algebra A B]
    [Module.Finite A B] [FaithfulSMul A B] :
    ∃ π : B →ₗ[A] A, π ∘ₗ Algebra.linearMap A B = .id :=
  DSMap.dsc_of_dsplit A (fun X f _ hs => main_dsplit_final A X f hs) B

end Work.DSFinal

