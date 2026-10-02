import Mathlib
import Submission.Work.KunnethEZ.normalizedDetectedPairSph
import Submission.Work.Cohomology.CupRing
import Submission.Work.Kunneth.kronecker_ezChain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Precomposition with the normalization projection is the identity on cohomology

`Work.KunnethEZ.normP X n` is the degree-`n` component of the projection
`toNormalizedChainComplex ≫ fromNormalizedChainComplex`, which is chain homotopic to the identity
of `C_*(X)`.  Consequently, for any `n`-cocycle `β`, the cochain `β ∘ normP` is a cocycle
(`cochainDiff_comp_normP`) with the same cohomology class:

  `cohomologyClassOf (β ∘ normP) = cohomologyClassOf β`.

Since `normP` kills the degenerate simplices (`normP_degenerate`), this produces a **normalized**
representative of every cohomology class, which is what removes the normalized-representative
hypothesis from the Kronecker rule `Work.Kunneth.kronH_homCrossLin`.

The proof is the elementary one: the homotopy relation at degree `n` reads
`normP X n = dNext n h + prevD n h + 𝟙`, and for a *cocycle* `β` the two corrections become
`δ(β ∘ h)` and `0`; two cocycles differing by a coboundary have the same class because the
difference of the two cycles is in the image of `toCycles` and `toCycles ≫ homologyπ = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

/-- The homotopy relation of the normalization projection, at degree `n`. -/
theorem normP_eq_dNext_add (X : SSet) (n : ℕ) :
    Work.KunnethEZ.normP X n
      = (dNext n
            (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom).hom
        + (prevD n
            (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom).hom
        + LinearMap.id := by
  have h := congrArg (fun (g : (sChain X).X n ⟶ (sChain X).X n) => ModuleCat.Hom.hom g)
    ((X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.comm n)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_add,
    ModuleCat.hom_id] at h
  have hP : Work.KunnethEZ.normP X n
      = ModuleCat.Hom.hom ((X.homotopyEquivNormalizedChainComplex zz).hom.f n
          ≫ (X.homotopyEquivNormalizedChainComplex zz).inv.f n) := rfl
  rw [hP, h]

/-- **Two cocycles differing by a coboundary have the same cohomology class.** -/
theorem cohomologyClassOf_eq_of_sub_eq_cochainDiff (X : SSet) (m : ℕ)
    (γ γ' : Cochain ℤ X (m + 1)) (hγ : cochainDiff ℤ X γ = 0) (hγ' : cochainDiff ℤ X γ' = 0)
    (ψ : Cochain ℤ X m) (h : γ - γ' = cochainDiff ℤ X ψ) :
    cohomologyClassOf ℤ X γ hγ = cohomologyClassOf ℤ X γ' hγ' := by
  have hto : ((cochainC ℤ X).iCycles (m + 1)).hom
      ((HomologicalComplex.toCycles (cochainC ℤ X) m (m + 1)).hom ψ)
      = cochainDiff ℤ X ψ := by
    have h3 := congrArg (fun (g : (cochainC ℤ X).X m ⟶ (cochainC ℤ X).X (m + 1)) => g.hom ψ)
      (HomologicalComplex.toCycles_i (cochainC ℤ X) m (m + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
      Work.Cohomology.SSetCochainComplex_d_apply] using h3
  have hcyc : cocycleOf ℤ X γ hγ - cocycleOf ℤ X γ' hγ'
      = (HomologicalComplex.toCycles (cochainC ℤ X) m (m + 1)).hom ψ := by
    apply Work.Cohomology.iCycles_injective ℤ X (m + 1)
    rw [map_sub, Work.Cohomology.iCycles_cocycleOf, Work.Cohomology.iCycles_cocycleOf, hto]
    exact h
  have hπ : ((cochainC ℤ X).homologyπ (m + 1)).hom
      ((HomologicalComplex.toCycles (cochainC ℤ X) m (m + 1)).hom ψ) = 0 := by
    have h3 := congrArg (fun (g : (cochainC ℤ X).X m ⟶ (cochainC ℤ X).homology (m + 1)) =>
        g.hom ψ)
      (HomologicalComplex.toCycles_comp_homologyπ (cochainC ℤ X) m (m + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h3
  have hc := sub_eq_iff_eq_add.mp hcyc
  show ((cochainC ℤ X).homologyπ (m + 1)).hom (cocycleOf ℤ X γ hγ)
    = ((cochainC ℤ X).homologyπ (m + 1)).hom (cocycleOf ℤ X γ' hγ')
  rw [hc, map_add, hπ, zero_add]

/-- **Precomposition with the normalization projection does not change the cohomology class.** -/
theorem cohomologyClassOf_comp_normP (X : SSet) (n : ℕ)
    (β : Cochain ℤ X n) (hβ : cochainDiff ℤ X β = 0) :
    ∃ h : cochainDiff ℤ X (β.comp (Work.KunnethEZ.normP X n)) = 0,
      cohomologyClassOf ℤ X (β.comp (Work.KunnethEZ.normP X n)) h
        = cohomologyClassOf ℤ X β hβ := by
  refine ⟨Work.KunnethEZ.cochainDiff_comp_normP X n β hβ, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- degree 0: the two cochains are equal
    subst hn
    have heq : β.comp (Work.KunnethEZ.normP X 0) = β := by
      rw [normP_eq_dNext_add X 0, LinearMap.comp_add, LinearMap.comp_add, LinearMap.comp_id]
      have h1 : (dNext 0
          (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom).hom = 0 := by
        rw [dNext_eq_zero
            (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom 0
            (by rw [ComplexShape.down_Rel]; omega),
          ModuleCat.hom_zero]
      have h2 : β.comp (prevD 0
          (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom).hom = 0 := by
        rw [prevD_eq (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom
            (show (ComplexShape.down ℕ).Rel 1 0 from rfl),
          ModuleCat.hom_comp, ← LinearMap.comp_assoc]
        rw [show LinearMap.comp β (ModuleCat.Hom.hom ((sChain X).d 1 0))
            = cochainDiff ℤ X β from rfl, hβ, LinearMap.zero_comp]
      rw [h1, h2, LinearMap.comp_zero, zero_add, zero_add]
    exact cohomologyClassOf_congr ℤ X heq _ hβ
  · -- positive degree: the difference is the coboundary of `β ∘ h`
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine cohomologyClassOf_eq_of_sub_eq_cochainDiff X m _ _ _ _
      (β.comp (((X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom m (m + 1)).hom)) ?_
    rw [normP_eq_dNext_add X (m + 1), LinearMap.comp_add, LinearMap.comp_add,
      LinearMap.comp_id]
    have h1 : β.comp (dNext (m + 1)
        (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom).hom
        = cochainDiff ℤ X
            (β.comp (((X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom m (m + 1)).hom)) := by
      rw [dNext_eq (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom
          (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl),
        ModuleCat.hom_comp, ← LinearMap.comp_assoc]
      rfl
    have h2 : β.comp (prevD (m + 1)
        (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom).hom = 0 := by
      rw [prevD_eq (X.homotopyEquivNormalizedChainComplex zz).homotopyHomInvId.hom
          (show (ComplexShape.down ℕ).Rel (m + 2) (m + 1) from rfl),
        ModuleCat.hom_comp, ← LinearMap.comp_assoc]
      rw [show LinearMap.comp β (ModuleCat.Hom.hom ((sChain X).d (m + 2) (m + 1)))
          = cochainDiff ℤ X β from rfl, hβ, LinearMap.zero_comp]
    rw [h1, h2, add_zero]
    abel

end

end Work.Kunneth
