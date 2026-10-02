import Mathlib
import Submission.Work.Kunneth.CohKunneth.Defs
import Submission.Work.Kunneth.ctensHomologyValue
import Submission.Work.Kunneth.awMapDualTensorCochain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Cohomology (dualComplex dualComplexMap Cochain cochainDiff cohomologyClassOf
  cohomologyClassOf_congr)

/-! ## The cycle of a cocycle, for an arbitrary cochain complex -/

noncomputable def cocycleCyc (K : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (γ : ↥(K.X n)) (hγ : (K.d n (n + 1)).hom γ = 0) : ↥(K.cycles n) :=
  (kcCycIso K n).inv.hom ⟨γ, hγ⟩

theorem iCycles_cocycleCyc (K : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (γ : ↥(K.X n)) (hγ : (K.d n (n + 1)).hom γ = 0) :
    (K.iCycles n).hom (cocycleCyc K n γ hγ) = γ := by
  have h : (kcCycIso K n).hom.hom ((kcCycIso K n).inv.hom ⟨γ, hγ⟩) = ⟨γ, hγ⟩ :=
    homIso_hom_apply (kcCycIso K n) ⟨γ, hγ⟩
  have h2 := congrArg (fun w : ↥(kcCycKer K n) => (w : ↥(K.X n))) h
  rw [kcCycIso_hom_val] at h2
  exact h2

/-! ## The Eilenberg–Zilber step -/

noncomputable def ezDualMap (X Y : SSet) :
    dualComplex ℤ (sChain (sProd X Y)) ⟶ dualComplex ℤ (tChain X Y) :=
  dualComplexMap ℤ (tChain X Y) (sChain (sProd X Y)) (ezMap X Y)

noncomputable def awDualMap (X Y : SSet) :
    dualComplex ℤ (tChain X Y) ⟶ dualComplex ℤ (sChain (sProd X Y)) :=
  dualComplexMap ℤ (sChain (sProd X Y)) (tChain X Y) (awMap X Y)

theorem ezDualMap_comp_awDualMap (X Y : SSet) :
    ezDualMap X Y ≫ awDualMap X Y
      = dualComplexMap ℤ (sChain (sProd X Y)) (sChain (sProd X Y))
          (awMap X Y ≫ ezMap X Y) :=
  (Work.Cohomology.dualComplexMap_comp ℤ (awMap X Y) (ezMap X Y)).symm

theorem awDualMap_comp_ezDualMap (X Y : SSet) :
    awDualMap X Y ≫ ezDualMap X Y
      = dualComplexMap ℤ (tChain X Y) (tChain X Y) (ezMap X Y ≫ awMap X Y) :=
  (Work.Cohomology.dualComplexMap_comp ℤ (ezMap X Y) (awMap X Y)).symm

theorem homologyMap_ezDualMap_comp_awDualMap (X Y : SSet) (n : ℕ) :
    HomologicalComplex.homologyMap (ezDualMap X Y) n
        ≫ HomologicalComplex.homologyMap (awDualMap X Y) n
      = 𝟙 ((dualComplex ℤ (sChain (sProd X Y))).homology n) := by
  rw [← HomologicalComplex.homologyMap_comp, ezDualMap_comp_awDualMap]
  have hhom : HomologicalComplex.homologyMap
        (dualComplexMap ℤ (sChain (sProd X Y)) (sChain (sProd X Y))
          (awMap X Y ≫ ezMap X Y)) n
      = HomologicalComplex.homologyMap
          (dualComplexMap ℤ (sChain (sProd X Y)) (sChain (sProd X Y))
            (𝟙 (sChain (sProd X Y)))) n :=
    (Homotopy.homologyMap_eq (Work.Cohomology.dualHomotopy ℤ (aw_ez_homotopy X Y).some) n).symm
  rw [hhom, Work.Cohomology.dualComplexMap_id, HomologicalComplex.homologyMap_id]

theorem homologyMap_awDualMap_comp_ezDualMap (X Y : SSet) (n : ℕ) :
    HomologicalComplex.homologyMap (awDualMap X Y) n
        ≫ HomologicalComplex.homologyMap (ezDualMap X Y) n
      = 𝟙 ((dualComplex ℤ (tChain X Y)).homology n) := by
  rw [← HomologicalComplex.homologyMap_comp, awDualMap_comp_ezDualMap]
  have hhom : HomologicalComplex.homologyMap
        (dualComplexMap ℤ (tChain X Y) (tChain X Y) (ezMap X Y ≫ awMap X Y)) n
      = HomologicalComplex.homologyMap
          (dualComplexMap ℤ (tChain X Y) (tChain X Y) (𝟙 (tChain X Y))) n :=
    (Homotopy.homologyMap_eq (Work.Cohomology.dualHomotopy ℤ (ez_aw_homotopy X Y).some) n).symm
  rw [hhom, Work.Cohomology.dualComplexMap_id, HomologicalComplex.homologyMap_id]

noncomputable def ezDualIso (X Y : SSet) (n : ℕ) :
    (dualComplex ℤ (sChain (sProd X Y))).homology n
      ≅ (dualComplex ℤ (tChain X Y)).homology n :=
  Iso.mk (HomologicalComplex.homologyMap (ezDualMap X Y) n)
    (HomologicalComplex.homologyMap (awDualMap X Y) n)
    (homologyMap_ezDualMap_comp_awDualMap X Y n)
    (homologyMap_awDualMap_comp_ezDualMap X Y n)

/-- The transpose of the Alexander–Whitney map sends the tensor cochain `α ⊗ β` to the cross
product cochain `α × β`. -/
theorem awDualMap_tensorCochain (X Y : SSet) (p q : ℕ)
    (α : Cochain ℤ X p) (β : Cochain ℤ Y q) :
    ((awDualMap X Y).f (p + q)).hom
      (tensorCochain (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ α β)
      = crossCochain X Y p q α β :=
  awMapDualTensorCochain X Y p q α β

/-- The cycle of the cross product cochain. -/
noncomputable def crossCycle (X Y : SSet) (p q : ℕ) (α : Cochain ℤ X p)
    (β : Cochain ℤ Y q)
    (h : ((dualComplex ℤ (sChain (sProd X Y))).d (p + q) (p + q + 1)).hom
      (crossCochain X Y p q α β) = 0) :
    ↥((dualComplex ℤ (sChain (sProd X Y))).cycles (p + q)) :=
  cocycleCyc _ _ _ h

/-- The cycle of the tensor cochain `α ⊗ β` of the Koszul tensor product. -/
noncomputable def tensorCycle (X Y : SSet) (p q : ℕ) (α : Cochain ℤ X p)
    (β : Cochain ℤ Y q)
    (hα : ((dualComplex ℤ (sChain X)).d p (p + 1)).hom α = 0)
    (hβ : ((dualComplex ℤ (sChain Y)).d q (q + 1)).hom β = 0) :
    ↥((dualComplex ℤ (tChain X Y)).cycles (p + q)) :=
  cocycleCyc _ _ _
    (tensorCochain_isCocycle (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ α β hα hβ)

/-- **The value rule of the Eilenberg–Zilber step.** -/
theorem ezDualIso_crossH (X Y : SSet) (p q : ℕ)
    (α : Cochain ℤ X p) (β : Cochain ℤ Y q)
    (hα : cochainDiff ℤ X α = 0) (hβ : cochainDiff ℤ Y β = 0) :
    (ezDualIso X Y (p + q)).hom.hom
        (crossH X Y p q (cohomologyClassOf ℤ X α hα) (cohomologyClassOf ℤ Y β hβ))
      = ((dualComplex ℤ (tChain X Y)).homologyπ (p + q)).hom
          (tensorCycle X Y p q α β
            (by rw [← cochainDiff_eq_dualComplex_d]; exact hα)
            (by rw [← cochainDiff_eq_dualComplex_d]; exact hβ)) := by
  have hα' : ((dualComplex ℤ (sChain X)).d p (p + 1)).hom α = 0 := by
    rw [← cochainDiff_eq_dualComplex_d]; exact hα
  have hβ' : ((dualComplex ℤ (sChain Y)).d q (q + 1)).hom β = 0 := by
    rw [← cochainDiff_eq_dualComplex_d]; exact hβ
  have hX := crossCochain_isCocycle X Y p q α β hα hβ
  have hXd : ((dualComplex ℤ (sChain (sProd X Y))).d (p + q) (p + q + 1)).hom
      (crossCochain X Y p q α β) = 0 := by
    rw [dualComplex_d_apply_eq_cochainDiff]; exact hX
  have hcross : crossH X Y p q (cohomologyClassOf ℤ X α hα) (cohomologyClassOf ℤ Y β hβ)
      = ((dualComplex ℤ (sChain (sProd X Y))).homologyπ (p + q)).hom
          (crossCycle X Y p q α β hXd) := by
    refine (crossH_cohomologyClassOf X Y p q α β hα hβ hX).trans ?_
    have hcoe : crossCochain X Y p q α β
        = ((dualComplex ℤ (sChain (sProd X Y))).iCycles (p + q)).hom
            (crossCycle X Y p q α β hXd) :=
      (iCycles_cocycleCyc (dualComplex ℤ (sChain (sProd X Y))) (p + q)
        (crossCochain X Y p q α β) hXd).symm
    have hcycE : cochainDiff ℤ (sProd X Y)
        (((dualComplex ℤ (sChain (sProd X Y))).iCycles (p + q)).hom
          (crossCycle X Y p q α β hXd)) = 0 := by
      rw [← hcoe]; exact hX
    exact (cohomologyClassOf_congr ℤ (sProd X Y) hcoe hX hcycE).trans
      (cohomologyClassOf_eq_homologyπ_dual (sProd X Y) (p + q)
        (crossCycle X Y p q α β hXd) hcycE)
  have hcyc : (HomologicalComplex.cyclesMap (awDualMap X Y) (p + q)).hom
        (tensorCycle X Y p q α β hα' hβ')
      = crossCycle X Y p q α β hXd := by
    have hkey : (kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)).hom.hom
          ((HomologicalComplex.cyclesMap (awDualMap X Y) (p + q)).hom
            (tensorCycle X Y p q α β hα' hβ'))
        = (kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)).hom.hom
            (crossCycle X Y p q α β hXd) := by
      apply Subtype.ext
      change ((kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)).hom
          ((HomologicalComplex.cyclesMap (awDualMap X Y) (p + q)).hom
            (tensorCycle X Y p q α β hα' hβ'))
            : ↥((dualComplex ℤ (sChain (sProd X Y))).X (p + q)))
        = ((kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)).hom
            (crossCycle X Y p q α β hXd)
            : ↥((dualComplex ℤ (sChain (sProd X Y))).X (p + q)))
      rw [kcCycIso_hom_val, kcCycIso_hom_val, coch_iCycles_cyclesMap]
      rw [show ((dualComplex ℤ (tChain X Y)).iCycles (p + q)).hom
            (tensorCycle X Y p q α β hα' hβ')
          = tensorCochain (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ α β from
        iCycles_cocycleCyc _ _ _ _]
      rw [show ((dualComplex ℤ (sChain (sProd X Y))).iCycles (p + q)).hom
            (crossCycle X Y p q α β hXd) = crossCochain X Y p q α β from
        iCycles_cocycleCyc _ _ _ _]
      exact awDualMap_tensorCochain X Y p q α β
    calc (HomologicalComplex.cyclesMap (awDualMap X Y) (p + q)).hom
          (tensorCycle X Y p q α β hα' hβ')
        = (kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)).inv.hom
            ((kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)).hom.hom
              ((HomologicalComplex.cyclesMap (awDualMap X Y) (p + q)).hom
                (tensorCycle X Y p q α β hα' hβ'))) :=
          (homIso_inv_apply (kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)) _).symm
      _ = (kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)).inv.hom
            ((kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)).hom.hom
              (crossCycle X Y p q α β hXd)) := by rw [hkey]
      _ = crossCycle X Y p q α β hXd :=
          homIso_inv_apply (kcCycIso (dualComplex ℤ (sChain (sProd X Y))) (p + q)) _
  have h2 : ((dualComplex ℤ (sChain (sProd X Y))).homologyπ (p + q)).hom
        ((HomologicalComplex.cyclesMap (awDualMap X Y) (p + q)).hom
          (tensorCycle X Y p q α β hα' hβ'))
      = ((dualComplex ℤ (sChain (sProd X Y))).homologyπ (p + q)).hom
          (crossCycle X Y p q α β hXd) := by rw [hcyc]
  rw [hcross, ← h2, ← cochHomologyMap_apply_homologyπ]
  have h3 := congrArg (fun (φ : (dualComplex ℤ (tChain X Y)).homology (p + q) ⟶
      (dualComplex ℤ (tChain X Y)).homology (p + q)) =>
      φ.hom (((dualComplex ℤ (tChain X Y)).homologyπ (p + q)).hom
        (tensorCycle X Y p q α β hα' hβ')))
    (homologyMap_awDualMap_comp_ezDualMap X Y (p + q))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    at h3
  exact h3

end

end Work.Kunneth
