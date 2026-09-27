import Mathlib
import Submission.Work.Drive.refRows_open_posDense
import Submission.Work.Drive.refOdd_of_refRows
import Submission.Work.Drive.refExists_homotopies
import Submission.Work.Drive.refParityRows
import Submission.Work.Drive.refRowB_pairReg_openDense
import Submission.Work.Drive.classRowsSweep_openDense
import Submission.Work.Drive.rowCD_linTrans_generalPosition_openDense
import Submission.Work.Drive.hn2RefParityDefs
import Submission.Work.Drive.hn2Clause6Sard
import Submission.Work.Drive.classTripleOdd
import Submission.Work.Drive.hasClassLinearizationAlt
import Submission.Work.Drive.refPlaneLinearization
import Submission.Work.Drive.endTripleRegRefTriple
import Submission.Work.Drive.pairRegRows
import Submission.Work.Drive.hendL012Row
import Submission.Work.Drive.endTripleRegUnrestricted
import Submission.Work.Drive.loopBoxData_eventually
import Submission.Work.Drive.threeBlock_dense_point
import Submission.Work.Drive.sgGoodChain_of_small_shift_sweep
import Submission.Work.Drive.boxThree_of_good_family
import Submission.Work.Drive.pairReg_of_loopBoxData
import Submission.Work.Drive.unrestrictedFromBox
import Submission.Work.Drive.rowsOpen
import Submission.Work.Drive.pairReg_refPlane_perturb_dense

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- **The pair row `hpairL0P2`**: `PairReg (model Ψ⟨τ⟩) P̂₂` — as a corollary of the proved
`Work.Drive.pairReg_refPlane_perturb_dense` applied with the **linear** loop
`diskPlane (linPlaneChart Ψ c hc)` (the rotation angle `0`), whose perturbed version is again a
transported linear model.  The parameter `σ` (the perturbation of the reference plane) is produced by
the lemma, arbitrarily small and with positive level coordinate. -/
theorem refPairRow_linModel_refPlane_dense
    (Ψ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (τ ρ : Eucl 3) (hρ : 0 < ρ 0) (c₂ : ℝ) (hc₂ : 0 < c₂) (hcl : c₂ < lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : Eucl 3, ‖σ‖ < ε ∧ 0 < (ρ + σ) 0 ∧
      PairReg (planeClassMap (fun y => chartPert τ (diskPlane (linPlaneChart Ψ c hc) y)))
        (planeClassMap (fun y => chartPert (ρ + σ) (refPlanePres φ lam hlam y))) := by
  obtain ⟨σ, hσ, hσ', hP⟩ :=
    pairReg_refPlane_perturb_dense (Q := linPlaneChart Ψ c hc) (linPlaneChart_contMDiff Ψ c hc)
      (0 : UnitAddCircle) φ lam hlam τ ρ hρ c₂ hc₂ hcl ε hε
  have hrot : (fun y : EuclideanSpace ℝ (Fin 2) =>
      chartPert τ (rotPresentation (linPlaneChart Ψ c hc) (0 : UnitAddCircle) y))
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert τ (diskPlane (linPlaneChart Ψ c hc) y) := by
    funext y
    simp only [rotPresentation, rotCapping_zero, Function.comp_apply, id_eq]
  exact ⟨σ, hσ, hσ', by rw [hrot] at hP; exact hP⟩

theorem refParityFamily {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u v : UnitAddCircle) (huv : v - u ∈ Zc γ)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam) :
    ∃ A : Set (EuclideanSpace ℝ (Fin 12)),
      RefParityFamily Q (refPlanePres φ lam hlam) u v A := by
  classical
  -- ## the fixed linear data: the shear `A₀` and the three untransported homotopies
  obtain ⟨A₀, H0, hH00, hH01, hH02, hH0end, hH0seam, hH0sm⟩ :=
    refExists_homotopies hγ.isEmbedding.injective hQ (angleRep u) (angleRep v) φ lam hlam
      1 one_pos
  -- ## the open set of parameters carrying the rows and the general position
  obtain ⟨R, hRopen, hRdense, hRows⟩ := refRows_open_posDense hQ u v φ lam hlam A₀
  refine ⟨R, hRopen, hRdense, ?_⟩
  intro t ht
  obtain ⟨hrows, hgp⟩ := hRows t ht
  -- ## the class parity of the perturbed reference triple at `t`
  refine refOdd_of_refRows hQ u v φ lam hlam A₀ H0 ?_ hH0end hH0seam hH0sm t hrows hgp
  intro k y
  fin_cases k
  · have h := hH00 y
    rwa [angleRep_coe] at h
  · have h := hH01 y
    rwa [angleRep_coe] at h
  · exact hH02 y

end

end Work.Drive
