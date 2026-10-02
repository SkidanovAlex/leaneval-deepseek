import Mathlib
import Submission.Work.Thom.tautQuotientComap
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.NowhereZeroDefs
import Submission.Work.Whitney.NowhereZeroChart
import Submission.Work.Whitney.NowhereZeroFunctional

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

namespace Work.Whitney

open Work.TangentClasses Work.Thom

theorem nonempty_bundleIso_of_nowhereZeroSection_of_paracompact {B : Type} [TopologicalSpace B]
    [ParacompactSpace B] [T2Space B] {ι : Type} [Fintype ι] {m : ℕ}
    (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).1 = b)
    {ι₀ : Type} [Inhabited ι₀] :
    Nonempty (Work.Thom.BundleIso V
      (Work.Whitney.whitneySum (Work.Thom.bundleComap (Work.Thom.tautQuotient V) σ)
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀))) := by
  obtain ⟨ℓ, hℓ1, hℓc⟩ := NZ.exists_splittingFunctional V σ hσ
  refine ⟨{ hom := fun b => (NZ.homCLM V σ ℓ b).toLinearMap
            inv := fun b => (NZ.invCLM V σ ℓ b).toLinearMap
            left_inv := fun b x => ?_
            right_inv := fun b y => ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · exact NZ.invCLM_homCLM_apply ℓ hσ hℓ1 b x
  · exact NZ.homCLM_invCLM_apply ℓ hσ hℓ1 b y
  · refine (Work.Thom.continuous_totalSpaceMap_clm_gen V (NZ.W V σ) (ContinuousMap.id B)
      (fun b => NZ.homCLM V σ ℓ b) (fun i₁ i₂ => ?_)).congr (fun p => rfl)
    exact NZ.continuousOn_hom_chart ℓ hσ hℓc hℓ1 i₁ i₂
  · refine (Work.Thom.continuous_totalSpaceMap_clm_gen (NZ.W V σ) V (ContinuousMap.id B)
      (fun b => NZ.invCLM V σ ℓ b) (fun i₁ i₂ => ?_)).congr (fun p => rfl)
    exact NZ.continuousOn_inv_chart ℓ hσ hℓc hℓ1 i₁ i₂

end Work.Whitney
