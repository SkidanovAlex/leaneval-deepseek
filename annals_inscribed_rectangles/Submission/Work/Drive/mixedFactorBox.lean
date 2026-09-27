import Mathlib
import Submission.Work.Drive.mixedFactorTransfer
import Submission.Work.Drive.referenceClassCount

/-!
# The mixed factor `(F1)` of `hn2` in the **box count** form consumed by the transport's T6

`Work.Drive.odd_coreSideCountPt_reference_mixed` (`Drive/mixedFactorTransfer`) proves `(F1)` for the
*geometric* (parameterisation-free) count `coreSideCountPt`, while the multiplicativity T6 of the
transport (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_avoidance`) computes with
the **box** count `coreSideCount`.  The two agree exactly when the box parameterisation of the meet set
is injective (`Work.Drive.coreMeetPt_ncard_eq_iff`), which is the *faithfulness* datum the design's
`GoodPair`-type genericity supplies.  This file performs that wiring, so that the two mixed factors of
`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine` (`Drive/refTripleEndpoint`) are available in the
form the T6 instances need.

The two extra hypotheses are exactly the two clauses of the faithfulness:
`hfinBox` (finitely many box meets) and `hinjBox` (no two box meets share the loop parameter).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **`(F1)` for the mixed factors, in the box-count form.**  Same hypotheses as
`Work.Drive.odd_coreSideCountPt_reference_mixed`, plus the two faithfulness clauses of the box
parameterisation on the meet set. -/
theorem odd_coreSideCount_reference_mixed (Q' : ℂ → CappingSpace)
    (φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ σ : Eucl 3) {c' β' lam : ℝ} (hc' : 0 < c') (hlampos : 0 < lam)
    (hclow' : ∀ z : ℂ, ‖z‖ ≤ 1 → c' ≤ levelOf ((chartPert τ ∘ Q') z))
    (hβ' : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf ((chartPert τ ∘ Q') z) ≤ β')
    (hβ'lam : β' < ((levelScale σ ⟨lam, hlampos⟩ : Set.Ioi (0 : ℝ)) : ℝ))
    (V : ℝ → Eucl 3) (hVne : ∀ t : ℝ, V t ≠ 0)
    (hVcls : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Projectivization.mk ℝ (V t) (hVne t)
        = (cappingSpaceHomeoProj (coreLoop Q' t)).2)
    {κ : ℝ} (hκ : κ < 0) (hesse : V 1 = κ • V 0)
    (hV0 : Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
      (Work.Drive.classEquiv τ (V 0)) ≠ 0)
    (hder : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
        (Work.Drive.classEquiv τ (V t)))
        (deriv (fun t : ℝ => Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
          (Work.Drive.classEquiv τ (V t))) x) x)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
        (Work.Drive.classEquiv τ (V t)) = 0}).Finite)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
        (Work.Drive.classEquiv τ (V t)) = 0 →
      deriv (fun t : ℝ => Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
        (Work.Drive.classEquiv τ (V t))) t ≠ 0)
    (hinj : Set.InjOn (Work.Drive.coreLoop (chartPert τ ∘ Q'))
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
        (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.coreLoop (chartPert τ ∘ Q') t)).2
          ∈ Work.Drive.projLine (Work.Drive.linSub (φ.trans (Work.Drive.classEquiv σ)))})
    (hfinBox : (coreMeet (chartPert τ ∘ Q') c'
      (diskPlane (chartPert σ ∘ Work.Drive.linPlaneChart φ lam hlampos))).Finite)
    (hinjBox : Set.InjOn (fun p : ℝ × Work.Drive.Amb 2 => coreLoop (chartPert τ ∘ Q') p.1)
      (coreMeet (chartPert τ ∘ Q') c'
        (diskPlane (chartPert σ ∘ Work.Drive.linPlaneChart φ lam hlampos)))) :
    Odd (coreSideCount (chartPert τ ∘ Q') c'
      (diskPlane (chartPert σ ∘ Work.Drive.linPlaneChart φ lam hlampos))) :=
  odd_coreSideCount_of_meetPt_ncard_eq (chartPert τ ∘ Q') c'
    (diskPlane (chartPert σ ∘ Work.Drive.linPlaneChart φ lam hlampos)) hfinBox hinjBox
    (odd_coreSideCountPt_reference_mixed Q' φ τ σ hc' hlampos hclow' hβ' hβ'lam V hVne hVcls
      hκ hesse hV0 hder hfin hreg hinj)

end

end Work.Drive
