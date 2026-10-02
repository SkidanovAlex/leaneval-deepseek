import Mathlib
import Submission.Work.Gen.EulerBundles
import Submission.Work.Gen.EulerGaugeIdentity
import Submission.Work.Gen.EulerBlockInverse
import Submission.Work.Gen.EulerGaugeInverse
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Gen.gauge_continuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.Gen

open Work.Projective

/-- **The complexified Euler sequence of `ℂP⁴`**:
`(TℂP⁴ ⊗_ℝ ℂ) ⊕ ε² ≅ (ℂ ⊗ O(1))⁵`. -/
theorem eulerSequence_iso :
    Nonempty (Work.Thom.BundleIso
      (Work.Whitney.whitneySum (Work.Gen.stdTangentC 4)
        (trivialVectorBundleCore ℂ (Work.Projective.CP 4) (EuclideanSpace ℂ (Fin 2)) (Fin 1)))
      Work.Gen.eulerTarget) := by
  show Nonempty (Work.Thom.BundleIso Work.Gen.Src Work.Gen.Tgt)
  obtain ⟨hclm, hclminv, hgauge, hgaugeinv⟩ := Work.Gen.gauge_continuous
  refine Work.Thom.nonempty_bundleIso_of_gauge Work.Gen.Src Work.Gen.Tgt
    (fun i t b => Work.Gen.gaugeCLM i.1 t b)
    (fun i t b => Work.Gen.gaugeInvCLM i.1 t b)
    (fun i i' => ?_) (fun i i' => ?_) ?_ ?_ ?_ ?_ ?_ ?_
  · exact hgauge i.1 i.2 i'
  · exact hgaugeinv i.1 i.2 i'
  · exact Work.Gen.gauge_htgt
  · exact Work.Gen.gauge_hsrc
  · exact Work.Gen.gauge_htgtinv
  · exact Work.Gen.gauge_hsrcinv
  · intro i i' b x hb
    have hp : b ∈ Work.Projective.chartSet i.1 := by
      have h : b ∈ (Work.Gen.stdTangentC 4).baseSet i.1 := by
        have h1 := hb.1
        rw [Work.Gen.Src, Work.Whitney.whitneySum_baseSet] at h1
        exact h1.1
      rwa [Work.Gen.stdTangentC_baseSet] at h
    simpa using Work.Gen.apply_congr (Work.Gen.gaugeInvCLM_gaugeCLM i.1 i' hp hb.2) x
  · intro i i' b y hb
    have hp : b ∈ Work.Projective.chartSet i.1 := by
      have h : b ∈ (Work.Gen.stdTangentC 4).baseSet i.1 := by
        have h1 := hb.1
        rw [Work.Gen.Src, Work.Whitney.whitneySum_baseSet] at h1
        exact h1.1
      rwa [Work.Gen.stdTangentC_baseSet] at h
    simpa using Work.Gen.apply_congr (Work.Gen.gaugeCLM_gaugeInvCLM i.1 i' hp hb.2) y

end Work.Gen
