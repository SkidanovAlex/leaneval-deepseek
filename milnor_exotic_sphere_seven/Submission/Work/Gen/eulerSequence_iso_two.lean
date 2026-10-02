import Mathlib
import Submission.Work.Gen.EulerDefs
import Submission.Work.Gen.Euler
import Submission.Work.Gen.Basic
import Submission.Work.Whitney.Basic
import Submission.Work.Gen.EulerToolkit
import Submission.Work.GenTwo.GaugeInverse
import Submission.Work.GenTwo.Continuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

open Work.Projective

/-- **The complexified Euler sequence of `ℂP²`**, in the form used by the `n = 2` Chern-class
computation: `ℂ ⊗ TℝℂP² ⊕ ε² ≅ (ℂ ⊗ O(1))³`. -/
theorem eulerSequence_iso_two :
    Nonempty (Work.Thom.BundleIso
      (Work.Whitney.whitneySum (Work.Gen.stdTangentC 2)
        (trivialVectorBundleCore ℂ (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 1)))
      (Work.Whitney.whitneySum (Work.Gen.lineC 2)
        (Work.Whitney.whitneySum (Work.Gen.lineC 2) (Work.Gen.lineC 2)))) := by
  show Nonempty (Work.Thom.BundleIso Work.Gen.E2.Src Work.Gen.E2.Tgt)
  obtain ⟨_, _, hgauge, hgaugeinv⟩ := Work.Gen.E2.gauge_continuous
  refine Work.Thom.nonempty_bundleIso_of_gauge Work.Gen.E2.Src Work.Gen.E2.Tgt
    (fun i t b => Work.Gen.E2.gaugeCLM i.1 t b)
    (fun i t b => Work.Gen.E2.gaugeInvCLM i.1 t b)
    (fun i i' => ?_) (fun i i' => ?_) ?_ ?_ ?_ ?_ ?_ ?_
  · exact hgauge i.1 i.2 i'
  · exact hgaugeinv i.1 i.2 i'
  · exact Work.Gen.E2.gauge_htgt
  · exact Work.Gen.E2.gauge_hsrc
  · exact Work.Gen.E2.gauge_htgtinv
  · exact Work.Gen.E2.gauge_hsrcinv
  · intro i i' b x hb
    have hp : b ∈ Work.Projective.chartSet i.1 := by
      have h : b ∈ (Work.Gen.stdTangentC 2).baseSet i.1 := by
        have h1 := hb.1
        rw [Work.Gen.E2.Src, Work.Whitney.whitneySum_baseSet] at h1
        exact h1.1
      rwa [Work.Gen.E2.stdTangentC_baseSet_two] at h
    simpa using Work.Gen.apply_congr (Work.Gen.E2.gaugeInvCLM_gaugeCLM i.1 i' hp hb.2) x
  · intro i i' b y hb
    have hp : b ∈ Work.Projective.chartSet i.1 := by
      have h : b ∈ (Work.Gen.stdTangentC 2).baseSet i.1 := by
        have h1 := hb.1
        rw [Work.Gen.E2.Src, Work.Whitney.whitneySum_baseSet] at h1
        exact h1.1
      rwa [Work.Gen.E2.stdTangentC_baseSet_two] at h
    simpa using Work.Gen.apply_congr (Work.Gen.E2.gaugeCLM_gaugeInvCLM i.1 i' hp hb.2) y

end Work.Gen
