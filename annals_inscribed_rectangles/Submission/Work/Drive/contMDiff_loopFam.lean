import Mathlib
import Submission.Work.Drive.collapseT5
import Submission.Work.Drive.collapseTransport

/-!
# Smoothness of the two loop families of the radial-collapse transport (T5)

`Work.Drive.odd_ncard_diamMeet_iff_arcMeet` and `Work.Drive.odd_ncard_arcMeet_iff_core`
(`Submission/Work/Drive/collapseT5.lean`) consume the loop-vs-chain parity engine
`Work.Drive.odd_ncard_loopFamMeet_iff` with the smoothness of the two loop families
`Work.Drive.diamFam Q t` and `Work.Drive.arcFam Q t` as a hypothesis.  This file supplies it from the
smoothness of the chart `Q` alone: each family is `Q` composed with an explicit trigonometric function
of the two square coordinates.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

noncomputable section

/-- `colCirclePt` composed with a smooth real function is smooth. -/
private lemma contDiff_colCirclePt_comp {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : EuclideanSpace ℝ (Fin 2) => colCirclePt (f p)) := by
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => (Real.pi : ℂ) * ((f p : ℝ) : ℂ) * Complex.I) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hf)).mul contDiff_const
  simpa only [colCirclePt, Function.comp_def] using Complex.contDiff_exp.comp hlin

/-- **Smoothness of the diameter-to-arc interpolation family.** -/
theorem contMDiff_diamFam {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) (t : ℝ) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (diamFam Q t) := by
  have hz : ContMDiff (𝓡 2) (𝓘(ℝ, ℂ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        (((1 - p 0) * (1 - 2 * p 1) : ℝ) : ℂ) * colCirclePt t
          + ((p 0 : ℝ) : ℂ) * colCirclePt (t + p 1)) := by
    rw [contMDiff_iff_contDiff]
    have hp0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin 2) => p 0) := by fun_prop
    have hp1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin 2) => p 1) := by fun_prop
    have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin 2) => (((1 - p 0) * (1 - 2 * p 1) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        ((contDiff_const.sub hp0).mul (contDiff_const.sub (contDiff_const.mul hp1)))
    have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin 2) => ((p 0 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hp0
    have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin 2) => colCirclePt (t + p 1)) :=
      contDiff_colCirclePt_comp (contDiff_const.add hp1)
    exact (hA.mul contDiff_const).add (hB.mul hC)
  change ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : EuclideanSpace ℝ (Fin 2) => diamInterp Q t (p 0) (p 1))
  simpa only [diamInterp, Function.comp_def] using hQ.comp hz

/-- **Smoothness of the rotation family of the half-circle loop.** -/
theorem contMDiff_arcFam {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) (t : ℝ) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (arcFam Q t) := by
  have hz : ContMDiff (𝓡 2) (𝓘(ℝ, ℂ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => colCirclePt ((1 - p 0) * t + p 1)) := by
    rw [contMDiff_iff_contDiff]
    have hp0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin 2) => p 0) := by fun_prop
    have hp1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin 2) => p 1) := by fun_prop
    exact contDiff_colCirclePt_comp (((contDiff_const.sub hp0).mul contDiff_const).add hp1)
  change ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : EuclideanSpace ℝ (Fin 2) => arcRot Q t (p 0) (p 1))
  simpa only [arcRot, Function.comp_def] using hQ.comp hz

end

end Work.Drive
