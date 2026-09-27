import Mathlib
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Drive.N2Lead.modelArc_im_strictMonoOn
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2.saddleModelPsi

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

noncomputable section

/-- **The model curve `ζ` avoids the branch slit.**  For `0 < δ < 1/2` and `s > 0` the point
`ζ w = σ (s, w) + i w` lies in `Complex.slitPlane` for every `w : ℝ`. -/
lemma modelZeta_mem_slitPlane {η δ s : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s) (w : ℝ) :
    modelZeta η δ s w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hw : w = 0
  · left
    rw [modelZeta_re, hw, modelSigma_eq, saddleM_zero hδ (by linarith), zero_mul, add_zero]
    exact hs
  · right
    rwa [modelZeta_im]

/-- **The model curve `ζ` is `C^∞`.** -/
lemma contDiff_modelZeta {η δ s : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => modelZeta η δ s w) := by
  have h2 : 0 < 2 - 4 * δ := by linarith
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => (s, w)) :=
    (contDiff_const (c := s)).prodMk contDiff_id
  have hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => (modelSigma η δ s w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_saddleSigma η δ hδ h2).comp hpair)
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => (w : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_id).mul (contDiff_const (c := Complex.I))
  exact hσ.add hw

/-- **The model arc `w ↦ √(ζ w)` is `C^∞`.** -/
theorem mobiusRho_contDiff {η δ s : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mobiusRho η δ s) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  have hsqrt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.sqrt (modelZeta η δ s w) :=
    contDiffAt_sqrt_of_mem_slitPlane (modelZeta_mem_slitPlane hδ hδ₂ hs w)
  have hz : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => modelZeta η δ s y) w :=
    (contDiff_modelZeta (η := η) hδ hδ₂).contDiffAt
  exact hsqrt.comp w hz

/-- `v ↦ twistY a s v` is `C^∞`. -/
lemma contDiff_twistY_apply (a s : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : E3 => twistY a s v) :=
  (contDiff_twistY a).comp ((contDiff_const (c := s)).prodMk contDiff_id)

/-- `v ↦ twistX ε s v` is `C^∞`. -/
lemma contDiff_twistX_apply (ε s : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : E3 => twistX ε s v) :=
  (contDiff_twistX ε).comp ((contDiff_const (c := s)).prodMk contDiff_id)

/-- **The twisted arcs are as smooth as the model arc.** -/
lemma contDiff_twisted {a ε : ℝ} {g : ℝ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ 1 (fun w : ℝ => twistX ε (-1) (twistY a (-1) (Work.Drive.N2.cE3 (g w)))) :=
  (((contDiff_twistX_apply ε (-1)).comp
      ((contDiff_twistY_apply a (-1)).comp (Work.Drive.N2.cE3.contDiff.comp hg)))).of_le (by simp)

/-- The twisted left model arc `mobiusAlpha` is `C¹`. -/
theorem mobiusAlpha_contDiff {η δ s a ε : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s) :
    ContDiff ℝ 1 (mobiusAlpha η δ s a ε) :=
  contDiff_twisted (g := fun w : ℝ => -(mobiusRho η δ s w))
    ((mobiusRho_contDiff (η := η) hδ hδ₂ hs).neg)

/-- The twisted right model arc `mobiusBeta` is `C¹`. -/
theorem mobiusBeta_contDiff {η δ s a ε : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s) :
    ContDiff ℝ 1 (mobiusBeta η δ s a ε) :=
  contDiff_twisted (g := mobiusRho η δ s) (mobiusRho_contDiff (η := η) hδ hδ₂ hs)

end

open scoped Manifold ContDiff Topology in
/-- **The model arc and its two twists are smooth.**  Let
`ζ w = σ (s,w) + i w` (`σ(s,w) = s + saddleM δ w * (-η - s)`, `saddleModelPsi.lean`), so that
`mobiusRho η δ s w = √(ζ w)` is the model arc of the level `Re ζ = s` in `ζ = Z²` coordinates, and
`mobiusAlpha`, `mobiusBeta` are the two arcs after the slab twists `twistY a (-1)` and
`twistX ε (-1)`.  Then

* `w ↦ √(ζ w)` is `C^∞` on `ℝ`: the curve `ζ` never meets the branch slit `(-∞, 0]`, because its
  imaginary part is `w` (and at `w = 0` the real part is `s > 0`, since the plateau `saddleM δ`
  vanishes there and `0 < δ < 1/2`);
* the twisted arcs are `C¹` as soon as `a ≠ 0` and `ε ≠ 0`.

This is the smoothing row that the certificate assembly needs in order to feed the arcs to
`Work.Drive.N2Lead.mobius_pushedStar` (whose hypothesis is `ContDiff ℝ 1 g`).  The tool is
`Work.Drive.N2.contDiffAt_sqrt_of_mem_slitPlane` (`saddleModelPsi.lean`, proved from
`Complex.contDiffAt_log`), together with `contDiff_saddleM`/`contDiff_saddleSigma`. -/
theorem mobiusArcSmooth {η δ s a ε : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hη : 0 < η) (hs : 0 < s)
    (ha : a ≠ 0) (hε : ε ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.N2Lead.mobiusRho η δ s) ∧
      ContDiff ℝ 1 (Work.Drive.N2Lead.mobiusAlpha η δ s a ε) ∧
      ContDiff ℝ 1 (Work.Drive.N2Lead.mobiusBeta η δ s a ε) :=
  ⟨mobiusRho_contDiff hδ hδ₂ hs, mobiusAlpha_contDiff hδ hδ₂ hs, mobiusBeta_contDiff hδ hδ₂ hs⟩

end Work.Drive.N2Lead
