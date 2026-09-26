import Mathlib
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.Drive.Mono.aboveGenericAt_of_junctionGen

namespace Work.Drive.Mono

noncomputable section

open LeanEval.KnotTheory.PardonDistortion Set in
open scoped ENNReal Topology in
/-- **Clause 2 at a point of the surface on the box sphere**, from the corrected junction bundle:
verbatim `Work.Drive.Mono.aboveGenericAt_of_boxSphere` with `JunctionGen` replaced by
`JunctionGenC`; only clause (a) of the bundle is used. -/
theorem aboveGenericAt_of_boxSphere_of_junctionGenC {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 lam : ℝ}
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1) (hlam : lam ∈ Set.Icc lam0 lam1)
    (hne : lam ∉ (exc : Set ℝ)) :
    ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∉ Submission.PBox s c σ →
      z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ∪
        ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  intro z hzc hznb hzcl hslab hzl
  -- `z ∈ closure PBox` together with `z ∉ PBox` forces `boxNorm c σ z = s`
  have hnorm_le : Submission.boxNorm c σ z ≤ s :=
    closure_minimal (fun _ hy => le_of_lt ((Submission.mem_PBox_iff s c σ _).mp hy))
      (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const) hzcl
  have hnorm : Submission.boxNorm c σ z = s := by
    refine le_antisymm hnorm_le ?_
    by_contra hlt
    exact hznb ((Submission.mem_PBox_iff s c σ z).mpr (lt_of_not_ge hlt))
  obtain ⟨p, hpar, hfne, hgne, hind⟩ := hJ.1 lam hlam hne z hzc hnorm hslab hzl
  refine Or.inl (Metric.mem_closure_iff.mpr fun ε hε => ?_)
  have hf : HasFDerivAt (Work.Drive.EpsForm.sweepHeight ψ ℓ)
      (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p) p :=
    (((Work.Smooth.Morse.pullback_contDiff_one ψ
        (ℓ.contDiff : ContDiff ℝ 1 (fun y : R3 => ℓ y))).contDiffAt.differentiableAt
      one_ne_zero)).hasFDerivAt
  have hg : HasFDerivAt (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q))
      (fderiv ℝ (fun q : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) p := by
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
      by_contra h
      rw [fderiv_zero_of_not_differentiableAt h] at hgne
      exact hgne rfl
    exact hd.hasFDerivAt
  have hfp : Work.Drive.EpsForm.sweepHeight ψ ℓ p = lam := by
    show ℓ (Work.BoxShrink.Pinch.par ψ p) = lam
    rw [hpar, hzl]
  have hgp : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s := by
    rw [hpar, hnorm]
  have hcont : ContinuousAt (Work.BoxShrink.Pinch.par ψ) p := by
    rw [Work.BoxShrink.Pinch.par_def]
    exact (Work.Smooth.Morse.param_continuous ψ).continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨q, hq, hqf, hqg⟩ := exists_near_lt_of_fderiv_indep hf hg hfne hgne hind δ hδpos
  -- the point `par ψ q` is in the open box and at a level strictly above `lam`
  have hbox : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) < s := by
    have h1 := hqg
    rw [hgp] at h1
    exact h1
  have hlvl : lam < ℓ (Work.BoxShrink.Pinch.par ψ q) := by
    have h1 := hqf
    rw [hfp] at h1
    exact h1
  refine ⟨Work.BoxShrink.Pinch.par ψ q, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Work.BoxShrink.Pinch.par_mem_carrier ψ q
  · exact (Submission.mem_PBox_iff s c σ _).mpr hbox
  · rintro ⟨-, hle⟩
    exact absurd hle (not_le.mpr hlvl)
  · have hd : dist (Work.BoxShrink.Pinch.par ψ q) z < ε := by
      have h1 : dist (Work.BoxShrink.Pinch.par ψ q) (Work.BoxShrink.Pinch.par ψ p) < ε :=
        hδ (by simpa [dist_eq_norm] using hq)
      rwa [hpar] at h1
    rwa [dist_comm] at hd

open LeanEval.KnotTheory.PardonDistortion Set in
open scoped ENNReal Topology in
/-- **Clause 2 of the trace data, from the corrected junction bundle.**

This is verbatim `Work.Drive.Mono.aboveGenericAt_of_junctionGen`
(`Submission/Work/Drive/Mono/aboveGenericAt_of_junctionGen.lean`) with the hypothesis
`Work.Drive.Mono.JunctionGen` replaced by the corrected bundle `Work.Drive.Mono.JunctionGenC`.
The resident proof uses only clause (a) of the bundle (through its auxiliary result
`Work.Drive.Mono.aboveGenericAt_of_boxSphere`, which takes the bundle but only ever uses its first
component), so the change is a pure type swap.  Proof strategy: copy the resident file, swap the
hypothesis type in both the auxiliary result and the main statement (a ≤ 3 line change, plus the
import of `JunctionGenC`), and the proofs go through unchanged. -/
theorem aboveGenericAt_of_junctionGenC {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 lam : ℝ}
    (hs : 0 < s)
    (hT : Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hJ : Work.Drive.Mono.JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (hlam : lam ∈ Set.Icc lam0 lam1) (hne : lam ∉ (exc : Set ℝ)) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  obtain ⟨hgen, _hv1, _hℓne, _hℓv, _hsize, _hh, _hRbox, _hlow, _hhigh, _hl, _hexc⟩ := hT
  have _ := hs
  intro z hzc hzcl hslab hzl
  by_cases hzb : z ∈ Submission.PBox s c σ
  · -- the open box: clause (i) of the genericity of the sweep height
    refine Or.inl (Metric.mem_closure_iff.mpr fun ε hε => ?_)
    obtain ⟨p₀, hp₀⟩ : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z := hzc
    have hreg : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀ ≠ 0 :=
      hgen.1 lam hne p₀ (by rw [hp₀]; exact hzb) (by rw [hp₀]; exact hslab)
        (by rw [hp₀]; exact hzl)
    have hsw : ContDiff ℝ 1 (Work.Drive.EpsForm.sweepHeight ψ ℓ) :=
      Work.Smooth.Morse.pullback_contDiff_one ψ
        (ℓ.contDiff : ContDiff ℝ 1 (fun y : R3 => ℓ y))
    have hF : HasFDerivAt (Work.Drive.EpsForm.sweepHeight ψ ℓ)
        (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀) p₀ :=
      (hsw.contDiffAt.differentiableAt one_ne_zero).hasFDerivAt
    have hswv : Work.Drive.EpsForm.sweepHeight ψ ℓ p₀ = lam := by
      show ℓ (Work.BoxShrink.Pinch.par ψ p₀) = lam
      rw [hp₀, hzl]
    have hboxopen : IsOpen (Submission.PBox s c σ) :=
      Work.Topology.SphereSlicing.isOpen_PBox s c σ
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.isOpen_iff.mp hboxopen z hzb
    have hcont : ContinuousAt (Work.BoxShrink.Pinch.par ψ) p₀ := by
      rw [Work.BoxShrink.Pinch.par_def]
      exact (Work.Smooth.Morse.param_continuous ψ).continuousAt
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont (min ε ρ) (lt_min hε hρpos)
    obtain ⟨q, hq, hqval⟩ := exists_near_gt_of_fderiv_ne_zero hF hreg δ hδpos
    have hdistz : dist (Work.BoxShrink.Pinch.par ψ q) z < min ε ρ := by
      have h1 : dist (Work.BoxShrink.Pinch.par ψ q) (Work.BoxShrink.Pinch.par ψ p₀) < min ε ρ :=
        hδ (by simpa [dist_eq_norm] using hq)
      rwa [hp₀] at h1
    have hlvl : lam < ℓ (Work.BoxShrink.Pinch.par ψ q) := by
      have h1 := hqval
      rw [hswv] at h1
      exact h1
    refine ⟨Work.BoxShrink.Pinch.par ψ q, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Work.BoxShrink.Pinch.par_mem_carrier ψ q
    · exact hρ (Metric.mem_ball.mpr (lt_of_lt_of_le hdistz (min_le_right _ _)))
    · rintro ⟨-, hle⟩
      exact absurd hle (not_le.mpr hlvl)
    · rw [dist_comm]
      exact lt_of_lt_of_le hdistz (min_le_left _ _)
  · -- on the box sphere: the junction genericity
    exact aboveGenericAt_of_boxSphere_of_junctionGenC hJ hlam hne z hzc hzb hzcl hslab hzl

end

end Work.Drive.Mono
