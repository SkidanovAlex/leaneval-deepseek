import Submission.Work.Drive.EpsForm.tiltedEps
import Submission.Work.Drive.EpsFormSphere.span_const_of_sweep_axioms

/-!
# The sweep-through: P1 + P2 + P3 + P4 give Pardon's `ε`-conclusion

This module assembles the four pieces of the lead's design into Pardon's `ε`-form, at the *stated*
interfaces (so it can be built while the four pieces are still being proved):

* **P1** supplies the tilted slab data — the unit normal `v` within `ε` of the `σ 2` direction, the
  half-width `h`, the wall functional `ℓ` parallel to the slab, the two end levels `lam0 < lam1` and
  the finite set `exc` of critical levels — plus the inclusion `R` of the box in the ball of radius
  `R` and the size estimate `ε·R < h` that Pardon's perturbation needs;
* **P2** is the hypothesis `hreg` on the swept region: between two levels with no critical value in
  between the winding span is constant;
* **P3** is `hjump`: crossing a single critical level changes the `H₁`-image rank by at most one;
* **P4** is `hdich`: at every regular level the span is `⊥` or `⊤`.

The bookkeeping is `Work.Drive.EpsFormSphere.span_const_of_sweep_axioms` (proved): the span at
`lam1` equals the span at `lam0`; since the box region at `lam0` carries an essential loop (the
crux's `HasEssBox`, hypothesis `h0`), the end region `boxRegion \ tiltedSlab` does too, and
`Work.Drive.EpsForm.epsConclusion_of_essentialLoop_sdiff_tiltedSlab` (proved) turns that loop into
the `ε`-conclusion of Pardon's `doublebubble2`, in its solid form.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

/-- **The sweep-through.**  From P1's tilted data, P2 (`hreg`), P3 (`hjump`), P4 (`hdich`), the two
end fields and the crux's essential loop in the box region, Pardon's `ε`-conclusion follows: an
essential loop of the surface lies within `ε` of one of the two solid half-boxes of the *untitled*
cutting plane. -/
theorem epsConclusion_of_sweep_axioms {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h ε R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {lam0 lam1 : ℝ} {exc : Finset ℝ}
    (hε : 0 < ε) (hv1 : ‖v‖ = 1) (hv : ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ ε)
    (hR : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) (hsize : ε * R < h)
    (hl : lam0 < lam1) (hexc : ∀ t ∈ exc, lam0 < t ∧ t < lam1)
    (hstart : Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam0 =
      Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
    (hfinish : Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam1 =
      Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ \
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h)
    (hreg : ∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 → (∀ t ∈ exc, t < μ ∨ ν < t) →
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
            (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ μ) =
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
            (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ ν))
    (hjump : ∀ lam ∈ exc, ∀ μ ν : ℝ, lam0 ≤ μ → μ < lam → lam < ν → ν ≤ lam1 →
      (∀ t ∈ exc, t < μ ∨ t = lam ∨ ν < t) →
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
            (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ μ)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
            (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ ν)) + 1 ∧
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
            (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ ν)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
            (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ μ)) + 1)
    (hdich : ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
            (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
            (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam) = ⊤)
    (h0 : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) ≠ ⊥) :
    (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
        Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) γ ∧
          ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ x (σ 2) < c (σ 2) + u ∧
            dist (γ t) x < ε) ∨
      (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
        Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) γ ∧
          ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ c (σ 2) + u < x (σ 2) ∧
            dist (γ t) x < ε) := by
  classical
  -- the swept region as a function of the level
  have hmono : ∀ μ ν : ℝ, μ ≤ ν →
      (fun lam : ℝ => Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
          (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam) ν ⊆
      (fun lam : ℝ => Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
          (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam) μ := by
    intro μ ν hμν y hy
    simp only [mem_sweepRegion] at hy ⊢
    exact ⟨hy.1, hy.2.1, fun hyW => le_trans hμν (hy.2.2 hyW)⟩
  have hspan := Work.Drive.EpsFormSphere.span_const_of_sweep_axioms (Work.Smooth.Morse.torus ψ)
    (fun lam : ℝ => Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam)
    lam0 lam1 exc hl hexc hmono hreg hjump hdich
  -- the span at the end level is the span at the start level, hence non-`⊥`
  have hspan' : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam1) =
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
          (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam0) := hspan.symm
  have hne : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam1) ≠ ⊥ := by
    rw [hspan', hstart]
    exact h0
  obtain ⟨γ, hess, hγ⟩ := (Work.SurgeryInvariance.windingSpan_ne_bot_iff
    (Work.Smooth.Morse.torus ψ) (Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam1)).mp hne
  -- the loop lies in the end region, hence off the (open) tilted slab
  have hγ' : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ \
      Work.Drive.EpsForm.tiltedSlab (inner ℝ v c + u) v h := by
    intro t
    have h1 : γ t ∈ Work.Drive.EpsForm.sweepRegion (Work.Smooth.Morse.torus ψ) s c σ
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ℓ lam1 := hγ t
    rw [hfinish] at h1
    exact ⟨h1.1, fun hs => h1.2 (tiltedSlab_subset_tiltedSlabClosed _ _ _ hs)⟩
  exact epsConclusion_of_essentialLoop_sdiff_tiltedSlab hε hv1 hv hR hsize hess hγ'

end Work.Drive.EpsForm
