import Mathlib
import Submission.Work.Drive.Mono.AE
import Submission.Work.Drive.Final.sweep_mono

/-!
# The tilted sweep at almost every cutting level

`Work.Drive.Final.TiltedSweepMono` is the residual of the fleet's route to Pardon's pinch: at every
configuration of the crux, and for the *given* cutting level `u`, there are tilt data whose sweep has
the dichotomy (D) and the no-drop field (L).  The counting of the sweep, however, is only available
when the level `u` avoids the critical values of the height `y (σ 2) ∘ K` on the box: at a tangency
the knot can graze the tilted slab without crossing it, and no count of the crux controls the grazing
visits (`Submission/Work/Drive/Mono/NOTES_H381_count_decoration.md` §4bis).

`Work.Drive.Mono.TiltedSweepMonoAE` below is the same residual with the level required only on a
conull set.  It is **weaker** than `TiltedSweepMono` (which implies it) and it **suffices** for the
a.e. crux, hence — through `Work.Drive.Mono.pardon_of_cruxCoreWdAE` — for the challenge; that is the
content of `Work.Drive.Mono.cruxCoreWdAE_of_tiltedSweepMonoAE`, which is
`Work.Drive.Final.cruxCoreWd_of_tiltedSweepMono` verbatim inside `Filter.Eventually.mono`.

So a prover of the pinch may choose the cutting level in general position (through the choice of the
tilt data, which are allowed to depend on `u`), which is exactly the freedom Pardon uses.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-- **The tilted sweep at almost every cutting level.**  Identical to
`Work.Drive.Final.TiltedSweepMono` except that the cutting level `u` is required only on a conull
set.  The tilt data are allowed to depend on `u` (they are inside the existential, after `u`), which
is the freedom that makes the counting of the sweep possible. -/
def TiltedSweepMonoAE (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
          ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
        ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          |u| < Submission.eps * r →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
            ‖v‖ = 1 ∧ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h ∧ 0 < h ∧
            (∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) ∧
            (∀ y ∈ Submission.PBox s c σ, lam0 < ℓ y) ∧
            (∀ y ∈ Submission.PBox s c σ, ℓ y < lam1) ∧ lam0 < lam1 ∧
            (∀ t ∈ exc, lam0 < t ∧ t < lam1) ∧
            (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
              Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                  (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ ∨
                Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                  (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊤) ∧
            (∀ lam ∈ Set.Icc lam0 lam1,
              Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                  (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ →
                ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
                  Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                    (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤)

/-- **The ordinary tilted sweep gives the a.e. one** (trivially: an a.e. statement follows from a
universal one). -/
theorem tiltedSweepMonoAE_of_tiltedSweepMono (h : Work.Drive.Final.TiltedSweepMono) :
    ∀ p q : ℕ, TiltedSweepMonoAE p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hS
  exact Filter.Eventually.of_forall fun u hu hU =>
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU

/-- **The a.e. tilted sweep gives the a.e. crux.**  This is
`Work.Drive.Final.cruxCoreWd_of_tiltedSweepMono` inside `Filter.Eventually.mono`. -/
theorem cruxCoreWdAE_of_tiltedSweepMonoAE (h : ∀ p q : ℕ, TiltedSweepMonoAE p q) :
    ∀ p q : ℕ, CruxCoreWdAE p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hS
  refine Filter.Eventually.mono
    (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hS) ?_
  intro u hdata hu hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hvtilt, hh, hR, hlow, hhigh, hl, hexc, hdich,
    hnodrop⟩ := hdata hu hU
  set P := Work.Drive.EpsSphere.torusOf ψ with hP
  have hs0 : 0 < s := lt_trans hr hrs
  -- the box region has span `⊤`
  have hnoS : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.EpsW.sphereTrace_inessential_of_countsWd p q hp hq hc ψ K hd himg hsmall hs0 c σ hslice
      hcl hS
  have hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr
      (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox)
  have hstart : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam0) = ⊤ := by
    rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_boxRegion hlow]
    exact Work.Drive.EpsForm.windingSpan_boxRegion_eq_top_of_sphereTrace_inessential hs0 hslice
      hnoS hne
  have hfin : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.Final.sweep P s c σ u v h ℓ lam1) ≠ ⊥ :=
    Work.Drive.Final.windingSpan_end_ne_bot_of_fields P s c σ u v h ℓ hstart hdich hnodrop
  obtain ⟨γ, hess, hγ⟩ := (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hfin
  simp only [Work.Drive.Final.sweep] at hγ
  have hγ' : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
    intro t
    rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_sdiff hhigh] at hγ
    exact hγ t
  exact Work.Drive.Final.exists_openHalf_of_essentialLoop_sdiff_tiltedSlabClosed
    P s c σ u v h R hvtilt hR hess hγ'

end

end Work.Drive.Mono
