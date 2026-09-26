import Mathlib
import Submission.Work.Drive.Mono.BoxGen
import Submission.Work.Drive.Mono.AEGen
import Submission.Work.Drive.Mono.AESweep

/-!
# The tilted sweep at almost every cutting level, at a box level in general position

`Work.Drive.Mono.TiltedSweepMonoAE` (`Mono/AESweep.lean`) is `Work.Drive.Final.TiltedSweepMono`
with the cutting level `u` required only on a conull set.  The tilted-sweep route to the crux,
however, needs in addition the *box level* `s` to be in general position
(`Work.Drive.Mono.BoxGen ψ c σ s`, a.e. by `Work.Drive.Mono.ae_boxGen`): at a *graze* of the surface
with the box sphere the trace of the sweep has junctions that are not locally Euclidean, and the set
of graze levels is generally infinite, so no finite exceptional set of levels can absorb it (see
`Mono/NOTES_H381_boxgen_thread.md` §2).

`Work.Drive.Mono.TiltedSweepMonoAEG` below is the honest form: the tilted sweep with (i) the
cutting level on a conull set and (ii) `BoxGen ψ c σ s` as an extra hypothesis.  It is weaker than
both `Work.Drive.Final.TiltedSweepMono` and `TiltedSweepMonoAE`, and it implies the crux in the
form the deliverable uses (`Work.Drive.Mono.CruxCoreWdAEG`), since the box level of the crux may be
chosen in an *arbitrary* conull set (`Work.Drive.Mono.exists_level_of_ae_count`).
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The tilted sweep at almost every cutting level, at a box level in general position.**
Identical to `Work.Drive.Mono.TiltedSweepMonoAE` except for the extra hypothesis
`Work.Drive.Mono.BoxGen ψ c σ s`. -/
def TiltedSweepMonoAEG (p q : ℕ) : Prop :=
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
        BoxGen ψ c σ s →
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

/-- **The ordinary tilted sweep gives the general-position one** (the extra hypothesis is discarded
and the universal statement is weakened to the a.e. one). -/
theorem tiltedSweepMonoAEG_of_tiltedSweepMono (h : Work.Drive.Final.TiltedSweepMono) :
    ∀ p q : ℕ, TiltedSweepMonoAEG p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  exact Filter.Eventually.of_forall fun u hu hU =>
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU

/-- **The a.e. general-position tilted sweep gives the general-position crux.**  This is
`Work.Drive.Mono.cruxCoreWdAE_of_tiltedSweepMonoAE` (`Mono/AESweep.lean`) with the `BoxGen`
hypothesis threaded through to `Work.Drive.Mono.CruxCoreWdAEG`. -/
theorem cruxCoreWdAEG_of_tiltedSweepMonoAEG (h : ∀ p q : ℕ, TiltedSweepMonoAEG p q) :
    ∀ p q : ℕ, CruxCoreWdAEG p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  refine Filter.Eventually.mono
    (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS) ?_
  intro u hdata hu hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hvtilt, hh, hR, hlow, hhigh, hl, hexc, hdich,
    hnodrop⟩ := hdata hu hU
  set P := Work.Drive.EpsSphere.torusOf ψ with hP
  have hs0 : 0 < s := lt_trans hr hrs
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
