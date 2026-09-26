import Mathlib
import Submission.Work.Drive.EpsFormSphere.Defs
import Submission.Work.Drive.pardon_of_cleansW_sphere

/-!
# Pardon's Lemma 3 in its *exact* (open half) form, in the honest (`Wd`) vocabulary

`Work.Drive.EpsSphere.CountingHalfEpsSphere` is Pardon's `doublebubble2` (the ε-form, a loop within
`ε` of the *trace* of a half box).  This file records the **stronger, exact** form of the same
statement at the same counted configurations — Pardon's `doublebubble` before the perturbation: an
essential loop of the surface inside the *open* upper half of the box, or inside the *open* lower
half.  It is the form the sweep naturally produces (with the *corrected* size condition
`‖v − e_{σ2}‖·R < h`, see `Submission/Work/Drive/Final/sweep_half.lean`), and it is the form the
halving geometry consumes directly (`Work.BoxShrink.hasEssBox_of_upperHalf` /
`hasEssBox_of_lowerHalf`) — no `ε`-margin is needed.

The hypotheses are exactly those of `Work.Drive.EpsSphere.CountingHalfEpsSphere` — in particular the
*corrected* cut-and-paste `Work.Drive.CleansDiscsWd` (the refuted `CleansDiscsW` does not occur) —
and the conclusion is the exact open half.

Everything here is proved; the single statement left open is `CruxCoreWd` itself, i.e. Pardon's
counted pinching argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Drive.Final

noncomputable section

/-- **Pardon's Lemma 3, exact form**: at every configuration carrying the counted crux data there is
an essential loop of the surface lying in the *open* upper half of the box `PBox s c σ`, or in its
*open* lower half. -/
def CruxCoreWd (p q : ℕ) : Prop :=
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
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          (∃ γ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ),
              Work.CoreTopology.IsEssential _ γ ∧
                ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ γ t (σ 2) < c (σ 2) + u) ∨
          (∃ γ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ),
              Work.CoreTopology.IsEssential _ γ ∧
                ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ c (σ 2) + u < γ t (σ 2))

/-- **The exact form implies the ε-form** `Work.Drive.EpsSphere.CountingHalfEpsSphere`: a loop
inside the open upper half of the box is within distance `0 < ε` of the upper half-*region*, and
dually. -/
theorem countingHalfEpsSphere_of_cruxCoreWd (h : ∀ p q : ℕ, CruxCoreWd p q) :
    Work.Drive.EpsSphere.CountingHalfEpsSphere := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  rcases h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    with ⟨γ, hγ, hmem⟩ | ⟨γ, hγ, hmem⟩
  · -- the loop lies strictly below the cutting plane: the lower half-region
    refine Or.inr ⟨γ, hγ, fun t => ?_⟩
    obtain ⟨hP, hlt⟩ := hmem t
    exact Metric.self_subset_thickening hε _
      ⟨⟨γ.mem t, hP⟩, by simpa [Work.BoxShrink.Core.lowerHalf, Work.BoxShrink.Core.cutPlane] using hlt⟩
  · -- the loop lies strictly above the cutting plane: the upper half-region
    refine Or.inl ⟨γ, hγ, fun t => ?_⟩
    obtain ⟨hP, hgt⟩ := hmem t
    exact Metric.self_subset_thickening hε _
      ⟨⟨γ.mem t, hP⟩, by simpa [Work.BoxShrink.Core.upperHalf, Work.BoxShrink.Core.cutPlane] using hgt⟩

open LeanEval.KnotTheory.PardonDistortion in
open scoped ENNReal in
/-- **Pardon's distortion bound for torus knots, from the exact form of his pinching lemma.** -/
theorem pardon_unconditional_of_cruxCoreWd (h : ∀ p q : ℕ, CruxCoreWd p q)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.Drive.pardon_of_cleansWd_of_epsSphere (countingHalfEpsSphere_of_cruxCoreWd h)
    p q hp hq hc K hclass

end

end Work.Drive.Final
