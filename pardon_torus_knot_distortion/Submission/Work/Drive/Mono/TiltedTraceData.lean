import Mathlib
import Submission.Work.Drive.Final.sweep_mono

/-!
# The trace data of the tilted sweep, as a residual

`Work.Drive.Final.TiltedSweepMono` (`sweep_mono.lean`) carries two span fields at the data of the
tilted sweep:

* **(D)** at every level outside the finite exceptional set the span of the swept region is `⊥` or
  `⊤` (Pardon's dichotomy, from the trace of the level being a family of pairwise disjoint simple
  *inessential* closed curves: `Work.Drive.Final.dichotomy_of_levelTrace`, proved);
* **(L)** no level with span `⊥` is reached by a drop from `⊤` (the "no-jump" content of Pardon's
  pinching lemma: `Work.Drive.Mono.ne_top_left_of_trace`, which turns the trace data at a level
  into the no-drop statement just below it).

This module isolates the *geometric* input which feeds both fields, so that the two fields become
theorems of a single clearly-stated residual:

`TiltedTraceData P s c σ u v h ℓ exc` is the conjunction of

1. at every level `lam ∉ exc`, the trace `F ∩ frontier (removed lam)` of the level is the union of
   the ranges of finitely many pairwise disjoint simple closed curves of `F`, each **inessential**
   in `F` (Pardon's Lemma 2 applied at the level, with the crux's counting);
2. at every level `lam ∉ exc`, every point of `F` in the closed box and the closed tilted slab at
   the level `lam` is a limit of points of the region `X lam` (the stratified genericity of the
   level: the level is not a local maximum of `ℓ|_F` there);
3. at every *exceptional* level `lam ∈ exc`, no level just below `lam` carries the full span (the
   no-drop at the finitely many non-transverse levels — the only place where Pardon's surgery
   count on the *intermediate* members of his pinching family is spent).

`Work.Drive.Mono.tiltedSweepMono_of_traceData` (the sibling module) then derives
`Work.Drive.Final.TiltedSweepMono` from it, hence — through the proved chain of `sweep_mono.lean`
and `pardon_unconditional.lean` — Pardon's distortion bound.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.Mono

noncomputable section

/-- The removed set of one level of the tilted sweep (the *open*-wall spelling, whose frontier
agrees with that of the region `openTiltedSweepRegion`). -/
def tiltedLevelRemoved (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  Submission.PBox s c σ \
    (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam})

/-- **The trace data of the tilted sweep** (the residual): the level's trace is a family of
pairwise disjoint simple inessential closed curves covering it, the level is approached from above
on the surface, and at the exceptional levels there is no drop of the span to `⊥`. -/
def TiltedTraceData (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ)
    (exc : Finset ℝ) : Prop :=
  (∀ lam : ℝ, lam ∉ (exc : Set ℝ) → ∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve P),
      (∀ i, Work.CoreTopology.IsSimple P (cs i)) ∧
      (∀ i, ¬ Work.CoreTopology.IsEssential P (cs i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
      (⋃ i, Set.range (cs i).γ) =
        P.carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) ∧
  (∀ lam : ℝ, lam ∉ (exc : Set ℝ) → ∀ z : R3, z ∈ P.carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam)) ∧
  (∀ lam : ℝ, lam ∉ (exc : Set ℝ) →
      Work.SurgeryInvariance.WindingSpan P
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) = ⊥ →
      ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
        Work.SurgeryInvariance.WindingSpan P
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu) ≠ ⊤) ∧
  (∀ lam : ℝ, lam ∈ (exc : Set ℝ) →
      Work.SurgeryInvariance.WindingSpan P
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) = ⊥ →
      ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
        Work.SurgeryInvariance.WindingSpan P
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu) ≠ ⊤)

end

end Work.Drive.Mono
