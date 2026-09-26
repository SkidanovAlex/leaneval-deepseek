import Mathlib
import Submission.Work.Drive.Mono.BoxGen
import Submission.Work.Drive.Mono.AEBridges

/-!
# The a.e. crux with the general position of the box sphere: `CruxCoreWdAEG`

`Work.Drive.Mono.CruxCoreWdAE` (`Mono/AE.lean`) is Pardon's crux with the cutting level only
required on a conull set.  Its *proof* by the tilted sweep, however, needs the box sphere
`{y | boxNorm c σ y = s}` to be in general position with respect to the surface **at that level**:
at a *graze* (the surface tangent to the box sphere) the trace of the sweep has junctions where the
trace is not a locally Euclidean curve, so the local models of `Mono/JunctionGen.lean` cannot be
applied, and the finite exceptional set of levels cannot absorb the (generally infinite) set of
graze levels.

`Work.Drive.Mono.CruxCoreWdAEG` below is the honest form: the same statement with
`Work.Drive.Mono.BoxGen ψ c σ s` as an extra **hypothesis**.  It is *weaker* than `CruxCoreWdAE`
(hence implied by it, `cruxCoreWdAEG_of_cruxCoreWdAE`, and by every route to the crux,
`cruxCoreWdAEG_of_tiltedSweepMono`), and the extra hypothesis costs nothing for the consumer:

* `Work.Drive.Mono.ae_boxGen` proves that `BoxGen ψ c σ s` holds for almost every `s`;
* `Work.Drive.Mono.exists_level_of_ae_count` produces the box level `s` in an *arbitrary* conull
  set, with the box-sphere count;
* hence `pardon_of_cruxCoreWdAEG` chooses `s` in the conull set
  `{BoxGen ∧ SlicedSphere}`, which is all the residual needs.

So replacing `CruxCoreWdAE` by `CruxCoreWdAEG` in the residual of the sweep *adds nothing* to its
proof obligations except the freedom to assume the box sphere is in general position at the level —
which is exactly what the tilted-sweep local models require.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-- **Pardon's crux at almost every cutting level, at a box level in general position.**

Identical to `Work.Drive.Mono.CruxCoreWdAE` except for the extra hypothesis
`BoxGen ψ c σ s` — the general position of the box sphere at the level `s`. -/
def CruxCoreWdAEG (p q : ℕ) : Prop :=
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
          (∃ γ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ),
              Work.CoreTopology.IsEssential _ γ ∧
                ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ γ t (σ 2) < c (σ 2) + u) ∨
          (∃ γ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ),
              Work.CoreTopology.IsEssential _ γ ∧
                ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ c (σ 2) + u < γ t (σ 2))

/-- **The a.e. crux implies its general-position form** (the extra hypothesis is simply discarded). -/
theorem cruxCoreWdAEG_of_cruxCoreWdAE (h : ∀ p q : ℕ, CruxCoreWdAE p q) :
    ∀ p q : ℕ, CruxCoreWdAEG p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  exact h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hS

/-- **Every route to the a.e. crux gives its general-position form.** -/
theorem cruxCoreWdAEG_of_tiltedSweepMono (h : Work.Drive.Final.TiltedSweepMono) :
    ∀ p q : ℕ, CruxCoreWdAEG p q :=
  cruxCoreWdAEG_of_cruxCoreWdAE (cruxCoreWdAE_of_tiltedSweepMono h)

/-- **Every route to the constancy form gives the general-position crux.** -/
theorem cruxCoreWdAEG_of_sweepSpanConst (h : SweepSpanConst) : ∀ p q : ℕ, CruxCoreWdAEG p q :=
  cruxCoreWdAEG_of_cruxCoreWdAE (cruxCoreWdAE_of_sweepSpanConst h)

end

end Work.Drive.Mono
