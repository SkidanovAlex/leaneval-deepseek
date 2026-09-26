import Mathlib
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.AEGen

/-!
# The general-position crux with the junction genericity: `CruxCoreWdAEG2`

`Work.Drive.Mono.CruxCoreWdAEG` (`Mono/AEGen.lean`) is Pardon's crux with the cutting level required
only on a conull set and the box level required to be in general position (`Work.Drive.Mono.BoxGen`).
The junction route needs the *stronger* box genericity `Work.Drive.Mono.BoxGenE` (the finiteness of
the vertical edge locus and, for almost every cutting level, the pair regularity of the face
crossing and the absence of a bend at a vertical-tangent crossing of the box trace).

`Work.Drive.Mono.CruxCoreWdAEG2` below is `CruxCoreWdAEG` with `BoxGen` replaced by `BoxGenE`; it is
implied by `CruxCoreWdAEG` (which is implied by every route to the a.e. crux), and the consumer
`Work.Drive.Mono.boxShrink_of_cruxCoreWdAEG2` (in `Mono/AEGenConsumer2.lean`) shows that the extra
genericity is free: the box centre may be shifted along the diagonal
(`Work.Drive.Mono.boxGenE_pairSard`) into the conull set, and the level is chosen in a conull set
anyway.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-- **Pardon's crux at almost every cutting level, at a box level in general position.**

Identical to `Work.Drive.Mono.CruxCoreWdAEG` except that the hypothesis is the stronger
`BoxGenE ψ c σ s` — the general position of the box sphere at the level `s`, with the junction genericity. -/
def CruxCoreWdAEG2 (p q : ℕ) : Prop :=
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
        BoxGenE ψ c σ s →
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

/-- **`CruxCoreWdAEG` implies its `BoxGenE` form** (the extra hypothesis is discarded). -/
theorem cruxCoreWdAEG2_of_cruxCoreWdAEG (h : ∀ p q : ℕ, CruxCoreWdAEG p q) :
    ∀ p q : ℕ, CruxCoreWdAEG2 p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  exact h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG.1 hS

/-- **The a.e. crux implies its `BoxGenE` form** (the extra hypothesis is discarded). -/
theorem cruxCoreWdAEG2_of_cruxCoreWdAE (h : ∀ p q : ℕ, CruxCoreWdAE p q) :
    ∀ p q : ℕ, CruxCoreWdAEG2 p q :=
  cruxCoreWdAEG2_of_cruxCoreWdAEG (cruxCoreWdAEG_of_cruxCoreWdAE h)

end

end Work.Drive.Mono
