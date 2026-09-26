import Submission.Work.BoxShrink.Pinch.Main
import Submission.Assemble
import Submission.Shrink

/-!
# The migrated final input, and the challenge from the pinch

`Submission/Work/BoxShrink/assemble.lean`'s `Work.BoxShrink.FinalInput` carries the field
`bubble : Work.BoxShrink.Bubble.SmoothHalf`, which is **false** (`Bubble/Refutation.lean`), and the
field `bubble : BubbleSweep` of `Work.BoxShrink.Core.BubbleInput` is false as well
(`Bubble/no_bubble_field`).  The corrected datum is Pardon's Lemma 3 under *both* of his endpoint
hypotheses (`Work.BoxShrink.Pinch.SmoothHalfS`: the vanishing of the sphere trace *and* of the slice
trace), which is exactly what the crux's counting supplies.

This module is the two-line switch: `FinalInputS` is `FinalInput` with `bubble : SmoothHalfS`, and
everything above it (`cruxCore_of_finalInputS` → `cruxStatement_of_finalInputS` →
`boxShrink_of_finalInputS` → `pardon_torus_knot_distortion_of_finalInputS`) is proved here, so the
challenge follows from the corrected datum alone.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **The corrected final input**: `Work.BoxShrink.FinalInput` with the false field
`bubble : Work.BoxShrink.Bubble.SmoothHalf` replaced by the corrected Pardon-Lemma-3 datum
`Work.BoxShrink.Pinch.SmoothHalfS`. -/
structure FinalInputS : Prop where
  /-- the classical (planar) innermost-disc input at every flat disc cut out of a box by a plane -/
  cleansInDisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.InnermostDisk.CleansInSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (Work.BoxShrink.Core.cutDisc s c σ u)
  /-- Pardon's Lemma 3 for the smooth tori of the challenge, under both endpoint hypotheses -/
  bubble : SmoothHalfS
  /-- Pardon's cut-and-paste step at the surface -/
  cleans : Work.BoxShrink.CleansDiscsAll
  /-- almost every level of the box norm meets the surface in general position -/
  ae : Work.BoxShrink.AeSlicedAll

/-- The corrected final input from Pardon's Lemma 3 and the two classical inputs. -/
def finalInputS_of_smoothHalfS
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothHalfS) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) : FinalInputS where
  cleansInDisc := hdisc
  bubble := h
  cleans := hclean
  ae := hae

/-- The double-bubble core from the corrected final input. -/
theorem cruxCore_of_finalInputS (h : FinalInputS) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_smoothHalfS h.cleansInDisc h.bubble

/-- The crux from the corrected final input. -/
theorem cruxStatement_of_finalInputS (h : FinalInputS) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  fun p q => ⟨h.cleans, cruxCore_of_finalInputS h p q, h.ae⟩

/-- Pardon's shrinking step from the corrected final input. -/
theorem boxShrink_of_finalInputS (h : FinalInputS) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux (cruxStatement_of_finalInputS h)

/-- **Pardon's theorem from the corrected final input.** -/
theorem pardon_torus_knot_distortion_of_finalInputS (h : FinalInputS) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  fun p q hp hq hc K hclass =>
    Submission.theorem_of_core
      (Submission.CoreStatement_of_boxShrink (boxShrink_of_finalInputS h)) p q hp hq hc K hclass

end

end Work.BoxShrink.Pinch
