import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Core.Crux

/-!
# Closing the crux with the push-off only for the smooth tori of the challenge

`Work.BoxShrink.Core.cruxCore_of_bubbleInput` consumes the field `bubble` of
`Work.BoxShrink.Core.BubbleInput`, which is quantified over *all* parametrised tori, but it
instantiates it at a single place: `P = ParamTorus.mapHomeomorph ψ.toHomeomorph`, the smooth torus
of the challenge.  This file makes that explicit: it re-proves the double-bubble core with the field
available **only for those smooth tori**

* `Work.BoxShrink.Bubble.RestrictedInput` — the restricted field: `BubbleSweep` for
  `P = ParamTorus.mapHomeomorph ψ.toHomeomorph` whenever the two cuts carry no essential loop
  (together with the planar innermost-disc input, which is the other field of `BubbleInput`);
* `Work.BoxShrink.Bubble.cruxCore_of_restrictedInput` — **the double-bubble core from the restricted
  field** (a verbatim replay of `cruxCore_of_bubbleInput`), and
  `Work.BoxShrink.Bubble.crux_of_restrictedInput` — `Work.BoxShrink.CruxStatement` from it;
* `Work.BoxShrink.Bubble.SmoothPushOff` — the same restricted datum in terms of the chapter's
  isolated input `SlicePushOff`, and `cruxCore_of_smoothPushOff` / `crux_of_smoothPushOff` —
  the crux from it.

So the crux is reduced to the push-off **for the smooth surfaces of the challenge only**
(`SmoothPushOff`), for which the parameter-plane flow formulation
`Work.BoxShrink.Bubble.slicePushOff_of_planeFlow` (gradient flow of the pull-back of the plane
coordinate) and the local model `Work.BoxShrink.Bubble.SlicePushModel` are the available routes.

**WARNING (stretch 17).**  `SmoothPushOff` and the field of `RestrictedInput` are **FALSE**: the
counterexample is the standard torus of revolution, which *is* the image of itself under the identity
diffeomorphism of `ℝ³` (`Work.BoxShrink.Bubble.mapHomeomorph_idDiffeo_eq_standard`), so
`Work.BoxShrink.Bubble.not_smoothPushOff` and `Work.BoxShrink.Bubble.not_nonempty_restrictedInput`
hold.  The theorems below are therefore vacuous, and the crux should be obtained from the corrected
interfaces instead: `Work.BoxShrink.Bubble.crux_of_pushOffHalf` / `crux_of_smoothHalf`
(`Corrected.lean`), or from Pardon's own input `Work.BoxShrink.Bubble.PardonPinchInput`
(`PardonLocalModel.lean`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **The push-off restricted to the smooth tori of the challenge**: the isolated input
`Work.BoxShrink.Bubble.SlicePushOff` at `P = ParamTorus.mapHomeomorph ψ.toHomeomorph` for every
diffeomorphism `ψ` and every plane level whose slice carries no essential loop. -/
def SmoothPushOff : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) s c σ u) →
    SlicePushOff (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) s c σ u

/-- The general input gives the restricted one. -/
theorem smoothPushOff_of_pushOffInput (h : PushOffInput) : SmoothPushOff :=
  fun ψ s c σ u hZ => h _ s c σ u hZ

/-- **The restricted field**: Pardon's double bubble for the smooth tori of the challenge, i.e. the
`bubble` field of `Work.BoxShrink.Core.BubbleInput` only where the crux needs it, together with the
planar innermost-disc input (which is exact — the crux needs it at the same tori). -/
structure RestrictedInput where
  /-- the planar innermost-disc input at every flat disc cut out of a box by a plane -/
  cleansInDisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.InnermostDisk.CleansInSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (Work.BoxShrink.Core.cutDisc s c σ u)
  /-- the double bubble for the smooth tori of the challenge -/
  bubble : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) s c σ u) →
    Work.BoxShrink.Core.BubbleSweep
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) s c σ u

/-- **The input from the restricted field**: the chapter's push-off for the smooth tori, together
with the planar innermost-disc input, gives the restricted field. -/
noncomputable def restrictedInput_of_smoothPushOff
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothPushOff) : RestrictedInput where
  cleansInDisc := hdisc
  bubble := fun ψ s c σ u _hS hZ => bubble_of_slicePushOff (h ψ s c σ u hZ)

/-- **The double-bubble core from the restricted field.**  A verbatim replay of
`Work.BoxShrink.Core.cruxCore_of_bubbleInput`, with the field used only at the smooth torus of the
challenge. -/
theorem cruxCore_of_restrictedInput (hin : RestrictedInput) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q := by
  intro p q
  unfold Work.BoxShrink.CruxCore
  intro hp hq hc ψ K d hd _hbound himg hsmall hcl r hr c σ hbox s hrs _hs hslice u _hu hS hU
  set P := Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph with hP
  have hs0 : 0 < s := lt_trans hr hrs
  have hnoS : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.BoxShrink.Core.not_containsEssentialLoop_sphereSet_of_slicing p q hp hq hc ψ K hd himg
      hsmall hs0 c σ hslice hcl hS
  have hnoZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) :=
    Work.BoxShrink.Core.not_containsEssentialLoop_sliceRegion p q hp hq hc ψ K hd himg hsmall hs0
      c σ u (hin.cleansInDisc ψ s c σ u) hU
  have hB : Work.BoxShrink.Core.BubbleSweep P s c σ u := hin.bubble ψ s c σ u hnoS hnoZ
  have hbox' : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ) :=
    Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (P := P) (c := c) (σ := σ)
      (le_of_lt hrs) hbox
  rcases Work.BoxShrink.Core.containsEssentialLoop_half_of_bubbleSweep (P := P) hB hbox' with
    hup | hlo
  · exact Or.inr ((Work.BoxShrink.Core.containsEssentialLoop_upperRegion_iff P s c σ u).mp hup)
  · exact Or.inl ((Work.BoxShrink.Core.containsEssentialLoop_lowerRegion_iff P s c σ u).mp hlo)

/-- **The double-bubble core from the push-off for the smooth tori only** (and the planar
innermost-disc input). -/
theorem cruxCore_of_smoothPushOff
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothPushOff) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_restrictedInput (restrictedInput_of_smoothPushOff hdisc h)

/-- **The crux (Pardon's shrinking step) from the restricted field.** -/
theorem crux_of_restrictedInput (hin : RestrictedInput) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  fun p q => ⟨hclean, cruxCore_of_restrictedInput hin p q, hae⟩

/-- **The crux from the push-off for the smooth tori of the challenge only.**  The whole of Pardon's
shrinking step now rests on `Work.BoxShrink.Bubble.SmoothPushOff` and the two classical inputs.-/
theorem crux_of_smoothPushOff
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothPushOff)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  crux_of_restrictedInput (restrictedInput_of_smoothPushOff hdisc h) hclean hae

end

end Work.BoxShrink.Bubble
