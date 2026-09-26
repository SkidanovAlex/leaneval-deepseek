import Submission.Work.BoxShrink.Pinch.Level
import Submission.Work.BoxShrink.Bubble.Corrected
import Submission.Work.BoxShrink.Bubble.PardonLocalModel
import Submission.Work.BoxShrink.assemble


/-!
# The shrinking step from the pinch

`Regions.lean`/`Level.lean` reduce Pardon's Lemma 3 to the pinch; this module replays Pardon's
shrinking step (`Work.BoxShrink.Core.cruxCore_of_bubbleInput`) with the *corrected* field, i.e.
with `Work.BoxShrink.Pinch.SmoothHalfS` in place of the false field of
`Work.BoxShrink.Core.BubbleInput`.

The replay is verbatim: the crux's own counting hypotheses (`hS` at the swept box sphere, `hU` at
the slicing disc) produce the two inessentiality facts that `SmoothHalfS` consumes, so nothing is
lost on the way to the challenge.  In particular the pinch theorem `bubbleHalf_of_pinchRegions`
lands directly on `Work.BoxShrink.CruxCore`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **Pardon's own pinch datum gives Pardon's Lemma 3 conclusion** under both endpoint
hypotheses. -/
theorem smoothHalfS_of_pardonPinchInput (h : Work.BoxShrink.Bubble.PardonPinchInput) :
    SmoothHalfS :=
  smoothHalfS_of_pinchInputSmoothAll (pinchInputSmoothAll_of_pardonPinchInput h)

/-- **The double-bubble core from Pardon's Lemma 3 under both endpoint hypotheses.** -/
theorem cruxCore_of_smoothHalfS
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothHalfS) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q := by
  intro p q
  unfold Work.BoxShrink.CruxCore
  intro hp hq hc ψ K d hd _hbound himg hsmall hcl r hr c σ hbox s hrs _hs hslice u _hu hS hU
  set P := Work.Smooth.Morse.torus ψ with hP
  have hs0 : 0 < s := lt_trans hr hrs
  have hnoS : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.BoxShrink.Core.not_containsEssentialLoop_sphereSet_of_slicing p q hp hq hc ψ K hd himg
      hsmall hs0 c σ hslice hcl hS
  have hnoZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) :=
    Work.BoxShrink.Core.not_containsEssentialLoop_sliceRegion p q hp hq hc ψ K hd himg hsmall hs0
      c σ u (hcleanD ψ s c σ u) hU
  have hbox' : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ) :=
    Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (P := P) (c := c) (σ := σ)
      (le_of_lt hrs) hbox
  rcases h ψ s c σ u hnoS hnoZ hbox' with hup | hlo
  · exact Or.inr ((Work.BoxShrink.Core.containsEssentialLoop_upperRegion_iff P s c σ u).mp hup)
  · exact Or.inl ((Work.BoxShrink.Core.containsEssentialLoop_lowerRegion_iff P s c σ u).mp hlo)

/-- **The shrinking step from Pardon's Lemma 3 under both endpoint hypotheses.** -/
theorem cruxStatement_of_smoothHalfS
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothHalfS) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  fun p q => ⟨hclean, cruxCore_of_smoothHalfS hcleanD h p q, hae⟩

/-- **`BoxShrinkStatement`, from Pardon's Lemma 3 under both endpoint hypotheses.** -/
theorem boxShrinkStatement_of_smoothHalfS
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothHalfS) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux (cruxStatement_of_smoothHalfS hcleanD h hclean hae)

/-! ## The pinch inputs -/

/-- **The shrinking step from the pinch** (`PinchInputSmoothAll`). -/
theorem cruxCore_of_pinchInputSmoothAll
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PinchInputSmoothAll) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_smoothHalfS hcleanD (smoothHalfS_of_pinchInputSmoothAll h)

/-- **The shrinking step from the pinch in level-set form** (`Equation1Input` plus the level
family). -/
theorem cruxCore_of_pinchLevelsInput
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (h2 : PinchLevelsInput) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_smoothHalfS hcleanD (smoothHalfS_of_pinchLevelsInput h1 h2)

/-- **The shrinking step from the invariant form of the pinch** (`PinchRegionsSmoothAll`). -/
theorem cruxCore_of_pinchRegionsSmoothAll
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PinchRegionsSmoothAll) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_smoothHalfS hcleanD (smoothHalfS_of_pinchRegionsSmoothAll h)

/-- **The shrinking step from Pardon's own pinch datum** (`PardonPinchInput`). -/
theorem cruxCore_of_pardonPinchInput
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : Work.BoxShrink.Bubble.PardonPinchInput) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_smoothHalfS hcleanD (smoothHalfS_of_pardonPinchInput h)

/-- **The shrinking step, from the corrected field `PushOffHalf`.** -/
theorem cruxCore_of_pushOffHalf
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : Work.BoxShrink.Bubble.PushOffHalf) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.Bubble.cruxCore_of_pushOffHalf hcleanD h

/-! ## The corrected input structures -/

/-- **Pardon's pinch gives the corrected field.** -/
theorem bubbleInputHalf_of_pardonPinchInput
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : Work.BoxShrink.Bubble.PardonPinchInput) : Work.BoxShrink.Bubble.BubbleInputHalf where
  cleansInDisc := hdisc
  bubble := Work.BoxShrink.Bubble.pushOffHalf_of_pardonPinchInput h

end

end Work.BoxShrink.Pinch
