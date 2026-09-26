import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.Refutation
import Submission.Work.BoxShrink.Bubble.cex_upperRegion_essential
import Submission.Work.BoxShrink.Core.Crux

/-!
# The corrected interface: Pardon's Lemma 3 conclusion instead of the push-off

The field `bubble` of `Work.BoxShrink.Core.BubbleInput` is **false**
(`Work.BoxShrink.Bubble.no_bubble_field`, `Work.BoxShrink.Bubble.standard_counterexample`): the
push-off `Work.BoxShrink.Bubble.SlicePushOff` — every winding vector realised in the region inside
the box is realised away from the slicing plane — fails at the standard torus of revolution, the box
of size `5/2` and the plane `{y = 0}`.  The reason is Pardon's own proof: he applies his counting
hypothesis (Lemma `mustbeinessential`) to **every** intermediate sphere of the pinching family, and
Lemma `spherefamily` only concludes that the *dimension* of `im(H₁(F ∩ int S_t) → H₁(F))` — whose
possible values are `0` and `2g` — is constant, allowing a change of at most `1` at each local move.
Our `Work.SurgeryInvariance.SweepLoops` local models are strictly stronger: `RegionEquivalent` and
`SurgeryStepZero` both preserve the winding span *exactly*
(`Work.SurgeryInvariance.SweepLoops.windingSpan_eq`), so they cannot model the pinch.

What Pardon's shrinking step *actually consumes*, however, is weaker than the push-off: the essential
loop of `F` inside the sphere has to survive to *one* of the two half-regions.  That is the
statement

`Work.BoxShrink.Bubble.BubbleHalf P s c σ u :
  P.ContainsEssentialLoop (boxRegion P s c σ) →
    P.ContainsEssentialLoop (upperRegion P s c σ u) ∨
      P.ContainsEssentialLoop (lowerRegion P s c σ u)`

— the loop-existence form of Pardon's Lemma 3 (`doublebubble`), which is *not* refuted by the
counterexample (indeed at the counterexample configuration the upper half-region contains the
meridian circle at longitude `π/2`, of winding `(0,1)`:
`Work.BoxShrink.Bubble.cex_upperRegion_essential`).

The definitions themselves (`BubbleHalf`, `PushOffHalf`, `SmoothHalf`, and the drop-in structures
`BubbleInputHalf` / `BubbleInputPardon`) are in `Work.BoxShrink.Bubble.HalfDefs`, whose dependency
footprint is small enough for `Work.BoxShrink.Core.Bubble.Defs` to import it (see `MIGRATION.md`).
This file

* shows the old field implies the corrected interface (`pushOffHalf_of_bubbleSweepAll`) and so does
  the push-off (`pushOffHalf_of_pushOffInput`, `smoothHalf_of_smoothPushOff`) — the corrected
  interface is strictly weaker, so nothing proved here about it is refuted by the counterexample,
  and `bubbleHalf_cex` shows it holding at the counterexample configuration itself;
* **replays the crux** (`Work.BoxShrink.CruxCore` / `Work.BoxShrink.CruxStatement`) with the
  corrected interface in place of `BubbleInput.bubble` (`cruxCore_of_pushOffHalf`,
  `crux_of_pushOffHalf`, `cruxCore_of_smoothHalf`, `crux_of_smoothHalf`), verbatim from
  `Work.BoxShrink.Core.cruxCore_of_bubbleInput` — this is the interface the requester should adopt.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **The counterexample does not refute the corrected field.**  At the counterexample
configuration of `Work.BoxShrink.Bubble.standard_counterexample` the push-off fails
(`cex_not_slicePushOff`) so no `BubbleSweep` exists there (`cex_not_nonempty_bubbleSweep`), but the
corrected conclusion still holds: the upper half-region contains the meridian circle at longitude
`π/2` (`Work.BoxShrink.Bubble.cex_upperRegion_essential`).  So `BubbleHalf` is a genuine weakening —
this is the sharpest available evidence that the corrected interface is the right one. -/
theorem bubbleHalf_cex :
    BubbleHalf Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 :=
  fun _ => Or.inl cex_upperRegion_essential

/-! ## Every sufficient condition already available gives the corrected conclusion -/

/-- The double-bubble family gives the corrected conclusion (this is Pardon's Lemma 3 at the loop
level, `Work.BoxShrink.Core.containsEssentialLoop_half_of_bubbleSweep`). -/
theorem bubbleHalf_of_bubbleSweep {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (B : Work.BoxShrink.Core.BubbleSweep P s c σ u) :
    BubbleHalf P s c σ u :=
  fun hbox => Work.BoxShrink.Core.containsEssentialLoop_half_of_bubbleSweep B hbox

/-- The span-level push-off gives the corrected conclusion. -/
theorem bubbleHalf_of_slicePushOffSpan {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : SlicePushOffSpan P s c σ u) :
    BubbleHalf P s c σ u :=
  fun hbox => containsEssentialLoop_half_of_slicePushOffSpan h hbox

/-- The push-off gives the corrected conclusion. -/
theorem bubbleHalf_of_slicePushOff {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : SlicePushOff P s c σ u) :
    BubbleHalf P s c σ u :=
  fun hbox => containsEssentialLoop_half_of_slicePushOff h hbox

/-- The (false) field of `Work.BoxShrink.Core.BubbleInput` implies the corrected field: the
corrected interface is a strict weakening, so the counterexample to the field does not refute it. -/
theorem pushOffHalf_of_bubbleSweepAll
    (hb : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
      (u : ℝ), ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Core.BubbleSweep P s c σ u) : PushOffHalf :=
  fun P s c σ u hS hZ => bubbleHalf_of_bubbleSweep (hb P s c σ u hS hZ)

/-- The chapter's push-off input implies the corrected field. -/
theorem pushOffHalf_of_pushOffInput (h : PushOffInput) : PushOffHalf :=
  fun P s c σ u _ hZ => bubbleHalf_of_slicePushOff (h P s c σ u hZ)

/-- The push-off for the smooth tori of the challenge implies the corrected field there. -/
theorem smoothHalf_of_smoothPushOff (h : SmoothPushOff) : SmoothHalf :=
  fun ψ s c σ u hZ => bubbleHalf_of_slicePushOff (h ψ s c σ u hZ)

/-! ## The shrinking step from the corrected field -/

/-- **The double-bubble core from the corrected field.**  A verbatim replay of
`Work.BoxShrink.Core.cruxCore_of_bubbleInput`: the counting input gives that the sphere and the
slice of the box/plane configuration carry no essential loop, and the corrected field then carries
the essential loop of the region inside the box into one of the two half-regions. -/
theorem cruxCore_of_pushOffHalf
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalf) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q := by
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
      c σ u (hcleanD ψ s c σ u) hU
  have hbox' : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ) :=
    Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (P := P) (c := c) (σ := σ)
      (le_of_lt hrs) hbox
  rcases h P s c σ u hnoS hnoZ hbox' with hup | hlo
  · exact Or.inr ((Work.BoxShrink.Core.containsEssentialLoop_upperRegion_iff P s c σ u).mp hup)
  · exact Or.inl ((Work.BoxShrink.Core.containsEssentialLoop_lowerRegion_iff P s c σ u).mp hlo)

/-- **The shrinking step from the corrected field.** -/
theorem crux_of_pushOffHalf
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalf) (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  fun p q => ⟨hclean, cruxCore_of_pushOffHalf hcleanD h p q, hae⟩

/-- **The double-bubble core from the corrected field for the smooth tori of the challenge.**  A
verbatim replay of `Work.BoxShrink.Core.cruxCore_of_bubbleInput` with the corrected conclusion. -/
theorem cruxCore_of_smoothHalf
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothHalf) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q := by
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
      c σ u (hcleanD ψ s c σ u) hU
  have hbox' : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ) :=
    Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (P := P) (c := c) (σ := σ)
      (le_of_lt hrs) hbox
  rcases h ψ s c σ u hnoZ hbox' with hup | hlo
  · exact Or.inr ((Work.BoxShrink.Core.containsEssentialLoop_upperRegion_iff P s c σ u).mp hup)
  · exact Or.inl ((Work.BoxShrink.Core.containsEssentialLoop_lowerRegion_iff P s c σ u).mp hlo)

/-- **The shrinking step from the corrected field for the smooth tori of the challenge.**  This is
the form in which the corrected interface should replace the field of
`Work.BoxShrink.Core.BubbleInput`: together with the planar innermost-disc input, the two classical
inputs (`Work.BoxShrink.CleansDiscsAll`, `Work.BoxShrink.AeSlicedAll`) and `SmoothHalf`, Pardon's
shrinking step `Work.BoxShrink.CruxStatement` follows for all `p, q`. -/
theorem crux_of_smoothHalf
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothHalf) (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  fun p q => ⟨hclean, cruxCore_of_smoothHalf hcleanD h p q, hae⟩

/-- The (false) `BubbleInput` of the caller implies the corrected structure — the corrected field is
a strict weakening, so the counterexample does not refute it. -/
theorem bubbleInputHalf_of_bubbleInput (hin : Work.BoxShrink.Core.BubbleInput) : BubbleInputHalf where
  cleansInDisc := hin.cleansInDisc
  bubble := pushOffHalf_of_bubbleSweepAll hin.bubble

/-- **The double-bubble core from the corrected structure**: the exact analogue of
`Work.BoxShrink.Core.cruxCore_of_bubbleInput` with the weakened field. -/
theorem cruxCore_of_bubbleInputHalf (hin : BubbleInputHalf) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_pushOffHalf hin.cleansInDisc hin.bubble

/-- **The shrinking step from the corrected structure.**  A verbatim analogue of
`Work.BoxShrink.Core.crux_of_bubbleInput` with the corrected field. -/
theorem crux_of_bubbleInputHalf (hin : BubbleInputHalf) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) : ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  crux_of_pushOffHalf hin.cleansInDisc hin.bubble hclean hae

/-! ## The corrected conclusion from the library's spatial sweep

The library's own vocabulary for Pardon's sphere family is `Work.SurgeryInvariance.Sweep` (the
regions `F ∩ int(S_t)`, with local models given by ambient isotopies and `2`-surgeries whose changed
pieces are the interiors of embedded discs of `F`) and `Work.SurgeryInvariance.SphereSweep` (the same
recorded through the spheres themselves).  Its `double_bubble` theorem is Pardon's Lemma 3 in that
vocabulary: if the final region is the union of the two half-regions *together with the interior of
an embedded disc* (Pardon's perturbed double bubble, `doublebubble2` in the paper) then one of the
half-regions carries an essential loop.  Since `Sweep`'s local models preserve the winding span
exactly (`Work.SurgeryInvariance.Sweep.windingSpan_eq`), a `Sweep` from the box region to the two
halves *alone* does not exist in general — this is exactly the counterexample — so this route needs
the perturbed endpoint (the extra disc), which is the form in which Pardon's counting delivers it.
-/

variable {P : Work.CoreTopology.ParamTorus} in
/-- **`BubbleHalf` from the library's spatial sweep**: a `Work.SurgeryInvariance.Sweep` whose
initial region is the region inside the box and whose final region is the union of the two
half-regions together with the interior of an embedded disc of `F`, the two pieces being disjoint,
gives an essential loop in one of the two half-regions.  This is
`Work.SurgeryInvariance.Sweep.double_bubble`. -/
theorem bubbleHalf_of_sweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {S : Work.SurgeryInvariance.Sweep P} {D : Work.SurgeryInvariance.DiscRegion P}
    (h0 : S.region 0 = Work.BoxShrink.Core.boxRegion P s c σ)
    (hdisjZ : Disjoint (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) D.interior)
    (hcover : S.region 1 = (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ D.interior) :
    BubbleHalf P s c σ u :=
  fun hbox => Work.SurgeryInvariance.Sweep.double_bubble (S := S)
    (H₁ := Work.BoxShrink.Core.upperRegion P s c σ u)
    (H₂ := Work.BoxShrink.Core.lowerRegion P s c σ u) (D := D)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)
    hdisjZ hcover (by rw [h0]; exact hbox)

end

end Work.BoxShrink.Bubble
