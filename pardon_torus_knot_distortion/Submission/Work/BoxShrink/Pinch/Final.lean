import Submission.Work.BoxShrink.Pinch.Main
import Submission.Work.BoxShrink.Pinch.Migrated

/-!
# The challenge from each form of the pinch input

Every corrected residual input of the chapter yields Pardon's theorem.  The list, in order of
increasing weakness of the datum:

* `pardon_torus_knot_distortion_of_finalInputS` (`Migrated.lean`) — the corrected final input
  (`cleansInDisc`, `SmoothHalfS`, `cleans`, `ae`), the form in which `Submission.lean` should be
  read;
* `pardon_torus_knot_distortion_of_pinchInputSmoothAll` — the pinch for the smooth tori;
* `pardon_torus_knot_distortion_of_pinchLevelsInput` — the pinch in level-set form, together with
  Pardon's equation (1) (`Equation1Input`);
* `pardon_torus_knot_distortion_of_pinchRegionsSmoothAll` — the pinch in invariant form;
* `pardon_torus_knot_distortion_of_pushOffHalf` — the corrected field `PushOffHalf` of
  `Work.BoxShrink.Bubble.HalfDefs`;
* `pardon_torus_knot_distortion_of_pardonPinchInput` — Pardon's own pinch datum.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

/-- The challenge from Pardon's Lemma 3 under both endpoint hypotheses. -/
theorem pardon_torus_knot_distortion_of_smoothHalfS
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : SmoothHalfS) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_finalInputS (finalInputS_of_smoothHalfS hdisc h hclean hae)

/-- The challenge from the pinch for the smooth tori. -/
theorem pardon_torus_knot_distortion_of_pinchInputSmoothAll
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PinchInputSmoothAll) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hdisc (smoothHalfS_of_pinchInputSmoothAll h)
    hclean hae

/-- The challenge from the pinch in level-set form and Pardon's equation (1). -/
theorem pardon_torus_knot_distortion_of_pinchLevelsInput
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (h2 : PinchLevelsInput)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hdisc (smoothHalfS_of_pinchLevelsInput h1 h2)
    hclean hae

/-- The challenge from the pinch in invariant form. -/
theorem pardon_torus_knot_distortion_of_pinchRegionsSmoothAll
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PinchRegionsSmoothAll) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hdisc (smoothHalfS_of_pinchRegionsSmoothAll h)
    hclean hae

/-- The challenge from the corrected field `PushOffHalf`. -/
theorem pardon_torus_knot_distortion_of_pushOffHalf
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : Work.BoxShrink.Bubble.PushOffHalf) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  fun p q hp hq hc K hclass =>
    Submission.theorem_of_core
      (Submission.CoreStatement_of_boxShrink
        (Work.BoxShrink.boxShrink_of_crux
          (fun p q => ⟨hclean,
            Work.BoxShrink.Bubble.cruxCore_of_pushOffHalf hdisc h p q, hae⟩)))
      p q hp hq hc K hclass

/-- The challenge from Pardon's own pinch datum. -/
theorem pardon_torus_knot_distortion_of_pardonPinchInput
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : Work.BoxShrink.Bubble.PardonPinchInput) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hdisc (smoothHalfS_of_pardonPinchInput h)
    hclean hae

end

end Work.BoxShrink.Pinch
