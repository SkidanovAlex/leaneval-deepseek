import Submission.Work.BoxShrink.PinchOff.Basic
import Submission.Work.BoxShrink.PinchOff.Instances
import Submission.Work.BoxShrink.PinchOff.Laminar
import Submission.Work.BoxShrink.Pinch.TameTarget

/-!
# The corrected residual: the pinch in general position

`KeyRefuted.lean` proves that the residual of the pinch *as it was stated* — `Key`, `KeyCase`, the
parent chapter's `PinchNoJump` and `Work.PinchLemma3.SliceWall`, the library input
`Work.BoxShrink.Bubble.PardonPinchInput`, and the two abstract forms `SmoothHalfS` and `PushOffHalf`
— is **false**, at the standard torus with the box centre `(1,0,0)` (where the cutting plane is
*tangent* to the surface), `s = 13/10`, `σ = (0 1 2)`, `u = 0`.  The missing hypothesis is the
**general position of the cutting plane**, and the exact form of it that Pardon's counting argument
supplies is already in the parent chapter:

* `Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u` — `∇G ≠ 0` on `{G = 0} ∩ {B < s}`;
* `Work.BoxShrink.Pinch.TameSlice ψ s c σ u` — the flat disc of the plane inside the box meets the
  surface in finitely many embedded arcs and simple closed curves.

The chapter's corrected residual is therefore the parent chapter's own tamed target

  `Work.BoxShrink.Pinch.PushOffHalfTame`

— the conclusion of Pardon's Lemma 3 for every smooth torus, box and plane for which the slice is
transverse and tame.  It is *not* refuted by the counterexample of `KeyRefuted.lean`, because that
configuration violates `TransverseSlice`; and it is the statement the deliverable names once the two
geometric inputs are carried by the caller (`smoothHalfS_of_tame_transversality` below, the parent's
`Work.BoxShrink.Pinch.smoothHalfS_of_pushOffHalfTame`).

This module

* names the corrected residual `SmoothHalfSTame` and proves it *is* `PushOffHalfTame`
  (`smoothHalfSTame_iff_pushOffHalfTame`), with the two conversions
  `pushOffHalfTame_of_smoothHalfSTame` / `smoothHalfSTame_of_pushOffHalfTame`;
* gives its dimension-bound form `KeyTame` — the tamed analogue of `Key` — and proves that Pardon's
  Lemma 3 conclusion implies it at every configuration (`keyTame_of_bubbleHalf`,
  `keyTame_of_smoothHalfSTame`);
* records the tamed instances (`pushOffHalfTame_of_emptySlice`,
  `pushOffHalfTame_of_sliceDiscCovering`, `keyTame_of_boxRegion_inessential`,
  `keyTame_of_boxRegion_finrank_le_one`), which is what the residual *is* proved for at present.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The corrected residual -/

/-- **The corrected residual of the pinch**: Pardon's Lemma 3 for the smooth tori of the challenge,
with the general position of the cutting plane carried as a hypothesis and formulated *as* that
hypothesis (the parent chapter's `PushOffHalfTame`, under the argument order of this chapter). -/
def SmoothHalfSTame : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u

/-- The corrected residual *is* the parent chapter's tamed target. -/
theorem smoothHalfSTame_iff_pushOffHalfTame :
    SmoothHalfSTame ↔ Work.BoxShrink.Pinch.PushOffHalfTame := Iff.rfl

/-- The corrected residual, in the parent chapter's name. -/
theorem pushOffHalfTame_of_smoothHalfSTame (h : SmoothHalfSTame) :
    Work.BoxShrink.Pinch.PushOffHalfTame := h

/-- Conversely. -/
theorem smoothHalfSTame_of_pushOffHalfTame (h : Work.BoxShrink.Pinch.PushOffHalfTame) :
    SmoothHalfSTame := h

/-- **The corrected residual implies the abstract one** as soon as the general position hypotheses
are available for every configuration.  *Warning*: the hypothesis `htrans` is refuted at the tangent
configuration (`Work.BoxShrink.PinchOff.not_forall_transverseSlice` in
`Submission.Work.BoxShrink.PinchOff.NotTransverse`), so this implication cannot be applied in the
challenge; it is recorded to show that `SmoothHalfSTame` is exactly `SmoothHalfS` minus the general
position of the cutting plane. -/
theorem smoothHalfS_of_tame_transversality (h : SmoothHalfSTame)
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    Work.BoxShrink.Pinch.SmoothHalfS :=
  Work.BoxShrink.Pinch.smoothHalfS_of_pushOffHalfTame h htrans htame

/-! ## The dimension-bound form of the corrected residual -/

/-- **The tamed dimension bound** — `Key` with the general position of the cutting plane. -/
def KeyTame : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) + 1

/-- **Pardon's Lemma 3 conclusion gives the dimension bound**: if an essential loop of the box
region survives to one of the halves, then the box region loses at most one dimension to the halves.

Indeed, if the box region carries no essential loop then its span is `⊥`; otherwise one of the two
halves carries an essential loop, so the halves' span has dimension at least `1`, while the box
region's span has dimension at most `2`. -/
theorem keyTame_of_bubbleHalf (h : Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) + 1 := by
  by_cases hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥
  · rw [hbot, finrank_bot]
    exact Nat.zero_le _
  · have hne : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥ := by
      intro hH
      have hbox : (surface ψ).ContainsEssentialLoop (Omega ψ s c σ) :=
        (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hbot
      rcases h hbox with hup | hlo
      · refine (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp ?_ hup
        exact le_bot_iff.mp ((Work.SurgeryInvariance.WindingSpan_mono (P := surface ψ)
          (Set.subset_union_left : HalfUp ψ s c σ u ⊆ Halves ψ s c σ u)).trans (le_of_eq hH))
      · refine (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp ?_ hlo
        exact le_bot_iff.mp ((Work.SurgeryInvariance.WindingSpan_mono (P := surface ψ)
          (Set.subset_union_right : HalfDown ψ s c σ u ⊆ Halves ψ s c σ u)).trans (le_of_eq hH))
    have h1 : 1 ≤ Module.finrank ℚ
        ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) :=
      (Submodule.one_le_finrank_iff).mpr hne
    have h2 : Module.finrank ℚ
        ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤ 2 := by
      have hle := Submodule.finrank_mono
        (show Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤ ⊤ from le_top)
      rwa [finrank_top, finrank_rat_sq] at hle
    omega

/-- **The corrected residual gives its dimension-bound form.** -/
theorem keyTame_of_smoothHalfSTame (h : SmoothHalfSTame) : KeyTame :=
  fun ψ s c σ u hT hTame hS hZ => keyTame_of_bubbleHalf (h ψ s c σ u hT hTame hS hZ)

/-! ## The instances of the corrected residual

Each of these is a configuration in which the conclusion is *proved* outright, with no general
position hypothesis — hence a fortiori an instance of the corrected residual. -/

/-- **The slice is empty**: the box region is already the union of the two halves. -/
theorem pushOffHalfTame_of_emptySlice
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Sigma ψ s c σ u = ∅) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  fun ψ s c σ u _ _ _ _ => bubbleHalf_of_empty_slice (h ψ s c σ u)

/-- **The slice is covered by the interiors of discs inside the box region** (the circles-only case
when the discs bounded by the slice circles lie in the box). -/
theorem pushOffHalfTame_of_sliceDiscCovering
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceDiscCovering ψ s c σ u) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  fun ψ s c σ u _ _ _ _ => bubbleHalf_of_sliceDiscCovering (h ψ s c σ u)

/-- **The box region carries no essential loop**: the bound is trivial. -/
theorem keyTame_of_boxRegion_inessential
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      ¬ (surface ψ).ContainsEssentialLoop (Omega ψ s c σ)) : KeyTame := by
  intro ψ s c σ u _ _ _ _
  have hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥ :=
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr (h ψ s c σ)
  rw [hbot, finrank_bot]
  exact Nat.zero_le _

/-- **The box region's span has dimension at most one**: the bound is trivial. -/
theorem keyTame_of_boxRegion_finrank_le_one
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤ 1) :
    KeyTame :=
  fun ψ s c σ u _ _ _ _ => by
    have := h ψ s c σ
    omega

/-- **The slice is finite** (the parent chapter's perturbation argument in the parameter plane). -/
theorem pushOffHalfTame_of_finiteSlice
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      (Sigma ψ s c σ u).Finite) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  fun ψ s c σ u _ _ _ _ => bubbleHalf_of_finite_slice (h ψ s c σ u)

end

end Work.BoxShrink.PinchOff
