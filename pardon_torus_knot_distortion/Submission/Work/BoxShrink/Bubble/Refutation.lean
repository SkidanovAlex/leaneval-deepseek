import Submission.Work.BoxShrink.Bubble.standard_counterexample
import Submission.Work.BoxShrink.Bubble.Equivalence
import Submission.Work.BoxShrink.Bubble.Restricted

/-!
# The field `BubbleInput.bubble` is false: the refutation

`Submission/Work/BoxShrink/Bubble/standard_counterexample.lean` exhibits a concrete box/plane
configuration at which both hypotheses of the field `bubble` of
`Work.BoxShrink.Core.BubbleInput` hold, but the conclusion `BubbleSweep` fails
(`cex_not_slicePushOff` + `Work.BoxShrink.Bubble.bubbleSweep_nonempty_iff_slicePushOff`).

This file draws every consequence of that counterexample which the rest of the workspace needs:

* **no function of the field's type exists** (`no_bubble_field`): there is no term of the exact type
  of `BubbleInput.bubble`;
* **`Work.BoxShrink.Core.BubbleInput` is not inhabited** (`not_nonempty_bubbleInput`), and so is
  `Work.BoxShrink.Core.PhysicalBubbleInput` (`not_nonempty_physicalBubbleInput`).  Consequently
  `Work.BoxShrink.Core.crux_of_bubbleInput` / `Work.BoxShrink.Core.crux` can never be applied, and
  the assembly `Submission/Work/BoxShrink/assemble.lean` cannot be completed through that route;
* **the same is true of the *restricted* interfaces** used by `Work.BoxShrink.Bubble.Restricted`:
  the counterexample is the standard torus of revolution, which is the image of itself under the
  identity diffeomorphism of `ℝ³` (`mapHomeomorph_idDiffeo_eq_standard`), so
  `Work.BoxShrink.Bubble.SmoothPushOff` is false (`not_smoothPushOff`) and
  `Work.BoxShrink.Bubble.RestrictedInput` is not inhabited (`not_nonempty_restrictedInput`).  In
  other words, **no amount of work on the analytic push-off** (`Smooth/*`: the gauge, the flow of
  the auxiliary function, the Sard/critical-value statements) **can repair the interface** — the
  obstruction is at the standard torus itself.

The diagnosis and the recommended replacement of the field are in `README.md` (section "The field
is false") and in `PLAN.md` (stretch 16); the *corrected* interface, whose conclusion is Pardon's
Lemma 3 conclusion, is in `Work.BoxShrink.Bubble.Corrected`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-! ## The identity diffeomorphism of `ℝ³` and the standard torus -/

/-- The identity diffeomorphism of `ℝ³`. -/
def idDiffeo : Submission.Diffeo where
  toFun := id
  invFun := id
  smooth_toFun := contDiff_id
  smooth_invFun := contDiff_id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The identity diffeomorphism acts as the identity. -/
@[simp] theorem idDiffeo_toFun : idDiffeo.toFun = id := rfl

/-- **Two parametrised tori with the same parametrising map are equal** (the remaining fields are
proofs). -/
theorem ParamTorus.ext_psi {P Q : Work.CoreTopology.ParamTorus} (h : P.psi = Q.psi) : P = Q := by
  cases P with
  | mk p1 c1 l1 r1 i1 =>
  cases Q with
  | mk p2 c2 l2 r2 i2 =>
  simp only at h
  subst h
  congr 1 <;> exact Subsingleton.elim _ _

/-- **The standard torus of revolution is the image of itself under the identity diffeomorphism.**
This is what makes the counterexample fatal for the *restricted* interfaces as well: the smooth
tori of the challenge include the standard one. -/
theorem mapHomeomorph_idDiffeo_eq_standard :
    Work.CoreTopology.ParamTorus.mapHomeomorph idDiffeo.toHomeomorph =
      Work.CoreTopology.standard := by
  apply ParamTorus.ext_psi
  funext x y
  simp [Work.CoreTopology.ParamTorus.mapHomeomorph_psi, Work.CoreTopology.standard_psi,
    Submission.Diffeo.toHomeomorph_apply, idDiffeo]

/-! ## The region inside the box contains an essential loop -/

/-- The winding span of the region inside the box is nonzero (the longitude `{z = -1}` lies in the
box and has winding `(1,0)`). -/
theorem cex_containsEssentialLoop_boxRegion :
    Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2)) := by
  obtain ⟨γ, hγ, hw⟩ := cex_onezero_mem_realizedWindings
  refine ⟨γ, (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero _ γ).mpr ?_, hγ⟩
  rw [hw]
  decide

/-- The winding span of the region inside the box is nonzero. -/
theorem cex_windingSpan_boxRegion_ne_bot :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2)) ≠ ⊥ := by
  rw [Work.SurgeryInvariance.windingSpan_ne_bot_iff]
  exact cex_containsEssentialLoop_boxRegion

/-! ## No `BubbleSweep` exists at the counterexample configuration -/

/-- **Pardon's double-bubble datum fails at the counterexample configuration**: there is no
`BubbleSweep` for the standard torus, the box of size `5/2` and the plane `{y = 0}`. -/
theorem cex_not_nonempty_bubbleSweep :
    ¬ Nonempty (Work.BoxShrink.Core.BubbleSweep Work.CoreTopology.standard (5 / 2) 0
      (Equiv.swap (1 : Fin 3) 2) 0) := by
  intro h
  exact standard_counterexample.2.2
    ((bubbleSweep_nonempty_iff_slicePushOff (P := Work.CoreTopology.standard)
      (s := 5 / 2) (c := 0) (σ := Equiv.swap (1 : Fin 3) 2) (u := 0)
      cex_windingSpan_boxRegion_ne_bot).mp h)

/-! ## The field of `BubbleInput` does not exist -/

/-- **There is no function of the type of the field `BubbleInput.bubble`.**

The field would be a function `b` turning every box/plane configuration whose two cuts carry no
essential loop of `F` into Pardon's double-bubble family.  Evaluating `b` at the counterexample
configuration produces a `BubbleSweep` there, which does not exist
(`cex_not_nonempty_bubbleSweep`). -/
theorem no_bubble_field :
    ¬ ∃ b : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
        (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
        ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
        Work.BoxShrink.Core.BubbleSweep P s c σ u, True := by
  rintro ⟨b, -⟩
  exact cex_not_nonempty_bubbleSweep
    ⟨b _ _ _ _ _ standard_counterexample.1 standard_counterexample.2.1⟩

/-- **`Work.BoxShrink.Core.BubbleInput` is not inhabited.**  Its field `bubble` cannot exist
(`no_bubble_field`), so neither can an inhabitant of the structure — hence every theorem taking a
`BubbleInput` (`Work.BoxShrink.Core.crux_of_bubbleInput`, `Work.BoxShrink.Core.crux`, ...) is
vacuous. -/
theorem not_nonempty_bubbleInput : ¬ Nonempty Work.BoxShrink.Core.BubbleInput := by
  rintro ⟨hin⟩
  exact no_bubble_field ⟨hin.bubble, trivial⟩

/-- **The same for the "physical" form of the input**: the field
`PhysicalBubbleInput.bubbleSweep` demands a `Sweep` of the surface whose two endpoint regions are
the region inside the box and the union of the two half-regions; converted to loops by
`Work.SurgeryInvariance.Sweep.toLoops` it would give a `BubbleSweep` at every configuration,
contradicting the counterexample. -/
theorem not_nonempty_physicalBubbleInput :
    ¬ Nonempty Work.BoxShrink.Core.PhysicalBubbleInput := by
  rintro ⟨hin⟩
  obtain ⟨sw, h0, h1⟩ := hin.bubbleSweep Work.CoreTopology.standard (5 / 2) 0
    (Equiv.swap (1 : Fin 3) 2) 0 standard_counterexample.1 standard_counterexample.2.1
  exact cex_not_nonempty_bubbleSweep ⟨sw.toLoops, h0, h1⟩

/-! ## The restricted interfaces are false too

The counterexample is the *standard* torus of revolution, i.e. the image of itself under the
identity diffeomorphism of `ℝ³`, so restricting the field to the smooth tori of the challenge does
not help: `SmoothPushOff` (the analytic input that the whole `Smooth/*` development — the box
gauge, the flow of `auxFun`, the Sard/critical-value statements — was built to prove) is false.
-/

/-- The restricted push-off fails at the counterexample configuration. -/
theorem cex_not_slicePushOff_id :
    ¬ SlicePushOff (Work.CoreTopology.ParamTorus.mapHomeomorph idDiffeo.toHomeomorph) (5 / 2) 0
      (Equiv.swap (1 : Fin 3) 2) 0 := by
  rw [mapHomeomorph_idDiffeo_eq_standard]
  exact standard_counterexample.2.2

/-- **`Work.BoxShrink.Bubble.SmoothPushOff` is false.** -/
theorem not_smoothPushOff : ¬ SmoothPushOff := by
  intro h
  set P' := Work.CoreTopology.ParamTorus.mapHomeomorph idDiffeo.toHomeomorph with hP'
  have hstd : P' = Work.CoreTopology.standard := by
    rw [hP']; exact mapHomeomorph_idDiffeo_eq_standard
  have hZ : ¬ P'.ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion P' (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0) := by
    rw [hstd]; exact standard_counterexample.2.1
  have hsp : SlicePushOff P' (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 :=
    h idDiffeo (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 hZ
  rw [hstd] at hsp
  exact standard_counterexample.2.2 hsp

/-- **`Work.BoxShrink.Bubble.RestrictedInput` is not inhabited**: the restricted field
`RestrictedInput.bubble` cannot exist either. -/
theorem not_nonempty_restrictedInput : ¬ Nonempty RestrictedInput := by
  rintro ⟨hin⟩
  set P' := Work.CoreTopology.ParamTorus.mapHomeomorph idDiffeo.toHomeomorph with hP'
  have hstd : P' = Work.CoreTopology.standard := by
    rw [hP']; exact mapHomeomorph_idDiffeo_eq_standard
  have hS : ¬ P'.ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet 0 (Equiv.swap (1 : Fin 3) 2) (5 / 2)) := by
    rw [hstd]; exact standard_counterexample.1
  have hZ : ¬ P'.ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion P' (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0) := by
    rw [hstd]; exact standard_counterexample.2.1
  have hb : Work.BoxShrink.Core.BubbleSweep P' (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 :=
    hin.bubble idDiffeo (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 hS hZ
  rw [hstd] at hb
  exact cex_not_nonempty_bubbleSweep ⟨hb⟩

end

end Work.BoxShrink.Bubble
