import Submission.Work.BoxShrink.Pinch.PinchSweep
import Submission.Work.BoxShrink.Pinch.CutOff

/-!
# The residual of the pinch, in its weakest form

`PinchSweep.lean` reduces the challenge to Pardon's equation (1) (`Equation1Input`, the
classification of compact surfaces), the general position of the box-sphere trace (`BoxSliceNice`,
Sard plus the classification of compact `1`-manifolds) and the dimension bound `PinchStepInput`.

This module records the **sharpening** of the last of the three:

* `Work.BoxShrink.Pinch.PinchNoJump` is the *one-sided* dimension bound
  `dim (W_span boxRegion) ≤ dim (W_span (upperRegion ∪ lowerRegion)) + 1`;
* the *reverse* inequality `dim (W_span (upper ∪ lower)) ≤ dim (W_span boxRegion) + 1` of
  `PinchStepInput` is **not an input at all**: it is free, because `upperRegion ∪ lowerRegion` is
  contained in `boxRegion` and the winding span is monotone, so it never adds a dimension
  (`Work.BoxShrink.Pinch.finrank_windingSpan_halves_le_box`), whence
  `Work.BoxShrink.Pinch.pinchStepInput_of_pinchNoJump`.

So a caller who wants the chapter's residual has to supply only the dimension bound in the
direction Pardon's Lemma 2.3 supplies it — "passing the pinch does not lose *two* dimensions".

The degenerate cases of the bound are proved here outright:

* `Work.BoxShrink.Pinch.pinchNoJump_of_box_inessential` — if the box region carries no essential
  loop then its invariant is zero and the bound is trivial;
* `Work.BoxShrink.Pinch.pinchNoJump_of_sliceRegion_empty` — if the cutting plane misses the
  surface inside the box then the box region *is* the union of the two halves, so the bound holds
  with `0` on the right.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {ψ : Submission.Diffeo}

/-! ## The sharpened residual -/

/-- **Pardon's dimension bound at the pinch, in its weakest usable form.**  If neither the sphere
`∂PBox s c σ` nor the cutting plane meets the surface in an essential curve, then passing the pinch
(the single `2`-surgery of Pardon's Lemma 2.3) lowers the dimension of the invariant
`im (H₁ (F ∩ int S) ; ℚ) → H₁ (F ; ℚ)` by at most one: the region inside the box is not allowed to
collapse from the whole of `H₁` to nothing.

This is *only* the lower bound on the dimension of the union of the halves; the reverse bound is a
consequence of monotonicity (`pinchStepInput_of_pinchNoJump`). -/
def PinchNoJump : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) + 1

/-! ## The reverse inequality is free -/

/-- **The union of the two half-regions never adds a dimension.**  It is contained in the box
region, and the winding span is monotone, so its invariant is a subspace of the box region's:
the reverse inequality of `PinchStepInput` needs no geometric input. -/
theorem finrank_windingSpan_halves_le_box {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) :=
  Submodule.finrank_mono (Work.SurgeryInvariance.WindingSpan_mono _
    (Work.BoxShrink.Bubble.upper_union_lower_subset_boxRegion _ s c σ u))

/-- **`PinchStepInput` from `PinchNoJump`**: the two-sided dimension bound of `PinchSweep.lean`
follows from the one-sided bound, the other side being monotonicity. -/
theorem pinchStepInput_of_pinchNoJump (h : PinchNoJump) : PinchStepInput :=
  fun ψ s c σ u hS hZ =>
    ⟨h ψ s c σ u hS hZ,
      le_trans (finrank_windingSpan_halves_le_box (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u))
        (Nat.le_succ _)⟩

/-- **The chapter's residual, with the dimension bound in its weakest form.** -/
theorem smoothHalfS_of_pinchNoJump (h1 : Equation1Input) (hnice : BoxSliceNice)
    (hstep : PinchNoJump) : SmoothHalfS :=
  smoothHalfS_of_eq1_boxStep h1 hnice (pinchStepInput_of_pinchNoJump hstep)

/-- The same, in the vocabulary of the level-set form (`PinchLevelsInput`): the dimension bound in
its one-sided form, together with Pardon's equation (1) and the general position of the box-sphere
trace, gives Pardon's Lemma 3 for the smooth tori. -/
theorem smoothHalfS_of_equation1_boxNice_pinchNoJump (h1 : Equation1Input) (hnice : BoxSliceNice)
    (hstep : PinchNoJump) : SmoothHalfS :=
  smoothHalfS_of_pinchNoJump h1 hnice hstep

/-! ## The degenerate discharges -/

/-- **If the box region is inessential the bound is trivial.** -/
theorem pinchNoJump_of_box_inessential
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) :
    PinchNoJump := by
  intro ψ s c σ u _hS _hZ
  have hbot : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) = ⊥ :=
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr (h ψ s c σ)
  rw [hbot, Submodule.finrank_eq_zero.mpr rfl]
  exact Nat.zero_le _

/-- **If the cutting plane misses the surface inside the box then the box region is the union of
the two halves.** -/
theorem eq_halves_of_sliceRegion_empty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u = ∅) :
    Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ =
      Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u := by
  rw [Work.BoxShrink.Core.boxRegion_eq_union, h, union_empty]

/-- **If the cutting plane misses the surface inside the box the bound is trivial**: there is no
pinch at all, the region is unchanged. -/
theorem pinchNoJump_of_sliceRegion_empty
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u = ∅) :
    PinchNoJump := by
  intro ψ s c σ u _hS _hZ
  rw [eq_halves_of_sliceRegion_empty (ψ := ψ) (h ψ s c σ u)]
  exact Nat.le_succ _

end

end Work.BoxShrink.Pinch
