import Submission.Work.BoxShrink.Pinch.SliceSpanStep

/-!
# The residual in its sharpest form: only the `⊤ → ⊥` jump is at stake

`SliceSpanStep.lean` isolated the chapter's residual as the one-sided dimension bound
`PinchNoJump`.  This module removes the last slack: the winding span is a `ℚ`-subspace of
`ℚ² = H₁(T²; ℚ)`, so both sides of the bound are at most `2`, and the only way the bound can fail
is that the box region spans *everything* while the two half-regions together span *nothing*.

* `Invariant.lean`'s `finrank_windingSpan_le_two` — every winding span has dimension at most `2`;
* `pinchNoJump_iff_keyCase` — `PinchNoJump` holds exactly when the configuration

  `finrank (W_span boxRegion) = 2  ⟹  W_span (upperRegion ∪ lowerRegion) ≠ ⊥`

  holds for every box/plane configuration satisfying the two endpoint hypotheses.

So the residual is *unconditionally* (with no dichotomy input) the statement that the single
`2`-surgery of Pardon's Lemma 2.3 cannot take the invariant from the whole of `H₁` to zero — which
is Pardon's own formulation ("doing any of the allowed surgeries can change this value by at most
`1`"), and the one statement of that lemma which his paper asserts without proof.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **The key case of the residual.**  If the box region spans the whole of `H₁(T²; ℚ)`, then the
union of the two half-regions does not span nothing. -/
def PinchNoJumpKeyCase : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) = 2 →
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) ≠ ⊥

/-- **`PinchNoJump` is exactly its key case.**  Since the box region contains the two halves, its
winding span is at least as large; so the dimension bound can only fail when the box region has
dimension `2` (the maximum) and the halves have dimension `0`. -/
theorem pinchNoJump_iff_keyCase : PinchNoJump ↔ PinchNoJumpKeyCase := by
  constructor
  · intro h ψ s c σ u hS hZ htop
    intro hbot
    have hf : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
        (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) = 0 := by
      rw [hbot, Submodule.finrank_eq_zero.mpr rfl]
    have := h ψ s c σ u hS hZ
    rw [htop, hf] at this
    omega
  · intro h ψ s c σ u hS hZ
    have hbox := finrank_windingSpan_le_two (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
    rcases lt_or_ge (Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
        (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ))) 2 with hlt | hge
    · omega
    · have htop : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
          (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) = 2 :=
        le_antisymm hbox hge
      have hne := h ψ s c σ u hS hZ htop
      have hpos : 1 ≤ Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
          (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
            Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) :=
        Nat.one_le_iff_ne_zero.mpr
          (fun h0 => hne (Submodule.finrank_eq_zero.mp h0))
      omega

/-! ## The target of the chapter, as a named declaration

`PinchNoJumpKeyCaseHolds` below is *not* proved: it is the exact `Prop` that a prover must inhabit
in order to close the chapter, given the name under which it should be delegated.  By
`pinchNoJump_iff_keyCase` it is equivalent to `PinchNoJump` and hence yields, with Pardon's
dichotomy (`bubbleHalf_of_dichotomy_noJump`), `PushOffHalf`, `BubbleInputHalf`, `CruxStatement` and
Pardon's theorem — the whole chain is wired behind this single statement. -/
def PinchNoJumpKeyCaseHolds : Prop := PinchNoJumpKeyCase

theorem pinchNoJumpKeyCaseHolds_iff : PinchNoJumpKeyCaseHolds ↔ PinchNoJump := by
  rw [PinchNoJumpKeyCaseHolds, ← pinchNoJump_iff_keyCase]

end

end Work.BoxShrink.Pinch
