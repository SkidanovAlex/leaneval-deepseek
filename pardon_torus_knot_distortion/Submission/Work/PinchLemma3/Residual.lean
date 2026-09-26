import Submission.Work.PinchLemma3.Defs

/-!
# The residual of the pinch, in the wall form

This module states the chapter's residual and proves that it is the parent chapter's residual, and
that it gives Pardon's Lemma 3 and Pardon's theorem.

## The residual, and why it is a *dimension* bound and not a span containment

The configuration is: `F = Work.Smooth.Morse.torus ψ`, the box `PBox s c σ`, the cutting plane
`{y | y (σ 2) = c (σ 2) + u}`, and

* `Ω = boxRegion P s c σ = F ∩ PBox` — the region inside the box,
* `Ω⁺`, `Ω⁻` — the two half-regions, `halfRegions = Ω⁺ ∪ Ω⁻`,
* `Σ = sliceRegion P s c σ u` — the **walls**: the trace of the cutting plane inside the box,
* `Γ = planeTrace P c σ u = F ∩ P` — the trace of the cutting plane.

The residual `SliceWall` is the one-sided dimension bound

  `dim W(Ω) ≤ dim W(Ω⁺ ∪ Ω⁻) + 1`,

under both of Pardon's endpoint hypotheses (the box sphere `∂PBox s c σ` and the slice `Σ` carry no
essential loop of the surface).  This is *exactly* `Work.BoxShrink.Pinch.PinchNoJump` and
`Work.BoxShrink.PinchOff.Key` (`sliceWall_iff_pinchNoJump`, `key_of_sliceWall`); the module exists
in order to state it in the chapter's own vocabulary — with the walls, the caps and the *closed*
halves of `Defs.lean` — and to carry the reductions to Pardon's Lemma 3 and Pardon's theorem.

**The bound must be a dimension bound.**  The natural-looking *stronger* statements — the span
containment `W(Ω) ≤ W(Ω⁺ ∪ Ω⁻)` (`Work.BoxShrink.Pinch.SpanPushOff`,
`Work.BoxShrink.Pinch.TraceClassBoundSpanBot`), the "one trace class" form
`Work.BoxShrink.Pinch.TraceClassBound`, and every *transport* form
(`Work.BoxShrink.Pinch.RegionTransport`) — are **false** for the box/plane geometry at
configurations satisfying both endpoint hypotheses, and their falsity is recorded in the parent
chapter (`Work.BoxShrink.Pinch.RefuteSpan.not_windingSpan_le_halves_standard`,
`Work.BoxShrink.PinchOff.Refute.not_transport`, the numerical tables of
`Submission/Work/BoxShrink/Pinch/EXP`).  What survives is the `+ 1` bound: the box region may lose
exactly one dimension at the pinch, never two.  The only form of the residual worth stating is
therefore the dimension bound, and `sliceWall_of_traceClassBound` below records that the (false)
span forms would have been *sufficient*: they imply it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchLemma3

noncomputable section

/-! ## The residual -/

/-- **The wall budget — Pardon's Lemma 3 as a dimension bound.**  Under both of Pardon's endpoint
hypotheses, passing the pinch (the single `2`-surgery of the double bubble along the flat disc cut
out of the box by the cutting plane) lowers the dimension of the invariant
`im (H₁ (F ∩ int S) ; ℚ) → H₁ (F ; ℚ)` — computed here as the winding span — by at most one.

This is `Work.BoxShrink.Pinch.PinchNoJump` in the vocabulary of this chapter. -/
def SliceWall : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (halfRegions (Work.Smooth.Morse.torus ψ) s c σ u)) + 1

/-- **The residual is the parent chapter's `PinchNoJump`** — the definition is the same, the two
half-regions being `Work.PinchLemma3.halfRegions`. -/
theorem sliceWall_iff_pinchNoJump : SliceWall ↔ Work.BoxShrink.Pinch.PinchNoJump := Iff.rfl

/-- The residual gives Pardon's one-sided dimension bound. -/
theorem pinchNoJump_of_sliceWall (h : SliceWall) : Work.BoxShrink.Pinch.PinchNoJump := h

/-- Conversely. -/
theorem sliceWall_of_pinchNoJump (h : Work.BoxShrink.Pinch.PinchNoJump) : SliceWall := h

/-- **The residual gives the sibling chapter's residual** (`Work.BoxShrink.PinchOff.Key`, the
one-sided dimension bound with the primitive lattice in place of `2πℤ²`). -/
theorem key_of_sliceWall (h : SliceWall) : Work.BoxShrink.PinchOff.Key :=
  Work.BoxShrink.PinchOff.key_iff_pinchNoJump.mpr h

/-- **The span forms are *sufficient*.**  `Work.BoxShrink.Pinch.TraceClassBound` is stronger than
the wall budget and implies it: a class whose multiples realised in `Ω` lie in the span of the
halves costs at most one dimension
(`Work.BoxShrink.Pinch.finrank_le_succ_of_inf_span_le`).  The span forms are false for the
box/plane geometry (see the module docstring), so this is a one-way implication, recorded because
it is the route along which the *proved* cases of the pinch reach the residual. -/
theorem pinchNoJump_of_traceClassBound {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : Work.BoxShrink.Pinch.TraceClassBound P s c σ u) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u)) + 1 := by
  rcases h with hle | ⟨v, hv, -, hperp⟩
  · exact le_trans (Submodule.finrank_mono hle) (Nat.le_succ _)
  · exact Work.BoxShrink.Pinch.finrank_le_succ_of_inf_span_le hv hperp

/-- The same at the level of the residual. -/
theorem sliceWall_of_traceClassBoundAll
    (h : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Pinch.TraceClassBound P s c σ u) : SliceWall :=
  fun ψ s c σ u _hS hZ => pinchNoJump_of_traceClassBound (h _ s c σ u hZ)

/-! ## Pardon's Lemma 3, and the challenge -/

/-- **Pardon's Lemma 3 under both of his endpoint hypotheses, from the wall budget.**  Besides the
wall budget the two classical inputs of the chapter are used: Pardon's equation (1)
(`Equation1Input`, the classification of compact surfaces in the shape the dichotomy consumes) and
the general position of the box-sphere trace (`BoxSliceNice`, Sard plus the classification of
compact `1`-manifolds). -/
theorem smoothHalfS_of_sliceWall (h1 : Work.BoxShrink.Pinch.Equation1Input)
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice) (h : SliceWall) :
    Work.BoxShrink.Pinch.SmoothHalfS :=
  Work.BoxShrink.Pinch.smoothHalfS_of_pinchNoJump h1 hnice h

/-- **The corrected final input of the challenge** (`Work.BoxShrink.Pinch.FinalInputS`) from the
wall budget, the cut-and-paste input at the flat disc and the two classical inputs. -/
theorem finalInputS_of_sliceWall
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Work.BoxShrink.Pinch.Equation1Input) (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : SliceWall) (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    Work.BoxShrink.Pinch.FinalInputS :=
  Work.BoxShrink.Pinch.finalInputS_of_smoothHalfS hdisc (smoothHalfS_of_sliceWall h1 hnice h)
    hclean hae

/-- **Pardon's theorem from the wall budget.**  The wall budget and the classical inputs of the
development give Pardon's Theorem 1.1. -/
theorem pardon_torus_knot_distortion_of_sliceWall
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Work.BoxShrink.Pinch.Equation1Input) (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : SliceWall) (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q) (K : Knot)
      (_hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.Pinch.pardon_torus_knot_distortion_of_smoothHalfS hdisc
    (smoothHalfS_of_sliceWall h1 hnice h) hclean hae

end

end Work.PinchLemma3
