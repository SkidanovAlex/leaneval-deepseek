import Submission.Work.BoxShrink.Pinch.PerpForm

/-!
# The pinch residual: the cases in which it is discharged, and its sharpest form

`Work.BoxShrink.Pinch.PerpForm` states the residual of the pinch (`TraceMultipleRealisable`) as

  `W(boxRegion) ≤ W(halves)`  **or**  there is a nonzero class `v` lying in a *trace line*
  (`TraceLine`, i.e. a line containing all the periods of the trace `F ∩ Π` of the cutting plane)
  with `W(boxRegion) ⊓ ℚ∙v ≤ W(halves)`.

This module records what that disjunction *is* in terms of the trace line, and discharges it in
three cases.  Its content is the following observation, which localises the residual precisely.

Let `L` be a trace line (a line containing every period of the trace, so that (K0) — the theorem
`Work.BoxShrink.Pinch.TraceLineAll` for the smooth tori of the challenge — can supply it), and let
`W(box)`, `W(halves)` be the winding spans of the box region and of the union of the two
half-regions.

* If `W (box) ≤ W (halves)`, the residual holds (its first disjunct).
* If `L` realises a class `v ≠ 0` which is *already realised in the halves* (`v ∈ W (halves)`), the
  residual holds: `W (box) ⊓ ℚ∙v ≤ ℚ∙v ≤ W (halves)`.
* **New.** If `L ⊄ W (box)` — if the trace realises a period of the torus which the region inside the
  box does *not* realise — the residual **also holds**, and no hypothesis on the halves is needed:
  choose `v ∈ L ∖ W (box)`; then `v ≠ 0` and `W (box) ⊓ ℚ∙v = ⊥`, because `W (box)` is a `ℚ`-subspace
  and `v ∉ W (box)` forbids nonzero multiples of `v` from lying in it.

Consequently the residual reduces to its hard case: *every* trace line is contained in `W (box)`
(so the trace's periods are all realised inside the box), and the trace's line meets `W (halves)`
only in `0`.  Formally, the residual follows from

  `TraceLineAll` + `TraceSharp`,

where `TraceSharp` is the statement that for every configuration with inessential slice and every
trace line `L`: `L ⊄ W (box)`, or `L ⊓ W (halves) ≠ ⊥`, or `W (box) ≤ W (halves)`
(`traceMultipleRealisableAll_of_traceSharp`).  The two first alternatives are the cases discharged
here; the third is the first disjunct of the residual; so `TraceSharp` is precisely "no
configuration in which the trace's period line is realised in the box but misses the halves".

The hard case is the *finger move*: a loop of the box region whose algebraic crossing number with
the trace vanishes has to be pushed off the trace by a homotopy inside the box (Pardon's
cancellation of crossings).  All the geometric content of Pardon's Lemma 3 which is still open sits
there; see `README.md` §6.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- Abbreviation: the winding span of the region of the surface inside the box. -/
abbrev Wbox (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Submodule ℚ (ℚ × ℚ) :=
  Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ)

/-- Abbreviation: the winding span of the union of the two half-regions. -/
abbrev Whalves (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Submodule ℚ (ℚ × ℚ) :=
  Work.SurgeryInvariance.WindingSpan P
    (Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u)

/-! ## The three discharged cases -/

/-- **The first disjunct of the residual**: if the box region does not enlarge the winding span,
Pardon's bound holds at the configuration. -/
theorem traceMultipleRealisable_of_le (h : Wbox P s c σ ≤ Whalves P s c σ u) :
    Work.BoxShrink.Pinch.TraceMultipleRealisable P s c σ u :=
  Or.inl h

/-- **A trace class realised in the halves discharges the residual.**  If a nonzero class lying in a
trace line is already realised by a loop of the union of the two half-regions, then
`W (box) ⊓ ℚ∙v ≤ ℚ∙v ≤ W (halves)` and the second disjunct of the residual applies. -/
theorem traceMultipleRealisable_of_mem_halves
    (h : ∃ v : ℚ × ℚ, v ≠ 0 ∧ (∃ L : Submodule ℚ (ℚ × ℚ),
        Work.BoxShrink.Pinch.TraceLine P c σ u L ∧ v ∈ L) ∧ v ∈ Whalves P s c σ u) :
    Work.BoxShrink.Pinch.TraceMultipleRealisable P s c σ u := by
  obtain ⟨v, hv, hvL, hvW⟩ := h
  refine Or.inr ⟨v, hv, hvL, ?_⟩
  refine le_trans inf_le_right ?_
  rw [Submodule.span_le]
  simpa using hvW

/-- **A trace line which is not contained in the span of the box region discharges the residual.**

If the trace of the cutting plane realises a period which the region inside the box does not
realise, then choosing `v ∈ L ∖ W (box)` gives `v ≠ 0` and `W (box) ⊓ ℚ∙v = ⊥`, so the second
disjunct of the residual holds *without any knowledge of the half-regions*.  This is the case in
which the box region is "too small" to carry the trace's class (for instance a box cutting the
surface in an annulus whose core is not the trace's class). -/
theorem traceMultipleRealisable_of_trace_line_not_le
    (h : ∃ L : Submodule ℚ (ℚ × ℚ), Work.BoxShrink.Pinch.TraceLine P c σ u L ∧
      ¬ L ≤ Wbox P s c σ) :
    Work.BoxShrink.Pinch.TraceMultipleRealisable P s c σ u := by
  classical
  obtain ⟨L, hL, hLnot⟩ := h
  obtain ⟨v, hvL, hvnot⟩ : ∃ v ∈ L, v ∉ Wbox P s c σ := by
    by_contra hc
    apply hLnot
    intro x hx
    by_contra hxnot
    exact hc ⟨x, hx, hxnot⟩
  have hvne : v ≠ 0 := by
    intro h0
    exact hvnot (h0 ▸ Submodule.zero_mem _)
  have hfin : Wbox P s c σ ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxb, hxv⟩ := hx
    rw [Submodule.mem_span_singleton] at hxv
    obtain ⟨a, rfl⟩ := hxv
    by_cases ha : a = 0
    · simp [ha]
    · exact absurd (show v ∈ Wbox P s c σ from by
        have : v = a⁻¹ • (a • v) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ hxb) hvnot
  exact Or.inr ⟨v, hvne, ⟨L, hL, hvL⟩, by rw [hfin]; exact bot_le⟩

/-! ## The sharpened residual -/

/-- **The sharp form of the residual.**  For every configuration whose slice carries no essential
loop, and every trace line `L`: either `L` is not contained in the span of the box region, or `L`
meets the span of the halves, or the span does not grow at all.  This is what remains of Pardon's
Lemma 3 after the two discharge theorems above: only configurations in which the trace's period line
*is* realised inside the box and *misses* the halves are left. -/
def TraceSharp : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    ∀ L : Submodule ℚ (ℚ × ℚ), Work.BoxShrink.Pinch.TraceLine P c σ u L →
      (¬ L ≤ Wbox P s c σ) ∨ (L ⊓ Whalves P s c σ u ≠ ⊥) ∨ (Wbox P s c σ ≤ Whalves P s c σ u)

/-- **The sharp form, together with (K0), gives the residual.**  If every plane trace has a line
containing all its periods (`TraceLineAll`, the proved statement
`Work.BoxShrink.Pinch.TraceLineAll` for the smooth tori of the challenge) and the sharp form
`TraceSharp` holds, then the residual `TraceMultipleRealisableAll` holds: the first alternative is
`traceMultipleRealisable_of_trace_line_not_le`, the second is
`traceMultipleRealisable_of_mem_halves` (a nonzero element of `L ⊓ W (halves)` is a trace class
realised in the halves), and the third is the first disjunct of the residual. -/
theorem traceMultipleRealisableAll_of_traceSharp
    (hline : Work.BoxShrink.Pinch.TraceLineAll) (hsharp : TraceSharp) :
    Work.BoxShrink.Pinch.TraceMultipleRealisableAll := by
  intro P s c σ u hZ
  obtain ⟨L₀, hL₀⟩ := hline P c σ u
  rcases hsharp P s c σ u hZ L₀ hL₀ with hnotle | hmeet | hle
  · exact traceMultipleRealisable_of_trace_line_not_le ⟨L₀, hL₀, hnotle⟩
  · obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmeet
    exact traceMultipleRealisable_of_mem_halves
      ⟨v, hvne, ⟨L₀, hL₀, (Submodule.mem_inf.mp hv).1⟩, (Submodule.mem_inf.mp hv).2⟩
  · exact traceMultipleRealisable_of_le hle

/-- **The endgame in the sharp form**: the two carried classical inputs (Pardon's equation (1) and
the general position of the box-sphere trace) and the sharp form of the residual give Pardon's
Lemma 3 for the smooth tori of the challenge. -/
theorem smoothHalfS_of_traceSharp (h1 : Work.BoxShrink.Pinch.Equation1Input)
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice) (hline : Work.BoxShrink.Pinch.TraceLineAll)
    (hsharp : TraceSharp) : Work.BoxShrink.Pinch.SmoothHalfS :=
  Work.BoxShrink.Pinch.smoothHalfS_of_traceMultipleRealisableAll h1 hnice
    (traceMultipleRealisableAll_of_traceSharp hline hsharp)

/-- **Pardon's theorem from the sharp form of the residual.** -/
theorem pardon_torus_knot_distortion_of_traceSharp
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Work.BoxShrink.Pinch.Equation1Input) (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hline : Work.BoxShrink.Pinch.TraceLineAll) (hsharp : TraceSharp)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.Pinch.pardon_torus_knot_distortion_of_smoothHalfS hdisc
    (smoothHalfS_of_traceSharp h1 hnice hline hsharp) hclean hae

end

end Work.BoxShrink.PinchOff
