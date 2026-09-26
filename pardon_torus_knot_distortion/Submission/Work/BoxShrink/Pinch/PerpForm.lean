import Submission.Work.BoxShrink.Pinch.Trace

/-!
# The concrete form of the residual: the trace class and its multiples

`Trace.lean` states the pinch's residual as a *perpendicularity* statement: with `v` a nonzero
class of the trace of the cutting plane,

  `W(boxRegion) ⊓ ker (crossLin v) ≤ W(upperRegion ∪ lowerRegion)`,

where `crossLin v` is the functional `u ↦ cross u v` and `cross u v = u.1 * v.2 - u.2 * v.1`
is the symplectic intersection form on `ℚ² = H₁(T²; ℚ)`.  This module makes the statement
*concrete* by computing the kernel of that functional.

## What is new here

* `Work.BoxShrink.Pinch.cross_eq_zero_iff_eq_smul` — in the *two*-dimensional symplectic module
  `ℚ²`, a vector is crossed trivially by `v ≠ 0` exactly when it is a multiple of `v`:
  `cross u v = 0 ↔ ∃ a : ℚ, u = a • v`;
* `Work.BoxShrink.Pinch.ker_crossLin_eq_span` — hence `ker (crossLin v) = ℚ ∙ v` for `v ≠ 0`;
* `Work.BoxShrink.Pinch.inf_span_le_iff_inf_ker_le` — so the residual is *equivalent* to the much
  more concrete `W(boxRegion) ⊓ ℚ ∙ v ≤ W(halves)`;
* `Work.BoxShrink.Pinch.finrank_le_succ_of_inf_span_le` — and that containment gives the pinch
  `dim (W box) ≤ dim (W halves) + 1` whenever `v ≠ 0`;
* `Work.BoxShrink.Pinch.TraceMultipleRealisable`, `…All` — the residual in the concrete form;
* `Work.BoxShrink.Pinch.tracePerpRealisable_iff_traceMultipleRealisable` — the two forms of the
  residual are *the same statement*;
* the whole endgame again in the concrete form
  (`pinchNoJumpAll_of_traceMultipleRealisableAll`, `smoothHalfS_of_…`,
  `pushOffHalf_of_boxDichotomy_multiple`, `bubbleInputHalf_of_boxDichotomy_multiple`,
  `cruxStatement_of_boxDichotomy_multiple`,
  `pardon_torus_knot_distortion_of_equation1_boxNice_multiple`), so that a caller may consume
  whichever form is proved.

## Why this is the "right" form of the residual

`v` is the class of a component of the trace `F ∩ P`, i.e. of a loop of the *surface* lying in
the cutting plane, and the statement is:

> **every multiple of the trace class realised by a loop of the region inside the box is already
> realised in the union of the two half-regions.**

Geometrically this is exactly the statement that a loop whose *algebraic crossing number with the
trace vanishes* can be pushed off the trace — and hence off the slice, since the loop lies in the
box and the trace leaves the box — with the push staying inside the region.  It is *strictly
stronger* than the pinch: at the standard small box the trace is essential
(`Work.BoxShrink.Pinch.BubbleHalfRefuted`), the lost class is the longitudinal one, and the bound
`≤ + 1` is tight, yet the trace class itself (`(0,1)` there) is *not* realised by any loop of the
box, so the containment holds with `W(box) ⊓ ℚ ∙ v = ⊥`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The kernel of the crossing functional -/

/-- **In the two-dimensional symplectic module `ℚ²`, the orthogonal of `v ≠ 0` is the line
through `v`.**  If `cross u v = 0` and `v ≠ 0`, then `u` is a multiple of `v`. -/
theorem cross_eq_zero_iff_eq_smul {v u : ℚ × ℚ} (hv : v ≠ 0) :
    cross u v = 0 ↔ ∃ a : ℚ, u = a • v := by
  constructor
  · intro h
    rcases eq_or_ne v.1 0 with h1 | h1
    · -- `v.1 = 0`, so `v.2 ≠ 0` and `cross u v = u.1 * v.2`, whence `u.1 = 0`
      have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
      have hu1 : u.1 = 0 := by
        have h0 : u.1 * v.2 = 0 := by simpa [cross, h1] using h
        exact (mul_eq_zero.mp h0).resolve_right h2
      refine ⟨u.2 / v.2, Prod.ext ?_ ?_⟩
      · rw [Prod.smul_fst, smul_eq_mul, h1, mul_zero]; exact hu1
      · rw [Prod.smul_snd, smul_eq_mul, div_mul_cancel₀ _ h2]
    · -- `v.1 ≠ 0`: write `u = (u.1 / v.1) • v` using `cross u v = 0`
      have hcross : u.2 * v.1 = u.1 * v.2 := by
        have h' := h; simp only [cross] at h'; linarith
      refine ⟨u.1 / v.1, Prod.ext ?_ ?_⟩
      · rw [Prod.smul_fst, smul_eq_mul, div_mul_cancel₀ _ h1]
      · rw [Prod.smul_snd, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h1]
        linarith
  · rintro ⟨a, rfl⟩
    simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- **The kernel of `u ↦ cross u v` is the line spanned by `v`** (for `v ≠ 0`). -/
theorem ker_crossLin_eq_span {v : ℚ × ℚ} (hv : v ≠ 0) :
    LinearMap.ker (crossLin v) = Submodule.span ℚ {v} := by
  ext u
  rw [LinearMap.mem_ker, crossLin_apply, cross_eq_zero_iff_eq_smul hv]
  constructor
  · rintro ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  · intro hu
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨a, ha⟩ := hu
    exact ⟨a, ha.symm⟩

/-- **Two classes with vanishing cross product lie in one line.**  Packaged form of
`cross_eq_zero_iff_eq_smul`: this is the linear-algebra step that turns the collinearity of the
trace's classes (`Work.BoxShrink.Pinch.DisjointLoopsWindingDet` for two disjoint trace components)
into the existence of the trace's line. -/
theorem exists_line_of_cross_eq_zero {v w : ℚ × ℚ} (hw : w ≠ 0) (h : cross v w = 0) :
    ∃ L : Submodule ℚ (ℚ × ℚ), Module.finrank ℚ ↥L ≤ 1 ∧ v ∈ L ∧ w ∈ L := by
  obtain ⟨a, ha⟩ := (cross_eq_zero_iff_eq_smul hw).mp h
  refine ⟨Submodule.span ℚ {w}, ?_, ?_, Submodule.subset_span (Set.mem_singleton w)⟩
  · rcases eq_or_ne w 0 with rfl | hw'
    · rw [Set.singleton_zero, Submodule.span_zero, finrank_bot]
      norm_num
    · rw [finrank_span_singleton hw']
  · rw [ha]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))

/-- **The two forms of the residual are the same statement.**  The perpendicularity form
`W ⊓ ker (crossLin v) ≤ B` coincides with the concrete form `W ⊓ ℚ ∙ v ≤ B`. -/
theorem inf_span_le_iff_inf_ker_le {W B : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ} (hv : v ≠ 0) :
    W ⊓ Submodule.span ℚ {v} ≤ B ↔ W ⊓ LinearMap.ker (crossLin v) ≤ B := by
  rw [ker_crossLin_eq_span hv]

/-- **The pinch from the concrete form.**  If the multiples of a nonzero class `v` realised in `A`
are realised in `B`, then `dim (W A) ≤ dim (W B) + 1`. -/
theorem finrank_le_succ_of_inf_span_le {A B : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ} (hv : v ≠ 0)
    (h : A ⊓ Submodule.span ℚ {v} ≤ B) :
    Module.finrank ℚ ↥A ≤ Module.finrank ℚ ↥B + 1 :=
  finrank_le_succ_of_inf_ker_le hv ((inf_span_le_iff_inf_ker_le hv).mp h)

/-! ## The residual in the concrete form -/

/-- **The residual, concrete form.**  Either the box region does not drop at all, or there is a
nonzero *trace* class `v` such that every multiple of `v` realised in the box region is already
realised in the union of the two half-regions.

By `ker_crossLin_eq_span` this is *literally* the first branch of
`Work.BoxShrink.Pinch.TracePerpRealisable`, but it is the form in which the geometric content
("a loop whose crossing number with the trace vanishes can be pushed off the trace") is visible:
the multiples of the trace class are the loops that cross the trace trivially. -/
def TraceMultipleRealisable (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∨
    ∃ v : ℚ × ℚ, v ≠ 0 ∧ (∃ L : Submodule ℚ (ℚ × ℚ), TraceLine P c σ u L ∧ v ∈ L) ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
          Submodule.span ℚ {v} ≤
        Work.SurgeryInvariance.WindingSpan P
          (Work.BoxShrink.Core.upperRegion P s c σ u ∪
            Work.BoxShrink.Core.lowerRegion P s c σ u)

/-- The concrete residual for every configuration whose slice carries no essential loop. -/
def TraceMultipleRealisableAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    TraceMultipleRealisable P s c σ u

/-- **The two forms of the residual coincide.** -/
theorem tracePerpRealisable_iff_traceMultipleRealisable {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    TracePerpRealisable P s c σ u ↔ TraceMultipleRealisable P s c σ u := by
  constructor
  · rintro (h | ⟨v, hv, hL, hperp⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, hL, (inf_span_le_iff_inf_ker_le hv).mpr hperp⟩
  · rintro (h | ⟨v, hv, hL, hperp⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, hL, (inf_span_le_iff_inf_ker_le hv).mp hperp⟩

theorem tracePerpRealisableAll_iff_traceMultipleRealisableAll :
    TracePerpRealisableAll ↔ TraceMultipleRealisableAll := by
  constructor
  · intro h P s c σ u hZ
    exact (tracePerpRealisable_iff_traceMultipleRealisable (P := P)).mp (h P s c σ u hZ)
  · intro h P s c σ u hZ
    exact (tracePerpRealisable_iff_traceMultipleRealisable (P := P)).mpr (h P s c σ u hZ)

/-! ## The endgame in the concrete form -/

/-- **The pinch from the concrete residual.** -/
theorem pinchNoJumpAll_of_traceMultipleRealisableAll (h : TraceMultipleRealisableAll) :
    PinchNoJumpAll :=
  pinchNoJumpAll_of_tracePerpRealisableAll
    (tracePerpRealisableAll_iff_traceMultipleRealisableAll.mpr h)

/-- **The chapter's residual `PinchNoJump` from the concrete form.** -/
theorem pinchNoJump_of_traceMultipleRealisableAll (h : TraceMultipleRealisableAll) :
    PinchNoJump :=
  pinchNoJump_of_tracePerpRealisableAll
    (tracePerpRealisableAll_iff_traceMultipleRealisableAll.mpr h)

/-- **Pardon's Lemma 3 for the smooth tori, from the concrete residual.** -/
theorem smoothHalfS_of_traceMultipleRealisableAll (h1 : Equation1Input) (hnice : BoxSliceNice)
    (h : TraceMultipleRealisableAll) : SmoothHalfS :=
  smoothHalfS_of_tracePerpRealisableAll h1 hnice
    (tracePerpRealisableAll_iff_traceMultipleRealisableAll.mpr h)

/-- **The caller's field `Work.BoxShrink.Bubble.PushOffHalf`, from the concrete residual.** -/
theorem pushOffHalf_of_boxDichotomy_multiple (hdich : BoxDichotomyInput)
    (h : TraceMultipleRealisableAll) : Work.BoxShrink.Bubble.PushOffHalf :=
  pushOffHalf_of_boxDichotomy_trace hdich
    (tracePerpRealisableAll_iff_traceMultipleRealisableAll.mpr h)

/-- **The caller's field `Work.BoxShrink.Bubble.BubbleInputHalf`, from the concrete residual.** -/
theorem bubbleInputHalf_of_boxDichotomy_multiple
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (h : TraceMultipleRealisableAll) :
    Work.BoxShrink.Bubble.BubbleInputHalf :=
  bubbleInputHalf_of_boxDichotomy_trace hcleanD hdich
    (tracePerpRealisableAll_iff_traceMultipleRealisableAll.mpr h)

/-- **The crux, from the concrete residual.** -/
theorem cruxStatement_of_boxDichotomy_multiple
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (h : TraceMultipleRealisableAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  cruxStatement_of_boxDichotomy_trace hcleanD hdich
    (tracePerpRealisableAll_iff_traceMultipleRealisableAll.mpr h) hclean hae

/-- **Pardon's Theorem 1.1 from the concrete residual.** -/
theorem pardon_torus_knot_distortion_of_equation1_boxNice_multiple
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (hnice : BoxSliceNice) (h : TraceMultipleRealisableAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q) (K : Knot)
      (_hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_equation1_boxNice_trace hcleanD h1 hnice
    (tracePerpRealisableAll_iff_traceMultipleRealisableAll.mpr h) hclean hae

end

end Work.BoxShrink.Pinch
