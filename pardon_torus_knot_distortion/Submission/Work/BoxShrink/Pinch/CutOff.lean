import Submission.Work.BoxShrink.Pinch.Surfaces
import Submission.Work.BoxShrink.Pinch.PinchSweep

/-!
# The cut-off family of the slice, and the endgame of the pinch

The **cut-off** of the box region at scale `ε` is

  `cutOff P s c σ u ε = boxRegion ∩ {y | ε ≤ |y (σ 2) - (c (σ 2) + u)|}`,

the part of the box region at height at least `ε` from the cutting plane.  It is antitone in `ε`,
it is contained in `upperRegion ∪ lowerRegion` for `ε > 0`, and every compact loop of the two
half-regions lies in some `cutOff ε` — so `ContainsEssentialLoop (upperRegion ∪ lowerRegion)` is
equivalent to `∃ ε > 0, ContainsEssentialLoop (cutOff P s c σ u ε)`.

The endgame of the pinch is the single statement

  `bubbleHalf_of_span_le`: `PardonDichotomy`-free — if the slice carries no essential loop and the
  winding span of the box region is contained in the span of the two halves together with that of
  the slice, then one of the two halves carries an essential loop.

This is Pardon's last step in its cleanest form: the pinch is the passage from "the whole box" to
"the box minus the slice", and the only thing it can lose is the slicing plane, whose span is `⊥`
under the hypothesis `hZ`.  `SpanPushOff` is the corresponding uniform input, and
`pinchStepInput_of_spanPushOff` shows that it implies the dimension bound of `PinchSweep.lean`, so
the two presentations of the residual are interlocked.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The cut-off family -/

/-- **The cut-off of the box region at scale `ε`**: the part at height at least `ε` from the plane. -/
def cutOff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u ε : ℝ) : Set R3 :=
  Work.BoxShrink.Core.boxRegion P s c σ ∩
    {y : R3 | ε ≤ |y (σ 2) - (c (σ 2) + u)|}

@[simp] theorem mem_cutOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u ε : ℝ} {y : R3} :
    y ∈ cutOff P s c σ u ε ↔ y ∈ Work.BoxShrink.Core.boxRegion P s c σ ∧
      ε ≤ |y (σ 2) - (c (σ 2) + u)| := Iff.rfl

theorem cutOff_subset_boxRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u ε : ℝ} :
    cutOff P s c σ u ε ⊆ Work.BoxShrink.Core.boxRegion P s c σ := inter_subset_left

/-- The cut-off family is antitone in the scale. -/
theorem cutOff_antitone {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u ε ε' : ℝ} (h : ε ≤ ε') :
    cutOff P s c σ u ε' ⊆ cutOff P s c σ u ε :=
  fun _ hy => ⟨hy.1, le_trans h hy.2⟩

/-- **A positive cut-off lies in the two half-regions.** -/
theorem cutOff_subset_union {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u ε : ℝ} (hε : 0 < ε) :
    cutOff P s c σ u ε ⊆ Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u := by
  intro y hy
  have hyc : y ∈ P.carrier := hy.1.1
  have hyb : y ∈ Submission.PBox s c σ := hy.1.2
  have hne : y (σ 2) - (c (σ 2) + u) ≠ 0 := by
    intro h0
    have hle : ε ≤ |y (σ 2) - (c (σ 2) + u)| := hy.2
    rw [h0, abs_zero] at hle
    linarith
  rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with h | h | h
  · exact Or.inr ((Work.BoxShrink.Core.mem_lowerRegion).mpr ⟨hyc, hyb, h⟩)
  · exact absurd (by linarith : y (σ 2) - (c (σ 2) + u) = 0) hne
  · exact Or.inl ((Work.BoxShrink.Core.mem_upperRegion).mpr ⟨hyc, hyb, h⟩)

theorem windingSpan_cutOff_antitone {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u ε ε' : ℝ}
    (h : ε ≤ ε') :
    Work.SurgeryInvariance.WindingSpan P (cutOff P s c σ u ε') ≤
      Work.SurgeryInvariance.WindingSpan P (cutOff P s c σ u ε) :=
  Work.SurgeryInvariance.WindingSpan_mono P (cutOff_antitone h)

/-! ## Splitting a set of curves into three pieces -/

/-- **The winding span of a set of curves is contained in the supremum of three pieces** when every
loop in the set lies entirely in one of the three. -/
theorem windingSpan_le_sup_of_three_splits {A A' B C : Set R3}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ.γ t ∈ A) →
      (∀ t : ℝ, γ.γ t ∈ A') ∨ (∀ t : ℝ, γ.γ t ∈ B) ∨ (∀ t : ℝ, γ.γ t ∈ C)) :
    Work.SurgeryInvariance.WindingSpan P A ≤
      Work.SurgeryInvariance.WindingSpan P A' ⊔ Work.SurgeryInvariance.WindingSpan P B ⊔
        Work.SurgeryInvariance.WindingSpan P C := by
  rw [Work.SurgeryInvariance.WindingSpan]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨γ, hγ, hv⟩
  rw [← hv]
  rcases h γ hγ with hA' | hB | hC
  · have h1 : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈
        Work.SurgeryInvariance.WindingSpan P A' := Submodule.subset_span ⟨γ, hA', rfl⟩
    exact (SetLike.le_def.mp le_sup_left) ((SetLike.le_def.mp le_sup_left) h1)
  · have h1 : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈
        Work.SurgeryInvariance.WindingSpan P B := Submodule.subset_span ⟨γ, hB, rfl⟩
    exact (SetLike.le_def.mp le_sup_left) ((SetLike.le_def.mp le_sup_right) h1)
  · have h1 : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈
        Work.SurgeryInvariance.WindingSpan P C := Submodule.subset_span ⟨γ, hC, rfl⟩
    exact (SetLike.le_def.mp le_sup_right) h1

/-! ## The endgame of the pinch -/

/-- **Pardon's endgame, without any dichotomy.**  If the slice carries no essential loop
(`WSpan sliceRegion = ⊥`, Pardon's hypothesis `hZ`) and the winding span of the box region is
contained in the span of the two half-regions together with that of the slice, then an essential
loop of the box region survives to one of the two halves.

This is the passage from `boxRegion` to `boxRegion ∖ sliceRegion` = `upperRegion ∪ lowerRegion`:
the removed piece is the slice, and `hZ` says it contributes nothing. -/
theorem bubbleHalf_of_span_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hZ : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.sliceRegion P s c σ u) = ⊥)
    (hspan : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
          Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) ⊔
        Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.sliceRegion P s c σ u)) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hbox
  have hsup : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ := by
    intro hbot
    refine hne (le_bot_iff.mp ?_)
    refine le_trans hspan ?_
    rw [hZ, sup_bot_eq]
    exact le_of_eq hbot
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ =>
      hsup (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

/-- **A positive cut-off being essential forces the endgame.**  Since every cut-off is contained in
the union of the two half-regions, this is the endgame for the cut-off family. -/
theorem bubbleHalf_of_cutOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan P (cutOff P s c σ u ε) ≠ ⊥) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  obtain ⟨ε, hε, hne⟩ := h
  intro hbox
  have hspan := Work.SurgeryInvariance.Span.union_eq_sup (P := P)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)
  have hle : Work.SurgeryInvariance.WindingSpan P (cutOff P s c σ u ε) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
        Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) := by
    rw [← hspan]
    exact Work.SurgeryInvariance.WindingSpan_mono P (cutOff_subset_union hε)
  have hsup : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ :=
    fun hbot => hne (le_bot_iff.mp (by rw [hbot] at hle; exact hle))
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ =>
      hsup (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

/-- **A loop of the two half-regions lies in a positive cut-off.**  The image of a closed curve is
compact and the height function is continuous and nowhere zero on it, so it is bounded below by a
positive constant: the cut-off family is cofinal in the union of the two half-regions. -/
theorem exists_cutOff_of_mem_union {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (γ : Work.CoreTopology.ClosedCurve P)
    (h : ∀ t : ℝ, γ.γ t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, γ.γ t ∈ cutOff P s c σ u ε := by
  have hmem : ∀ t : ℝ, γ.γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ := fun t => by
    rcases h t with hh | hh
    · exact ⟨(Work.BoxShrink.Core.mem_upperRegion.mp hh).1,
        (Work.BoxShrink.Core.mem_upperRegion.mp hh).2.1⟩
    · exact ⟨(Work.BoxShrink.Core.mem_lowerRegion.mp hh).1,
        (Work.BoxShrink.Core.mem_lowerRegion.mp hh).2.1⟩
  have hpos : ∀ t : ℝ, 0 < |γ.γ t (σ 2) - (c (σ 2) + u)| := by
    intro t
    refine abs_pos.mpr ?_
    rcases h t with hh | hh
    · intro h0
      have := (Work.BoxShrink.Core.mem_upperRegion.mp hh).2.2
      linarith
    · intro h0
      have := (Work.BoxShrink.Core.mem_lowerRegion.mp hh).2.2
      linarith
  have hcont : Continuous fun t : ℝ => |γ.γ t (σ 2) - (c (σ 2) + u)| := by
    refine Continuous.abs ?_
    have h1 : Continuous fun t : ℝ => Work.BoxShrink.Bubble.planeCoord c σ u (γ.γ t) :=
      (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).continuous.comp γ.cont
    simpa only [Work.BoxShrink.Bubble.planeCoord] using h1
  have hper : Function.Periodic (fun t : ℝ => |γ.γ t (σ 2) - (c (σ 2) + u)|) (2 * Real.pi) := by
    intro t
    show |γ.γ (t + 2 * Real.pi) (σ 2) - (c (σ 2) + u)| = |γ.γ t (σ 2) - (c (σ 2) + u)|
    rw [γ.periodic t]
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨t₀, -, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_isMinOn
    ⟨0, le_refl 0, le_of_lt hT⟩ hcont.continuousOn
  refine ⟨|γ.γ t₀ (σ 2) - (c (σ 2) + u)|, hpos t₀, fun t => ?_⟩
  obtain ⟨y, hy, hyf⟩ := hper.exists_mem_Ioc hT t 0
  refine ⟨hmem t, ?_⟩
  have hyIcc : y ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨hy.1.le, by simpa using hy.2⟩
  have hle : |γ.γ t₀ (σ 2) - (c (σ 2) + u)| ≤ |γ.γ y (σ 2) - (c (σ 2) + u)| := hmin hyIcc
  show |γ.γ t₀ (σ 2) - (c (σ 2) + u)| ≤ |γ.γ t (σ 2) - (c (σ 2) + u)|
  rw [hyf]
  exact hle

/-- **The union of the two half-regions is the union of the positive cut-offs**: it carries an
essential loop exactly when one of the cut-offs does. -/
theorem containsEssentialLoop_union_iff_exists_cutOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} :
    P.ContainsEssentialLoop (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ↔
      ∃ ε : ℝ, 0 < ε ∧ P.ContainsEssentialLoop (cutOff P s c σ u ε) := by
  constructor
  · rintro ⟨γ, hess, hγ⟩
    obtain ⟨ε, hε, hcut⟩ := exists_cutOff_of_mem_union γ hγ
    exact ⟨ε, hε, ⟨γ, hess, hcut⟩⟩
  · rintro ⟨ε, hε, hcon⟩
    exact (Work.CoreTopology.ParamTorus.containsEssentialLoop_mono P (cutOff_subset_union hε)) hcon

/-! ## The uniform input, and its link with the dimension bound -/

/-- **The uniform endgame input**: the slice is inessential and the box region's span is contained
in the spans of the two halves together with that of the slice.  This is Pardon's endgame as a
configuration-uniform statement; by `bubbleHalf_of_span_le` it gives `SmoothHalfS`, and by
`pinchStepInput_of_spanPushOff` it implies the dimension bound of `PinchSweep.lean`. -/
def SpanPushOff : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) ≤
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u) ⊔
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u)

/-- **Pardon's Lemma 3 under both endpoint hypotheses, from the endgame input.** -/
theorem smoothHalfS_of_spanPushOff (h : SpanPushOff) : SmoothHalfS :=
  fun ψ s c σ u _hS hZ =>
    bubbleHalf_of_span_le ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr hZ)
      (h ψ s c σ u hZ)

/-- **The endgame input gives the dimension bound of the pinch.**  Both inequalities are immediate
from the span containment of `SpanPushOff` together with `hZ`: the two spans are *equal* under the
hypotheses. -/
theorem pinchStepInput_of_spanPushOff (h : SpanPushOff) : PinchStepInput :=
  fun ψ s c σ u hS hZ => by
    have hZ' : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) = ⊥ :=
      (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr hZ
    have hle := h ψ s c σ u hZ
    have hsplit := Work.SurgeryInvariance.Span.union_eq_sup (P := Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion _ s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion _ s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion _ s c σ u)
    have hbox : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
            Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) := by
      rw [hsplit]
      simpa only [hZ', sup_bot_eq] using hle
    have hsub : Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u ⊆
        Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ := by
      intro y hy
      rcases hy with h | h
      · exact ⟨(Work.BoxShrink.Core.mem_upperRegion.mp h).1,
          (Work.BoxShrink.Core.mem_upperRegion.mp h).2.1⟩
      · exact ⟨(Work.BoxShrink.Core.mem_lowerRegion.mp h).1,
          (Work.BoxShrink.Core.mem_lowerRegion.mp h).2.1⟩
    have hEq : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) =
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) :=
      le_antisymm (Work.SurgeryInvariance.WindingSpan_mono _ hsub) hbox
    refine ⟨le_trans (Submodule.finrank_mono hbox) (Nat.le_succ _), ?_⟩
    rw [hEq]
    exact Nat.le_succ _


/-- **Pardon's theorem from the endgame input.** -/
theorem pardon_torus_knot_distortion_of_spanPushOff (hspan : SpanPushOff)
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hdisc (smoothHalfS_of_spanPushOff hspan)
    hclean hae

end

end Work.BoxShrink.Pinch
