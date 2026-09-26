import Submission.Work.BoxShrink.Pinch.Defs
import Submission.Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty
import Submission.Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top
import Submission.Work.BoxShrink.Bubble.cex_not_slicePushOffSpan

/-!
# The pinch: which local models are admissible, and which are not

The pinch of `Work.BoxShrink.Pinch.PinchFamily` is Pardon's one-parameter family of spheres, and
its local models are Pardon's (`Work.BoxShrink.Bubble.SurgeryStepSmall` + his dichotomy + the
endgame).  It is worth recording, with proofs, *why* stronger-looking local models cannot be used —
they are the natural first guess, and they are what an earlier version of this chapter (and the
spatial vocabulary `Work.SurgeryInvariance.Sweep` / `SphereSweep`, cf. the `PLAN.md` of
`Submission/Work/BoxShrink/Bubble`) proposed.  There are two distinct obstructions, both proved
here:

1. **The local models of `Work.SurgeryInvariance.SweepLoops` / `Work.SurgeryInvariance.Sweep` /
   `Work.Smooth.Morse.LevelFamily` preserve the winding span exactly** (`SweepLoops.windingSpan_eq`,
   `Sweep.windingSpan_eq`, `LevelFamily.windingSpan_eq`).  But at the counterexample configuration of
   the sibling chapter the region inside the box has span `⊤` while the union of the two halves has
   span `ℚ·(0,1) ⊊ ⊤`: the pinch *must* change the span, so **no** family with those local models
   can reach the two halves from the box region.  See `pinchFamilyConstSpan_span_eq`,
   `not_nonempty_pinchFamilyConstSpan_cex` and `not_exists_sweep_cex` — the last one refutes the
   `Sweep`/`SphereSweep` route (the added zero-span disc of Pardon's `doublebubble2` does *not*
   repair it, because a zero-span piece adds nothing to the span).
2. **A single `2`-surgery cannot shrink a preconnected region**: if `SurgeryStepSmall P A A'` and
   `A` is preconnected (as the regions `F ∩ int(S_t)` of a family of spheres are), then `A'` is
   `A`, or `∅`, or `A` with an open piece *added*.  Hence the pinch itself (which shrinks the region
   from `boxRegion` to the two halves) cannot be a local move and must be the separate endgame field
   — as in Pardon's proof, where it is the inclusion argument "the property of having a connected
   component of genus `g` is preserved under small perturbations".

Together these two facts say: the local models of `PinchFamily` are the strongest admissible ones,
and the family must consist of genuine pinches, not of transports.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## 1. A `2`-surgery cannot shrink a preconnected region -/

/-- **Pardon's local move cannot shrink a preconnected region.**  If `A` is preconnected and open
in the surface and `SurgeryStepSmall P A A'`, then the region can only be left unchanged, emptied,
or *grown*: `A' = A ∪ Z` for an open piece `Z` disjoint from `A`.

(The proof is the argument of `Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty`,
which does not use the vanishing of the span: two disjoint open pieces cutting out `A` force `A` to
be disconnected.) -/
theorem surgeryStepSmall_grow_or_empty {A A' : Set R3}
    (h : Work.BoxShrink.Bubble.SurgeryStepSmall P A A') (hAc : A ⊆ P.carrier)
    (hpre : IsPreconnected A) :
    A' = A ∨ A' = ∅ ∨ ∃ Z : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
      Disjoint A Z ∧ A' = A ∪ Z := by
  obtain ⟨Z, _hZtop, _hAo, hA'o, hZo, hcase⟩ := h
  rcases hcase with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · rcases Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty hAc hA'o hZo hc hd
      hpre with hA' | hA'
    · exact Or.inl hA'
    · exact Or.inr (Or.inl hA')
  · exact Or.inr (Or.inr ⟨Z, hZo, hd, hc⟩)

/-! ## 1bis. The span is everything along a Pardon family before the pinch -/

/-- **The winding span of the region is everything all the way up to the pinch.**  If the span of
the initial region of a `SweepLoopsSmall` family is `⊤`, then so is the span of every region with
`t < 1`:  the vanishing of the span is constant on `[0,1)`
(`Work.BoxShrink.Bubble.SweepLoopsSmall.bot_iff`) and Pardon's dichotomy leaves only the two values
`⊥` and `⊤`. -/
theorem sweepLoopsSmall_windingSpan_eq_top_of_lt_one {S : Work.BoxShrink.Bubble.SweepLoopsSmall P}
    (h0 : Work.SurgeryInvariance.WindingSpan P (S.region 0) = ⊤) {t : ℝ} (ht : t < 1) :
    Work.SurgeryInvariance.WindingSpan P (S.region t) = ⊤ := by
  have hne : Work.SurgeryInvariance.WindingSpan P (S.region t) ≠ ⊥ := by
    intro h
    exact absurd ((S.bot_iff ht).mp h) (by rw [h0]; exact top_ne_bot)
  rcases S.dichotomy t ht with h | h
  · exact absurd h hne
  · exact h

/-- **What the last step of a Pardon family must do.**  Suppose the region inside the box spans
everything, while the union of the two half-regions with the zero-span piece `Z` does not (as at the
counterexample configuration of the sibling chapter, where the span of the region inside the box is
`⊤` and the span of the two halves is `≤ ℚ·(0,1)`).  Then:

* the span is `⊤` at every parameter before the pinch
  (`sweepLoopsSmall_windingSpan_eq_top_of_lt_one`), so the pinching parameter `1` is exceptional: the
  family cannot *transport* the region to the final one, since a transport
  (`Work.SurgeryInvariance.RegionEquivalent`) preserves the winding span;
* at the pinching parameter the family must therefore **grow** the region: for every parameter `t`
  just below `1` the region is the final region together with an open piece `Z'` which is disjoint
  from the final region (hence lies off the two halves, i.e. in the trace of the cutting plane or
  outside the box), has winding span different from `⊤`, and together with the final region spans
  everything.

This is the precise shape a construction of the pinch has to produce; in particular the pinch is
*not* a transport of the loops of the region, and the piece `Z'` has to carry the homology direction
which the two half-regions are missing. -/
theorem pinch_lastStep_grows {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (S : Work.BoxShrink.Bubble.SweepLoopsSmall P)
    (h0 : S.region 0 = Work.BoxShrink.Core.boxRegion P s c σ)
    (hspan : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊤)
    {Z : Set R3} (hZopen : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hZdisj : Disjoint (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) Z)
    (hZspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (h1 : S.region 1 = (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ Z)
    (hne : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊤) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε < t → t < 1 →
      ∃ Z' : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P Z' ∧
        Disjoint (S.region 1) Z' ∧ S.region t = S.region 1 ∪ Z' ∧
        Work.SurgeryInvariance.WindingSpan P Z' ≠ ⊤ ∧
        Work.SurgeryInvariance.WindingSpan P (S.region 1) ⊔
          Work.SurgeryInvariance.WindingSpan P Z' = ⊤ := by
  classical
  have hspan0 : Work.SurgeryInvariance.WindingSpan P (S.region 0) = ⊤ := by rw [h0, hspan]
  have hlt : ∀ t : ℝ, t < 1 → Work.SurgeryInvariance.WindingSpan P (S.region t) = ⊤ :=
    fun t ht => sweepLoopsSmall_windingSpan_eq_top_of_lt_one hspan0 ht
  have hspan1 : Work.SurgeryInvariance.WindingSpan P (S.region 1) =
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) := by
    rw [h1, Work.SurgeryInvariance.Span.union_eq_sup
      (Work.SurgeryInvariance.isOpenInCarrier_union P
        (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
        (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u))
      hZopen hZdisj, hZspan, sup_bot_eq]
  have hspan1ne : Work.SurgeryInvariance.WindingSpan P (S.region 1) ≠ ⊤ := by
    rw [hspan1]; exact hne
  -- `1` is an exceptional parameter
  have hexc : (1 : ℝ) ∈ S.exc := by
    by_contra hnot
    obtain ⟨ε, hε, -, heq⟩ := S.regular 1 hnot
    have hmem : |(1 - ε / 2) - 1| < ε := by
      rw [abs_lt]; constructor <;> linarith
    have hsp := Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq (heq (1 - ε / 2) hmem)
    rw [hsp] at hspan1ne
    exact hspan1ne (hlt (1 - ε / 2) (by linarith))
  obtain ⟨ε, hε, hsurg⟩ := S.surgery 1 hexc
  refine ⟨min ε 1, lt_min hε one_pos, fun t hlt1 ht1 => ?_⟩
  have hmem : |t - 1| < ε := by
    have h1' : 1 - t < min ε 1 := by linarith
    have h2' : 1 - t < ε := lt_of_lt_of_le h1' (min_le_left ε 1)
    rw [abs_of_neg (by linarith : t - 1 < 0)]
    linarith
  have htop : Work.SurgeryInvariance.WindingSpan P (S.region t) = ⊤ := hlt t ht1
  rcases hsurg t hmem with hsmall | hequiv
  · -- the region grows: the shrinking case would bound its span by the final one
    obtain ⟨Z', hZ'top, hA, -, hZ'o, hcase⟩ := hsmall
    rcases hcase with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · exfalso
      have hmono := Work.SurgeryInvariance.WindingSpan_mono P
        (show S.region t ⊆ S.region 1 from by rw [hc]; exact Set.subset_union_left)
      rw [htop, hspan1] at hmono
      exact hne (top_le_iff.mp hmono)
    · refine ⟨Z', hZ'o, hd, hc, hZ'top, ?_⟩
      rw [← Work.SurgeryInvariance.Span.union_eq_sup hA hZ'o hd, ← hc]
      exact htop
  · exfalso
    exact hspan1ne
      (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq hequiv |>.trans htop)

/-! ## 2. The constant-span local models cannot reach the two halves -/

/-- The pinch recorded with the *constant-span* local models
(`Work.SurgeryInvariance.SweepLoops`): this is the natural first guess, recorded here only in order
to prove that it is unusable (`not_nonempty_pinchFamilyConstSpan_cex`).  It is **not** the interface
of the chapter: `PinchFamily` uses Pardon's local models instead. -/
structure PinchFamilyConstSpan (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) where
  /-- the family of regions -/
  sweep : Work.SurgeryInvariance.SweepLoops P
  /-- at time `0` the family is the region inside the box -/
  zero : sweep.region 0 = Work.BoxShrink.Core.boxRegion P s c σ
  /-- the piece through which the pinch passes -/
  Z : Set R3
  /-- it is open in the surface -/
  Z_open : Work.SurgeryInvariance.IsOpenInCarrier P Z
  /-- it contributes nothing to the winding span -/
  Z_span : Work.SurgeryInvariance.WindingSpan P Z = ⊥
  /-- it is disjoint from the two half-regions -/
  Z_disj : Disjoint (Work.BoxShrink.Core.upperRegion P s c σ u ∪
    Work.BoxShrink.Core.lowerRegion P s c σ u) Z
  /-- at time `1` the family is the two half-regions together with that piece -/
  one : sweep.region 1 =
    (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ Z

/-- **A constant-span pinch forces the spans of its endpoints to agree.**  (The span of the union of
the two half-regions with the zero-span piece `Z` is the span of the two half-regions, by
`Span.union_eq_sup`.) -/
theorem pinchFamilyConstSpan_span_eq {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : PinchFamilyConstSpan P s c σ u) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) =
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  have h1 : Work.SurgeryInvariance.WindingSpan P (D.sweep.region 1) =
      Work.SurgeryInvariance.WindingSpan P (D.sweep.region 0) := D.sweep.windingSpan_eq 1
  rw [D.one, D.zero] at h1
  have h2 : Work.SurgeryInvariance.WindingSpan P
      ((Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ D.Z) =
      Work.SurgeryInvariance.WindingSpan P
        ((Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u)) := by
    rw [Work.SurgeryInvariance.Span.union_eq_sup
      (Work.SurgeryInvariance.isOpenInCarrier_union P
        (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
        (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u))
      D.Z_open D.Z_disj, D.Z_span, sup_bot_eq]
  exact h1.symm.trans h2

/-- **The counterexample configuration, with the span of the two half-regions.** -/
theorem cex_windingSpan_union_ne_top :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) ≠ ⊤ := by
  intro h
  refine Work.BoxShrink.Bubble.cex_not_slicePushOffSpan ?_
  show Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2)) ≤
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0)
  rw [Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top, h]

/-- **The constant-span pinch does not exist at the counterexample configuration.**  The region
inside the box has winding span `⊤` (`Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top`) while
the union of the two halves has span `≠ ⊤`
(`Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`); a family with the local models of
`Work.SurgeryInvariance.SweepLoops` would force the two to be equal.

This is the machine-checked reason why the chapter's `PinchFamily` uses Pardon's local models
`Work.BoxShrink.Bubble.SurgeryStepSmall` (which allow the span to change) together with the separate
endgame, rather than `Work.SurgeryInvariance.SweepLoops`. -/
theorem not_nonempty_pinchFamilyConstSpan_cex :
    ¬ Nonempty (PinchFamilyConstSpan Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2) 0) := by
  rintro ⟨D⟩
  have h := pinchFamilyConstSpan_span_eq D
  rw [Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top] at h
  exact cex_windingSpan_union_ne_top h.symm

/-- **The same obstruction for the spatial vocabulary.**  There is no
`Work.SurgeryInvariance.Sweep` of the surface from the region inside the box to the two
half-regions together with a zero-span open piece `Z` at the counterexample configuration: the
`surgery`/`regular` local models of `Sweep` preserve the winding span exactly
(`Sweep.windingSpan_eq`), while the pinch must change it.

So the route through `Work.SurgeryInvariance.SphereSweep` / `Sweep` (the "spatial vocabulary" of
`Submission/Work/BoxShrink/Bubble/PLAN.md`) is closed, and the added zero-span disc of Pardon's
`doublebubble2` does not repair it: a zero-span piece contributes nothing to the span. -/
theorem not_exists_sweep_cex :
    ¬ ∃ S : Work.SurgeryInvariance.Sweep Work.CoreTopology.standard,
        S.region 0 = Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) ∧
        ∃ Z : Set R3, Work.SurgeryInvariance.IsOpenInCarrier Work.CoreTopology.standard Z ∧
          Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard Z = ⊥ ∧
          Disjoint (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
              (Equiv.swap (1 : Fin 3) 2) 0 ∪
            Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
              (Equiv.swap (1 : Fin 3) 2) 0) Z ∧
          S.region 1 = (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
              (Equiv.swap (1 : Fin 3) 2) 0 ∪
            Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
              (Equiv.swap (1 : Fin 3) 2) 0) ∪ Z := by
  rintro ⟨S, h0, Z, hZo, hZs, hZd, h1⟩
  have h := S.windingSpan_eq 1
  rw [h1, h0] at h
  have h2 : Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      ((Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) ∪ Z) =
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
            (Equiv.swap (1 : Fin 3) 2) 0 ∪
          Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
            (Equiv.swap (1 : Fin 3) 2) 0) := by
    rw [Work.SurgeryInvariance.Span.union_eq_sup
      (Work.SurgeryInvariance.isOpenInCarrier_union Work.CoreTopology.standard
        (Work.BoxShrink.Core.isOpenInCarrier_upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0)
        (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0))
      hZo hZd, hZs, sup_bot_eq]
  rw [h, Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top] at h2
  exact cex_windingSpan_union_ne_top h2.symm

end

end Work.BoxShrink.Pinch
