import Submission.Work.BoxShrink.Pinch.Invariant
import Submission.Work.BoxShrink.Pinch.Defs
import Submission.Work.SurgeryInvariance.SphereSweep
import Submission.Work.BoxShrink.Bubble.Reduce

/-!
# The pinch, in the invariant form: `PinchRegions`

Pardon's Lemma 3 (`doublebubble`) is proved by pushing the invariant

  `W t = im (H₁ (F ∩ int S_t ; ℚ) → H₁ (F ; ℚ))`

along a one-parameter family of spheres pinching the boundary `∂PBox s c σ` of the box along the
flat disc `cutDisc s c σ u`.  In the curve-level vocabulary of this development the invariant is
`Work.SurgeryInvariance.WindingSpan P (region t)`, and Pardon's argument is:

* **the dichotomy** (`Work.BoxShrink.Bubble.PardonDichotomy`): at every parameter at which the
  trace `S_t ∩ F` is a union of curves *inessential* in `F`, the invariant is `⊥` or `⊤` — this is
  Pardon's equation (1), and it is the isolated surface-theory input of the chapter
  (`Work.BoxShrink.Pinch.Equation1Input`, `Level.lean`);
* **the dimension bound**: a single surgery changes the invariant by at most one dimension
  (Pardon's Lemma 2.3: "doing any of the allowed surgeries can change this value by at most 1").

Given those two, the invariant is locally constant on `(-∞, 1)` and hence (a connected parameter
line) constant there; since `region 0 = boxRegion` carries an essential loop it is `⊤` at `0` and
therefore everywhere below `1`; and one more dimension bound at the pinching parameter `1` makes it
nonzero there.  The pinching parameter is the only place where Pardon's *perturbation* step
(`doublebubble2`) enters, and it is recorded as the field `pinch` — in the form of the covering
`Work.BoxShrink.Pinch.PinchFamily` (`Defs.lean`), i.e. as the endgame of the family.

This module contains the invariant form `PinchRegions` (no field of which carries a conclusion
about `upperRegion`/`lowerRegion`), the derivation of Pardon's Lemma 3 conclusion from it
(`bubbleHalf_of_pinchRegions`), the derivation of the `step` field from a spatial sweep
(`PinchRegions.ofSweep`), and the transport from `PinchRegions` to the chapter's interfaces.

The datum is *optimal*: `nonempty_pinchRegions_iff` shows that it is equivalent to
`PardonDichotomy P (boxRegion) ∧ BubbleHalf P s c σ u` — inhabiting it is proving the theorem
(§4bis of the chapter's `README.md`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The datum -/

/-- **Pardon's pinching family, in the invariant form.**

A one-parameter family `region : ℝ → Set R3` of regions of the surface with

* `region 0 = boxRegion` — the region inside the initial sphere `∂PBox s c σ`;
* `region 1 = upperRegion ∪ lowerRegion` — the region inside the double bubble at the end of the
  pinch, i.e. the two half-boxes;
* `dichotomy` — Pardon's equation (1) at every parameter *before* the pinch (the trace is a union of
  inessential curves there, so the invariant is `⊥` or `⊤`);
* `step` — the dimension bound: at every parameter, the dimensions of the invariants at nearby
  parameters differ by at most one (the local model of a single surgery of `S_t` or of `S_t ∩ F`).

**No field carries the conclusion.**  The whole content of the pinch is that *such a family exists*:
its existence is Pardon's Lemma `doublebubble` construction (`PinchInputAll`,
`PinchInputSmoothAll` in `Defs.lean` and `Main.lean`). -/
structure PinchRegions (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Type where
  /-- the region `F ∩ int (S_t)` -/
  region : ℝ → Set R3
  /-- at time `0` the region is the one inside the boundary sphere of the box -/
  zero : region 0 = Work.BoxShrink.Core.boxRegion P s c σ
  /-- at time `1` the region is the union of the two half-regions -/
  one : region 1 = Work.BoxShrink.Core.upperRegion P s c σ u ∪
    Work.BoxShrink.Core.lowerRegion P s c σ u
  /-- **Pardon's dichotomy** (equation (1)), at every parameter before the pinching parameter -/
  dichotomy : ∀ t < 1, Work.BoxShrink.Bubble.PardonDichotomy P (region t)
  /-- **the dimension bound**: a single surgery changes the invariant by at most one dimension -/
  step : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (region s)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (region t)) + 1 ∧
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (region t)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (region s)) + 1

/-- **The dimension bound and the dichotomy of a spatial sweep.**  A `Work.SurgeryInvariance.Sweep`
has both: its invariant is *constant* along the family (`Sweep.windingSpan_eq`), whence the
dimension bound, and the dichotomy at the initial region transfers to every earlier parameter. -/
def PinchRegions.ofSweep (S : Work.SurgeryInvariance.Sweep P) {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hzero : S.region 0 = Work.BoxShrink.Core.boxRegion P s c σ)
    (hone : S.region 1 = Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u)
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (S.region 0)) :
    PinchRegions P s c σ u where
  region := S.region
  zero := hzero
  one := hone
  dichotomy := fun t _ => by
    have h := S.windingSpan_eq t
    rcases hdich with hb | ht
    · left; rw [h, hb]
    · right; rw [h, ht]
  step := S.hstep

/-! ## The two-piece family of the pinch

`stepRegion A B` is the region `A` up to time `1` and `B` afterwards.  It is the family of the
*endgame* of the pinch: at `t = 1` the region jumps from `A = boxRegion` to `B = upper ∪ lower`.
The three lemmas below are all that is needed to control its dimension bound. -/

/-- **The two-piece family**: `A` below `1`, `B` from `1` on. -/
def stepRegion (A B : Set R3) (t : ℝ) : Set R3 := if t < 1 then A else B

theorem stepRegion_of_lt {A B : Set R3} {t : ℝ} (h : t < 1) : stepRegion A B t = A := if_pos h

theorem stepRegion_of_ge {A B : Set R3} {t : ℝ} (h : ¬ t < 1) : stepRegion A B t = B := if_neg h

/-- The two-piece family is locally constant away from `1`. -/
theorem stepRegion_eq_near {A B : Set R3} {t : ℝ} (ht : t ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε → stepRegion A B s = stepRegion A B t := by
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · refine ⟨(1 - t) / 2, by linarith, fun s hs => ?_⟩
    have hs' : s < 1 := by
      have := (abs_lt.mp hs).2
      linarith
    rw [stepRegion_of_lt hs', stepRegion_of_lt hlt]
  · refine ⟨(t - 1) / 2, by linarith, fun s hs => ?_⟩
    have hs' : ¬ s < 1 := by
      have := (abs_lt.mp hs).1
      linarith
    rw [stepRegion_of_ge hs', stepRegion_of_ge (by linarith)]

/-! ## Pardon's Lemma 3 from the pinch -/

/-- **Pardon's Lemma 3 (`doublebubble`) from the pinch.**  This is `spherefamily` followed by the
double-bubble decomposition.

* the invariant at `0` is `⊤`: the dichotomy at the initial sphere says it is `⊥` or `⊤`, and the
  hypothesis `hbox` rules out `⊥`;
* `submodule_ne_bot_of_lt_one` (Pardon's local-constancy argument, `Invariant.lean`) shows that
  the invariant of `region t` is `⊤` for every `t < 1` and nonzero at `1`;
* at `1` the region is the union of the two *disjoint open* half-regions, so its invariant is the
  supremum of theirs (`Span.union_eq_sup`), and a nonzero supremum has a nonzero member. -/
theorem bubbleHalf_of_pinchRegions {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : PinchRegions P s c σ u) : Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have h0 : Work.SurgeryInvariance.WindingSpan P (D.region 0) = ⊤ := by
    rcases D.dichotomy 0 (by norm_num) with h | h
    · rw [D.zero] at h
      exact absurd hbox ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mp h)
    · exact h
  have hne : Work.SurgeryInvariance.WindingSpan P (D.region 1) ≠ ⊥ :=
    submodule_ne_bot_of_lt_one (fun t => Work.SurgeryInvariance.WindingSpan P (D.region t))
      (by rw [Module.finrank_prod, Module.finrank_self]; norm_num)
      D.dichotomy D.step h0
  rw [D.one] at hne
  have hsplit := Work.SurgeryInvariance.Span.union_eq_sup (P := P)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)
  have hsup : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ := by
    rw [← hsplit]; exact hne
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ =>
      hsup (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

/-! ## The datum is optimal -/

/-- **`PinchRegions` is equivalent to `PardonDichotomy (boxRegion) ∧ BubbleHalf`.**  The forward
direction is `bubbleHalf_of_pinchRegions` plus the dichotomy at `0`; the backward direction uses the
two-piece family `stepRegion boxRegion (upperRegion ∪ lowerRegion)`, whose `step` field is the
dimension bound at the jump: if the invariant of the box region is `⊥` then both regions have
vanishing span, and if it is `⊤` then — by `BubbleHalf` — one half carries an essential loop, so the
invariant of `upper ∪ lower` is nonzero, and both dimensions lie in `{2} ∪ [1,2]`. -/
theorem nonempty_pinchRegions_iff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Nonempty (PinchRegions P s c σ u) ↔
      Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ) ∧
        Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  constructor
  · rintro ⟨D⟩
    refine ⟨?_, bubbleHalf_of_pinchRegions D⟩
    have h := D.dichotomy 0 (by norm_num)
    rwa [D.zero] at h
  · rintro ⟨hdich, hbubble⟩
    set A := Work.BoxShrink.Core.boxRegion P s c σ with hA
    set B := Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u with hB
    have hsub : B ⊆ A := Work.BoxShrink.Bubble.upper_union_lower_subset_boxRegion P s c σ u
    refine ⟨{ region := stepRegion A B
              zero := stepRegion_of_lt (by norm_num)
              one := stepRegion_of_ge (by norm_num)
              dichotomy := ?_
              step := ?_ }⟩
    · intro t ht
      rw [stepRegion_of_lt ht]
      exact hdich
    · intro t
      rcases eq_or_ne t 1 with rfl | ht
      · refine ⟨1, one_pos, fun r _ => ?_⟩
        have hle : Work.SurgeryInvariance.WindingSpan P B ≤
            Work.SurgeryInvariance.WindingSpan P A :=
          Work.SurgeryInvariance.WindingSpan_mono P hsub
        have key : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A) ≤
              Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P B) + 1 ∧
            Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P B) ≤
              Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A) + 1 := by
          rcases hdich with hbot | htop
          · have hB0 : Work.SurgeryInvariance.WindingSpan P B = ⊥ := by
              rw [hbot] at hle
              exact le_bot_iff.mp hle
            rw [hbot, hB0, Submodule.finrank_eq_zero.mpr rfl]
            exact ⟨Nat.le_succ 0, Nat.le_succ 0⟩
          · have hA2 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A) = 2 := by
              rw [htop, finrank_top, Module.finrank_prod, Module.finrank_self]
            have hbox : P.ContainsEssentialLoop A :=
              (Work.SurgeryInvariance.windingSpan_ne_bot_iff P A).mp
                (by rw [htop]; exact top_ne_bot)
            have hBne : Work.SurgeryInvariance.WindingSpan P B ≠ ⊥ := by
              intro hb
              have hu : Work.SurgeryInvariance.WindingSpan P
                  (Work.BoxShrink.Core.upperRegion P s c σ u) ≤
                  Work.SurgeryInvariance.WindingSpan P B :=
                Work.SurgeryInvariance.WindingSpan_mono P Set.subset_union_left
              have hl : Work.SurgeryInvariance.WindingSpan P
                  (Work.BoxShrink.Core.lowerRegion P s c σ u) ≤
                  Work.SurgeryInvariance.WindingSpan P B :=
                Work.SurgeryInvariance.WindingSpan_mono P Set.subset_union_right
              rcases hbubble hbox with h | h
              · exact ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff P
                    (Work.BoxShrink.Core.upperRegion P s c σ u)).mp
                  (le_bot_iff.mp (by rw [hb] at hu; exact hu))) h
              · exact ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff P
                    (Work.BoxShrink.Core.lowerRegion P s c σ u)).mp
                  (le_bot_iff.mp (by rw [hb] at hl; exact hl))) h
            have hB1 : 1 ≤ Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P B) :=
              Nat.one_le_iff_ne_zero.mpr (fun hn => hBne (Submodule.finrank_eq_zero.mp hn))
            have hB2 := Work.BoxShrink.Pinch.finrank_windingSpan_le_two P B
            rw [hA2]
            omega
        have h1 : stepRegion A B 1 = B := stepRegion_of_ge (by norm_num)
        rcases lt_or_ge r 1 with hr | hr
        · rw [stepRegion_of_lt hr, h1]
          exact key
        · rw [stepRegion_of_ge (not_lt.mpr hr), h1]
          exact ⟨Nat.le_succ _, Nat.le_succ _⟩
      · obtain ⟨ε, hε, hconst⟩ := stepRegion_eq_near (A := A) (B := B) ht
        refine ⟨ε, hε, fun r hr => ?_⟩
        rw [hconst r hr]
        exact ⟨Nat.le_succ _, Nat.le_succ _⟩

/-! ## The residual input of the chapter, in invariant form -/

/-- **The residual input, for all parametrised tori.** -/
def PinchRegionsAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    Nonempty (PinchRegions P s c σ u)

/-- **The residual input for the smooth tori of the challenge** (all the crux needs). -/
def PinchRegionsSmoothAll : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Nonempty (PinchRegions (Work.Smooth.Morse.torus ψ) s c σ u)

theorem pinchRegionsSmoothAll_of_pinchRegionsAll (h : PinchRegionsAll) :
    PinchRegionsSmoothAll :=
  fun ψ s c σ u hS hZ => h (Work.Smooth.Morse.torus ψ) s c σ u hS hZ

/-- **Pardon's Lemma 3 from the residual input, for all parametrised tori.** -/
theorem pushOffHalf_of_pinchRegionsAll (h : PinchRegionsAll) : Work.BoxShrink.Bubble.PushOffHalf :=
  fun P s c σ u hS hZ => bubbleHalf_of_pinchRegions (h P s c σ u hS hZ).some

/-! ## The transport to the chapter's interfaces -/

/-- **The corrected field, from the pinch.** -/
theorem bubbleInputHalf_of_pinchRegionsAll
    (hclean : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PinchRegionsAll) : Work.BoxShrink.Bubble.BubbleInputHalf where
  cleansInDisc := hclean
  bubble := pushOffHalf_of_pinchRegionsAll h

/-- **Pardon's Lemma 3 under both endpoint hypotheses, from the pinch** (the form the crux
consumes). -/
theorem smoothHalfS_of_pinchRegionsSmoothAll (h : PinchRegionsSmoothAll) :
    SmoothHalfS :=
  fun ψ s c σ u hS hZ => bubbleHalf_of_pinchRegions (h ψ s c σ u hS hZ).some

end

end Work.BoxShrink.Pinch
