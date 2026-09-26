import Submission.Work.BoxShrink.Pinch.SliceSpanStep
import Submission.Work.BoxShrink.Pinch.PlaneFlowImpossible
import Submission.Work.BoxShrink.Pinch.Final

/-!
# The push-off from Pardon's two topological facts

This is the assembly of the area.  Pardon's Lemma 3 (`doublebubble2`) for the box/plane
configuration is the conjunction of two classical facts about compact surfaces:

* **the dichotomy** (his equation (1)): a sphere whose trace on the surface consists of inessential
  curves has a sublevel region whose invariant is either zero or the whole of `H₁`;
* **the dimension bound** of a single `2`-surgery (his Lemma 2.3): the invariant cannot jump from
  the whole of `H₁` to zero in one surgery.

The first is the surface-classification input which the chapter carries as
`Work.BoxShrink.Pinch.Equation1Input` and which, together with the general position of the
box-sphere trace (`Work.BoxShrink.Pinch.BoxSliceNice`), *discharges* the dichotomy at the box
sphere (`pardonDichotomy_boxRegion_of_equation1` below, re-proving here what the lost module
`Work.BoxShrink.Pinch.BoxDichotomy` had established).

The second is `Work.BoxShrink.Pinch.PinchNoJump`, in its one-sided form — whose reverse half is a
theorem of monotonicity (`Work.BoxShrink.Pinch.pinchStepInput_of_pinchNoJump`), and which is *not*
the conclusion: the dimension bound alone says nothing about the box region being full-rank.

The theorems below give Pardon's Lemma 3 (`BubbleHalf`), the residual field `PushOffHalf` — hence
`Work.BoxShrink.Bubble.BubbleInputHalf` — and the challenge itself, from those two facts; and, in
the all-parametrised-torus form, from their all-`P` versions `BoxDichotomyInput` and
`PinchNoJumpAll`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The dichotomy at the box sphere, from Pardon's equation (1) -/

/-- **The dichotomy at the box sphere, from Pardon's equation (1) and the general position of the
box-sphere trace.**  This is Pardon's equation (2.1) at the initial sphere of the pinch: the trace
`F ∩ ∂PBox` is a nice (compact, one-dimensional) level set carrying no essential loop, so its
sublevel region — the region inside the box — has invariant `⊥` or `⊤`.

(Reproves `Work.BoxShrink.Pinch.pardonDichotomy_boxRegion_of_niceLevel` of the lost
`Work.BoxShrink.Pinch.BoxDichotomy` inside this chapter.) -/
theorem pardonDichotomy_boxRegion_of_equation1 (h : Equation1Input) {ψ : Submission.Diffeo} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hnice : Work.Smooth.Morse.NiceLevel ψ (boxLevel s c σ) 0)
    (hS : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) := by
  have hcont : Continuous (boxLevel s c σ) := boxLevel_continuous s c σ
  have hregion : Work.Smooth.Morse.region ψ (boxLevel s c σ) 0 =
      Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ := by
    ext x
    simp only [Work.Smooth.Morse.region, Work.BoxShrink.Core.boxRegion, boxLevel,
      Set.mem_setOf_eq, Set.mem_inter_iff, sub_lt_zero, Submission.mem_PBox_iff]
  have htrace : Work.Smooth.Morse.levelSet ψ (boxLevel s c σ) 0 =
      (Work.Smooth.Morse.torus ψ).carrier ∩ Work.BoxShrink.Core.sphereSet c σ s := by
    ext x
    simp only [Work.Smooth.Morse.levelSet, Work.BoxShrink.Core.sphereSet, boxLevel,
      Set.mem_setOf_eq, Set.mem_inter_iff, sub_eq_zero]
  have hS' : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (boxLevel s c σ) 0) := fun hcon =>
    hS (Work.CoreTopology.ParamTorus.containsEssentialLoop_mono _
      (by rw [htrace]; exact Set.inter_subset_right) hcon)
  refine (h ψ (boxLevel s c σ) 0 hcont hnice hS').imp ?_ ?_ <;> intro hh <;> rwa [hregion] at hh

/-! ## The all-parametrised-torus forms of the two facts -/

/-- **Pardon's dichotomy at the box sphere, for every parametrised torus.**  The surface-theory
input of the pinch, in the form in which the caller's `BubbleInputHalf` needs it: the box region of
a configuration whose boundary sphere carries no essential loop has invariant `⊥` or `⊤`. -/
def BoxDichotomyInput : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ)

/-- **Pardon's dimension bound for the pinch, for every parametrised torus**, in the one-sided form
(see `Work.BoxShrink.Pinch.PinchNoJump` for the smooth-torus form and the discussion). -/
def PinchNoJumpAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.boxRegion P s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u)) + 1

/-! ## Pardon's Lemma 3 from the two facts -/

/-- **Pardon's Lemma 3 from the dichotomy and the dimension bound.**  If the invariant of the box
region is `⊥` or `⊤` and passing the pinch lowers its dimension by at most one, then an essential
loop of the box region survives to one of the two half-regions. -/
theorem bubbleHalf_of_dichotomy_noJump {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ))
    (hstep : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.boxRegion P s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u)) + 1) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have htop : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊤ :=
    hdich.resolve_left (fun hbot =>
      (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mp hbot hbox)
  have h2 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ)) = 2 := by
    rw [htop, finrank_top, Module.finrank_prod, Module.finrank_self]
  have h1 : 1 ≤ Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u)) := by
    have := hstep
    rw [h2] at this
    omega
  have hne : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.finrank_eq_zero.mpr rfl] at h1
    omega
  rw [Work.SurgeryInvariance.Span.union_eq_sup (P := P)
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)] at hne
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ =>
      hne (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

/-- **The residual field `PushOffHalf` of the challenge, from the two topological facts.** -/
theorem pushOffHalf_of_boxDichotomy_noJump (hdich : BoxDichotomyInput)
    (hstep : PinchNoJumpAll) : Work.BoxShrink.Bubble.PushOffHalf :=
  fun P s c σ u hS hZ => bubbleHalf_of_dichotomy_noJump (hdich P s c σ hS) (hstep P s c σ u hS hZ)

/-- **The caller's field `Work.BoxShrink.Bubble.BubbleInputHalf`, from the two topological
facts.** -/
theorem bubbleInputHalf_of_boxDichotomy_noJump
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (hstep : PinchNoJumpAll) :
    Work.BoxShrink.Bubble.BubbleInputHalf where
  cleansInDisc := hcleanD
  bubble := fun P s c σ u hS hZ => bubbleHalf_of_dichotomy_noJump (hdich P s c σ hS) (hstep P s c σ u hS hZ)

/-! ## The challenge -/

/-- **Pardon's theorem from the two topological facts** (all-parametrised-torus form). -/
theorem pardon_torus_knot_distortion_of_boxDichotomy_noJump
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (hstep : PinchNoJumpAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_pushOffHalf hcleanD
    (pushOffHalf_of_boxDichotomy_noJump hdich hstep) hclean hae

/-- **Pardon's theorem from Pardon's equation (1), the general position of the box-sphere trace and
the dimension bound** (the form in which the crux needs it: only the smooth tori of the
challenge, `Work.BoxShrink.Pinch.SmoothHalfS`). -/
theorem pardon_torus_knot_distortion_of_equation1_boxNice_noJump
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (hnice : BoxSliceNice) (hstep : PinchNoJump)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hcleanD
    (smoothHalfS_of_pinchNoJump h1 hnice hstep) hclean hae

/-- **The crux, from the two topological facts** (all-parametrised-torus form): Pardon's shrinking
step for all `p, q`. -/
theorem cruxStatement_of_boxDichotomy_noJump
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (hstep : PinchNoJumpAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  Work.BoxShrink.Bubble.crux_of_pushOffHalf hcleanD
    (pushOffHalf_of_boxDichotomy_noJump hdich hstep) hclean hae

end

end Work.BoxShrink.Pinch
