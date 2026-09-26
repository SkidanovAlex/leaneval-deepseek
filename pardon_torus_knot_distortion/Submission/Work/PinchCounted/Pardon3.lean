import Submission.Work.PinchCounted.Local
import Submission.Work.CoreTopology.IntersectionNumberStandard

/-!
# Pardon's Lemma 3 in the paper's own form

This module records Pardon's Lemma 3 (`doublebubble`, Annals **174** (2011)) in the form in which
the paper states it for the box double bubble — the sphere `∂PBox s c σ` with the flat slicing disc
`cutDisc s c σ u` glued to it along its boundary circle — and proves that it implies
`Work.BoxShrink.Pinch.CountingHalf`:

```
Work.PinchCounted.PardonLemma3  ⟹  Work.BoxShrink.Pinch.CountingHalf
```

The hypothesis of `PardonLemma3` is Pardon's own inequality
`|S ∩ β| + 2 |D ∩ β| < I(F,β)` between the *point* counts of the knot with the two pieces of the
double bubble, and his conclusion — at the loop level, in the sharp form the workspace uses — is
`BubbleHalf`: if the region of the surface inside the box carries an essential loop, then one of the
two half-regions does.

The two counting lemmas proved here (`encard_inter_sphereSet_le_sphCount`,
`encard_inter_cutDisc_le_planeCount`) are the bridge between the crux's hypotheses — which count
*parameters* in the fundamental period — and Pardon's point counts: they are immediate from
`Work.BoxBubble.encard_range_inter_le_param`, and are useful independently of the residual.

`PardonLemma3` is *stronger* than the residual of `Local.lean` (`CountedPinch`), not weaker: it is
quantified over all configurations satisfying the double-bubble inequality, whereas `CountedPinch`
only asks for the pinching family at the configurations of the crux.  It is recorded because it is
the published theorem, so that a prover may aim at the literature.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The two counting lemmas -/

/-- The knot `K` of the crux, as a closed curve of the surface `torus ψ` of the challenge. -/
def knotCurve (ψ : Submission.Diffeo) (p q : ℕ) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ) :
    Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ) where
  γ := K.curve
  cont := K.smooth.continuous
  periodic := K.periodic
  mem := fun t => by
    have ht : K.curve t ∈ Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph
        ψ.toHomeomorph (Work.CoreTopology.standardCurve p q)).γ := by
      rw [← himg]; exact Set.mem_range_self t
    obtain ⟨u, hu⟩ := ht
    rw [← hu]
    exact (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
      (Work.CoreTopology.standardCurve p q)).mem u

@[simp] theorem knotCurve_apply (ψ : Submission.Diffeo) (p q : ℕ) (K : Knot) (himg) (t : ℝ) :
    knotCurve ψ p q K himg t = K.curve t := rfl

/-- The knot curve of the crux has the same range as the image of the standard curve. -/
theorem range_knotCurve (ψ : Submission.Diffeo) (p q : ℕ) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ) :
    Set.range (knotCurve ψ p q K himg).γ = Set.range K.curve := by
  ext x
  constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, ht⟩

/-- **The point count of the box sphere is at most the parameter count of the crux.**  The knot has
at most as many intersection *points* with the box sphere as it has intersection *parameters* in
the fundamental period. -/
theorem encard_inter_sphereSet_le_sphCount {p q : ℕ} (ψ : Submission.Diffeo) (K : Knot)
    {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ}
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ) :
    Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩ Work.BoxShrink.Core.sphereSet c σ s)
      ≤ Work.BoxShrink.sphCount K c σ s := by
  have h := Work.BoxBubble.encard_range_inter_le_param (knotCurve ψ p q K himg)
    (Work.BoxShrink.Core.sphereSet c σ s)
  rw [range_knotCurve] at h
  rw [← himg]
  simpa only [knotCurve_apply, Work.BoxShrink.Core.mem_sphereSet, Work.BoxShrink.sphCount] using h

/-- **The point count of the slicing disc is at most the parameter count of the crux.** -/
theorem encard_inter_cutDisc_le_planeCount {p q : ℕ} (ψ : Submission.Diffeo) (K : Knot)
    {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ) :
    Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩ Work.BoxShrink.Core.cutDisc s c σ u)
      ≤ Work.BoxShrink.planeCount K c σ s u := by
  have h := Work.BoxBubble.encard_range_inter_le_param (knotCurve ψ p q K himg)
    (Work.BoxShrink.Core.cutDisc s c σ u)
  rw [range_knotCurve] at h
  rw [← himg]
  simpa only [knotCurve_apply, Work.BoxShrink.Core.mem_cutDisc, Work.BoxShrink.planeCount] using h

/-- **The double-bubble inequality of Pardon's Lemma 3**, from the two counts of the crux. -/
theorem doubleBubbleInequality {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo)
    (K : Knot) {d : ℝ} (hd : 0 ≤ d) (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩ Work.BoxShrink.Core.sphereSet c σ s)
      + 2 * Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩ Work.BoxShrink.Core.cutDisc s c σ u)
      < Work.CoreTopology.pardonsI (Work.Smooth.Morse.torus ψ)
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)) := by
  have h1 := encard_inter_sphereSet_le_sphCount (p := p) (q := q) ψ K (c := c) (σ := σ)
    (s := s) himg
  have h2 := encard_inter_cutDisc_le_planeCount (p := p) (q := q) ψ K (c := c) (σ := σ)
    (s := s) (u := u) himg
  have hsum : Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩ Work.BoxShrink.Core.sphereSet c σ s)
      + 2 * Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩ Work.BoxShrink.Core.cutDisc s c σ u)
      ≤ Work.BoxShrink.sphCount K c σ s + 2 * Work.BoxShrink.planeCount K c σ s u :=
    add_le_add h1 (mul_le_mul_right h2 2)
  have hlt : Work.BoxShrink.sphCount K c σ s + 2 * Work.BoxShrink.planeCount K c σ s u
      < (Nat.min p q : ℕ∞) := by
    have hE := Work.BoxShrink.count_add_two_mul_lt (lt_min hp hq) hd hsmall hS hU
    rw [← ENat.toENNReal_lt]
    rw [ENat.toENNReal_add, ENat.toENNReal_mul]
    norm_num
    exact hE
  have hpid : Work.CoreTopology.pardonsI (Work.Smooth.Morse.torus ψ)
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)) = (Nat.min p q : ℕ∞) :=
    Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ.toHomeomorph
  rw [hpid]
  exact lt_of_le_of_lt hsum hlt


/-! ## The residual: Pardon's Lemma 3 in the paper's own form -/

/-- **Pardon's Lemma 3 (`doublebubble`, Annals 174 (2011)), for the box double bubble.**

The double bubble is the sphere `∂PBox s c σ = sphereSet c σ s` together with the flat disc
`cutDisc s c σ u = PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}` glued to it along its boundary; its two
halves are the two half-boxes, so Pardon's conclusion `F ∩ int(H_i)` having a component of genus `g`
becomes, in the winding-span vocabulary of this chapter, `Work.BoxShrink.Bubble.BubbleHalf`.

The hypothesis is Pardon's own inequality `|S ∩ β| + 2 |D ∩ β| < I(F,β)` between the *point* counts
of the knot with the two pieces of the double bubble; the sphere is required to be in general
position with respect to the surface (`Work.BoxShrink.SlicedSphere`), and the classical
cut-and-paste step (`Work.InnermostDisk.CleansDiscs`, the input which the ledger also carries
separately) is made explicit, since the innermost-disc argument at the intermediate spheres of the
pinch is what turns the counting into inessentiality (Pardon's Lemma 2).  The planar innermost
input at the slicing *disc* is **not** required: Pardon's proof applies Lemma 2 to spheres only.

This is a *stronger* statement than `Work.PinchCounted.CountedPinch` (it is quantified over all such
double bubbles, not only over the configurations of the crux); it is recorded because it is the
published theorem, so that a prover may aim at the literature. -/
def PardonLemma3 : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    0 < s →
    Work.BoxShrink.SlicedSphere P (Work.BoxShrink.Core.sphereSet c σ s) →
    Work.InnermostDisk.CleansDiscs P →
    (Set.encard (Set.range β.γ ∩ Work.BoxShrink.Core.sphereSet c σ s)
        + 2 * Set.encard (Set.range β.γ ∩ Work.BoxShrink.Core.cutDisc s c σ u)
        < Work.CoreTopology.pardonsI P β) →
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u

/-- **Pardon's Lemma 3 gives the counted form of the chapter.**  The counting hypotheses of the crux
give Pardon's double-bubble inequality (`doubleBubbleInequality`), and `I(F,β) = min p q` at the
knots of the challenge (`Work.CoreTopology.pardonsI_standard_mapHomeomorph`). -/
theorem countingHalf_of_pardonLemma3 (h : PardonLemma3) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    h (Work.Smooth.Morse.torus ψ)
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)) s c σ u (lt_trans hr hrs)
      hslice hcl
      (doubleBubbleInequality hp hq hc ψ K hd hsmall himg hS hU)

/-- **Pardon's shrinking step from Pardon's Lemma 3.** -/
theorem cruxCore_of_pardonLemma3 (h : PardonLemma3) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_pardonLemma3 h)

/-- **`Submission.BoxShrinkStatement` from Pardon's Lemma 3** (with Pardon's cut-and-paste and the
almost-everywhere general position). -/
theorem boxShrink_of_pardonLemma3 (h : PardonLemma3)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux fun p q =>
    ⟨Work.BoxShrink.cleansDiscsAll_of_pushThrough hpush,
      cruxCore_of_pardonLemma3 h p q,
      Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis⟩

/-- **Pardon's theorem from Pardon's Lemma 3 and Pardon's cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_pardonLemma3 (h : PardonLemma3)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_pardonLemma3 h)⟩

/-! ## Non-vacuity of the double-bubble inequality -/

/-- **A sufficient condition for Pardon's double-bubble inequality**: if the knot misses both pieces
of the double bubble and `I(F,β)` is positive, then the inequality of `PardonLemma3` holds.

This is the elementary form of the hypothesis; it is what a configuration with a small knot (or a
box far from the knot) realises, and it shows that the hypothesis of `PardonLemma3` is not vacuous. -/
theorem doubleBubbleInequality_of_disjoint {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hS : Set.range β.γ ∩ Work.BoxShrink.Core.sphereSet c σ s = ∅)
    (hD : Set.range β.γ ∩ Work.BoxShrink.Core.cutDisc s c σ u = ∅)
    (hI : (0 : ℕ∞) < Work.CoreTopology.pardonsI P β) :
    Set.encard (Set.range β.γ ∩ Work.BoxShrink.Core.sphereSet c σ s)
        + 2 * Set.encard (Set.range β.γ ∩ Work.BoxShrink.Core.cutDisc s c σ u)
        < Work.CoreTopology.pardonsI P β := by
  rw [hS, hD, Set.encard_empty]
  simpa using hI

/-! ## Non-vacuity of the conclusion -/

/-- **The conclusion of `PardonLemma3` holds at the standard `5/2` configuration** (the configuration
at which the *span* form fails, `Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`): so the residual's
conclusion is not vacuous, and the failure of the span form is not a failure of the conclusion. -/
theorem pardonLemma3_conclusion_fiveHalves :
    Work.BoxShrink.Bubble.BubbleHalf Work.CoreTopology.standard (5 / 2) 0
      (Equiv.swap (1 : Fin 3) 2) 0 :=
  Work.BoxShrink.Bubble.bubbleHalf_cex

/-- **The conclusion of `PardonLemma3` fails at the standard `3/2` configuration**
(`Work.BoxShrink.Pinch.BubbleHalfRefuted`): so no residual of this chapter is provable from `True`,
and the counting hypothesis is what excludes that configuration
(`Work.PinchCounted.no_counted_of_sphereTrace_essential`). -/
theorem pardonLemma3_conclusion_false_threeHalves :
    ¬ Work.BoxShrink.Bubble.BubbleHalf Work.CoreTopology.standard (3 / 2) 0
      (Equiv.swap (1 : Fin 3) 2) 0 :=
  Work.BoxShrink.Pinch.BubbleHalfRefuted

end

end Work.PinchCounted
