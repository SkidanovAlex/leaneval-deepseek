import Submission.Work.BoxShrink.Pinch.PushOffNoJump
import Submission.Work.BoxShrink.Pinch.SliceSpanStep
import Submission.Work.BoxShrink.Pinch.Final
import Submission.Work.BoxShrink.Pinch.Migrated

/-!
# The pinch, from Pardon's per-step assertion along a sweep

This module isolates the *local* content of Pardon's Lemma 2.3 ("the double bubble") in the form
in which he states it, and shows that it suffices.

Pardon's assertion (Annals 174 (2011), proof of Lemma 2.2 `spherefamily`) is, verbatim:

> *"Doing any of the allowed surgeries can change this value by at most 1, so since it always
> equals either `2g` or `0`, we conclude that it must be constant."*

where "this value" is `dim_ℚ im (H₁ (F ∩ int S_t) ; ℚ) → H₁ (F ; ℚ)`, i.e. the dimension of
`Work.SurgeryInvariance.WindingSpan` of the region of the surface inside the current sphere of the
sweep, and the "allowed surgeries" are the members of the one-parameter family of spheres that
Performs the `2`-surgery along the cutting disc.  Two facts make this sufficient:

* every member of the family meets the surface in curves inessential in `F`, so the value is `0` or
  `2` (Pardon's equation (1), the dichotomy `Work.BoxShrink.Bubble.PardonDichotomy`, which is
  *derived* here from the classification of compact surfaces `Work.BoxShrink.Pinch.Equation1Input`
  for regions of the form `F ∩ int S`);
* consecutive members differ by a single surgery, so the value drops by at most `1`.

Hence the value is *constant*, and in particular the value at the last member — the union of the
two half-regions — is the value at the first — the region inside the box.  So the drop is not just
`≤ 1`, it is `0`:  `Work.BoxShrink.Pinch.PinchNoJump` and `Work.BoxShrink.Bubble.BubbleHalf`
follow, and with them the crux and Pardon's Theorem 1.1.

## What is carried, and why it is not the conclusion

The single carried statement below is `Work.BoxShrink.Pinch.SweepChain`, whose content is the
*existence of the sweep* together with the two facts above; its per-step half is
`Work.BoxShrink.Pinch.SpanStep`, the faithful rendering of Pardon's sentence.  Note what it is
*not*: it does not mention the two ends of the pinch only — it is a statement about a whole
one-parameter family of intermediate regions, each of which must carry the dichotomy and each
consecutive pair of which must be a single surgery.  In particular it is a *strengthening* of
`PinchNoJump` (which is about the box region and the two half-regions alone, and which
`Work.BoxShrink.Pinch.pinchNoJump_iff_keyCase` shows is *equivalent* to the conclusion of the
pinch), so this module is not a restatement of the goal: it says precisely which geometric object
has to be produced (Pardon's sphere family) and proves that producing it suffices.

The other ingredient is the *sufficient condition* `Work.BoxShrink.Pinch.spanStep_of_le_sup`: a
step is a single surgery whenever the invariant of the smaller region is the invariant of the
larger one modulo the span of one additional loop — the surgery shape.  Every step of Pardon's
family is of that shape, and the two degenerate instances (`spanStep_of_subset`, the isotopy steps,
and `spanStep_of_span_le`, the steps of a region inside the slice's span) are *proved* here, so the
carried condition is not vacuous.

## Main results

* `Work.BoxShrink.Pinch.SpanStep` — a single surgery changes the dimension by at most one;
* `Work.BoxShrink.Pinch.SpanStep.of_le_sup`, `…_of_subset` — proved instances;
* `Work.BoxShrink.Pinch.finrank_eq_zero_or_two_of_pardonDichotomy` — the dichotomy pins the value;
* `Work.BoxShrink.Pinch.chain_value_eq` — hence the value is constant along a chain;
* `Work.BoxShrink.Pinch.SweepChain`, `Work.BoxShrink.Pinch.SweepChainAll` — the carried input;
* `Work.BoxShrink.Pinch.pinchNoJumpAll_of_sweepChainAll`,
  `Work.BoxShrink.Pinch.pinchNoJump_of_sweepChainAll` — the residual from the sweep;
* `Work.BoxShrink.Pinch.smoothHalfS_of_sweepChainAll` — Pardon's Lemma 3 for the smooth tori;
* `Work.BoxShrink.Pinch.pushOffHalf_of_boxDichotomy_sweepChain`,
  `Work.BoxShrink.Pinch.bubbleInputHalf_of_boxDichotomy_sweepChain`,
  `Work.BoxShrink.Pinch.cruxStatement_of_boxDichotomy_sweepChain`,
  `Work.BoxShrink.Pinch.boxShrink_of_sweepChain`,
  `Work.BoxShrink.Pinch.pardon_torus_knot_distortion_of_sweepChain` — the challenge.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## A single surgery changes the value by at most one -/

/-- **Pardon's per-step assertion.**  Passing through a single allowed surgery of the sweep lowers
the dimension of the invariant by at most one:

  `dim (W S) ≤ dim (W S') + 1`.

This is "doing any of the allowed surgeries can change this value by at most `1`" of the proof of
Pardon's `spherefamily`, restricted to the direction needed for a sweep that *loses* dimensions.
The reverse inequality is not needed: for a chain of dichotomy regions it is the *drop* that has to
be controlled. -/
def SpanStep (P : Work.CoreTopology.ParamTorus) (A A' : Set R3) : Prop :=
  Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A) ≤
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A') + 1

/-- **The surgery shape.**  If the invariant of `A` is contained in the invariant of `A'` together
with a space of dimension at most one, then passing from `A` to `A'` lowers the dimension by at
most one.  This is the shape in which a single surgery presents itself: the surgery adds or removes
one loop's worth of homology (`Span.union_eq_sup` and its relatives). -/
theorem spanStep_of_le_sup {A A' : Set R3} {L : Submodule ℚ (ℚ × ℚ)}
    (hL : Module.finrank ℚ ↥L ≤ 1)
    (h : Work.SurgeryInvariance.WindingSpan P A ≤ Work.SurgeryInvariance.WindingSpan P A' ⊔ L) :
    SpanStep P A A' := by
  have h1 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A' ⊔ L) :=
    Submodule.finrank_mono h
  have h2 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A' ⊔ L) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A') + Module.finrank ℚ ↥L := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq
      (Work.SurgeryInvariance.WindingSpan P A') L]
    exact Nat.le_add_right _ _
  exact le_trans h1 (le_trans h2 (Nat.add_le_add_left hL
    (Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A'))))

/-- **Isotopy steps are steps of the sweep.**  A step in which the region only grows or only
shrinks (an isotopy of the family of spheres, away from its critical times) satisfies Pardon's
bound, by monotonicity of the winding span. -/
theorem spanStep_of_subset {A A' : Set R3} (h : A ⊆ A') : SpanStep P A A' :=
  Nat.le_add_right_of_le
    (Submodule.finrank_mono (Work.SurgeryInvariance.WindingSpan_mono P h))

/-- **Steps dominated by the slice.**  If the step's dimension is already bounded by the slice's,
the bound holds trivially — this is the shape of the degenerate configurations
(`pinchNoJump_of_sliceRegion_empty`). -/
theorem spanStep_of_span_le {A A' : Set R3} (h : Work.SurgeryInvariance.WindingSpan P A ≤
    Work.SurgeryInvariance.WindingSpan P A') : SpanStep P A A' :=
  Nat.le_add_right_of_le (Submodule.finrank_mono h)

/-- **The loop-splitting instance of a single surgery.**  If every loop of `A` lies either in
`A'` or in a piece `C` of invariant of dimension at most one, then passing from `A` to `A'` is a
step of the sweep.  This is the shape of Pardon's `spherefamily` argument: the loops of the region
either avoid the surgery zone (and lie in the new region) or lie inside the zone (and contribute at
most one dimension). -/
theorem spanStep_of_splits {A A' C : Set R3}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ.γ t ∈ A) →
      (∀ t : ℝ, γ.γ t ∈ A') ∨ (∀ t : ℝ, γ.γ t ∈ C))
    (hC : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P C) ≤ 1) :
    SpanStep P A A' := by
  refine spanStep_of_le_sup (L := Work.SurgeryInvariance.WindingSpan P C) hC ?_
  have hsplit := windingSpan_le_sup_of_three_splits (P := P) (A := A) (A' := A') (B := C) (C := C)
    (fun γ hγ => by
      rcases h γ hγ with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2))
  rwa [sup_assoc, sup_idem] at hsplit

/-! ## The dichotomy pins the value to `0` or `2` -/

/-- **Pardon's equation (1) pins the dimension.**  If the region's invariant is `⊥` or `⊤` (the
dichotomy), then its dimension is `0` or `2`. -/
theorem finrank_eq_zero_or_two_of_pardonDichotomy {X : Set R3}
    (h : Work.BoxShrink.Bubble.PardonDichotomy P X) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X) = 0 ∨
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X) = 2 := by
  rcases h with h | h
  · exact Or.inl (by rw [h, Submodule.finrank_eq_zero.mpr rfl])
  · exact Or.inr (by
      rw [h, finrank_top, Module.finrank_prod, Module.finrank_self])

/-! ## The value is constant along a chain of dichotomy regions with surgery steps -/

/-- **The value of a swept family is constant.**  Along a chain of regions each carrying the
dichotomy whose consecutive members differ by a single surgery, the dimension of the invariant
never drops: if the first region has dimension `2`, so does every region. -/
theorem chain_value_eq {k : ℕ} {A : ℕ → Set R3}
    (hdich : ∀ i ≤ k, Work.BoxShrink.Bubble.PardonDichotomy P (A i))
    (hstep : ∀ i < k, SpanStep P (A i) (A (i + 1)))
    (h0 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A 0)) = 2) :
    ∀ n ≤ k, Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A n)) = 2 := by
  intro n
  induction n with
  | zero => intro _; simpa using h0
  | succ n ih =>
      intro hn
      have hn' : n ≤ k := le_trans (Nat.le_succ n) hn
      have ih' := ih hn'
      have hstep' := hstep n (Nat.succ_le_iff.mp hn)
      unfold SpanStep at hstep'
      rw [ih'] at hstep'
      rcases finrank_eq_zero_or_two_of_pardonDichotomy (hdich (n + 1) hn) with hd | hd
      · omega
      · exact hd

/-! ## The carried input: Pardon's sweep -/

/-- **Pardon's sweep, for one box/plane configuration.**  There is a finite chain of regions of the
surface, each carrying the dichotomy (equation (1)) and each consecutive pair differing by a single
allowed surgery, running from the region inside the box to the union of the two half-regions.

This is the geometric content of Pardon's Section 2.3: the one-parameter family of spheres obtained
by performing the `2`-surgery along the cutting disc, put in general position, whose traces on the
surface are inessential at every regular time (which his counting hypothesis supplies) and which
changes the region by a single surgery at finitely many times. -/
def SweepChain (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ k : ℕ, ∃ A : ℕ → Set R3,
    A 0 = Work.BoxShrink.Core.boxRegion P s c σ ∧
    A k = Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u ∧
    (∀ i ≤ k, Work.BoxShrink.Bubble.PardonDichotomy P (A i)) ∧
    (∀ i < k, SpanStep P (A i) (A (i + 1)))

/-- **The sweep for every configuration of a parametrised torus.**  (For the challenge only the
smooth tori occur: `Work.BoxShrink.Pinch.smoothHalfS_of_sweepChainAll` below.) -/
def SweepChainAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    SweepChain P s c σ u

/-- **The sweep in the degenerate case of an empty slice.**  If the cutting plane misses the
surface inside the box, the box region *is* the union of the two half-regions, so the sweep has
length `0` and the only thing to supply is the dichotomy at the two (equal) endpoints.  This shows
that the carried condition is not vacuous and pins down its shape: a sweep of length `0` is a
partition of the box region by the plane that misses it. -/
theorem sweepChain_of_sliceRegion_empty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hempty : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅)
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ)) :
    SweepChain P s c σ u := by
  refine ⟨0, fun _ => Work.BoxShrink.Core.boxRegion P s c σ, rfl, ?_, ?_, ?_⟩
  · rw [Work.BoxShrink.Core.boxRegion_eq_union, hempty, Set.union_empty]
  · intro i hi
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    subst hi0
    exact hdich
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)

/-! ## The residual, from the sweep -/

/-- **Pardon's dimension bound from the sweep.**  The sweep starts at the box region and ends at
the union of the two half-regions; if the box region has dimension `2` then so does the union, so
in particular the drop is at most one. -/
theorem pinchNoJumpAll_of_sweepChainAll (h : SweepChainAll) : PinchNoJumpAll := by
  intro P s c σ u hS hZ
  obtain ⟨k, A, h0, hk, hdich, hstep⟩ := h P s c σ u hS hZ
  have hbox := finrank_windingSpan_le_two P (Work.BoxShrink.Core.boxRegion P s c σ)
  rcases lt_or_ge (Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ))) 2 with hlt | hge
  · omega
  · have htop : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.boxRegion P s c σ)) = 2 := le_antisymm hbox hge
    have hall := chain_value_eq hdich hstep (by rw [h0]; exact htop) k le_rfl
    have hk2 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u)) = 2 := by
      rw [← hk]; exact hall
    omega

/-- **The chapter's residual `PinchNoJump` from the sweep** (the smooth-torus form). -/
theorem pinchNoJump_of_sweepChainAll (h : SweepChainAll) : PinchNoJump := by
  intro ψ s c σ u hS hZ
  have := pinchNoJumpAll_of_sweepChainAll h (Work.Smooth.Morse.torus ψ) s c σ u hS hZ
  simpa using this

/-! ## The endgame: Pardon's Lemma 3, the crux and Theorem 1.1 -/

/-- **Pardon's Lemma 3 for the smooth tori, from the sweep** (with Pardon's equation (1) and the
general position of the box-sphere trace, both of which are classical). -/
theorem smoothHalfS_of_sweepChainAll (h1 : Equation1Input) (hnice : BoxSliceNice)
    (h : SweepChainAll) : SmoothHalfS :=
  smoothHalfS_of_pinchNoJump h1 hnice (pinchNoJump_of_sweepChainAll h)

/-- **The caller's field `Work.BoxShrink.Bubble.PushOffHalf`, from the sweep** (with the dichotomy
at the box sphere for arbitrary parametrised tori, which is the classical input). -/
theorem pushOffHalf_of_boxDichotomy_sweepChain (hdich : BoxDichotomyInput) (h : SweepChainAll) :
    Work.BoxShrink.Bubble.PushOffHalf :=
  pushOffHalf_of_boxDichotomy_noJump hdich (pinchNoJumpAll_of_sweepChainAll h)

/-- **The caller's field `Work.BoxShrink.Bubble.BubbleInputHalf`, from the sweep**. -/
theorem bubbleInputHalf_of_boxDichotomy_sweepChain
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (h : SweepChainAll) :
    Work.BoxShrink.Bubble.BubbleInputHalf :=
  bubbleInputHalf_of_boxDichotomy_noJump hcleanD hdich (pinchNoJumpAll_of_sweepChainAll h)

/-- **The crux, from the sweep**: Pardon's shrinking step for all `p, q`. -/
theorem cruxStatement_of_boxDichotomy_sweepChain
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (h : SweepChainAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  cruxStatement_of_boxDichotomy_noJump hcleanD hdich (pinchNoJumpAll_of_sweepChainAll h) hclean hae

/-- **Pardon's shrinking step from the sweep** (with the classical cut-and-paste step and the
almost-everywhere general position of the box-norm level sets). -/
theorem boxShrink_of_sweepChain
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (hnice : BoxSliceNice) (h : SweepChainAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  boxShrinkStatement_of_smoothHalfS hcleanD (smoothHalfS_of_sweepChainAll h1 hnice h) hclean hae

/-- **Pardon's Theorem 1.1 from the sweep, Pardon's equation (1), the general position of the
box-sphere trace and the two classical inputs.** -/
theorem pardon_torus_knot_distortion_of_equation1_boxNice_sweepChain
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (hnice : BoxSliceNice) (h : SweepChainAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q) (K : Knot)
      (_hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hcleanD
    (smoothHalfS_of_sweepChainAll h1 hnice h) hclean hae

end

end Work.BoxShrink.Pinch
