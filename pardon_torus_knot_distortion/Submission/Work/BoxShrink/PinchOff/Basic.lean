import Submission.Work.BoxShrink.Pinch.All

/-!
# The pinch-off: the last geometric datum of Pardon's argument

This is the entry module of the chapter `Work.BoxShrink.PinchOff`, whose object is the *last
geometric datum* of the challenge: Pardon's Lemma 3 (his `doublebubble`) for the **smooth tori of
the challenge**, under **both** of his endpoint hypotheses -- the box sphere `∂PBox s c σ` and the
flat slicing disc `cutDisc s c σ u` carry no essential loop of the surface.

## The configuration

For a smooth configuration `(ψ, s, c, σ, u)` (`ψ : Submission.Diffeo` a diffeomorphism of `ℝ³`,
`F = torus ψ` the surface, `PBox s c σ` Pardon's box, `{y (σ 2) = c (σ 2) + u}` the cutting plane)
the chapter writes

* `Omega` for the region of `F` inside the box, `F ∩ PBox s c σ` (the parent chapter's `boxRegion`);
* `Sigma` for the **slice**, `F ∩ PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}` (the parent chapter's
  `sliceRegion`);
* `HalfUp`, `HalfDown`, `Halves = HalfUp ∪ HalfDown` for the two half-regions, the trace of the
  cutting plane removed (`upperRegion`, `lowerRegion`);
* `SphereTrace` for the trace `F ∩ ∂PBox s c σ` of the box sphere (`sphereSet`).

The invariant is the **winding span** `Work.SurgeryInvariance.WindingSpan F X ≤ ℚ² = H₁(F;ℚ)`, the
`ℚ`-span of the winding vectors of the closed curves of `F` lying in `X`; it vanishes exactly when
`X` contains no essential loop (`Work.SurgeryInvariance.WindingSpan_eq_bot_iff`).

## Pardon's Lemma 3, and its sharpest provable form

Pardon's Lemma 3 (`doublebubble`) says: **if `Omega` carries an essential loop and neither
`SphereTrace` nor `Sigma` does, then one of the two halves carries an essential loop.**  In the
vocabulary of the winding span this is `BubbleHalf`, and the whole chapter is about inhabiting the
`Prop`

  `Work.BoxShrink.Pinch.SmoothHalfS` -- `BubbleHalf` for every smooth configuration with `hS` and
  `hZ`.

The parent chapter `Work.BoxShrink.Pinch` proved (and this chapter re-exports) that `SmoothHalfS`
follows from Pardon's dichotomy (equation (1), the classical classification of compact surfaces,
carried as `Work.BoxShrink.Pinch.Equation1Input`) and the general position of the box-sphere trace
(`BoxSliceNice`) together with **one** remaining statement, the dimension bound of a single
`2`-surgery -- Pardon's own "doing any of the allowed surgeries can change this value by at most
`1`".  This chapter records that statement as `Key`, in the sharpest form the parent chapter
isolated, and

* proves the **equivalences** between the forms of the residual (`key_iff_keyCase`,
  `key_iff_loopForm`) and its **monotonicity** (`transport_to_strong`, `strong_to_key`);
* proves it in a **list of configurations** (`Instances.lean`, `DiscPush.lean`), including the
  configurations in which the slice is contained in finitely many embedded discs inside the box
  (which is the case of a slice made of *circles only*, when the discs bounded by those circles lie
  in the box);
* records, in `DiscPush.lean`, the one **new** mathematical statement the general case needs beyond
  what the parent chapter has: the *local disc push-off* `DiscRoute` -- every loop of the box region
  is homotopic, moving only points inside the disc, to a loop of the box region avoiding the
  disc -- which is the local model of Pardon's pinch;
* names the classical inputs which remain (`Equation1Input`, `BoxSliceNice` and the two inputs of
  `DiscRoute`) and wires the whole reduction to the challenge
  (`pardon_torus_knot_distortion_of_key`).

## The transport form is *false*, and the residual is not it

The parent chapter's `RegionTransport`/`SlicePushOff` form (`Transport` below) asks for *every*
winding vector of the box region to be realised in the halves.  It is **refuted**
(`Work.BoxShrink.Bubble.standard_counterexample`,
`Work.BoxShrink.Pinch.regionTransport_iff_slicePushOff`), and the numerical study recorded in
`Submission/Work/BoxShrink/Pinch/EXP` shows that it stays false even under the additional
hypothesis `W(SphereTrace) = ⊥` (the script `spanbot.py` produces configurations with an inessential
sphere trace *and* an inessential plane trace, a rank-`2` box region and halves of rank `1`).  What
Pardon's Lemma 3 needs -- and what the challenge consumes -- is only that *some* essential loop
survives, so the residual has to be the one-sided dimension bound `Key`, not the transport form.
`transport_to_strong` and `strong_to_key` below record the (one-way) implications.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The configuration -/

/-- The smooth surface of the configuration: Pardon's surface `F = ψ(F_standard)`. -/
abbrev surface (ψ : Submission.Diffeo) : Work.CoreTopology.ParamTorus :=
  Work.Smooth.Morse.torus ψ

/-- **`Ω`**: the region of the surface inside Pardon's box `PBox s c σ`. -/
abbrev Omega (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  Work.BoxShrink.Core.boxRegion (surface ψ) s c σ

/-- **`Σ`**: the slice, the trace of the cutting plane `{y (σ 2) = c (σ 2) + u}` inside the box. -/
abbrev Sigma (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sliceRegion (surface ψ) s c σ u

/-- **`Ω₊`**: the upper half-region (above the cutting plane, inside the box). -/
abbrev HalfUp (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.upperRegion (surface ψ) s c σ u

/-- **`Ω₋`**: the lower half-region (below the cutting plane, inside the box). -/
abbrev HalfDown (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.lowerRegion (surface ψ) s c σ u

/-- **The union of the two half-regions**: the region the pinch has to land in. -/
abbrev Halves (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  HalfUp ψ s c σ u ∪ HalfDown ψ s c σ u

/-- **The trace of the box sphere** `∂PBox s c σ` on the surface. -/
abbrev SphereTrace (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  Work.BoxShrink.Core.sphereSet c σ s

/-! ## The parameter plane

The chapter keeps, next to the sets on the surface, their preimages in the **parameter plane** of
the parametrisation `par ψ : ℝ × ℝ → ℝ³`, `par ψ (x, y) = ψ (torusMap x y)`.  Read there, the
configuration is `Ω̃ = {B < s}`, `Σ̃ = {B < s, G = 0}` and the halves' preimage `{B < s, G ≠ 0}`,
where `B = boxB ψ c σ = boxNorm c σ ∘ par ψ` and `G = planeG ψ c σ u = planeCoord c σ u ∘ par ψ`
(parent chapter, `Basic.lean`).  This is the form in which a routing/perturbation argument about
the *slice* is run, and the form in which the loop reformulation of the residual
(`Sharpening.key_iff_loopForm`) is stated. -/

/-- The preimage of `Ω` in the parameter plane. -/
def OmegaTilde (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Set (ℝ × ℝ) :=
  {p | Work.BoxShrink.Pinch.par ψ p ∈ Omega ψ s c σ}

/-- The preimage of the slice `Σ` in the parameter plane. -/
def SigmaTilde (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Set (ℝ × ℝ) :=
  {p | Work.BoxShrink.Pinch.par ψ p ∈ Sigma ψ s c σ u}

/-- The preimage of the union of the halves in the parameter plane. -/
def HalvesTilde (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Set (ℝ × ℝ) :=
  {p | Work.BoxShrink.Pinch.par ψ p ∈ Halves ψ s c σ u}

/-- **The dictionary**: the preimage of the box region is the sublevel set `{B < s}` of the
pull-back box norm. -/
theorem OmegaTilde_eq (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    OmegaTilde ψ s c σ = {p : ℝ × ℝ | Work.BoxShrink.Pinch.boxB ψ c σ p < s} :=
  Work.BoxShrink.Pinch.preimage_boxRegion ψ s c σ

/-- **The dictionary**: the preimage of the slice is `{B < s, G = 0}`. -/
theorem SigmaTilde_eq (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    SigmaTilde ψ s c σ u =
      {p : ℝ × ℝ | Work.BoxShrink.Pinch.boxB ψ c σ p < s ∧
        Work.BoxShrink.Pinch.planeG ψ c σ u p = 0} :=
  Work.BoxShrink.Pinch.preimage_sliceRegion ψ s c σ u

/-- **The dictionary**: the preimage of the two half-regions is `{B < s, G ≠ 0}`. -/
theorem HalvesTilde_eq (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    HalvesTilde ψ s c σ u =
      {p : ℝ × ℝ | Work.BoxShrink.Pinch.boxB ψ c σ p < s ∧
        Work.BoxShrink.Pinch.planeG ψ c σ u p ≠ 0} :=
  Work.BoxShrink.Pinch.preimage_union_halfRegions ψ s c σ u

/-- The preimages are invariant under the period lattice `2πℤ²`. -/
theorem mem_OmegaTilde_add_lattice {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {p : ℝ × ℝ} (hp : p ∈ OmegaTilde ψ s c σ) (k l : ℤ) :
    (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) ∈
      OmegaTilde ψ s c σ := by
  rw [OmegaTilde_eq] at hp ⊢
  show Work.BoxShrink.Pinch.boxB ψ c σ
    (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) < s
  rw [Work.BoxShrink.Pinch.boxB_period]
  exact hp

/-! ## The residual statements

The parent chapter isolates the residual of the pinch as a one-sided *dimension* bound
(`Work.BoxShrink.Pinch.PinchNoJump`, equivalent to its key case by
`Work.BoxShrink.Pinch.pinchNoJump_iff_keyCase`).  This chapter uses the same statements under the
short names below, and proves that they are exactly equivalent to the *loop-level* form
(`key_iff_loopForm`) in which a routing or flow argument can be applied. -/

/-- **The residual of the pinch, in its weakest usable form** (Pardon's "a single `2`-surgery
changes the invariant by at most `1`"): if the sphere trace and the slice both carry no essential
loop, then passing the pinch lowers the dimension of the winding span by at most one.

This is the exact statement the challenge's field `bubble` needs, given Pardon's equation (1) and
the general position of the box-sphere trace; see `smoothHalfS_of_key`. -/
def Key : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ)
        (Halves ψ s c σ u)) + 1

/-- **The key case of the residual**: the box region cannot span the whole of `H₁(F;ℚ)` while the
two halves together span nothing.  By `key_iff_keyCase` this is *equivalent* to `Key`. -/
def KeyCase : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) = 2 →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥

/-- **The strong (span) form of the pinch-off**: the winding span of the box region *equals* that
of the two half-regions, so that no winding vector at all is lost at the pinch.  This form is
strictly stronger than `Key` (and, by the parent chapter's refutations, *false* in general); it is
recorded because it is what several natural arguments (routing, isotopy) produce directly. -/
def Strong : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) =
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)

/-- **The transport (push-off) form of the pinch-off**: every loop of the box region is matched by
a loop of the two half-regions with the same winding vector.

**This form is false** -- the parent chapter's `standard_counterexample` and
`regionTransport_iff_slicePushOff` refute it, and the numerical study in
`Submission/Work/BoxShrink/Pinch/EXP` shows that it fails even under the extra hypothesis
`W(planeTrace) = ⊥`.  It is recorded because it is the form in which a push-off is naturally
phrased, and because `transport_to_strong` shows that it implies the (also false) strong form: the
useful residual is the one-sided `Key`. -/
def Transport : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.SurgeryInvariance.RegionEquivalent (surface ψ) (Halves ψ s c σ u) (Omega ψ s c σ)

/-! ## The dictionary with the parent chapter -/

/-- `Key` *is* the parent chapter's `PinchNoJump`, definitionally. -/
theorem key_iff_pinchNoJump : Key ↔ Work.BoxShrink.Pinch.PinchNoJump := Iff.rfl

/-- `KeyCase` *is* the parent chapter's `PinchNoJumpKeyCase`, definitionally. -/
theorem keyCase_iff_pinchNoJumpKeyCase : KeyCase ↔ Work.BoxShrink.Pinch.PinchNoJumpKeyCase :=
  Iff.rfl

/-- **`Key` is exactly its key case**: the one-sided dimension bound can only fail at a full-rank
box region whose halves are empty of essential loops (the parent chapter's
`pinchNoJump_iff_keyCase`). -/
theorem key_iff_keyCase : Key ↔ KeyCase :=
  Work.BoxShrink.Pinch.pinchNoJump_iff_keyCase

/-! ## The monotonicity of the residual -/

/-- The transport form gives the strong form: the two regions then have the same winding span
(parent chapter, `windingSpan_eq_of_regionTransport`). -/
theorem transport_to_strong (h : Transport) : Strong :=
  fun ψ s c σ u hS hZ =>
    (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq (h ψ s c σ u hS hZ)).symm

/-- The strong form gives the weak (one-sided) form, by pure linear algebra: the dimensions are
equal, hence the `+1` bound holds. -/
theorem strong_to_key (h : Strong) : Key :=
  fun ψ s c σ u hS hZ => by
    rw [h ψ s c σ u hS hZ]
    exact Nat.le_succ _

/-- **The strong form gives Pardon's Lemma 3 conclusion** at every configuration: if the two
regions have the same winding span and the box region is essential, then so is the union of the two
halves, and hence one of them (they are disjoint open pieces of the surface). -/
theorem bubbleHalf_of_strong {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ}
    (h : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) =
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u := by
  intro hbox
  have hne : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥ := by
    rw [← h]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr hbox
  rw [Work.SurgeryInvariance.Span.union_eq_sup (P := surface ψ)
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion (surface ψ) s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion (surface ψ) s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion (surface ψ) s c σ u)] at hne
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan (surface ψ)
        (HalfUp ψ s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u) = ⊥ =>
      hne (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hlo)

/-- **A `Strong` configuration discharges `BubbleHalf`** at that configuration. -/
theorem bubbleHalf_of_strong_of_hS_hZ (h : Strong) (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (hS : ¬ (surface ψ).ContainsEssentialLoop
      (SphereTrace s c σ))
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u)) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_strong (h ψ s c σ u hS hZ)

/-! ## The reduction to the deliverable

`Key`, together with the two classical inputs of the pinch (Pardon's equation (1) — the
classification of compact surfaces, `Work.BoxShrink.Pinch.Equation1Input` — and the general
position of the box-sphere trace, `Work.BoxShrink.Pinch.BoxSliceNice`), gives Pardon's Lemma 3 for
the smooth tori (`SmoothHalfS`), hence the field `bubble` of the corrected final input, hence the
challenge.  All the implications are the parent chapter's; they are re-exported here under the
names of this chapter so that a caller only has to import `Work.BoxShrink.PinchOff.All`. -/

/-- **Pardon's Lemma 3 for the smooth tori, from the residual and the two classical inputs.** -/
theorem smoothHalfS_of_key (h1 : Work.BoxShrink.Pinch.Equation1Input)
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice) (h : Key) :
    Work.BoxShrink.Pinch.SmoothHalfS :=
  Work.BoxShrink.Pinch.smoothHalfS_of_pinchNoJump h1 hnice h

/-- The same, in the form in which the parent chapter's `TameTarget.lean` states the deliverable
(with the transversality and tameness of the slice exposed as hypotheses). -/
theorem pushOffHalfTame_of_key (h1 : Work.BoxShrink.Pinch.Equation1Input)
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice) (h : Key) :
    Work.BoxShrink.Pinch.PushOffHalfTame :=
  Work.BoxShrink.Pinch.pushOffHalfTame_of_smoothHalfS (smoothHalfS_of_key h1 hnice h)

/-- The weak residual gives the strong residual whenever the slice is empty (the two regions then
coincide) -- recorded to show that `Weak` is not vacuous. -/
theorem not_strong_of_not_key : ¬ Key → ¬ Strong := fun h h' => h (strong_to_key h')

/-- **The corrected final input, from the residual and the classical inputs.** -/
theorem finalInputS_of_key
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Work.BoxShrink.Pinch.Equation1Input) (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : Key) (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    Work.BoxShrink.Pinch.FinalInputS :=
  Work.BoxShrink.Pinch.finalInputS_of_smoothHalfS hdisc (smoothHalfS_of_key h1 hnice h) hclean hae

/-- **Pardon's double-bubble core, from the residual.** -/
theorem cruxCore_of_key
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (surface ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Work.BoxShrink.Pinch.Equation1Input) (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : Key) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.Pinch.cruxCore_of_smoothHalfS hdisc (smoothHalfS_of_key h1 hnice h)

/-- **Pardon's shrinking step, from the residual.** -/
theorem cruxStatement_of_key
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (surface ψ) (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Work.BoxShrink.Pinch.Equation1Input) (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : Key) (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  Work.BoxShrink.Pinch.cruxStatement_of_smoothHalfS hdisc (smoothHalfS_of_key h1 hnice h)
    hclean hae

/-- **The challenge, from the residual and the classical inputs.**  This is the end-to-end theorem
of the chapter: a proof of `Key` (plus the classical inputs, all of which are named in the
README) gives Pardon's lower bound for the distortion of the torus knots of the challenge. -/
theorem pardon_torus_knot_distortion_of_key
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Work.BoxShrink.Pinch.Equation1Input) (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : Key) (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.Pinch.pardon_torus_knot_distortion_of_smoothHalfS hdisc
    (smoothHalfS_of_key h1 hnice h) hclean hae

end

end Work.BoxShrink.PinchOff
