import Submission.Work.BoxShrink.Pinch.SlicedPushOff
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq
import Submission.Work.SurgeryInvariance.Span.union_eq_sup
import Submission.Work.SurgeryInvariance.Span.le_sup_of_splits

/-!
# Splitting the loop content of the box region: the homotopy form of the push-off

**WARNING (found by a colleague after this module was written): `PushOffHalfHomotopic` below is
FALSE**, and so is the claim in the first paragraph of this file that it is "strictly weaker" than
the realized-winding statements.  Homotopy preserves the winding vector
(`Work.SurgeryInvariance.WindingOf.homotopic_eq`), so "every essential loop of the box region is
homotopic to a loop of `upperRegion ∪ lowerRegion`" *forces* the winding vector of every essential
loop of the box region to be realized in the union — which is exactly the (refuted) push-off of
winding vectors.  At the model configuration this fails for the longitude `{z = -1}`, which lies in
the box region with winding `(1,0)`) while
`cex_onezero_not_mem_realizedWindings` forbids `(1,0)` in the union
(`cex_windingOf_longitudeCurve`, `cex_longitudeCurve_mem`,
`cex_not_containsEssentialLoop_sliceRegion`).  Consequently `bubbleHalf_of_pushOffHalfHomotopic`,
`pushOffHalf_of_pushOffHalfHomotopic` and the end-to-end chain below are vacuous, and the projection
of README §14 (that `RemovalInput` plus the gluing gives `PushOffHalfHomotopic`) is *not* a route to
`PushOffHalf`: the gluing cannot hold either, as `cex_windingSpan_boxRegion_eq_top` (`⊤`) against
`windingSpan_union_halfRegions_model_eq` (`ℚ·(0,1)`) shows.  The genuine residual of the area remains
the one of README §13, `Work.BoxShrink.Pinch.PushOffHalfSliced` (or Pardon's pinch datum
`PinchRegions`/`PinchLevels`), and the material of this file that is still valid is the *general*
lemma `windingSpan_le_of_homotopic_split`, which is a correct strengthening of
`Work.SurgeryInvariance.Span.le_sup_of_splits` and is used by nothing here.

The residual of the push-off is consumed by the crux in the *existence* form (`BubbleHalf`): an
essential loop of the region inside the box survives to one of the two half-regions.  Every
sufficient condition for it that the library produces, however, produces something slightly
different: a *homotopy* of loops, or a statement about the realized winding vectors
(`SlicePushOff`, `RegionEquivalent`).  This module closes that gap:

* `Work.BoxShrink.Pinch.windingSpan_le_of_homotopic_split` — **the homotopy form of
  `Work.SurgeryInvariance.Span.le_sup_of_splits`**: if every closed curve of `P` lying in `A` is
  homotopic (in the torus) to a curve lying in `A'`, or lies in a set `Z` of vanishing winding
  span, then `WindingSpan P A ≤ WindingSpan P A'`.  (`le_sup_of_splits` requires the curve itself
  to lie in `A'`; the flow theorems of `Work.Smooth.Morse.Flow` produce homotopies, so this is the
  form in which their output is consumed.  The winding vector is a homotopy invariant —
  `Work.SurgeryInvariance.WindingOf.homotopic_eq`.)
* `Work.BoxShrink.Pinch.windingSpan_boxRegion_le_sup_halves` — the box/plane instance, with the
  piece `Z` standing for a "collar" of the slice.
* `Work.BoxShrink.Pinch.bubbleHalf_of_splits` — and hence `BubbleHalf`, whenever the slice is
  inessential and the loops of the box region split between the halves and the collar.
* `Work.BoxShrink.Pinch.PushOffHalfHomotopic` — **the residual in the homotopy form**: every
  *essential* loop of the box region is homotopic in the torus to a loop of `upperRegion ∪
  lowerRegion`, given that the slice is inessential.  This is exactly the output of a push-off and
  it is *not* refuted by any configuration in this chapter (the refuted statements are about
  *realized winding vectors*, which is strictly more than homotopy of loops).
* `Work.BoxShrink.Pinch.pushOffHalf_of_pushOffHalfHomotopic` and
  `Work.BoxShrink.Pinch.bubbleInputHalf_bubble_of_pushOffHalfHomotopic`: it implies the residual
  field `Work.BoxShrink.Bubble.PushOffHalf` and hence the `bubble` field of
  `Work.BoxShrink.Bubble.BubbleInputHalf`.

Everything here is unconditional; the single hypothesis is carried explicitly in
`PushOffHalfHomotopic`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The homotopy form of the spanning lemma -/

/-- **The winding span is bounded by a target into which every curve can be homotoped.**

If every closed curve of `P` lying in `A` is homotopic (through closed curves of the torus) to a
closed curve lying in `A'`, or else lies in a set `Z` whose winding span vanishes, then
`WindingSpan P A ≤ WindingSpan P A'`.

This is `Work.SurgeryInvariance.Span.le_sup_of_splits` with "lies in `A'`" weakened to "is
homotopic to a curve lying in `A'`" — which is the form in which the push-off is naturally
proved (a homotopy of loops, not an inclusion of sets). -/
theorem windingSpan_le_of_homotopic_split
    {A A' Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ A) →
      (∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ A') ∧ Work.CoreTopology.Homotopic P γ γ') ∨
      (∀ t : ℝ, γ t ∈ Z))
    (hZ : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.WindingSpan P A ≤ Work.SurgeryInvariance.WindingSpan P A' := by
  rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.WindingSpan]
  apply Submodule.span_le.mpr
  rintro v ⟨γ, hγ, rfl⟩
  rcases h γ hγ with ⟨γ', hγ', hhom⟩ | hZγ
  · have hw : Work.SurgeryInvariance.windingOf P γ = Work.SurgeryInvariance.windingOf P γ' :=
      Work.SurgeryInvariance.WindingOf.homotopic_eq hhom
    rw [hw]
    exact Submodule.subset_span ⟨γ', hγ', rfl⟩
  · have hv : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := by
      rw [← hZ]
      exact Submodule.subset_span ⟨γ, hZγ, rfl⟩
    rw [Submodule.mem_bot] at hv
    rw [hv]
    exact Submodule.zero_mem _

/-- **The box/plane instance.**  If the loops of the region inside the box split into loops that
can be homotoped into the two half-regions and loops lying in a piece `Z` of vanishing winding
span (a collar of the slice), then the winding span of the region inside the box is contained in
the supremum of the spans of the two half-regions. -/
theorem windingSpan_boxRegion_le_sup_halves {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hsplit : ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
      (∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∧
        Work.CoreTopology.Homotopic P γ γ') ∨ (∀ t : ℝ, γ t ∈ Z))
    (hZ : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
        Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  refine le_trans (windingSpan_le_of_homotopic_split (P := P) hsplit hZ) ?_
  · rw [Work.SurgeryInvariance.Span.union_eq_sup (P := P)
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)]

/-- **Pardon's conclusion from the splitting of the loops of the box region.** -/
theorem bubbleHalf_of_splits {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hsplit : ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
      (∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∧
        Work.CoreTopology.Homotopic P γ γ') ∨ (∀ t : ℝ, γ t ∈ Z))
    (hZ : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have hne : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
    fun hbot => absurd hbox ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mp hbot)
  have hle := windingSpan_boxRegion_le_sup_halves (P := P) hsplit hZ
  have hsup : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ :=
    fun hbot => hne (le_antisymm (hbot ▸ hle) bot_le)
  rcases not_and_or.mp (fun hh :
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ =>
      hsup (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

/-! ## The residual in the homotopy form -/

/-- **The push-off in the homotopy form.  FALSE** (see the warning at the head of this module):
since homotopy preserves the winding vector, this statement *is* the realized-winding push-off, which
`Work.BoxShrink.Bubble.cex_not_slicePushOff` refutes.  It is kept only as the record of the failed
route; do not use it. -/
def PushOffHalfHomotopic : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
      Work.CoreTopology.IsEssential P γ →
      ∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∧
        Work.CoreTopology.Homotopic P γ γ'

/-- **The homotopy form of the push-off gives Pardon's conclusion.**  A loop of the union of the
two half-regions which is homotopic to an essential loop of the box region is essential, so the
union of the halves carries an essential loop; the two halves are disjoint open pieces of the
surface, so one of them does. -/
theorem bubbleHalf_of_pushOffHalfHomotopic (h : PushOffHalfHomotopic) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro P s c σ u hZ hbox
  obtain ⟨γ, hess, hγ⟩ := hbox
  obtain ⟨γ', hγ', hhom⟩ := h P s c σ u hZ γ hγ hess
  -- the transported loop is essential, since the winding vector is a homotopy invariant
  have hw : Work.SurgeryInvariance.windingOf P γ = Work.SurgeryInvariance.windingOf P γ' :=
    Work.SurgeryInvariance.WindingOf.homotopic_eq hhom
  have hess' : Work.CoreTopology.IsEssential P γ' :=
    (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ').mpr
      (fun hzero => (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mp hess
        (by rw [hw, hzero]))
  have hspan : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr ⟨γ', hess', hγ'⟩
  rw [Work.SurgeryInvariance.Span.union_eq_sup (P := P)
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)] at hspan
  rcases not_and_or.mp (fun hh :
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ =>
      hspan (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

/-- **The residual field of the challenge from the homotopy form of the push-off.** -/
theorem pushOffHalf_of_pushOffHalfHomotopic (h : PushOffHalfHomotopic) :
    Work.BoxShrink.Bubble.PushOffHalf :=
  fun P s c σ u _hS hZ => bubbleHalf_of_pushOffHalfHomotopic h P s c σ u hZ

/-- **The caller's `bubble` field from the homotopy form of the push-off.** -/
theorem bubbleInputHalf_bubble_of_pushOffHalfHomotopic (h : PushOffHalfHomotopic) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Bubble.BubbleHalf P s c σ u :=
  fun P s c σ u _hS hZ => bubbleHalf_of_pushOffHalfHomotopic h P s c σ u hZ

/-! ## The end-to-end chain from the homotopy form of the push-off

The same replay of the delivered chain as in `SlicedPushOff.lean`, with the residual supplied in the
homotopy form: the crux, Pardon's shrinking statement and the challenge itself. -/

/-- **The crux from the homotopy form of the push-off.** -/
theorem cruxCore_of_pushOffHalfHomotopic
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalfHomotopic) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_pushOffHalfSliced hcleanD (pushOffHalf_of_slicedPushOff
    (pushOffHalf_of_pushOffHalfHomotopic h))

/-- **The crux statement from the homotopy form of the push-off.** -/
theorem cruxStatement_of_pushOffHalfHomotopic
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalfHomotopic) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) : ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  cruxStatement_of_pushOffHalfSliced hcleanD (pushOffHalf_of_slicedPushOff
    (pushOffHalf_of_pushOffHalfHomotopic h)) hclean hae

/-- **Pardon's shrinking statement from the homotopy form of the push-off.** -/
theorem boxShrinkStatement_of_pushOffHalfHomotopic
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalfHomotopic) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) : ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  boxShrinkStatement_of_pushOffHalfSliced hcleanD (pushOffHalf_of_slicedPushOff
    (pushOffHalf_of_pushOffHalfHomotopic h)) hclean hae

/-- **Pardon's theorem from the homotopy form of the push-off.** -/
theorem pardon_torus_knot_distortion_of_pushOffHalfHomotopic
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalfHomotopic) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_pushOffHalfSliced hcleanD
    (pushOffHalf_of_slicedPushOff (pushOffHalf_of_pushOffHalfHomotopic h)) hclean hae
    p q hp hq hc K hclass

end

end Work.BoxShrink.Pinch
