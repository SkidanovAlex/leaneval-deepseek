import Submission.Work.PinchFamily.Defs
import Submission.Work.PinchFamily.Family
import Submission.Work.PinchFamily.matched_of_countedStep
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_union_zeroSpan
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans

/-!
# The local residual of Pardon's counted Lemma 3 **is** the push-off

This module proves the converse of `Family.lean`: the family of
`Work.PinchCounted.CountedPinch` forces the push-off of the slice, whenever the two half-regions
carry an essential loop — the only case in which Pardon's conclusion has content.

The proof is the loop-content argument of Pardon's Lemma 2.3 in the vocabulary of
`Work.PinchCounted.CountedStep`:

* a `CountedStep` matches the loops of its first region by loops of its second, with the same winding
  vector, as soon as the second region meets the surface (`matched_of_countedStep`);
* the winding span is constant along the family, so with `halves` essential *every* region of the
  family is essential, hence meets the surface — the hypothesis needed for the previous point;
* hence the relation "the loop content did not change from `region 0`" is *clopen* in the connected
  parameter line `ℝ` (the local move at `t` and its reverse, `CountedStep.symm`, both hold on a
  neighbourhood of `t`), so it holds all the way to `region 1 = halves ∪ Z`;
* the piece `Z` is open in the surface, disjoint from the two half-regions and of vanishing span, so
  pushing it off changes nothing (`Toolkit.regionEquivalent_union_zeroSpan`), and the loop content
  of the region inside the box equals that of the two half-regions: the push-off.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

/-- **The local family of Pardon's counted Lemma 3 forces the push-off**, in the case in which the
two half-regions carry an essential loop. -/
theorem regionPushOff_of_localFamilyBody {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : LocalFamilyBody P β s c σ u)
    (hess : P.ContainsEssentialLoop (halves P s c σ u)) :
    RegionPushOff P s c σ u := by
  obtain ⟨region, hzero, ⟨Z, hZopen, hZspan, hZdisj, hone⟩, hloc⟩ := h
  -- the span is constant along the family, and non-zero
  have hspan_eq : Work.SurgeryInvariance.WindingSpan P (box P s c σ) =
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) :=
    Work.PinchCounted.windingSpan_eq_of_countedLocalFamily β region hzero hZopen hZspan hZdisj
      hone hloc
  have hbox_ne : Work.SurgeryInvariance.WindingSpan P (box P s c σ) ≠ ⊥ := by
    rw [hspan_eq]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hess
  have hconst : ∀ t : ℝ, Work.SurgeryInvariance.WindingSpan P (region t) =
      Work.SurgeryInvariance.WindingSpan P (region 0) := fun t =>
    Work.SurgeryInvariance.eq_of_locally_const (f := fun r : ℝ =>
      Work.SurgeryInvariance.WindingSpan P (region r)) (by
        intro r
        obtain ⟨ε, hε, hε'⟩ := hloc r
        exact ⟨ε, hε, fun r' hr' =>
          (Work.PinchCounted.CountedStep.windingSpan_eq (hε' r' hr')).symm⟩) t 0
  -- every region of the family carries an essential loop, hence meets the surface
  have hmeet : ∀ t : ℝ, (region t ∩ P.carrier).Nonempty := by
    intro t
    have hne : Work.SurgeryInvariance.WindingSpan P (region t) ≠ ⊥ := by
      rw [hconst t, hzero]
      exact hbox_ne
    obtain ⟨γ, -, hγ⟩ := (Work.SurgeryInvariance.windingSpan_ne_bot_iff P (region t)).mp hne
    exact ⟨γ 0, hγ 0, γ.mem 0⟩
  -- the local move at `t`, in both directions
  have hstep : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
      Work.SurgeryInvariance.RegionEquivalent P (region t) (region r) := by
    intro t
    obtain ⟨ε, hε, hε'⟩ := hloc t
    refine ⟨ε, hε, fun r hr => ⟨?_, ?_⟩⟩
    · exact matched_of_countedStep β (hε' r hr) (hmeet r)
    · exact matched_of_countedStep β (Work.PinchCounted.CountedStep.symm (hε' r hr)) (hmeet t)
  -- the set of parameters at which the loop content is unchanged is clopen
  let S : Set ℝ := {t | Work.SurgeryInvariance.RegionEquivalent P (region 0) (region t)}
  have hSopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro t ht
    obtain ⟨ε, hε, hε'⟩ := hstep t
    refine ⟨ε, hε, fun r hr => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hr
    exact Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans ht (hε' r hr)
  have hSclosed : IsOpen Sᶜ := by
    rw [Metric.isOpen_iff]
    intro t ht
    obtain ⟨ε, hε, hε'⟩ := hstep t
    refine ⟨ε, hε, fun r hr => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hr
    simp only [Set.mem_compl_iff, S, Set.mem_setOf_eq] at ht ⊢
    intro hrS
    exact ht (Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans hrS (hε' r hr).symm)
  have hmem0 : (0 : ℝ) ∈ S :=
    Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _
  have huniv : (Set.univ : Set ℝ) ⊆ S := by
    have hcover : (Set.univ : Set ℝ) ⊆ S ∪ Sᶜ := by
      intro x _
      by_cases hx : x ∈ S
      · exact Or.inl hx
      · exact Or.inr hx
    rcases IsPreconnected.subset_or_subset hSopen hSclosed disjoint_compl_right hcover
      isPreconnected_univ with h' | h'
    · exact h'
    · exact absurd (h' (Set.mem_univ 0)) (by simpa using hmem0)
  have hchain : Work.SurgeryInvariance.RegionEquivalent P (region 0) (region 1) :=
    huniv (Set.mem_univ 1)
  -- push the pinching collar off
  obtain ⟨γ₀, -, hγ₀⟩ := hess
  have huzs : Work.SurgeryInvariance.RegionEquivalent P (halves P s c σ u ∪ Z)
      (halves P s c σ u) :=
    Work.BoxShrink.Bubble.Toolkit.regionEquivalent_union_zeroSpan
      (Work.PinchCounted.PinchSweep.isOpenInCarrier_halves P s c σ u) hZopen hZdisj hZspan
      ⟨γ₀ 0, hγ₀ 0, γ₀.mem 0⟩
  have hchain' : Work.SurgeryInvariance.RegionEquivalent P (box P s c σ)
      (halves P s c σ u ∪ Z) := by
    rw [← hzero, ← hone]
    exact hchain
  have hbox_halves : Work.SurgeryInvariance.RegionEquivalent P (box P s c σ)
      (halves P s c σ u) :=
    Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans hchain' huzs
  exact hbox_halves.symm

end

end Work.PinchFamily
