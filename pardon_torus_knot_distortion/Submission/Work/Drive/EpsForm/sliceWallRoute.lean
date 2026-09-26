import Mathlib
import Submission.Work.Drive.EpsForm.Defs
import Submission.Work.PinchLemma3.Residual
import Submission.Work.PinchLemma3.Targets
import Submission.Work.Drive.EpsForm.wallTwoPieces
import Submission.Work.Drive.EpsForm.closedHalfBox
import Submission.Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
import Submission.Work.SurgeryInvariance.Span.union_eq_sup
import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.Drive.not_exists_weakCompressingLoop_of_counts
import Submission.Work.InnermostDisk.All

/-!
# The assignment from the fleet's residual `SliceWall`

`Work.PinchLemma3.SliceWall` (the fleet's current residual of field 2, alias of
`Work.BoxShrink.Pinch.PinchNoJump`) is the *dimension bound*

  `dim W(Ω) ≤ dim W(halfRegions) + 1`

at every configuration for which Pardon's two *endpoint* hypotheses hold: the trace of the box
sphere and the trace of the cutting plane carry no essential loop of the surface.

This module proves that this residual **implies the assignment**
`Work.Drive.CountingHalfEpsBody` — with *no* further hypothesis.  The point is the case split:

* if the slice `Σ` of the cutting plane carries an essential loop of the surface, then that loop lies
  in the closed lower half box (`sliceRegion_subset_closedLowerHalfBox`) and the geometric lemma
  `exists_mem_PBox_of_mem_closedHalfBox` turns it into a witness for the solid ε-conclusion — no
  dimension bound needed;
* otherwise the slice has no essential loop, so `SliceWall` applies at the configuration (the
  box-sphere hypothesis being supplied by Pardon's Lemma 2 at the box sphere,
  `sphereTrace_inessential_of_countsW_here`); the dimension bound then reads
  `2 = dim W(Ω) ≤ dim W(halfRegions) + 1`, which forces `W(halfRegions) ≠ ⊥`; additivity over the two
  open, disjoint half-regions produces an essential loop of one of them, and a loop of a half-region
  witnesses the solid ε-conclusion with distance `0`.

Note the *absence* of any hypothesis on the general position of the cutting plane: the "bad" case
(an essential loop in the slice) is exactly the case in which the solid form is witnessed by a loop
lying in the plane.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Drive.EpsForm

noncomputable section

/-- **Pardon's Lemma 2 at the box sphere, in the weak-disc vocabulary** (a copy of
`Work.Drive.EpsForm.sphereTrace_inessential_of_countsW`, kept here so that this module does not
import the sibling module carrying the trace-form `sorry`).  From the crux's sphere count, the
general position of the box sphere (`SlicedSphere`) and the weak cut-and-paste input
(`CleansDiscsW`), the trace of the box sphere carries no essential loop. -/
theorem sphereTrace_inessential_of_countsW_here
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcl : Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s) := by
  intro hcon
  have hIn : Work.InnermostDisk.InnermostDiscInput (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing hslice.some
  obtain ⟨D⟩ := hIn hcon
  exact Work.Drive.not_exists_weakCompressingLoop_of_counts p q hp hq hc ψ K hd himg hsmall
    c σ hcount ⟨D.α, D.simple, D.essential, hcl _ D, D.mem⟩

/-- **The box region has full winding span** at a configuration whose box-sphere trace is
inessential.  `W(Ω) ≠ ⊥` is `HasEssBox` at `r < s`; the wall of the box sphere
(`Work.Drive.EpsForm.Wall.exists_wall_of_slicedSphere`) with the two open pieces `Ω` and
`F ∖ closure (PBox)` pins `W(Ω)` to `{⊥, ⊤}`
(`Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary`). -/
theorem windingSpan_boxRegion_eq_top_of_sphereTrace_inessential
    {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} (hs : 0 < s)
    (hsl : Work.BoxShrink.SlicedSphere P (Work.BoxShrink.Core.sphereSet c σ s))
    (hess : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s))
    (hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊤ := by
  obtain ⟨n, γ, hsimple, hiness, hdisj, hcover⟩ :=
    Wall.exists_wall_of_slicedSphere (P := P) (s := s) (c := c) (σ := σ) hs hsl hess
  have hfront : Work.BoxShrink.Core.sphereSet c σ s = frontier (Submission.PBox s c σ) := by
    rw [Work.BoxShrink.Core.sphereSet_eq_BoxSphere,
      ← Work.Topology.SphereSlicing.frontier_PBox hs c σ]
  have hout : P.carrier \ closure (Submission.PBox s c σ) =
      P.carrier ∩ (closure (Submission.PBox s c σ))ᶜ := by
    ext x; simp
  have hdich := Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
    (P := P) (γ := γ)
    (X := Work.BoxShrink.Core.boxRegion P s c σ)
    (Y := P.carrier \ closure (Submission.PBox s c σ))
    hsimple hiness hdisj
    (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ) ?_ ?_ ?_
  · rcases hdich with h | h
    · exact absurd h hne
    · exact h
  · rw [hout]
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter isClosed_closure.isOpen_compl
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 (subset_closure hx.2)
  · have hW : ∀ x : R3, x ∈ (⋃ i, Set.range (γ i).γ) ↔
        x ∈ P.carrier ∧ x ∈ frontier (Submission.PBox s c σ) := by
      intro x
      rw [hcover]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [hfront] at h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [hfront]⟩
    have hfr : ∀ x : R3, x ∈ frontier (Submission.PBox s c σ) ↔
        x ∈ closure (Submission.PBox s c σ) ∧ x ∉ Submission.PBox s c σ := by
      intro x
      rw [frontier_eq_closure_inter_closure, closure_compl,
        (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq, Set.mem_inter_iff,
        Set.mem_compl_iff]
    ext x
    constructor
    · rintro ⟨hxc, hxW⟩
      have hxfr : ¬ (x ∈ closure (Submission.PBox s c σ) ∧ x ∉ Submission.PBox s c σ) :=
        fun h' => hxW ((hW x).mpr ⟨hxc, (hfr x).mpr h'⟩)
      rcases not_and_or.mp hxfr with hcl | hbox
      · exact Or.inr ⟨hxc, hcl⟩
      · exact Or.inl ⟨hxc, not_not.mp hbox⟩
    · rintro (⟨hxc, hxbox⟩ | ⟨hxc, hxcl⟩)
      · exact ⟨hxc, fun hxW => ((hfr x).mp ((hW x).mp hxW).2).2 hxbox⟩
      · exact ⟨hxc, fun hxW => hxcl ((hfr x).mp ((hW x).mp hxW).2).1⟩

/-- **The conclusion at a single configuration, from the dimension bound.** -/
theorem conclusion_of_sliceWall_dimensionBound {ψ : Submission.Diffeo} {r s u ε : ℝ}
    (hr : 0 < r) (hrs : r < s) (hε : 0 < ε) {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hbox : Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ)
    (hsl : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.sphereSet c σ s))
    (hSp : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s))
    (hbu : |u| < Submission.boxSide 2 * s)
    (hdim : Module.finrank ℚ
        ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) ≤
      Module.finrank ℚ
        ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.PinchLemma3.halfRegions (Work.Smooth.Morse.torus ψ) s c σ u)) + 1) :
    (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
        Work.CoreTopology.IsEssential _ γ ∧
          ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ x (σ 2) < c (σ 2) + u ∧
            dist (γ t) x < ε) ∨
    (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
        Work.CoreTopology.IsEssential _ γ ∧
          ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ c (σ 2) + u < x (σ 2) ∧
            dist (γ t) x < ε) := by
  set P := Work.Smooth.Morse.torus ψ with hP
  have hspos : 0 < s := lt_trans hr hrs
  by_cases hZ : P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u)
  · obtain ⟨γ, hess, hmem⟩ := hZ
    refine Or.inl ⟨γ, hess, fun t => ?_⟩
    have h1 := sliceRegion_subset_closedLowerHalfBox (P := P) (hmem t)
    exact exists_mem_PBox_of_mem_closedHalfBox hε hspos hbu h1.1 h1.2
  · have hΩne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
      (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr
        (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (P := P)
          (c := c) (σ := σ) (le_of_lt hrs) hbox)
    have hΩtop : Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.boxRegion P s c σ) = ⊤ :=
      windingSpan_boxRegion_eq_top_of_sphereTrace_inessential hspos hsl hSp hΩne
    have hdimΩ : Module.finrank ℚ
        ↥(Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ)) = 2 := by
      rw [hΩtop, finrank_top, Module.finrank_prod]
      simp
    have hhalves : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u)
        ≠ ⊥ := by
      intro hbot
      have h0 : Module.finrank ℚ ↥(⊥ : Submodule ℚ (ℚ × ℚ)) = 0 := by simp
      rw [hbot, h0, hdimΩ] at hdim
      omega
    have hsplit : Work.SurgeryInvariance.WindingSpan P
          (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
        Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ := by
      rw [← Work.SurgeryInvariance.Span.union_eq_sup
        (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
        (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
        (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)]
      exact hhalves
    have hcase : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u)
        ≠ ⊥ ∨ Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u)
        ≠ ⊥ := by
      by_contra hcon
      push_neg at hcon
      exact hsplit (by rw [hcon.1, hcon.2, bot_sup_eq])
    rcases hcase with hup | hlo
    · obtain ⟨γ, hess, hmem⟩ :=
        (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup
      refine Or.inr ⟨γ, hess, fun t => ?_⟩
      have hm := Work.BoxShrink.Core.mem_upperRegion.mp (hmem t)
      exact ⟨γ t, hm.2.1, hm.2.2, by rw [dist_self]; exact hε⟩
    · obtain ⟨γ, hess, hmem⟩ :=
        (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo
      refine Or.inl ⟨γ, hess, fun t => ?_⟩
      have hm := Work.BoxShrink.Core.mem_lowerRegion.mp (hmem t)
      exact ⟨γ t, hm.2.1, hm.2.2, by rw [dist_self]; exact hε⟩

/-- **The assignment `Work.Drive.CountingHalfEpsBody` from the fleet's residual
`Work.PinchLemma3.SliceWall`, with no further hypothesis.** -/
theorem countingHalfEpsBody_of_sliceWall (hW : Work.PinchLemma3.SliceWall) :
    Work.Drive.CountingHalfEpsBody := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU ε hε
  set P := Work.Smooth.Morse.torus ψ with hP
  have hspos : 0 < s := lt_trans hr hrs
  have hbu : |u| < Submission.boxSide 2 * s := by
    have hle : Submission.eps ≤ Submission.boxSide 2 := by
      rw [Submission.boxSide_two, Submission.eps]
      linarith [Submission.one_le_rpow_two_thirds]
    have h1 : Submission.eps * r ≤ Submission.boxSide 2 * r :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hr)
    have h2 : Submission.boxSide 2 * r < Submission.boxSide 2 * s := by
      nlinarith [Submission.boxSide_pos 2, hrs]
    linarith [hu, h1, h2]
  have hSp : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) :=
    sphereTrace_inessential_of_countsW_here p q hp hq hc ψ K hd himg hsmall hspos
      c σ hslice hcl hS
  by_cases hZ : P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u)
  · obtain ⟨γ, hess, hmem⟩ := hZ
    refine Or.inl ⟨γ, hess, fun t => ?_⟩
    have h1 := sliceRegion_subset_closedLowerHalfBox (P := P) (hmem t)
    exact exists_mem_PBox_of_mem_closedHalfBox hε hspos hbu h1.1 h1.2
  · exact conclusion_of_sliceWall_dimensionBound hr hrs hε hbox hslice hSp hbu
      (hW ψ s c σ u hSp hZ)

/-! ## The assignment from the fleet's decomposed residual

The fleet decomposes `SliceWall` into
`TrivialSurgeryTarget` (reduced to `Work.PinchLemma3.NoFullJump`) together with
`ClosedDiscsCoverTarget` and `ClosedDiscsBoundTarget`
(`Work.PinchLemma3.sliceWall_of_targets`, `Submission/Work/PinchLemma3/Targets.lean`).  Together with
the chain above this makes the assignment the *endpoint* of that decomposition. -/

/-- **The assignment from the fleet's three targets.** -/
theorem countingHalfEpsBody_of_targets
    (h0 : Work.PinchLemma3.TrivialSurgeryTarget)
    (h1 : Work.PinchLemma3.ClosedDiscsCoverTarget)
    (h2 : Work.PinchLemma3.ClosedDiscsBoundTarget) :
    Work.Drive.CountingHalfEpsBody :=
  countingHalfEpsBody_of_sliceWall (Work.PinchLemma3.sliceWall_of_targets h0 h1 h2)

/-- **The assignment from the trivial-surgery case and the essential-trace case.** -/
theorem countingHalfEpsBody_of_trivialSurgery_and_essential
    (h0 : Work.PinchLemma3.TrivialSurgeryTarget)
    (h1 : Work.PinchLemma3.EssentialTraceTarget) :
    Work.Drive.CountingHalfEpsBody :=
  countingHalfEpsBody_of_sliceWall
    (Work.PinchLemma3.sliceWall_of_trivialSurgery_and_essential h0 h1)


end

end Work.Drive.EpsForm
