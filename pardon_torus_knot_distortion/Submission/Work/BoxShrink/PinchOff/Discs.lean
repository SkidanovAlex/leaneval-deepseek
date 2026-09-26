import Submission.Work.BoxShrink.PinchOff.DiscPush

/-!
# Finitely many discs: the slice contained in a finite disjoint union of discs

`DiscPush.lean` proved that the local disc push-off `DiscRoute` transports every loop of the box
region into the two half-regions, when the slice is contained in one embedded disc inside the box.
This module iterates the argument over a finite family of **pairwise disjoint** discs, which is the
form in which the *circles-only* case of the assignment appears: a slice made of closed curves only
bounds a finite family of discs (one for each contractible circle of the slice), the slice is
contained in the union of their closed discs, and -- since the slice is a level set of the plane
coordinate -- those discs are pairwise disjoint (see the README).

The iteration uses the *locality* of `DiscRoute` (only points inside the disc move): after pushing a
loop off one disc, the points that moved lie inside that disc, which is disjoint from the others, so
they do not re-enter the interiors of the other discs.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The iterated disc push-off.**  For a finite family of pairwise disjoint embedded discs of the
box region, each satisfying the local push-off `DiscRoute`, every loop of the box region has a loop
of the box region with the same winding vector that avoids the interiors of all the discs. -/
theorem exists_loop_avoiding_discs :
    ∀ (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ))), L.Nodup →
      (∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier) →
      (∀ D ∈ L, DiscRoute ψ s c σ D) →
      ∀ (γ : Work.CoreTopology.ClosedCurve (surface ψ)),
        (∀ t : ℝ, γ t ∈ Omega ψ s c σ) →
        ∃ γ' : Work.CoreTopology.ClosedCurve (surface ψ),
          (∀ t : ℝ, γ' t ∈ Omega ψ s c σ) ∧
            (∀ D ∈ L, ∀ t : ℝ, γ' t ∉ D.interior) ∧
            Work.SurgeryInvariance.windingOf (surface ψ) γ'
              = Work.SurgeryInvariance.windingOf (surface ψ) γ := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ γ hγ
    exact ⟨γ, hγ, by simp, rfl⟩
  | cons D L ih =>
    intro hnodup hdisj hroute γ hγ
    rw [List.nodup_cons] at hnodup
    obtain ⟨hDnotin, hLnodup⟩ := hnodup
    have hdisj' : ∀ D' ∈ L, ∀ D'' ∈ L, D' ≠ D'' → Disjoint D'.carrier D''.carrier :=
      fun D' hD' D'' hD'' hne =>
        hdisj D' (List.mem_cons_of_mem D hD') D'' (List.mem_cons_of_mem D hD'') hne
    have hroute' : ∀ D' ∈ L, DiscRoute ψ s c σ D' :=
      fun D' hD' => hroute D' (List.mem_cons_of_mem D hD')
    obtain ⟨γ₁, hγ₁, hav, hw⟩ := ih hLnodup hdisj' hroute' γ hγ
    obtain ⟨γ₂, hγ₂, hloc, hhom⟩ := hroute D (List.mem_cons_self) γ₁ hγ₁
    refine ⟨γ₂, fun t => (hγ₂ t).1, ?_, ?_⟩
    · intro D' hD' t
      rcases List.mem_cons.mp hD' with rfl | hD'
      · exact (hγ₂ t).2
      · rcases hloc t with h | h
        · rw [h]; exact hav D' hD' t
        · intro hcon
          have hcarrier : γ₂ t ∈ D'.carrier :=
            Work.SurgeryInvariance.DiscRegion.interior_subset_carrier D' hcon
          have hne : D ≠ D' := fun heq => hDnotin (heq ▸ hD')
          have hmem' : D' ∈ D :: L := List.mem_cons_of_mem D hD'
          exact Set.disjoint_left.mp (hdisj D (List.mem_cons_self) D' hmem' hne) h hcarrier
    · rw [windingOf_eq_of_homotopic hhom, hw]

/-- **The loop transport, for a slice contained in finitely many disjoint discs.** -/
theorem regionEquivalent_of_slice_subset_discs
    (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ))) (hnodup : L.Nodup)
    (hdisj : ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier)
    (hroute : ∀ D ∈ L, DiscRoute ψ s c σ D)
    (hslice : ∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior) :
    Work.SurgeryInvariance.RegionEquivalent (surface ψ) (Halves ψ s c σ u) (Omega ψ s c σ) := by
  refine ⟨?_, ?_⟩
  · intro γ hγ
    refine ⟨γ, fun t => ?_, rfl⟩
    rcases hγ t with h | h
    · exact Work.BoxShrink.Core.upperRegion_subset (surface ψ) s c σ u h
    · exact Work.BoxShrink.Core.lowerRegion_subset (surface ψ) s c σ u h
  · intro γ hγ
    obtain ⟨γ', hγ', hav, hw⟩ := exists_loop_avoiding_discs L hnodup hdisj hroute γ hγ
    refine ⟨γ', fun t => ?_, hw⟩
    have hns : γ' t ∉ Sigma ψ s c σ u := by
      intro hs
      obtain ⟨D, hD, hmem⟩ := hslice (γ' t) hs
      exact hav D hD t hmem
    have hb : γ' t ∈ (HalfUp ψ s c σ u ∪ HalfDown ψ s c σ u) ∪ Sigma ψ s c σ u := by
      rw [← Work.BoxShrink.Core.boxRegion_eq_union]
      exact hγ' t
    rcases hb with h | h
    · exact h
    · exact absurd h hns

/-- **The strong form of the pinch-off, for a slice contained in finitely many disjoint discs.** -/
theorem strong_of_slice_subset_discs
    (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ))) (hnodup : L.Nodup)
    (hdisj : ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier)
    (hroute : ∀ D ∈ L, DiscRoute ψ s c σ D)
    (hslice : ∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)
      = Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
  (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq
    (regionEquivalent_of_slice_subset_discs (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u)
      L hnodup hdisj hroute hslice)).symm

/-- **Pardon's Lemma 3 conclusion, for a slice contained in finitely many disjoint discs.**  This is
the case of the assignment's named partial target (a slice made of circles only, the discs bounded by
those circles lying in the box), reduced to one instance of the local model `DiscRoute` per circle. -/
theorem bubbleHalf_of_slice_subset_discs
    (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ))) (hnodup : L.Nodup)
    (hdisj : ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier)
    (hroute : ∀ D ∈ L, DiscRoute ψ s c σ D)
    (hslice : ∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_strong
    (strong_of_slice_subset_discs (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u)
      L hnodup hdisj hroute hslice)

end

end Work.BoxShrink.PinchOff
