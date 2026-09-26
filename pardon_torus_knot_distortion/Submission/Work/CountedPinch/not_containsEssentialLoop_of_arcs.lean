import Mathlib
import Submission.Work.Smooth.Plane.All
import Submission.Work.InnermostDisk.All

/-!
# A region covered by finitely many disjoint embedded arcs of the surface contains no
essential loop

`Work.CountedPinch.not_containsEssentialLoop_of_arcs`: if the intersection `D ∩ F` of a set `D ⊆ ℝ³`
with the surface `F = P.carrier` of a parametrised torus is covered by finitely many pairwise
disjoint embedded arcs of `F` (`a : Fin n → C(ArcInterval, ℝ³)` injective, with image in `F`), then
`D` contains no essential loop of `F`.

The proof is the elementary one: the image of a closed curve `γ` of `F` is the continuous image of
the (preconnected) line `ℝ`, hence preconnected; it is covered by the pairwise disjoint closed sets
`range (a j)`, and a preconnected set cannot meet two disjoint closed sets that cover it.  So the
whole range of `γ` lands in a single arc `range (a j0)`, and
`Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc` finishes.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CountedPinch

noncomputable section

/-- **A loop of the torus lying in a finite union of pairwise disjoint embedded arcs of the surface
is inessential.**  Equivalently: a set `D` whose trace on the surface is covered by finitely many
pairwise disjoint embedded arcs of the surface contains no essential loop. -/
theorem not_containsEssentialLoop_of_arcs {P : Work.CoreTopology.ParamTorus}
    {D : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {n : ℕ} (a : Fin n → C(Work.Smooth.Plane.ArcInterval, LeanEval.KnotTheory.PardonDistortion.R3))
    (hinj : ∀ j : Fin n, Function.Injective (a j))
    (hmem : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ P.carrier)
    (hdisj : Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j')))
    (hcov : ∀ x : LeanEval.KnotTheory.PardonDistortion.R3, x ∈ D → x ∈ P.carrier →
      ∃ j : Fin n, x ∈ Set.range (a j)) :
    ¬ P.ContainsEssentialLoop D := by
  rintro ⟨γ, hess, hγD⟩
  -- Every point of `γ` lies on the surface and in `D`, hence in some arc.
  have hcovS : ∀ t : ℝ, ∃ j : Fin n, γ.γ t ∈ Set.range (a j) :=
    fun t => hcov (γ.γ t) (hγD t) (γ.mem t)
  -- The arc meeting `γ 0`; its image is one of the two closed sets below.
  obtain ⟨j0, hj0⟩ := hcovS 0
  -- The image of an arc is compact, hence closed.
  have hclosed : ∀ j : Fin n, IsClosed (Set.range (a j)) :=
    fun j => (isCompact_range (a j).continuous).isClosed
  -- The union of the remaining arcs.
  set t' : Set LeanEval.KnotTheory.PardonDistortion.R3 :=
    ⋃ j : {j : Fin n // j ≠ j0}, Set.range (a (j : Fin n)) with ht'def
  have ht' : IsClosed t' := by
    rw [ht'def]
    exact isClosed_iUnion_of_finite fun j => hclosed _
  -- The image of `γ` is covered by the arc of `j0` and the remaining arcs.
  have hsub : Set.range γ.γ ⊆ Set.range (a j0) ∪ t' := by
    rintro y ⟨t0, rfl⟩
    obtain ⟨j, hj⟩ := hcovS t0
    by_cases h : j = j0
    · exact Or.inl (h ▸ hj)
    · exact Or.inr (mem_iUnion.2 ⟨⟨j, h⟩, hj⟩)
  -- `γ 0` lies in the arc of `j0`
  have hne : (Set.range γ.γ ∩ Set.range (a j0)).Nonempty :=
    ⟨γ.γ 0, ⟨⟨0, rfl⟩, hj0⟩⟩
  -- ... and the two closed sets are disjoint on `range γ.γ` (the arcs are pairwise disjoint).
  have hdisj' : Set.range γ.γ ∩ (Set.range (a j0) ∩ t') = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨-, hx1, hx2⟩ := hx
    rw [ht'def] at hx2
    obtain ⟨j, hxj⟩ := mem_iUnion.1 hx2
    exact (Set.disjoint_left.1
      (hdisj (i := j0) (j := (j : Fin n)) (fun hh => j.2 hh.symm))) hx1 hxj
  have hconn : IsPreconnected (Set.range γ.γ) := isPreconnected_range γ.cont
  -- A preconnected set covered by two disjoint closed sets lies in one of them.
  have hsub2 : Set.range γ.γ ⊆ Set.range (a j0) := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hconn (Set.range (a j0)) t'
      (hclosed j0) ht' hsub hdisj') with h | h
    · exact h
    · exfalso
      have : γ.γ 0 ∈ t' := h ⟨0, rfl⟩
      rw [ht'def] at this
      obtain ⟨j, hj⟩ := mem_iUnion.1 this
      exact (Set.disjoint_left.1
        (hdisj (i := j0) (j := (j : Fin n)) (fun hh => j.2 hh.symm))) hj0 hj
  -- The whole loop lies in the single arc `a j0`, so it is inessential.
  exact (Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc (hinj j0) (hmem j0)
    (fun t => hsub2 ⟨t, rfl⟩)) hess

end

end Work.CountedPinch
