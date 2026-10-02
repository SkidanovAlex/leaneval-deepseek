import Mathlib
import Submission.Work.RatHurewicz.Triad.Helpers

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `0`-cell base of the preparation theorem

A `0`-cell of the grid is a single point `z`, and the cell homotopy needed to treat it is a path
from the current value `g z` to a point of `B ∩ C`, lying in `B` if `g z ∈ B` and in `C` if
`g z ∈ C` (that is the label of the cell), and staying in `P = pathComponent x₀` throughout (so that
the `P`-invariant of the induction is preserved).

That path is supplied by the hypotheses `hB0`/`hC0` of the target: they join points of `B ∩ C` to
points of `B` (resp. `C`) inside `B` (resp. `C`); one runs the path backwards. The disjunctive
conclusion below is exactly the form in which the induction consumes it (the label of the cell
decides the branch).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

theorem zeroCellPath {X : Type} [TopologicalSpace X] {B C : Set X} (x₀ : ↥(B ∩ C))
    (hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b))
    (hC0 : ∀ c : ↥C, (c : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ c))
    {z : X} (hz : z ∈ pathComponent (x₀ : X)) (hv : z ∈ B ∨ z ∈ C) :
    ∃ p : C(I, X), p 0 = z ∧ p 1 ∈ B ∩ C ∧ (∀ t, p t ∈ pathComponent (x₀ : X)) ∧
      ((z ∈ B ∧ ∀ t, p t ∈ B) ∨ (z ∈ C ∧ ∀ t, p t ∈ C)) := by
  -- the common form of the argument: a path inside `S` from a point of `S` to `B ∩ C`
  have key : ∀ (S : Set X) (ha_of : ∀ a : ↥(B ∩ C), (a : X) ∈ S)
      (hS : ∀ b : ↥S, (b : X) ∈ pathComponent (x₀ : X) →
        ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, ha_of a⟩ b))
      (z : X) (hzS : z ∈ S) (hzP : z ∈ pathComponent (x₀ : X)),
      ∃ p : C(I, X), p 0 = z ∧ p 1 ∈ B ∩ C ∧ (∀ t, p t ∈ pathComponent (x₀ : X)) ∧
        ∀ t, p t ∈ S := by
    intro S ha_of hS z hzS hzP
    obtain ⟨a, ⟨γ⟩⟩ := hS ⟨z, hzS⟩ hzP
    have hp0 : ((setIncl S).comp (γ.symm : C(I, ↥S))) 0 = z :=
      congrArg Subtype.val (Path.source γ.symm)
    have hp1 : ((setIncl S).comp (γ.symm : C(I, ↥S))) 1 = (a : X) :=
      congrArg Subtype.val (Path.target γ.symm)
    refine ⟨(setIncl S).comp (γ.symm : C(I, ↥S)), hp0, ?_, ?_, ?_⟩
    · rw [hp1]
      exact ⟨a.2.1, a.2.2⟩
    · -- everything stays in `P`
      intro t
      have hpc : IsPathConnected
          (Set.range ((setIncl S).comp (γ.symm : C(I, ↥S)) : C(I, X))) :=
        isPathConnected_range (ContinuousMap.continuous _)
      have hmem : ((setIncl S).comp (γ.symm : C(I, ↥S)) : C(I, X)) t ∈
          Set.range ((setIncl S).comp (γ.symm : C(I, ↥S)) : C(I, X)) := ⟨t, rfl⟩
      have h2 : ((setIncl S).comp (γ.symm : C(I, ↥S)) : C(I, X)) t ∈ pathComponent z :=
        hpc.subset_pathComponent ⟨0, hp0⟩ hmem
      simpa [pathComponent_congr hzP] using h2
    · -- everything stays in `S`
      intro t
      exact (γ.symm t).2
  rcases hv with hzB | hzC
  · obtain ⟨p, h0, h1, hP, hS⟩ := key B (fun a => a.2.1) (fun b => hB0 b) z hzB hz
    exact ⟨p, h0, h1, hP, Or.inl ⟨hzB, hS⟩⟩
  · obtain ⟨p, h0, h1, hP, hS⟩ := key C (fun a => a.2.2) (fun c => hC0 c) z hzC hz
    exact ⟨p, h0, h1, hP, Or.inr ⟨hzC, hS⟩⟩

end

end Work.RatHurewicz
