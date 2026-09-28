import Mathlib
import Submission.Work.RatHurewicz.cycleModelDefs

/-!
# The model is path connected

Every point of `Model D` is joined by a path to the base point `modelBase D`: a point of a copy of
`Δ^{n+2}` is joined to the vertex `0` of that copy inside the (convex, hence path connected)
simplex, the vertex `0` is identified with the end point `0` of the arc of that copy, and all the
arcs have the same end point `1`.  Consequently `π₀` of the model is trivial.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- Two points of `Model D` that are equal are joined by a path. -/
theorem joined_of_eq {Y : Type} [TopologicalSpace Y] {a b : Y} (h : a = b) : Joined a b :=
  ⟨Path.cast (Path.refl b) h rfl⟩

/-- A point of a copy of `Δ^{n+2}` is joined to the vertex `0` of that copy. -/
theorem joined_vertex_zero (D : MData X n x₀) (i : D.Idx) (x : stdSimplex ℝ (Fin (n + 2))) :
    Joined (Quotient.mk'' (Sum.inl ⟨i, x⟩ : Raw D) : Model D)
      (Quotient.mk'' (Sum.inl ⟨i, stdSimplex.vertex (0 : Fin (n + 2))⟩ : Raw D) : Model D) := by
  have hj : Joined x (stdSimplex.vertex (0 : Fin (n + 2))) :=
    PathConnectedSpace.joined x (stdSimplex.vertex (0 : Fin (n + 2)))
  exact hj.map (topMap D i).continuous

/-- Every point of the unit interval is joined to `1`. -/
theorem joined_unitInterval_one (s : unitInterval) : Joined s (1 : unitInterval) := by
  have hs : (0 : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ 1 := s.2
  refine ⟨⟨⟨fun t => ⟨(1 - (t : ℝ)) * (s : ℝ) + (t : ℝ), ?_⟩, ?_⟩, ?_, ?_⟩⟩
  · exact ⟨by nlinarith [t.2.1, hs.1], by nlinarith [t.2.2, hs.2]⟩
  · exact Continuous.subtype_mk (by fun_prop) _
  · exact Subtype.ext (by simp)
  · exact Subtype.ext (by simp)

/-- A point of an arc is joined to the end point `1` of that arc. -/
theorem joined_arc_one (D : MData X n x₀) (i : D.Idx) (s : unitInterval) :
    Joined (Quotient.mk'' (Sum.inr ⟨i, s⟩ : Raw D) : Model D)
      (Quotient.mk'' (Sum.inr ⟨i, (1 : unitInterval)⟩ : Raw D) : Model D) :=
  (joined_unitInterval_one s).map (arcMap D i).continuous

/-- Every point of the model is joined to the base point. -/
theorem joined_modelBase (D : MData X n x₀) [Nonempty D.Idx] (y : Model D) :
    Joined y (modelBase D) := by
  have h4 : ∀ i : D.Idx,
      Joined (Quotient.mk'' (Sum.inr ⟨i, (1 : unitInterval)⟩ : Raw D) : Model D)
        (modelBase D) := fun i =>
    joined_of_eq (Quotient.sound (Relation.EqvGen.rel _ _
      (Or.inr (Or.inr ⟨i, Classical.choice ‹Nonempty D.Idx›, rfl, rfl⟩))))
  induction y using Quotient.inductionOn with
  | h r =>
    rcases r with ⟨i, x⟩ | ⟨i, s⟩
    · have h2 : Joined
          (Quotient.mk'' (Sum.inl ⟨i, stdSimplex.vertex (0 : Fin (n + 2))⟩ : Raw D) : Model D)
          (Quotient.mk'' (Sum.inr ⟨i, (0 : unitInterval)⟩ : Raw D) : Model D) :=
        joined_of_eq (Quotient.sound (Relation.EqvGen.rel _ _
          (Or.inr (Or.inl ⟨i, rfl, rfl⟩))))
      have h3 : Joined (Quotient.mk'' (Sum.inr ⟨i, (0 : unitInterval)⟩ : Raw D) : Model D)
          (Quotient.mk'' (Sum.inr ⟨i, (1 : unitInterval)⟩ : Raw D) : Model D) :=
        (joined_unitInterval_one 0).map (arcMap D i).continuous
      exact ((joined_vertex_zero D i x).trans h2).trans (h3.trans (h4 i))
    · exact (joined_arc_one D i s).trans (h4 i)

/-- **`π₀` of the model is trivial.** -/
theorem subsingleton_pi0_model (D : MData X n x₀) [Nonempty D.Idx] :
    Subsingleton (HomotopyGroup (Fin 0) (Model D) (modelBase D)) := by
  have hz : Subsingleton (ZerothHomotopy (Model D)) := by
    refine ⟨fun a b => ?_⟩
    induction a using ZerothHomotopy.rec with
    | mk x =>
      induction b using ZerothHomotopy.rec with
      | mk y =>
        exact ZerothHomotopy.sound (Joined.somePath
          ((joined_modelBase D x).trans (joined_modelBase D y).symm))
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := Model D)
    (x := modelBase D)).injective (Subsingleton.elim _ _)⟩

end

end Work.RatHurewicz
