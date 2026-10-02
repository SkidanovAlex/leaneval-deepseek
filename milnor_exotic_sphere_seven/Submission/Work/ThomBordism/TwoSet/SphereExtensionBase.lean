import Mathlib
import Submission.Work.ThomBordism.TwoSet.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The base case of the sphere extension theorem

`SphereExtensionBase`: for `m = 1` a map `∂I¹ = {0,1} → Y` extends over `I¹` as soon as `π₀(Y)` is
trivial (i.e. `Y` is path connected).  This is the base case of the induction proving
`Work.ThomBordism.TwoSet.SphereExtension`.
-/

namespace Work.ThomBordism.TwoSet

open scoped Topology unitInterval

/-- The `m = 1` base case: `∂I^1 = {0,1}` and `Y` path connected. -/
theorem SphereExtensionBase {Y : Type*} [TopologicalSpace Y]
    (hconn : ∀ y : Y, Subsingleton (HomotopyGroup (Fin 0) Y y))
    (Φ : C({x : (Fin 1 → unitInterval) // x ∈ Cube.boundary (Fin 1)}, Y)) :
    ∃ Ψ : C(Fin 1 → unitInterval, Y),
      Ψ.comp ⟨Subtype.val, continuous_subtype_val⟩ = Φ := by
  classical
  have hpc : PathConnectedSpace Y := by
    rw [pathConnectedSpace_iff_zerothHomotopy]
    refine ⟨⟨Quotient.mk _ (Φ ⟨fun _ => 0, ⟨0, Or.inl rfl⟩⟩)⟩, ?_⟩
    exact (HomotopyGroup.pi0EquivZerothHomotopy
      (x := Φ ⟨fun _ => 0, ⟨0, Or.inl rfl⟩⟩)).surjective.subsingleton
  haveI := hpc
  obtain ⟨γ⟩ := (PathConnectedSpace.joined (Φ ⟨fun _ => 0, ⟨0, Or.inl rfl⟩⟩)
      (Φ ⟨fun _ => 1, ⟨0, Or.inr rfl⟩⟩) : Joined _ _)
  refine ⟨⟨fun x => γ (x 0), γ.continuous.comp (continuous_apply 0)⟩, ?_⟩
  apply ContinuousMap.ext
  intro y
  obtain ⟨i, hi⟩ := y.2
  rcases hi with h | h
  · have hy : (y : Fin 1 → unitInterval) = fun _ => (0 : unitInterval) := by
      funext j; rw [Subsingleton.elim j i]; simpa using h
    have hy' : y = ⟨fun _ => (0 : unitInterval), by refine ⟨0, Or.inl rfl⟩⟩ := Subtype.ext hy
    show γ ((y : Fin 1 → unitInterval) 0) = Φ y
    rw [hy']
    simpa using γ.source
  · have hy : (y : Fin 1 → unitInterval) = fun _ => (1 : unitInterval) := by
      funext j; rw [Subsingleton.elim j i]; simpa using h
    have hy' : y = ⟨fun _ => (1 : unitInterval), by refine ⟨0, Or.inr rfl⟩⟩ := Subtype.ext hy
    show γ ((y : Fin 1 → unitInterval) 0) = Φ y
    rw [hy']
    simpa using γ.target

end Work.ThomBordism.TwoSet
