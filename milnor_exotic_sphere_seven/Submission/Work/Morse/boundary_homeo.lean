import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The boundary of a two-ball decomposition carries a canonical homeomorphism

This file formalises the topological heart of the "two closed `n`-balls glued along their common
boundary form `Sⁿ`" argument (see `Work.Morse.two_balls`).

Suppose a space `X` is written as the union of two sets `A`, `B`, each homeomorphic to the closed
unit ball `Dⁿ ⊆ ℝⁿ` via homeomorphisms `α`, `β`.  Assume the two pieces meet exactly along the
unit sphere, i.e. a point of `A` lies in `B` iff its `α`-coordinate is on the unit sphere, and
symmetrically for `β`.  Then the common boundary `A ∩ B` is parametrised by the sphere in two
ways, and comparing the two parametrisations produces a self-homeomorphism `γ` of `Sⁿ⁻¹`.

The main result is `Work.Morse.boundary_homeo` below.
-/

open scoped Manifold ContDiff Topology
open Metric

namespace Work.Morse

/-- The part of the closed unit ball `Dⁿ` that lies on the unit sphere is homeomorphic, by the
inclusion, to the unit sphere `Sⁿ⁻¹`.  (As a subtype of `Dⁿ` the two points-of-view differ only
by the ambient space, so this is the identity on the underlying point.) -/
noncomputable def closedBallSphereHomeo (n : ℕ) :
    ({y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 |
        (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere 0 1} : Set _) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 where
  toFun y := ⟨(y.1 : EuclideanSpace ℝ (Fin n)), y.2⟩
  invFun z := ⟨⟨(z : EuclideanSpace ℝ (Fin n)),
      Metric.sphere_subset_closedBall z.2⟩, z.2⟩
  left_inv y := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- The boundary of the two-ball decomposition carries a canonical homeomorphism: mapping a
point of the common boundary of `A` and `B` to its `α`-coordinate (`s`) and then via `β`, and
conversely, sets up a homeomorphism `Sⁿ⁻¹ ≃ₜ Sⁿ⁻¹`, and `β` is `γ` applied to the `α`-coordinate
on the common boundary. -/
theorem boundary_homeo {n : ℕ} {X : Type*} [TopologicalSpace X]
    {A B : Set X}
    {α : A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1}
    {β : B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1}
    (hα : ∀ x : A, (x : X) ∈ B ↔ α x ∈ Metric.sphere 0 1)
    (hβ : ∀ x : B, (x : X) ∈ A ↔ β x ∈ Metric.sphere 0 1) :
    ∃ γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ (x : A) (hx : (x : X) ∈ B),
        (γ ⟨α x, (hα x).mp hx⟩ : EuclideanSpace ℝ (Fin n))
          = (β ⟨(x : X), hx⟩ : EuclideanSpace ℝ (Fin n)) := by
  -- `S` is the unit sphere of `ℝⁿ`; `SD` is the copy of it inside the closed unit ball `D`.
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let SD : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {y | (y : EuclideanSpace ℝ (Fin n)) ∈ S}
  -- The boundary of `A`: the points of `A` lying in `B`.
  let TA := {x : A // (x : X) ∈ B}
  -- The boundary of `B`: the points of `B` lying in `A`.
  let TB := {y : B // (y : X) ∈ A}
  -- The identification of the two copies of the common boundary, through `X`.
  let iAB : TA ≃ₜ TB := {
    toFun := fun x => ⟨⟨(x.1 : X), x.2⟩, x.1.2⟩
    invFun := fun y => ⟨⟨(y.1 : X), y.2⟩, y.1.2⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro y; apply Subtype.ext; apply Subtype.ext; rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
  }
  -- The `α`-coordinate identifies the boundary of `A` with the unit sphere.
  have hA_iff : ∀ x : A, ((x : X) ∈ B) ↔ x ∈ α ⁻¹' SD := by
    intro x; rw [Set.mem_preimage]; exact hα x
  let eα : TA ≃ₜ S := (Homeomorph.sets α (Set.ext hA_iff)).trans
    (closedBallSphereHomeo n)
  -- The `β`-coordinate identifies the boundary of `B` with the unit sphere.
  have hB_iff : ∀ y : B, ((y : X) ∈ A) ↔ y ∈ β ⁻¹' SD := by
    intro y; rw [Set.mem_preimage]; exact hβ y
  let eβ : TB ≃ₜ S := (Homeomorph.sets β (Set.ext hB_iff)).trans
    (closedBallSphereHomeo n)
  refine ⟨eα.symm.trans (iAB.trans eβ), ?_⟩
  intro x hx
  -- `γ (α x) = β (iAB (the point of the boundary with the same underlying point))`.
  have harg : (⟨α x, (hα x).mp hx⟩ : S) = eα ⟨x, hx⟩ := Subtype.ext rfl
  rw [harg, Homeomorph.trans_apply, Homeomorph.trans_apply, eα.symm_apply_apply]
  show ((eβ (iAB ⟨x, hx⟩)) : EuclideanSpace ℝ (Fin n))
      = (β ⟨(x : X), hx⟩ : EuclideanSpace ℝ (Fin n))
  have hi : iAB ⟨x, hx⟩ = (⟨⟨(x : X), hx⟩, x.2⟩ : TB) := rfl
  rw [hi]
  rfl

end Work.Morse
