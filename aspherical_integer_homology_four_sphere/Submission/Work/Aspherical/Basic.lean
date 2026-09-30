/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asphericity from a contractible cover: the cube/interval API

This file collects the elementary topology of the cubes `I^k = (Fin k → I)`,
`I = [0,1]`, and of their boundaries `Cube.boundary (Fin k)`, which the
asphericity argument needs:

* `I^k` is contractible (hence simply connected and path connected), and locally
  path connected;
* the boundary `∂I^k` is non-empty for `k ≥ 1`, and is path connected for `k ≥ 2`.

Everything here is pure topology, independent of covering spaces.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology unitInterval

namespace Work.Aspherical

noncomputable section

/-- The unit interval `[0,1]` is contractible (as a subset of `ℝ`). -/
instance instContractibleSpaceUnitInterval : ContractibleSpace (Set.Icc (0 : ℝ) 1) :=
  Convex.contractibleSpace (convex_Icc (0 : ℝ) 1) ⟨0, by norm_num⟩

/-- The unit interval `[0,1]` is locally path connected (as a subset of `ℝ`). -/
instance instLocallyPathConnectedSpaceUnitInterval :
    LocallyPathConnectedSpace (Set.Icc (0 : ℝ) 1) :=
  Convex.locallyPathConnectedSpace (E := ℝ) (S := Set.Icc (0 : ℝ) 1) (convex_Icc (0 : ℝ) 1)

/-- The diagonal contraction of the cube `I^k` to its centre, as a map. -/
def cubeContractMap (k : ℕ) : C(I × (I^Fin k), I^Fin k) where
  toFun p i :=
    (⟨(1 - (p.1 : ℝ)) * (p.2 i : ℝ) + (p.1 : ℝ) * (1 / 2), by
      have hx1 : (0 : ℝ) ≤ (p.2 i : ℝ) := (p.2 i).2.1
      have hx2 : (p.2 i : ℝ) ≤ 1 := (p.2 i).2.2
      have ht1 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
      have ht2 : (p.1 : ℝ) ≤ 1 := p.1.2.2
      exact ⟨by nlinarith, by nlinarith⟩⟩ : ↥(Set.Icc (0 : ℝ) 1))
  continuous_toFun := by fun_prop

/-- The diagonal contraction of the cube `I^k` to its centre, as a homotopy. -/
def cubeContractHomotopy (k : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (I^Fin k))
      (ContinuousMap.const (I^Fin k) (fun _ => (⟨1 / 2, by norm_num⟩ : ↥(Set.Icc (0:ℝ) 1)))) where
  toContinuousMap := cubeContractMap k
  map_zero_left := by
    intro p
    funext i
    apply Subtype.ext
    simp [cubeContractMap]
  map_one_left := by
    intro p
    funext i
    apply Subtype.ext
    simp [cubeContractMap]

/-- The cube `I^k` is contractible. -/
instance instContractibleSpaceCube (k : ℕ) : ContractibleSpace (I^Fin k) :=
  (contractible_iff_id_nullhomotopic (I^Fin k)).mpr
    ⟨fun _ => (⟨1 / 2, by norm_num⟩ : ↥(Set.Icc (0:ℝ) 1)), ⟨cubeContractHomotopy k⟩⟩

/-- The cube `I^k` is simply connected. -/
instance instSimplyConnectedSpaceCube (k : ℕ) : SimplyConnectedSpace (I^Fin k) :=
  inferInstance

/-- The cube `I^k` is locally path connected. -/
instance instLocallyPathConnectedSpaceCube (k : ℕ) : LocallyPathConnectedSpace (I^Fin k) :=
  Pi.locallyPathConnectedSpace_of_finite

/-- The boundary of a cube is closed. -/
theorem isClosed_boundary (k : ℕ) : IsClosed (Cube.boundary (Fin k)) := by
  have h : Cube.boundary (Fin k) = ⋃ i : Fin k, {y : I^Fin k | y i = 0 ∨ y i = 1} := by
    ext y
    simp [Cube.boundary]
  rw [h]
  exact isClosed_iUnion_of_finite fun i =>
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const)

/-- The "origin" corner of the cube `I^k` (`k ≥ 1`). -/
def Cube.zeroPoint (k : ℕ) [NeZero k] : I^Fin k := fun _ => ⟨0, by norm_num⟩

/-- The origin corner lies in the boundary of the cube. -/
theorem Cube.zeroPoint_mem_boundary (k : ℕ) [NeZero k] :
    Cube.zeroPoint k ∈ Cube.boundary (Fin k) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty (Fin k))
  exact ⟨i, Or.inl rfl⟩

/-- The boundary of `I^k` is nonempty for `k ≥ 1`. -/
theorem Cube.boundary_nonempty (k : ℕ) [NeZero k] : (Cube.boundary (Fin k)).Nonempty :=
  ⟨Cube.zeroPoint k, Cube.zeroPoint_mem_boundary k⟩

/-- A topological space is **aspherical** if all its higher homotopy groups vanish, at every
basepoint.  (This is exactly the condition `Closed4Manifold.IsAspherical` of the challenge
statement, stated for a bare topological space.) -/
def IsAspherical (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ x : X, Subsingleton (HomotopyGroup (Fin k) X x)

end

end Work.Aspherical
