import Mathlib
import Submission.SecantModel
import Submission.OpenMobiusHomotopy
import Submission.Pi1Mobius
import Submission.Commons.AlgebraicTopology.FundamentalGroup.pi1_circle_eq_int
import Submission.Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv

open ContinuousMap
open scoped Multiplicative

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# Layer C assembly: π₁(OpenMobius) ≅ ℤ

**Target of this layer.**  The fundamental group of the open Möbius band of
knot secants is the infinite cyclic group.  All four spans are in place:

  1. `openMobiusModelHomeo : OpenMobius ≃ₜ MobiusModel`
     (`Submission/SecantModel.lean`);
  2. the deformation retraction `openMobiusCoreRetract` onto the core circle
     (`Submission/SecantModel.lean`);
  3. the homotopy equivalence
     `openMobius_homotopyEquiv_core : Nonempty (OpenMobius ≃ₕ
     {c : OpenMobius // c ∈ Set.range coreFactor})`
     (`Submission/OpenMobiusHomotopy.lean`);
  4. `coreRangeCircle : Set.range coreFactor ≃ₜ Circle`
     (and `coreFactor_homeo : AddCircle halfPeriod ≃ₜ Set.range coreFactor`,
     `coreCircleHomeo : AddCircle halfPeriod ≃ₜ Circle`,
     `Submission/Pi1Mobius.lean`);
  5. `Commons.AlgebraicTopology.FundamentalGroup.pi1_circle_eq_int`:
     `π₁(Circle, 1) ≅ ℤ` (fleet commons lemma).

The generic glue (missing from Mathlib, delegated to the commons fleet as
`Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv`) is
that **π₁ respects homotopy equivalences**: a homotopy equivalence
`e : X ≃ₕ Y` induces a group isomorphism
`FundamentalGroup X x ≃* FundamentalGroup Y (e.toFun x)`.  (Homeomorphisms
are homotopy equivalences through Mathlib's `Homeomorph.toHomotopyEquiv`, so
the same lemma also glues the `coreRangeCircle` step.)

The chain, at the basepoint
`b = coreFactor (coreCircleHomeo.symm 1) : OpenMobius` (the parameter whose
circle image is `1`):

    π₁(OpenMobius, b)                        -- homotopy-equivalence lemma on
      ≃ π₁(range coreFactor, e.toFun b)      --   openMobius_homotopyEquiv_core
      ≃ π₁(Circle, coreRangeCircle (e.toFun b)) -- homeo-as-homotopy-equivalence
      = π₁(Circle, 1)                        --   basepoint computation (b is a core
                                             --   point, so the retraction fixes it,
                                             --   and `coreRangeCircle` of it is 1)
      ≅ ℤ                                    --   pi1_circle_eq_int

(`OpenMobius` is path connected through this very chain, so the choice of
basepoint is immaterial; a path-connectedness certificate can replace the
basepoint bookkeeping if that turns out cleaner.)
-/

/-- The basepoint of `OpenMobius` whose core-circle image is `1 : Circle`:
the antipodal pair at the parameter `coreCircleHomeo.symm 1`. -/
noncomputable def pi1BaseParam : AddCircle halfPeriod :=
  coreCircleHomeo.symm (1 : Circle)

/-- The corresponding basepoint of the open Möbius band. -/
noncomputable def pi1Base : OpenMobius := coreFactor pi1BaseParam

/-- The basepoint lies on the core circle. -/
lemma pi1Base_mem_core : pi1Base ∈ Set.range coreFactor := by
  exact ⟨pi1BaseParam, rfl⟩

/-- The core-circle homeomorphism computes on core points: `a ↦
`⟨coreFactor a, ⟨a, rfl⟩⟩`; written plainly: `coreFactor_homeo a =
⟨coreFactor a, ⟨a, rfl⟩⟩`. -/
lemma coreFactor_homeo_apply (a : AddCircle halfPeriod) :
    coreFactor_homeo a = ⟨coreFactor a, ⟨a, rfl⟩⟩ := by
  unfold coreFactor_homeo
  rfl

/-- The inverse of the core-circle homeomorphism on a core point is the
parameter. -/
lemma coreFactor_homeo_symm_mk (a : AddCircle halfPeriod) :
    coreFactor_homeo.symm ⟨coreFactor a, ⟨a, rfl⟩⟩ = a := by
  apply coreFactor_homeo.injective
  rw [coreFactor_homeo.apply_symm_apply]
  unfold coreFactor_homeo
  rfl

/-- The core image of the basepoint is `1 : Circle`. -/
lemma coreRangeCircle_pi1Base :
    coreRangeCircle ⟨pi1Base, pi1Base_mem_core⟩ = (1 : Circle) := by
  unfold coreRangeCircle
  rw [Homeomorph.trans_apply]
  change coreCircleHomeo (coreFactor_homeo.symm
    ⟨coreFactor pi1BaseParam, ⟨pi1BaseParam, rfl⟩⟩) = (1 : Circle)
  rw [coreFactor_homeo_symm_mk pi1BaseParam]
  simp [pi1BaseParam]

/-- **Target statement of this layer**: `π₁(OpenMobius) ≅ ℤ` (at the
basepoint `pi1Base`, whose core image is `1 : Circle`). -/
def Pi1OpenMobiusEqInt : Prop :=
  Nonempty (FundamentalGroup OpenMobius pi1Base ≃* Multiplicative ℤ)

/-- The core circle of the open Möbius band is path connected (it is the
image of the circle of half-period parameters under the homeomorphism
`coreFactor_homeo`). -/
instance coreRangePathConnected : PathConnectedSpace (Set.range coreFactor) :=
  coreFactor_homeo.surjective.pathConnectedSpace coreFactor_homeo.continuous

/-- **`π₁(OpenMobius) ≅ ℤ`**: the fundamental group of the open Möbius band
of knot secants is the infinite cyclic group.

Chain (at the core basepoint `pi1Base`, whose `coreRangeCircle` image is
`1 : Circle`):

* `φ1` — `π₁(OpenMobius, b) ≃ π₁(core, he.toFun b)` along the homotopy
  equivalence `openMobius_homotopyEquiv_core` (commons
  `pi1_equiv_of_homotopyEquiv`);
* `ψ1` — path-connected basepoint transport inside the core circle to
  `⟨b, mem⟩`;
* `φ2` — `π₁(core, ⟨b, mem⟩) ≃ π₁(Circle, coreRangeCircle ⟨b, mem⟩)`
  along the homeomorphism `coreRangeCircle` (a homotopy equivalence via
  `Homeomorph.toHomotopyEquiv`, whose `toFun` is the homeo map by `rfl`);
* `ψ2` — path-connected basepoint transport inside `Circle` to `1`;
* `γ` — the fleet commons lemma `pi1_circle_eq_int`. -/
lemma pi1_openMobius_eq_int : Pi1OpenMobiusEqInt := by
  rcases openMobius_homotopyEquiv_core with ⟨he⟩
  rcases Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv he pi1Base with ⟨φ1⟩
  let ψ1 : FundamentalGroup (Set.range coreFactor) (he.toFun pi1Base) ≃*
      FundamentalGroup (Set.range coreFactor) ⟨pi1Base, pi1Base_mem_core⟩ :=
    FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (X := (Set.range coreFactor))
      (x₀ := he.toFun pi1Base) (x₁ := ⟨pi1Base, pi1Base_mem_core⟩)
  rcases Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv
      (Homeomorph.toHomotopyEquiv coreRangeCircle) ⟨pi1Base, pi1Base_mem_core⟩ with ⟨φ2⟩
  let ψ2 : FundamentalGroup Circle (coreRangeCircle ⟨pi1Base, pi1Base_mem_core⟩) ≃*
      FundamentalGroup Circle (1 : Circle) :=
    FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (X := Circle)
      (x₀ := coreRangeCircle ⟨pi1Base, pi1Base_mem_core⟩) (x₁ := (1 : Circle))
  rcases Commons.AlgebraicTopology.FundamentalGroup.pi1_circle_eq_int with ⟨γ⟩
  exact ⟨(φ1.trans ψ1).trans ((φ2.trans ψ2).trans γ)⟩

end LeanEval.KnotTheory.Quadrisecant
