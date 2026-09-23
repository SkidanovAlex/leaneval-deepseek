import Mathlib
import Submission.Work.Final.DimOne.Defs

namespace Work.Final.DimOne

open scoped Manifold ContDiff Bundle Topology ENNReal
open LeanEval.Geometry.SphereTheorem
open CovariantDerivative
open Submission.GlobalExp

set_option linter.style.haveILetI false

/-- For `P > 0` the quotient map `ℝ → AddCircle P` is a covering map whose deck transformation
group is `ℤ • P`; by the theory of covering spaces the fundamental group of `AddCircle P` is
therefore that (non-trivial) group.  Since a simply connected space has trivial fundamental
group, `AddCircle P` is not simply connected.

This is the topological input excluding the one-dimensional case in the sphere theorem: a
compact one-dimensional manifold which is a geodesic circle `AddCircle P` cannot be simply
connected. -/
theorem not_simplyConnectedSpace_addCircle {P : ℝ} (hP : 0 < P) :
    ¬ SimplyConnectedSpace (AddCircle P) := by
  intro hsc
  -- `zmultiples P` is discrete for `P ≠ 0`, so `ℝ → AddCircle P` is a quotient covering map
  haveI : DiscreteTopology (AddSubgroup.zmultiples P) := by infer_instance
  haveI := hsc
  have hcov := AddCircle.isAddQuotientCoveringMap_coe (𝕜 := ℝ) P
  -- the fundamental group of the base is the opposite of the deck group `ℤ • P`
  have e : FundamentalGroup (AddCircle P) 0 ≃*
      (Multiplicative (AddSubgroup.zmultiples P))ᵐᵒᵖ :=
    hcov.fundamentalGroupEquiv (x := (0 : AddCircle P)) ⟨(0 : ℝ), by simp⟩
  -- a simply connected space has trivial fundamental group, so the deck group is trivial
  have htriv : ∀ u v : (Multiplicative (AddSubgroup.zmultiples P))ᵐᵒᵖ, u = v := fun u v => by
    have h : e.symm u = e.symm v := Subsingleton.elim _ _
    simpa using congrArg e h
  -- yet `0 ≠ P` in `ℤ • P`
  have hmem : P ∈ AddSubgroup.zmultiples P := AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩
  have hzero : (⟨P, hmem⟩ : AddSubgroup.zmultiples P) = 0 := by
    have h := htriv
      (MulOpposite.op (Multiplicative.ofAdd (⟨P, hmem⟩ : AddSubgroup.zmultiples P)))
      (MulOpposite.op (Multiplicative.ofAdd (0 : AddSubgroup.zmultiples P)))
    simpa [Multiplicative.ofAdd] using congrArg
      (fun u : (Multiplicative (AddSubgroup.zmultiples P))ᵐᵒᵖ =>
        (MulOpposite.unop u : Multiplicative (AddSubgroup.zmultiples P))) h
  exact hP.ne' (congrArg Subtype.val hzero)

end Work.Final.DimOne
