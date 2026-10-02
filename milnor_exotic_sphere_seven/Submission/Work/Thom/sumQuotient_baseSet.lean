import Mathlib
import Submission.Work.Thom.sumStableDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The base sets of the pulled-back tautological quotient `s^*(Z ⊕ ε¹ / ℂ·s)`

`Work.Thom.sumQuotient ι₀ Z` is the pullback `s^*(Q_{Z ⊕ ε¹})` of the tautological quotient of the
Whitney sum `Z ⊕ ε¹` along the tautological section `s : b ↦ (b, ∂)` of the trivial summand
(`Submission/Work/Thom/sumStableDefs.lean`).  This module computes its charts: the chart indexed by
`(a, c)` (`a : ι × ι₀` the index of the sum, `c : Fin (m+1)` the chosen coordinate of the standard
fibre) consists of the points `b` lying in the chart `a.1` of `Z` at which the `c`-th coordinate of
the *unit vector* `∂ = Work.Thom.sumUnit m` does not vanish.

The point is that the tautological section `s` has *constant* coordinate `∂` in every chart of the
sum (the trivial summand has constant transition functions, `Work.Thom.sumEps_coordChange_sumUnit`),
so the local trivialization of the sum along the section is the identity on this coordinate.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- The tautological section `s` of `Z ⊕ ε¹`, as a point of the (realified) total space, is
`b ↦ (b, ∂)`. -/
theorem sumSection_val_aux {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} {ι₀ : Type}
    [Inhabited ι₀] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    ((sumSection ι₀ Z b : ↥(zeroComplement (realification (sumEps ι₀ Z)))) :
      (realification (sumEps ι₀ Z)).TotalSpace) = ⟨b, sumUnit m⟩ := rfl

/-- **The base sets of the pulled-back tautological quotient.**  The chart of `Work.Thom.sumQuotient`
indexed by `(a, c)` is the locus of points of `Z.baseSet a.1` at which the `c`-th coordinate of the
unit vector `Work.Thom.sumUnit m` does not vanish. -/
theorem sumQuotient_baseSet {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type}
    {ι₀ : Type} [Inhabited ι₀] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (a : ι × ι₀) (c : Fin (m + 1)) :
    (sumQuotient ι₀ Z).baseSet (a, c) = {b : B | b ∈ Z.baseSet a.1 ∧ (sumUnit m) c ≠ 0} := by
  ext b
  rw [sumQuotient, bundleComap_baseSet, tautQuotientCore_baseSet, tqBaseSet]
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [VectorBundleCore.localTriv_apply, sumSection_val_aux]
  simp only [sumEps_baseSet, bundleSum_baseSet, trivialVectorBundleCore, Set.inter_univ,
    sumEps_coordChange_sumUnit]

end

end Work.Thom
