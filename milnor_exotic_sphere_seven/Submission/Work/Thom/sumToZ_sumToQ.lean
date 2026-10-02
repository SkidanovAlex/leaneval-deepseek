import Mathlib
import Submission.Work.Thom.sumStableDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `sumToZ ∘ sumToQ = id`: the two fibrewise maps of `Z ≅ s^*(Z ⊕ ε¹ / ℂ·s)` are inverse

`Work.Thom.sumToQ` sends `y : ℂ^m` to the class of `(y, 0)` in the tautological quotient
`s^*(Z ⊕ ε¹ / ℂ·s)` (in the chart coordinate `k = sumCoord ι₀ Z b`), and `Work.Thom.sumToZ`
sends a class with vanishing `ε`-coordinate back to `Z` by taking the `E`-part of its
representative with vanishing `ε`-coordinate.

The composite is the identity because the filling `fillFun k` of the quotient coordinate
`quoFun k (∂) (jCLM m y)` differs from `jCLM m y` by a multiple of the unit vector `∂ = sumUnit m`,
and `∂` has vanishing `E`-part:

  `sumToZ b (sumToQ b y) = EpartCLM m (fillFun k (quoFun k ∂ (jCLM m y)))`
                        `= EpartCLM m (jCLM m y) - c • EpartCLM m ∂ = y - 0 = y`.

The only point needing care is that the chosen chart coordinate `k = sumCoord ι₀ Z b` really is a
coordinate at which `∂` does not vanish, which is `Work.Thom.tqCoord_spec` together with the fact
that the transition functions of the sum fix `∂` (`Work.Thom.sumEps_coordChange_sumUnit`).
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Thom

/-- **The chart coordinate of `tqCoord` does not vanish on the tautological section.**  The
`tqCoord_spec` says that the coordinate of the tautological section *read in the preferred
trivialisation* is non-zero; in the preferred trivialisation the section is however its own
coordinate vector. -/
private lemma tqCoord_snd_ne_zero {n : ℕ} {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (q : ↥(zeroComplement (realification Z))) :
    (show EuclideanSpace ℂ (Fin (n + 1)) from ((q : (realification Z).TotalSpace)).snd)
      (tqCoord Z q) ≠ 0 := by
  have h := tqCoord_spec Z q
  rw [VectorBundleCore.localTrivAt_def] at h
  rw [VectorBundleCore.localTrivAt_apply] at h
  simpa using h

/-- **The coordinate supplied by `sumCoord` is a coordinate at which the unit vector `∂` of the
trivial summand does not vanish.** -/
private lemma sumUnit_sumCoord_ne_zero {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type}
    {ι₀ : Type} [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    (sumUnit m) (sumCoord ι₀ Z b) ≠ 0 := by
  have h := tqCoord_snd_ne_zero (sumEps ι₀ Z) (sumSection ι₀ Z b)
  rw [show ((sumSection ι₀ Z b : ↥(zeroComplement (realification (sumEps ι₀ Z)))) :
      (realification (sumEps ι₀ Z)).TotalSpace).snd = sumUnit m from rfl] at h
  exact h

/-- The `E`-part of `jCLM m y = (y, 0)` is `y`. -/
private lemma EpartCLM_jCLM (m : ℕ) (y : EuclideanSpace ℂ (Fin m)) :
    EpartCLM m (jCLM m y) = y := by
  simp only [EpartCLM, jCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.inl_apply]
  rfl

/-- The `E`-part of the unit vector `∂ = (0, 1)` of the trivial summand vanishes. -/
private lemma EpartCLM_sumUnit_zero (m : ℕ) : EpartCLM m (sumUnit m) = 0 := by
  simp only [EpartCLM, sumUnit, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem sumToZ_sumToQ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} {ι₀ : Type}
    [Inhabited ι₀] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (y : EuclideanSpace ℂ (Fin m)) :
    sumToZ ι₀ Z b (sumToQ ι₀ Z b y) = y := by
  -- `k` is the chart coordinate of the tautological quotient, `∂ = sumUnit m` the unit vector.
  have hw : (sumUnit m) (sumCoord ι₀ Z b) ≠ 0 := sumUnit_sumCoord_ne_zero Z b
  -- The filling of the quotient coordinate differs from `jCLM m y` by a multiple of `∂`.
  have hfill := sub_fillFun_quoFun (sumCoord ι₀ Z b) (sumUnit m) (jCLM m y) hw
  have hcongr := congrArg (EpartCLM m) hfill
  -- Applying the `E`-part kills the multiple of `∂`, leaving `y` on the left.
  simp only [map_sub, map_smul, EpartCLM_jCLM, EpartCLM_sumUnit_zero, smul_zero] at hcongr
  -- Unfold the two fibrewise maps and conclude.
  rw [sumToZ, sumToQ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    fillCLM_apply, quoCLM_apply]
  exact (sub_eq_zero.mp hcongr).symm

end Work.Thom
