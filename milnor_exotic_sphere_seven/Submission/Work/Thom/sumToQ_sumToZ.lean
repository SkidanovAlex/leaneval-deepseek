import Mathlib
import Submission.Work.Thom.sumStableDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 3200000

namespace Work.Thom

open Work.TangentClasses

open scoped Topology

noncomputable section

/-- **`sumToQ` is a left inverse of `sumToZ`**: the two fibrewise maps `ℂ^m → ℂ^m` of the
isomorphism `Z ≅ s^*(Z ⊕ ε¹ / ℂ·s)` are inverse to each other in this direction.

The proof decodes the definitions: `sumToZ z = EpartCLM m (fillFun k z)` (the `ℂ^m`-part of the
filled representative), and `sumToQ` is the quotient projection along `∂ = sumUnit m` of the class
obtained by re-inserting the `ℂ^m`-part into the trivial `ε`-summand.  The two representatives
differ precisely by a multiple of `∂`, which the quotient projection kills, and on the filled
representative `fillFun k z` the projection is the identity (`quoFun_fillFun`). -/
theorem sumToQ_sumToZ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} {ι₀ : Type}
    [Inhabited ι₀] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (z : EuclideanSpace ℂ (Fin m)) :
    sumToQ ι₀ Z b (sumToZ ι₀ Z b z) = z := by
  -- The `k`-th coordinate of the tautological section `∂ = sumUnit m` does not vanish.
  have hw : sumUnit m (sumCoord ι₀ Z b) ≠ 0 := by
    rw [sumCoord]
    have h := tqCoord_spec (sumEps ι₀ Z) (sumSection (ι₀ := ι₀) Z b)
    have hp : (↑(sumSection ι₀ Z b) : (realification (sumEps ι₀ Z)).TotalSpace)
        = (⟨b, sumUnit m⟩ : (sumEps ι₀ Z).TotalSpace) := rfl
    rw [hp] at h
    rw [VectorBundleCore.localTriv_apply] at h
    rw [VectorBundleCore.coordChange_self _ _ b ((sumEps ι₀ Z).mem_baseSet_at b)] at h
    exact h
  rw [sumToQ, sumToZ]
  simp only [ContinuousLinearMap.comp_apply, fillCLM_apply, quoCLM_apply]
  set k := sumCoord ι₀ Z b with hk
  set u : EuclideanSpace ℂ (Fin (m+1)) := fillFun k z with hu
  -- The quotient projection of the filled representative is `z` itself.
  have hfill : quoFun k (sumUnit m) u = z := by
    rw [hu]; exact quoFun_fillFun k (sumUnit m) z hw
  -- Any vector `v : ℂ¹` is a multiple of the basis vector.
  have hvec : ∀ v : EuclideanSpace ℂ (Fin 1), v = (v 0) • basisVec (0 : Fin 1) := by
    intro v; ext j; fin_cases j; simp [basisVec_apply]
  -- Decompose `u` in the standard identification `ℂ^m × ℂ¹ ≅ ℂ^{m+1}`.
  set a := ((prodFinEquiv m).symm u).1 with ha_def
  set bb := ((prodFinEquiv m).symm u).2 with hb_def
  have ha : EpartCLM m u = a := rfl
  have hp' : ((prodFinEquiv m).symm u) = (a, bb) := Prod.ext ha_def.symm hb_def.symm
  have hux : u = prodFinEquiv m (a, bb) := by
    rw [← hp']
    exact (ContinuousLinearEquiv.apply_symm_apply (prodFinEquiv m) u).symm
  have h3 : -(bb) = (-(bb 0)) • basisVec (0 : Fin 1) := by
    rw [hvec (-bb)]; simp
  have h4 : ((0 : EuclideanSpace ℂ (Fin m)), -(bb))
      = (-(bb 0)) • ((0 : EuclideanSpace ℂ (Fin m)), basisVec (0 : Fin 1)) := by
    rw [h3]; ext <;> simp
  -- The re-inserted representative differs from `u` by a multiple of `∂`.
  have hsplit : prodFinEquiv m (a, (0 : EuclideanSpace ℂ (Fin 1)))
      = u + (-(bb 0)) • sumUnit m := by
    have h1 : (a, (0 : EuclideanSpace ℂ (Fin 1)))
        = (a, bb) + ((0 : EuclideanSpace ℂ (Fin m)), -(bb)) := by ext <;> simp
    rw [h1, map_add, h4, map_smul, ← hux]
    rfl
  have hj : jCLM m (EpartCLM m u) = u + (-(bb 0)) • sumUnit m := by
    rw [show jCLM m (EpartCLM m u) = prodFinEquiv m (EpartCLM m u, 0) from rfl, ha, hsplit]
  rw [hj, quoFun_add, quoFun_smul, quoFun_self k (sumUnit m) hw, smul_zero, add_zero, hfill]

end

end Work.Thom
