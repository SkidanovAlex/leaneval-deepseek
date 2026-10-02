import Mathlib
import Submission.Work.LerayHirsch.TwistSection
import Submission.Work.LerayHirsch.TautEmbedCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The chart of `ℓ^* ⊗ π^*E` in which the tautological section is everywhere non-zero

On the chart `(i,k)` of the tautological line bundle, the tautological section of
`Work.LerayHirsch.tautTwist Z = ℓ^* ⊗ π^*E` (`Work.LerayHirsch.tautSectionVec`) has `k`-th
coordinate **exactly `1`** in the chart `((i,k), i)` of the twist; in particular it is non-zero
there.  This is the covering statement that lets the complement of the tautological line produced
by Whitney's splitting lemma be re-presented over the cover `ι × Fin (m+1)` of `ℓ`: its chart
`(((i,k),i),k)` contains the whole of `tautBaseSetProj Z (i,k)`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The tautological section has non-zero `k`-th coordinate on the chart `(i,k)`.** -/
theorem localTriv_tautSectionVec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (i : ι) (k : Fin (m + 1))
    {x : ProjSpace Z} (hx : x ∈ tautBaseSetProj Z (i, k)) :
    ((tautTwist Z).localTriv ((i, k), i)
      (⟨x, tautSectionVec Z x⟩ : (tautTwist Z).TotalSpace)).2 k ≠ 0 := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [mem_tautBaseSetProj_mk] at hx
  obtain ⟨hbase, hk⟩ := hx
  rw [VectorBundleCore.localTriv_apply]
  simp only [twistCore_indexAt, twistCore_coordChange, Work.Gen.dualLineCore_coordChange,
    Work.Gen.dualLineCore_indexAt, bundleComap_coordChange, bundleComap_indexAt,
    projMap_mkProj]
  rw [tautLine_coordChange, tautCoeffCLM, Work.Gen.scl_smul_id_eq]
  rw [tautSectionVec, TautEmbed.chartRatioVec_mk, TautEmbed.chartRatioRaw,
    if_pos (TautEmbed.chartCoord_indexAt_ne_zero Z p)]
  rw [tautLine_coordChange_eq_ratio Z (i, k) ((tautLine Z).indexAt (mkProj Z p)) p hk]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, projMap_mkProj, TautEmbed.chartCoord_indexAt]
  rw [← chartCoord_def]
  exact mul_ne_zero
    (inv_ne_zero (TautEmbed.chartCoord_indexAt_ne_zero Z p))
    (mul_ne_zero (div_ne_zero (TautEmbed.chartCoord_indexAt_ne_zero Z p) hk) hk)

end

end Work.LerayHirsch
