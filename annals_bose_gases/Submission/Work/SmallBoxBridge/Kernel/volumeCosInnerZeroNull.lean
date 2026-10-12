import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxBridge.Kernel

open MeasureTheory Set

/-- The set of points `p` in `ℝ³` where `cos (inner ℝ p z)` vanishes has Lebesgue measure
zero, for every `z ≠ 0`: it is the preimage under the nonzero linear functional
`p ↦ inner ℝ p z` of the countable set of zeros of `cos`, and preimages of countable unions
of level sets (cosets of a strict subspace) are null. -/
theorem volumeCosInnerZeroNull (z : EuclideanSpace ℝ (Fin 3)) (hz : z ≠ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      {p : EuclideanSpace ℝ (Fin 3) | Real.cos (inner ℝ p z) = 0} = 0 := by
  classical
  -- The continuous linear functional `p ↦ inner ℝ p z`, viewed as a linear map.
  let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ := (innerSL ℝ z : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
  have hLp : ∀ p, L p = inner ℝ p z := by
    intro p
    change (innerSL ℝ z : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) p = inner ℝ p z
    rw [innerSL_apply_apply, real_inner_comm]
  -- `L` is nonzero because `L z = ‖z‖ ^ 2 > 0`.
  have hLz : L z ≠ 0 := by
    rw [hLp, real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hker : L.ker ≠ ⊤ := by
    intro h
    have hzmem : z ∈ L.ker := by rw [h]; exact Submodule.mem_top
    rw [LinearMap.mem_ker] at hzmem
    exact hLz hzmem
  -- Every level set `L ⁻¹' {t}` is a translate of `ker L`, hence null.
  have hfiber : ∀ t : ℝ,
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        (L ⁻¹' {t}) = 0 := by
    intro t
    have hv : L ((t / L z) • z) = t := by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ t hLz]
    have hset : L ⁻¹' {t}
        = (fun x => -((t / L z) • z) + x) ⁻¹' (L.ker : Set (EuclideanSpace ℝ (Fin 3))) := by
      ext p
      simp only [mem_preimage, mem_singleton_iff]
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_add, map_neg, hv, neg_add_eq_sub, sub_eq_zero]
    rw [hset, measure_preimage_add]
    exact Measure.addHaar_submodule
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) L.ker hker
  -- The zero set of `cos` is countable.
  have hS : ({t : ℝ | Real.cos t = 0}).Countable := by
    have hr : {t : ℝ | Real.cos t = 0}
        = Set.range (fun k : ℤ => (2 * (k : ℝ) + 1) * Real.pi / 2) := by
      ext t
      rw [Set.mem_ofPred_eq, Real.cos_eq_zero_iff, Set.mem_range]
      exact exists_congr (fun k => eq_comm)
    rw [hr]
    exact Set.countable_range _
  have hA : {p : EuclideanSpace ℝ (Fin 3) | Real.cos (inner ℝ p z) = 0}
      = L ⁻¹' {t : ℝ | Real.cos t = 0} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [hLp p]
  have hUnion : L ⁻¹' {t : ℝ | Real.cos t = 0}
      = ⋃ t ∈ {t : ℝ | Real.cos t = 0}, L ⁻¹' {t} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro h; exact ⟨L p, h, rfl⟩
    · rintro ⟨t, ht, hpt⟩; rwa [hpt]
  rw [hA, hUnion, measure_biUnion_null_iff hS]
  intro t ht
  exact hfiber t

end Work.SmallBoxBridge.Kernel
