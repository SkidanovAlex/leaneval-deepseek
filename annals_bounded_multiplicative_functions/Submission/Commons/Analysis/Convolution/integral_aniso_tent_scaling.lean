import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Convolution

open MeasureTheory Matrix
open scoped BigOperators

theorem sum_fin_val_add_one (k : ℕ) : (∑ i : Fin k, (i.val + 1)) = k * (k + 1) / 2 := by
  have h := Finset.sum_range_succ' (fun i => i) k
  simp only [add_zero] at h
  rw [Finset.sum_fin_eq_sum_range]
  trans (∑ x ∈ Finset.range k, (x + 1))
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [dif_pos (Finset.mem_range.mp hx)]
  · rw [← h, Finset.sum_range_id]
    rw [show k + 1 - 1 = k by omega]
    rw [Nat.mul_comm (k+1) k]

theorem integral_aniso_tent_scaling (k : ℕ) (hk : 1 ≤ k) {A δ : ℝ} (hA : (k : ℝ) < A) (hδ : 0 < δ) :
    δ ^ (k * (k + 1) / 2) *
        (∫ y : Fin k → ℝ,
          (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            fun i => |δ ^ (i.val + 1) * y i|)) ^ (-A))
      = ∫ y : Fin k → ℝ,
          (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            fun i => |y i|)) ^ (-A) := by
  classical
  set s : Fin k → ℝ := fun i => δ ^ (i.val + 1) with hs
  set T : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) := Matrix.toLin' (Matrix.diagonal s) with hT
  set g : (Fin k → ℝ) → ℝ :=
    fun y => (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      fun i => |y i|)) ^ (-A) with hg
  have hTy : ∀ y : Fin k → ℝ, T y = fun i => δ ^ (i.val + 1) * y i := by
    intro y; funext i
    rw [hT, Matrix.toLin'_apply, Matrix.mulVec_diagonal, hs]
  have hdet : LinearMap.det T = δ ^ (k * (k + 1) / 2) := by
    rw [hT, LinearMap.det_toLin', Matrix.det_diagonal, hs]
    rw [Finset.prod_pow_eq_pow_sum, sum_fin_val_add_one]
  have hdetpos : 0 < LinearMap.det T := by
    rw [hdet]; exact pow_pos hδ _
  have hgmeas : Measurable g := by
    rw [hg]; fun_prop
  have hgasm : AEStronglyMeasurable g (Measure.map (⇑T) volume) := hgmeas.aestronglyMeasurable
  have hmap : Measure.map (⇑T) volume = ENNReal.ofReal |(LinearMap.det T)⁻¹| • volume :=
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hdetpos.ne'
  have hTmeas : AEMeasurable (⇑T) volume :=
    (LinearMap.continuous_of_finiteDimensional T).measurable.aemeasurable
  have hint : ∫ y, g y ∂(Measure.map (⇑T) volume) = ∫ y, g (T y) ∂volume :=
    integral_map hTmeas hgasm
  have hstep : ∫ y, g (T y) ∂volume = (δ ^ (k * (k + 1) / 2))⁻¹ * ∫ y, g y ∂volume := by
    rw [← hint, hmap, integral_smul_measure]
    congr 1
    rw [ENNReal.toReal_ofReal (abs_nonneg _), hdet,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hδ.le _))]
  have hmain : δ ^ (k * (k + 1) / 2) * (∫ y, g (T y) ∂volume) = ∫ y, g y ∂volume := by
    rw [hstep, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hδ.ne'), one_mul]
  have hL : (∫ y : Fin k → ℝ,
        (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          fun i => |δ ^ (i.val + 1) * y i|)) ^ (-A)) = ∫ y, g (T y) ∂volume := by
    apply integral_congr_ae
    filter_upwards with y
    rw [hg, hTy y]
  have hR : (∫ y : Fin k → ℝ,
        (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          fun i => |y i|)) ^ (-A)) = ∫ y, g y ∂volume := by
    rw [hg]
  rw [hL, hR]
  exact hmain

end Commons.Analysis.Convolution