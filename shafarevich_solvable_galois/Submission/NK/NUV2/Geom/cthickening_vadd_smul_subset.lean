import Mathlib.Analysis.Normed.Module.Ball.Pointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.Geom

open Metric Set
open scoped Pointwise

theorem cthickening_vadd_smul_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {t δ : ℝ} (ht : 0 < t) (w : E) :
    Metric.cthickening δ ((fun x : E => w + t • x) '' S) ⊆
      (fun x : E => w + t • x) '' (Metric.cthickening (δ / t) S) := by
  -- `infEDist` of a point of the image in the image scales by `t`.
  have key : ∀ z : E, Metric.infEDist (w + t • z) ((fun x : E => w + t • x) '' S)
      = ENNReal.ofReal t * Metric.infEDist z S := by
    intro z
    have hset : (fun x : E => w + t • x) '' S = (fun y : E => w + y) '' (t • S) := by
      rw [← Set.image_smul (a := t) (t := S)]
      exact (Set.image_image _ _ _).symm
    rw [hset]
    rw [Metric.infEDist_image (isometry_add_left w)]
    rw [infEDist_smul₀ ht.ne' S z]
    rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_of_nonneg ht.le]
  intro y hy
  -- the preimage of `y` under `x ↦ w + t • x`
  set x : E := t⁻¹ • (y - w) with hx
  have hfx : w + t • x = y := by
    rw [hx, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    abel
  have hmem : x ∈ Metric.cthickening (δ / t) S := by
    rw [Metric.mem_cthickening_iff]
    have h1 : Metric.infEDist (w + t • x) ((fun x : E => w + t • x) '' S) ≤
        ENNReal.ofReal δ := by
      rw [hfx]
      exact Metric.mem_cthickening_iff.mp hy
    rw [key x] at h1
    have hδ : ENNReal.ofReal δ = ENNReal.ofReal t * ENNReal.ofReal (δ / t) := by
      rw [← ENNReal.ofReal_mul ht.le, mul_div_cancel₀ δ ht.ne']
    rw [hδ] at h1
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr ht).ne'
      ENNReal.ofReal_ne_top).mp h1
  exact ⟨x, hmem, hfx⟩

end NK.NUV2.Geom
