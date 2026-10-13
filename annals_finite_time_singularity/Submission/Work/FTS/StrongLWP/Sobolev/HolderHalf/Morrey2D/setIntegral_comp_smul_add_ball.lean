import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.TotallySplit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Pointwise

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

/-- Change of variables for the Lebesgue integral over a ball of `ℝ × ℝ` (with the product,
i.e. sup, norm) under the affine map `y ↦ c + t • y` with `t > 0`: the ball of radius `a` centred
at `0` is transported to the ball of radius `t * a` centred at `c`, at the price of the Jacobian
factor `(t ^ 2)⁻¹` (the dimension being `2`). -/
theorem setIntegral_comp_smul_add_ball (f : ℝ × ℝ → ℝ) {a t : ℝ} (ht : 0 < t) (c : ℝ × ℝ) :
    ∫ y in Metric.ball (0 : ℝ × ℝ) a, f (c + t • y)
      = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), f w := by
  have ht0 : t ≠ 0 := ht.ne'
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hsmulball : t • Metric.ball (0 : ℝ × ℝ) a = Metric.ball (0 : ℝ × ℝ) (t * a) := by
    rw [smul_ball ht0, smul_zero, Real.norm_of_nonneg ht.le]
  -- the image of a ball under the translation `x ↦ c + x`
  have himg : (fun x : ℝ × ℝ => c + x) '' Metric.ball (0 : ℝ × ℝ) (t * a)
      = Metric.ball c (t * a) := by
    rw [show (fun x : ℝ × ℝ => c + x) = (fun x : ℝ × ℝ => c +ᵥ x) from by
      funext x; rw [vadd_eq_add]]
    rw [Set.image_vadd, Metric.vadd_ball]
    simp [vadd_eq_add]
  -- translation invariance of the set integral
  have htrans : ∫ x in Metric.ball (0 : ℝ × ℝ) (t * a), f (c + x)
      = ∫ w in Metric.ball c (t * a), f w := by
    have h1 : MeasureTheory.MeasurePreserving (fun x : ℝ × ℝ => c + x) MeasureTheory.volume
        MeasureTheory.volume := MeasureTheory.measurePreserving_add_left _ c
    have h2 : MeasurableEmbedding (fun x : ℝ × ℝ => c + x) := by
      have := (Homeomorph.addLeft c).measurableEmbedding
      simpa using this
    have h3 := MeasureTheory.MeasurePreserving.setIntegral_image_emb h1 h2 f
      (Metric.ball (0 : ℝ × ℝ) (t * a))
    rw [himg] at h3
    exact h3.symm
  calc ∫ y in Metric.ball (0 : ℝ × ℝ) a, f (c + t • y)
      = ∫ y in Metric.ball (0 : ℝ × ℝ) a, (fun x => f (c + x)) (t • y) := rfl
    _ = (t ^ Module.finrank ℝ (ℝ × ℝ))⁻¹ • ∫ x in t • Metric.ball (0 : ℝ × ℝ) a, f (c + x) :=
        MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := MeasureTheory.volume)
          (fun x => f (c + x)) (Metric.ball (0 : ℝ × ℝ) a) ht
    _ = (t ^ 2)⁻¹ * ∫ x in Metric.ball (0 : ℝ × ℝ) (t * a), f (c + x) := by
        rw [hsmulball, hfin, smul_eq_mul]
    _ = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), f w := by rw [htrans]

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
