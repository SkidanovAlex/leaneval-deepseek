import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotL2LeHkSq
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotHkGen.integral_slot_sq_rpow_le_HkSq_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.SlotHkGen

theorem integral_slot_sq_rpow_le_HkSq_mixed {α : ℝ} {g : ℝ → ℝ → ℝ} {c : ℝ} {j i : ℕ}
    (hα : 0 < α) (hc : -(Work.Spaces.gam α) ≤ c) (hi : 1 ≤ i) (hji : j + i ≤ 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∫ p : ℝ × ℝ, (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ Work.Spaces.HkSq α 4 g := by
  -- Integrability of the `ℋ⁴`-integrand
  have hHk : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.StrongEps.EpsE4Thr.HkIntegrand_integrable_prod_fts (k := 4) hsm hmem
  -- The pointwise domination on the open quadrant (`i ≥ 1`, so this is a mixed slot)
  have hdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ c)
        * (Work.Spaces.mixed j i g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z θ hz hθ hθ2
    exact Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
      (α := α) (c := c) (g := g) (a := i) (b := j) hα hc hi (by omega) ⟨hθ, hθ2⟩
  have hae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2 := by
    filter_upwards [Work.FTS.StrongEps.EpsE4Thr.ae_mem_openQuadrant_fts] with p hp
    exact hdom p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      0 ≤ (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2 := by
    filter_upwards [Work.FTS.StrongEps.EpsE4Thr.ae_mem_openQuadrant_fts] with p hp
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ c)) (sq_nonneg _)
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])).le
  have hle := MeasureTheory.integral_mono_of_nonneg hnn hHk hae
  have heq : (∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α 4 g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = Work.Spaces.HkSq α 4 g := by
    rw [Work.Spaces.HkSq]
    exact (MeasureTheory.integral_integral
      (f := fun z θ => Work.Spaces.HkIntegrand α 4 g z θ) hHk).symm
  calc (∫ p : ℝ × ℝ, (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        * (Work.Spaces.mixed j i g p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ ∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α 4 g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hle
    _ = Work.Spaces.HkSq α 4 g := heq

end Work.FTS.StrongEps.EpsE4Thr.SlotHkGen
