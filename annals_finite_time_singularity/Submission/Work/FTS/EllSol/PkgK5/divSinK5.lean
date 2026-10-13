import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.Defs
import Submission.Work.FTS.EllSol.PkgK5.PerSliceK

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem divSinK5 (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Φ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen Φ →
      (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) (Set.Ioo 0 (Real.pi / 2))) →
      (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
        (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
      (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
        (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.pth Φ) →
      Work.Spaces.HkMem α k (fun z θ => Φ z θ / Real.sin (2 * θ)) ∧
      Work.Spaces.HkNorm α k (fun z θ => Φ z θ / Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pth Φ) := by
  obtain ⟨K, hKpos, hperz⟩ := perSliceCmpK k hk
  refine ⟨Real.sqrt K, Real.sqrt_pos.mpr hKpos, ?_⟩
  intro α Φ hα hα1 hSO hsl ht0 ht1 hmem
  set U : ℝ → ℝ → ℝ := fun z θ => Φ z θ / Real.sin (2 * θ) with hUdef
  have hcmp : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ)
        ≤ K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth Φ) z θ) :=
    fun z hz => (hperz α Φ hα hα1 hSO hsl ht0 ht1 hmem z hz).2
  have hint : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k U z θ)
        Work.Spaces.Iθ :=
    fun z hz => (hperz α Φ hα hα1 hSO hsl ht0 ht1 hmem z hz).1
  have hsq : Work.Spaces.HkSq α k U ≤ K * Work.Spaces.HkSq α k (Work.Spaces.pth Φ) := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k U z θ)
      (hmem.2.const_mul K) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact hcmp z hz
  have hnorm : Work.Spaces.HkNorm α k U
      ≤ Real.sqrt K * Work.Spaces.HkNorm α k (Work.Spaces.pth Φ) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← Real.sqrt_mul hKpos.le]
    exact Real.sqrt_le_sqrt hsq
  have hmemQ : Work.Spaces.HkMem α k U := by
    refine ⟨hint, ?_⟩
    have hKnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k U z θ :=
      fun z _ => MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k U z θ
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul K) ?_ ?_
    · have hSOQ : Work.FTS.EllipticEst.SmoothOpen U := by
        rw [hUdef]
        exact Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hSO
      have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k U p.1 p.2)
          ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
            (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact (hSOQ.continuousOn_HkIntegrand α k).aestronglyMeasurable
          (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h2 : AEStronglyMeasurable
          (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.HkIntegrand α k U z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        have h1 := hprod.integral_prod_right'
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
            Work.Spaces.HkIntegrand α k U z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
            (b := Real.pi / 2))
      rw [← hfun]
      exact h2
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (hKnn z hz)]
      exact hcmp z hz
  refine ⟨?_, ?_⟩
  · simpa only [hUdef] using hmemQ
  · simpa only [hUdef] using hnorm

end Work.FTS.EllSol.PkgK5
