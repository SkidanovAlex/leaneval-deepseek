import Mathlib
import Submission.Work.MRMT.Found.PLWD.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found.PLWD

/-- The `L²(B(0,R))`-inner product of `u` against the class of a test function `ψ` is the
integral over the whole plane of `star (u z) * ψ z` (which is legitimate because `ψ` vanishes
outside `B(0,R)`). -/
theorem inner_testLp_eq_integral_star_mul {R : ℝ}
    (u : MeasureTheory.Lp ℂ 2 ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict (Metric.ball 0 R)))
    (ψ : Work.MRMT.Found.testSpace R) :
    inner ℂ u (Work.MRMT.Found.testLp R ψ)
      = ∫ z, star (u z) * (ψ : ℂ → ℂ) z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∫ a, inner ℂ (u a) ((Work.MRMT.Found.testLp R ψ : ℂ → ℂ) a)
        ∂((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict (Metric.ball 0 R))
      = ∫ a, star (u a) * (ψ : ℂ → ℂ) a
        ∂((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict (Metric.ball 0 R)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp
      (Work.MRMT.Found.memLp_of_mem_testSpace ψ.2)] with a ha
    rw [Work.MRMT.Found.testLp_apply R ψ, ha, RCLike.inner_apply, RCLike.star_def]
    exact mul_comm _ _
  rw [h1]
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)
  have h0 : (ψ : ℂ → ℂ) z = 0 := by
    by_contra h
    exact hz (ψ.2.2.2 (subset_tsupport (ψ : ℂ → ℂ) (Function.mem_support.mpr h)))
  rw [h0, mul_zero]

end Work.MRMT.Found.PLWD
