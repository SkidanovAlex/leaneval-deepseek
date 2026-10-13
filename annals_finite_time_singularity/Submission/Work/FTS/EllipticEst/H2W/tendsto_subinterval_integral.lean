import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.Honest.IntervalIntegralTendstoSetIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

/-- `gapDelta n = 1/(n+2)` is positive and tends to `0`; consequently the pair
`(gapDelta n, π/2 - gapDelta n)` converges to `(0, π/2)` from inside the open rectangle,
and the absolute continuity of the Lebesgue integral (the helper
`IntervalIntegralTendstoSetIntegral`) gives the claim. -/
theorem tendsto_subinterval_integral {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g Work.Spaces.Iθ) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x in (Work.FTS.EllipticEst.Honest.gapDelta n)..(Real.pi / 2 - Work.FTS.EllipticEst.Honest.gapDelta n), g x)
      Filter.atTop (nhds (∫ x in Work.Spaces.Iθ, g x)) := by
  -- `gapDelta` is positive at every index
  have hdpos : ∀ n : ℕ, 0 < Work.FTS.EllipticEst.Honest.gapDelta n := by
    intro n
    simp only [Work.FTS.EllipticEst.Honest.gapDelta]
    positivity
  -- and converges to `0`
  have hdlim : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.Honest.gapDelta n) Filter.atTop
      (nhds 0) := by
    have h0 := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (Filter.tendsto_add_atTop_nat 2)
    have hfun : (fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℝ)))
        = fun n : ℕ => Work.FTS.EllipticEst.Honest.gapDelta n := by
      funext n
      simp only [Work.FTS.EllipticEst.Honest.gapDelta]
      push_cast
      ring
    simpa only [Function.comp_def, hfun] using h0
  -- hence `gapDelta n → 0` inside `Ioi 0`
  have h1 : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.Honest.gapDelta n) Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hdlim, Filter.Eventually.of_forall hdpos⟩
  -- and `π/2 - gapDelta n → π/2` inside `Iio (π/2)`
  have h2 : Filter.Tendsto
      (fun n : ℕ => Real.pi / 2 - Work.FTS.EllipticEst.Honest.gapDelta n) Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (tendsto_const_nhds (x := Real.pi / 2)).sub hdlim
      simpa using h
    · filter_upwards with n
      simp only [Set.mem_Iio]
      linarith [hdpos n]
  -- the two coordinates together converge in the product filter
  have hseq : Filter.Tendsto
      (fun n : ℕ =>
        (Work.FTS.EllipticEst.Honest.gapDelta n, Real.pi / 2 - Work.FTS.EllipticEst.Honest.gapDelta n))
      Filter.atTop
      (Filter.comap Prod.fst (nhdsWithin 0 (Set.Ioi 0)) ⊓
        Filter.comap Prod.snd (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))) := by
    rw [← Filter.prod_eq_inf]
    exact h1.prodMk h2
  -- absolute continuity of the Lebesgue integral, composed with the sequence
  have hmain : Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in (Work.FTS.EllipticEst.Honest.gapDelta n)..(Real.pi / 2 - Work.FTS.EllipticEst.Honest.gapDelta n), g x)
      Filter.atTop (nhds (∫ x in Set.Icc 0 (Real.pi / 2), g x)) := by
    simpa only [Function.comp_def] using
      (Work.FTS.EllipticEst.Honest.IntervalIntegralTendstoSetIntegral hg).comp hseq
  exact hmain

end Work.FTS.EllipticEst.H2W
