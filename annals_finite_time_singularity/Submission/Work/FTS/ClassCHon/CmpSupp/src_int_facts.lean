import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.CmpSupp

/-- **Integrability of the `(z,θ)`-source, slicewise and on the open quadrant.**

The source is jointly `C^∞` (in this pin: analytic) on `ℝ²` and is supported in the strip
`z ∈ [a,b]` with `a > 0`.  Consequently

* every angular slice `θ ↦ F z θ ^ 2 * cos θ` is continuous, hence integrable on the compact
  interval `Iθ = [0, π/2]` (first conjunct);
* the singular weight `sEta θ = sin(2θ)^{-η}` is integrable on `Iθ`
  (`Work.Spaces.sin_two_rpow`, `η = 99/100 ∈ [0,1)`) and the slice `θ ↦ F z θ ^ 2` is bounded
  there, so the product is integrable (second conjunct, by `Integrable.bdd_mul`);
* on the open quadrant `Q0 = (0,∞) × (0,π/2)` the function `p ↦ F p.1 p.2 ^ 2` is supported in
  the compact rectangle `[a, max a b] × [0, π/2]`, where it is continuous; hence it is integrable
  there, and it vanishes identically off that rectangle inside `Q0` (third conjunct, by splitting
  `Q0 = (rectangle ∩ Q0) ∪ (Q0 \ rectangle)`). -/
theorem src_int_facts {a b : ℝ} (ha : 0 < a) {F : ℝ → ℝ → ℝ}
    (hFsm : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry F))
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → F z θ = 0) :
    (∀ z ∈ Set.Ioi (0 : ℝ),
        MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    ∧ (∀ z ∈ Set.Ioi (0 : ℝ),
        MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 := by
  -- (the hypothesis `0 < a` is not needed: the third conjunct only uses the *z*-support)
  have _ha : (0 : ℝ) < a := ha
  -- joint continuity of the source
  have hFc : Continuous (Function.uncurry F) := hFsm.continuous
  refine ⟨?_, ?_, ?_⟩
  · -- ## first conjunct: the `cos θ`-weighted slice
    intro z _
    have hslice : Continuous (fun θ : ℝ => F z θ) :=
      hFc.comp (continuous_const.prodMk continuous_id)
    exact (((hslice.pow 2).mul Real.continuous_cos).continuousOn).integrableOn_compact
      isCompact_Icc
  · -- ## second conjunct: the `sEta`-weighted slice
    intro z _
    have hslice : Continuous (fun θ : ℝ => F z θ) :=
      hFc.comp (continuous_const.prodMk continuous_id)
    -- a bound for the slice on `Iθ`
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hslice.continuousOn : ContinuousOn (fun θ : ℝ => F z θ) Work.Spaces.Iθ)
    have hMnn : 0 ≤ max M 0 := le_max_right _ _
    have hFbd : ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ max M 0 := fun θ hθ =>
      le_trans (by simpa [Real.norm_eq_abs] using hM θ hθ) (le_max_left _ _)
    -- the weight `sEta = sin(2θ)^{-η}` is integrable on `Iθ` (`η = 99/100 ∈ [0,1)`)
    have hσ : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ :=
      (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
        (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).1
    -- the bounded factor is a.e. strongly measurable and bounded by `(max M 0)²`
    have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (F z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hslice.pow 2).aestronglyMeasurable
    have hbdd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ‖(F z θ) ^ 2‖ ≤ (max M 0) ^ 2 := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (F z θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hFbd θ hθ) 2
    exact hσ.bdd_mul haesm hbdd
  · -- ## third conjunct: integrability on the open quadrant
    have hgc : Continuous (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2) := hFc.pow 2
    -- the compact rectangle containing the support
    have hIntS : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
        (Set.Icc a (max a b) ×ˢ Set.Icc 0 (Real.pi / 2)) :=
      hgc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    -- on the rectangle intersected with `Q0`
    have hInt1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
        ((Set.Icc a (max a b) ×ˢ Set.Icc 0 (Real.pi / 2)) ∩ Work.FTS.EllipticEst.Q0) :=
      hIntS.mono_set Set.inter_subset_left
    -- off the rectangle (inside `Q0`) the source vanishes by compact support
    have hInt2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
        (Work.FTS.EllipticEst.Q0 \ (Set.Icc a (max a b) ×ˢ Set.Icc 0 (Real.pi / 2))) :=
      MeasureTheory.integrableOn_zero.congr_fun (fun p hp => by
        show (0 : ℝ) = (F p.1 p.2) ^ 2
        obtain ⟨hpQ, hpS⟩ := hp
        obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hpQ
        have hθ : p.2 ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hθ1, le_of_lt hθ2⟩
        have h1 : p.1 ∉ Set.Icc a b := by
          intro hcon
          exact hpS ⟨⟨hcon.1, le_trans hcon.2 (le_max_right a b)⟩, hθ⟩
        rw [hsupp p.1 p.2 h1]
        ring)
        (Work.FTS.EllipticEst.isOpen_Q0.measurableSet.diff
          (measurableSet_Icc.prod measurableSet_Icc))
    have hU := hInt1.union hInt2
    have hset : ((Set.Icc a (max a b) ×ˢ Set.Icc 0 (Real.pi / 2)) ∩ Work.FTS.EllipticEst.Q0)
        ∪ (Work.FTS.EllipticEst.Q0 \ (Set.Icc a (max a b) ×ˢ Set.Icc 0 (Real.pi / 2)))
        = Work.FTS.EllipticEst.Q0 := by
      rw [Set.inter_comm (Set.Icc a (max a b) ×ˢ Set.Icc 0 (Real.pi / 2))
        Work.FTS.EllipticEst.Q0]
      exact Set.inter_union_sdiff _ _
    rwa [hset] at hU

end Work.FTS.ClassCHon.CmpSupp
