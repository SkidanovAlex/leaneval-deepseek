import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ang1HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.GalBasis.cut.LN_slot_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cut

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary facts used by the assembly

The argument has three layers.

* The **per-slice domination** `∫θ 1_{LN N}(θ)·(D_z^b f z θ·Wt α z θ)² ≤ C·∫θ HkIntegrand α 4 f z θ`
  for `z > 0` (with `C` independent of `N` and `z`): the layer mass is at most the `γ`-weighted
  angular mass `w z²∫θ (D_z^b f z θ)² sin(2θ)^{-γ}` of the whole interval, which the slice Hardy
  inequality `Work.FTS.GalBasis.cut.sliceGamma` bounds by the angular derivative; the derivative is
  `mixed b 1 f / sin(2θ)`, which is (a `w z²`-multiple of) the `(i,j) = (1,b)` summand of
  `HkIntegrand α 4 f`.  Proved here (`LN_slot_slice_bound_priv`).
* The **per-slice vanishing** of the layer mass, from the two endpoint traces
  (`Work.FTS.GalBasis.cut.LN_indicator_weighted_tendsto`).
* The **dominated convergence in `z`**: the integrands are dominated by
  `z ↦ C·∫θ HkIntegrand α 4 f z θ` (integrable by `HkMem`), and for almost every `z` they converge
  to `0` by the layer lemma applied to the `θ`-slice `θ ↦ D_z^b f z θ`, whose endpoint traces are
  the `a = 0` conjunct of `BdryTraces α 4 f`. -/

/-- `Wt α z θ = w z · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
private theorem continuousOn_Wt_quad (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ContinuousOn.rpow_const
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hsin




/-! ### The per-slice domination -/

/-- A.e. a point of `Iθ` is an interior point of the interval. -/
private theorem ae_Ioo_of_restrict_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  have h := MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set h]
  exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo


/-- The angular part of the wrong-weight slot: `(M·(W·s^{-γ/2}))² = W²·(M²·s^{-γ})` for `s > 0`. -/
private lemma wt_sq_eq {α : ℝ} {s M W : ℝ} (hs : 0 < s) :
    (M * (W * s ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = W ^ 2 * (M ^ 2 * s ^ (-(Work.Spaces.gam α))) := by
  rw [mul_pow, mul_pow, Work.FTS.GalBasis.cc.sq_rpow_neg_half hs]
  ring_nf



end Work.FTS.GalBasis.cut
end
