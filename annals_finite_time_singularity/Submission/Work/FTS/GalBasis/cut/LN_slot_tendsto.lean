import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.GalBasis.cut.sliceGamma
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.FTS.GalBasis.cc.wwBasic
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.GalBasis.cut.LN_indicator_weighted_tendsto

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

/-- Almost every `z ∈ Iz` is positive. -/
private theorem ae_pos_of_restrict_Iz :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
  have hset : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz := MeasureTheory.Ioi_ae_eq_Ici
  rw [← MeasureTheory.Measure.restrict_congr_set hset]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  exact Filter.Eventually.of_forall fun z hz => hz

/-- A.e. strong measurability of the uncurried layer integrand on the product measure. -/
private theorem aesm_LN_slot {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (b N : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) p.2 *
          (Work.Spaces.DzIter b f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter b f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (((hsm.DzIter b).continuousOn).mul (continuousOn_Wt_quad α)).pow 2
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter b f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    ((measurable_const.indicator (Work.FTS.GalBasis.cc.measurableSet_LN N)).comp
      measurable_snd).aestronglyMeasurable
  have h3 := h2.mul h1
  exact h3

/-- **The wrong-weight slot is a `w²`-multiple of the trace datum.**  For `θ ∈ Iθ`,
`(D_z^b f · Wt α)² = w z²·(D_z^b f)²·sin(2θ)^{-γ}`. -/
private lemma LN_slot_factor {α : ℝ} (hγ : Work.Spaces.gam α ≠ 0) {f : ℝ → ℝ → ℝ} {b : ℕ}
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2
      = Work.Spaces.w z ^ 2 * ((Work.Spaces.DzIter b f z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0, Real.zero_rpow (by simp [hγ] : -(Work.Spaces.gam α / 2) ≠ 0),
      Real.zero_rpow (by simp [hγ] : -(Work.Spaces.gam α) ≠ 0)]
    ring
  · rw [mul_pow, mul_pow, Work.FTS.GalBasis.cc.sq_rpow_neg_half hspos]
    ring

/-! ### The per-slice domination -/

/-- A.e. a point of `Iθ` is an interior point of the interval. -/
private theorem ae_Ioo_of_restrict_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  have h := MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set h]
  exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo

/-- `(M/s)²·s^{2-γ} = M²·s^{-γ}` for `s > 0`. -/
private lemma sq_div_mul_rpow {s γ M : ℝ} (hs : 0 < s) :
    (M / s) ^ 2 * s ^ (2 - γ) = M ^ 2 * s ^ (-γ) := by
  have h2 : (M / s) ^ 2 = M ^ 2 * s ^ (-2 : ℝ) := by
    rw [div_pow, div_eq_mul_inv, ← Real.rpow_two s, ← Real.rpow_neg (le_of_lt hs) 2]
  rw [h2, mul_assoc, ← Real.rpow_add hs (-2) (2 - γ)]
  congr 1
  ring_nf

/-- The angular part of the wrong-weight slot: `(M·(W·s^{-γ/2}))² = W²·(M²·s^{-γ})` for `s > 0`. -/
private lemma wt_sq_eq {α : ℝ} {s M W : ℝ} (hs : 0 < s) :
    (M * (W * s ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = W ^ 2 * (M ^ 2 * s ^ (-(Work.Spaces.gam α))) := by
  rw [mul_pow, mul_pow, Work.FTS.GalBasis.cc.sq_rpow_neg_half hs]
  ring_nf

/-- **The wrong-weight `D_z^b`-slot on the layers `LN N` is dominated, uniformly in `N` and `z`.**
See the module docstring for the route. -/
private theorem LN_slot_slice_bound_priv {α : ℝ} {f : Work.FTS.Galerkin.Fn} {b : ℕ}
    (hα : 0 < α) (hb4 : b ≤ 3) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) (hbT : Work.FTS.Nonlin.BdryTraces α 4 f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (z : ℝ), 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hγ1 : 1 < Work.Spaces.gam α := by
    rw [Work.Spaces.gam]
    have : 0 < α / 10 := by positivity
    linarith
  have hγne : Work.Spaces.gam α ≠ 0 := by linarith
  obtain ⟨Cg, hCgpos, hCg⟩ := sliceGamma (γ := Work.Spaces.gam α) hγ1
  refine ⟨Cg, hCgpos, fun N z hz => ?_⟩
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hwz : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hwz2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hwz)
  set G : ℝ → ℝ := fun θ => Work.Spaces.DzIter b f z θ with hGdef
  have hHk : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      (volume.restrict Work.Spaces.Iθ) := hmem.1 z hzI
  -- the mixed slot squared is integrable
  have hmixAesm : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _
      ((((hsm.mixed b 1).continuousOn).mul (continuousOn_Wt_quad α)).pow 2) hz
  have hmixInt : Integrable
      (fun θ : ℝ => (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    Integrable.mono' hHk hmixAesm (Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b le_rfl (by omega))
  -- the `γ`-weighted mixed slot is integrable
  have hmidInt : Integrable
      (fun θ : ℝ => (Work.Spaces.mixed b 1 f z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.congr (hmixInt.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_
    filter_upwards [ae_Ioo_of_restrict_Iθ] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, wt_sq_eq (α := α) hs,
      inv_mul_cancel_left₀ hwz2]
  -- the angular derivative integrand is integrable (a.e. equal to the previous one)
  have hderiv_eq : ∀ θ ∈ Set.Ioo 0 (π / 2),
      deriv G θ = Work.Spaces.mixed b 1 f z θ / Real.sin (2 * θ) := by
    intro θ hθ
    simpa only [hGdef, Work.Spaces.pth] using
      Work.FTS.GalBasis.cc.pth_dzIter_slice hsm hz hθ
  have hDint : Integrable
      (fun θ : ℝ => (deriv G θ) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.congr hmidInt ?_
    filter_upwards [ae_Ioo_of_restrict_Iθ] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [hderiv_eq θ hθ, sq_div_mul_rpow hs]
  -- the slice Hardy inequality `sliceGamma`
  have hGcd : ContDiffOn ℝ 1 G (Set.Ioo 0 (π / 2)) := by
    have hone : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder :=
      WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)
    simpa only [hGdef] using ((hsm.DzIter b).curry_θ hz).of_le hone
  obtain ⟨ht0, htπ⟩ := (hbT 0 b (by omega)).2 z hz
  have htr0 : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * G θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa only [hGdef, Work.Spaces.mixed_zero_right] using ht0
  have htrπ : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * G θ ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa only [hGdef, Work.Spaces.mixed_zero_right] using htπ
  obtain ⟨hGint, hGineq⟩ := hCg G hGcd htr0 htrπ hDint
  -- the layer integrand is `w²` times the trace density
  have hstep1 : (∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
        (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = Work.Spaces.w z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
            * (G θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
    rw [LN_slot_factor hγne hθ]
    simp only [hGdef]
    ring_nf
  -- the layer density is dominated by the full density
  have hnn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ G θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
    intro θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := by
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have hind_aesm : AEStronglyMeasurable
      (fun θ : ℝ => (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ)
      (volume.restrict Work.Spaces.Iθ) :=
    (measurable_const.indicator (Work.FTS.GalBasis.cc.measurableSet_LN N)).aestronglyMeasurable
  have hstep2 : (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
          * (G θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))))
      ≤ ∫ θ in Work.Spaces.Iθ, (G θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by
    have haesm := hind_aesm.mul hGint.aestronglyMeasurable
    have hlhs : Integrable
        (fun θ : ℝ => (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
          * (G θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))))
        (volume.restrict Work.Spaces.Iθ) := by
      refine Integrable.mono' hGint haesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
      by_cases h : θ ∈ Work.FTS.GalBasis.cc.LN N
      · rw [Real.norm_eq_abs, Set.indicator_of_mem h, one_mul,
          abs_of_nonneg (hnn θ hθ)]
      · rw [Real.norm_eq_abs, Set.indicator_of_notMem h, zero_mul, abs_zero]
        exact hnn θ hθ
    refine MeasureTheory.integral_mono_ae hlhs hGint ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
    by_cases h : θ ∈ Work.FTS.GalBasis.cc.LN N
    · rw [Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, zero_mul]
      exact hnn θ hθ
  -- slice Hardy
  have hstep3 : Work.Spaces.w z ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (G θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))))
      ≤ Work.Spaces.w z ^ 2 * (Cg * ∫ θ in Work.Spaces.Iθ,
          (deriv G θ) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_left hGineq (sq_nonneg _)
  -- identification with the mixed slot
  have hstep4 : Work.Spaces.w z ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (deriv G θ) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_Ioo_of_restrict_Iθ] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [hderiv_eq θ hθ, sq_div_mul_rpow hs, Work.Spaces.Wt, Work.Spaces.wTheta,
      ← wt_sq_eq (α := α) hs]
  have hstep5 : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ :=
    MeasureTheory.integral_mono_ae hmixInt hHk (Filter.Eventually.of_forall fun θ =>
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b le_rfl (by omega))
  calc (∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
        (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = Work.Spaces.w z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
            * (G θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := hstep1
    _ ≤ Work.Spaces.w z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (G θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_left hstep2 (sq_nonneg _)
    _ ≤ Work.Spaces.w z ^ 2 * (Cg * ∫ θ in Work.Spaces.Iθ,
          (deriv G θ) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)) := hstep3
    _ = Cg * (Work.Spaces.w z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (deriv G θ) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)) := by ring
    _ = Cg * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hstep4]
    _ ≤ Cg * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ :=
        mul_le_mul_of_nonneg_left hstep5 hCgpos.le

theorem LN_slot_tendsto {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn} {b : ℕ} (hb4 : b ≤ 3)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hbT : Work.FTS.Nonlin.BdryTraces α 4 f) :
    Filter.Tendsto (fun N : ℕ => ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Filter.atTop (nhds 0) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hγ1 : 1 < Work.Spaces.gam α := by
    rw [Work.Spaces.gam]
    have : 0 < α / 10 := by positivity
    linarith
  have hγne : Work.Spaces.gam α ≠ 0 := by linarith
  -- the two ingredients
  have hlayer : ∀ G : ℝ → ℝ,
      Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * G θ ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * G θ ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      Filter.Tendsto (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
            * (G θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))))
        Filter.atTop (nhds 0) :=
    fun G => LN_indicator_weighted_tendsto (γ := Work.Spaces.gam α) hγ1 (G := G)
  obtain ⟨C, hCpos, hCbnd⟩ :=
    LN_slot_slice_bound_priv (α := α) (f := f) (b := b) hα hb4 hsm hmem hbT
  -- the dominator
  have hKint : Integrable
      (fun z : ℝ => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      (volume.restrict Work.Spaces.Iz) :=
    (show Integrable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        (volume.restrict Work.Spaces.Iz) from hmem.2).const_mul C
  -- a.e. strong measurability of the radial marginal
  have haesm : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    intro N
    have h := (aesm_LN_slot (α := α) hsm b N).integral_prod_right'
      (μ := volume.restrict Work.Spaces.Iz)
    simpa only [Function.uncurry] using h
  -- the a.e. domination
  have hbound : ∀ N : ℕ, ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ‖(∫ θ in Work.Spaces.Iθ,
        (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)‖
        ≤ C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
    intro N
    filter_upwards [ae_pos_of_restrict_Iz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
      MeasureTheory.integral_nonneg fun θ => mul_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) θ) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    exact hCbnd N z hz
  -- the a.e. convergence
  have hconv : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Filter.atTop (nhds 0) := by
    filter_upwards [ae_pos_of_restrict_Iz] with z hz
    obtain ⟨ht0, htπ⟩ := (hbT 0 b (by omega)).2 z hz
    have ht0' : Filter.Tendsto
        (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.DzIter b f z θ) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa only [Work.Spaces.mixed_zero_right] using ht0
    have htπ' : Filter.Tendsto
        (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.DzIter b f z θ) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa only [Work.Spaces.mixed_zero_right] using htπ
    have hgen := hlayer (fun θ => Work.Spaces.DzIter b f z θ) ht0' htπ'
    have hmul : Filter.Tendsto (fun N : ℕ => Work.Spaces.w z ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
          * ((Work.Spaces.DzIter b f z θ) ^ 2
              * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))))
        Filter.atTop (nhds 0) := by
      simpa using hgen.const_mul (Work.Spaces.w z ^ 2)
    refine Filter.Tendsto.congr (fun N => ?_) hmul
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
        rw [LN_slot_factor hγne hθ]
        ring)
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iz)
    (F := fun (N : ℕ) (z : ℝ) => ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
        (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)
    (f := fun _ : ℝ => (0 : ℝ))
    (fun z : ℝ => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
    haesm hKint hbound hconv
  simpa only [MeasureTheory.integral_zero] using hmain

end Work.FTS.GalBasis.cut
