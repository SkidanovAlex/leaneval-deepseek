import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.far_vBound
import Submission.Work.FTS.EllipticEst.remov.sliceV2IntervalUniform
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceSelfForm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option maxHeartbeats 1000000

/-- **The angular self-form of `L₀` for a slice that is smooth on the open interval only.**
For `f` of class `C^∞` on `(0, π/2)`, continuous on `[0, π/2]`, with `f 0 = 0`, `f (π/2) = 0`
and `σ`-square-integrable second derivative (`σ = sEta`), the pairing of `Lzero1 f` with `f` is
the quadratic form `∫ (f')² + (1/2) ∫ (f/cos)² - 6 ∫ f²`. -/
private theorem sliceSelfForm (f : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n f (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv f t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)
        + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (f θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) := by
  have hlt : (0 : ℝ) < Real.pi / 2 := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- ### 1. Integrability of `f''` on the open interval.
  have hsq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv f t) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta f hint
  have habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv f t) θ|) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq f hsq
  have hf2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' habs
      (measurable_deriv (fun t : ℝ => deriv f t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => le_of_eq (Real.norm_eq_abs _))
  -- ### 2. The endpoint limits of `f`, from continuity on the closed interval.
  have hmem0' : Set.Ioo (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt),
      eventually_mem_nhdsWithin] with s hs hs'
    exact ⟨hs', hs⟩
  have hmem0 : Set.Icc (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_of_superset hmem0' (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hmempi' : Set.Ioo (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hlt]
    exact self_mem_nhdsWithin
  have hmempi : Set.Icc (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    mem_of_superset hmempi' (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hlim0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcw : ContinuousWithinAt f (Set.Icc (0 : ℝ) (Real.pi / 2)) 0 :=
      hcont.continuousWithinAt ⟨le_rfl, hlt.le⟩
    have hle : nhdsWithin (0 : ℝ) (Set.Ioi 0)
        ≤ nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2)) := nhdsWithin_le_iff.mpr hmem0
    simpa [h0] using hcw.mono_left hle
  have hlimpi : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hcw : ContinuousWithinAt f (Set.Icc (0 : ℝ) (Real.pi / 2)) (Real.pi / 2) :=
      hcont.continuousWithinAt ⟨by linarith, le_rfl⟩
    have hle : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))
        ≤ nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2)) := nhdsWithin_le_iff.mpr hmempi
    simpa [h1] using hcw.mono_left hle
  -- ### 3. The bounds `M` (for `f'`), `B` (for `f`) and `K` (for `f / cos`).
  obtain ⟨M, hM0, hM⟩ :=
    Work.FTS.EllipticEst.Honest.SelfAux.SliceDerivBound f (hsm 2) hf2
  have hlin : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * (Real.pi / 2 - θ) :=
    Work.FTS.EllipticEst.Honest.SelfAux.SliceULinearRight f (hsm 1) hM hlimpi
  have hB : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * (Real.pi / 2) := fun θ hθ =>
    (hlin θ hθ).trans (mul_le_mul_of_nonneg_left (by linarith [hθ.1]) hM0)
  obtain ⟨K, hK⟩ := Work.FTS.EllipticEst.Honest.SelfAux.SliceUDivCosBdd f hB hlin
  obtain ⟨hl0, hlpi⟩ :=
    Work.FTS.EllipticEst.Honest.SelfAux.SliceTendstoAntiderivZero f hlim0 hlimpi hM hB hK
  -- ### 4. Integrability of `Lzero1 f · f` (delegated) and of the three quadratic pieces.
  have hLint : MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Lzero1MulSelfIntegrable (hsm 2) hB hM hK habs
  have hderiv_cont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm 2).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hsq_int : MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (M ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact ((hderiv_cont.pow 2).aemeasurable measurableSet_Ioo).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM θ hθ) 2
  have hu2_int : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ ((M * (Real.pi / 2)) ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact (((hsm 1).continuousOn.pow 2).aemeasurable measurableSet_Ioo).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB θ hθ) 2
  have hdiv_cont : ContinuousOn (fun θ => f θ / Real.cos θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm 1).continuousOn.div Real.continuous_cos.continuousOn
      (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩))
  have hdiv2_int : MeasureTheory.IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (K ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact ((hdiv_cont.pow 2).aemeasurable measurableSet_Ioo).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hK θ hθ) 2
  -- ### 5. The fundamental theorem of calculus on the open interval.
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2)
        (Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
          - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2) θ :=
    fun θ hθ => Work.FTS.EllipticEst.Honest.SelfAux.SliceAntiderivDeriv f hθ
      ((hsm 2).contDiffAt (isOpen_Ioo.mem_nhds hθ))
  have h_ab : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := hLint.sub hsq_int
  have h_abc : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
        - (1 / 2) * (f θ / Real.cos θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    h_ab.sub (hdiv2_int.const_mul (1 / 2))
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
        - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    h_abc.add (hu2_int.const_mul 6)
  have hzero : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
        - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2) = 0 := by
    have h := Work.FTS.EllipticEst.Honest.integral_Ioo_eq_sub_of_tendsto hlt hderiv hGint hl0 hlpi
    simpa using h
  have hsplit : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
        - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2)
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 f θ * f θ)
        - (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv f θ) ^ 2)
        - (1 / 2) * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ / Real.cos θ) ^ 2)
        + 6 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2) := by
    rw [integral_add h_abc (hu2_int.const_mul 6),
      integral_sub h_ab (hdiv2_int.const_mul (1 / 2)),
      integral_sub hLint hsq_int, integral_const_mul, integral_const_mul]
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv f θ) ^ 2)
        + (1 / 2) * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2) := by
    linarith [hzero, hsplit]
  -- ### 6. Transfer the four integrals from `(0, π/2)` to `Iθ = [0, π/2]`.
  have e1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 f θ * f θ := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e2 : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv f θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e3 : (∫ θ in Work.Spaces.Iθ, (f θ / Real.cos θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ / Real.cos θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e4 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  rw [e1, e2, e3, e4]
  exact hmain

theorem AeSliceSelfForm (u : ℝ → ℝ → ℝ) (z : ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)))
    (h0 : u z 0 = 0) (h1 : u z (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv (fun θ' => u z θ') t) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => u z θ') θ) ^ 2)
        + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (u z θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
  have hL : ∀ θ : ℝ, Work.Elliptic.Lzero u z θ
      = Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => u z θ') θ := by
    intro θ
    rw [Work.Elliptic.Lzero_eq_deriv, Work.FTS.EllipticEst.Lzero1]
  simp only [hL]
  exact sliceSelfForm (fun θ' : ℝ => u z θ') hsm hcont h0 h1 hint

end Work.FTS.EllipticEst.H2W.AeProof
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.weakHetaBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology Interval



end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonSliceSelfForm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

/-!
## The angular self-form of `L₀` for an honestly smooth slice

`Lzero1 u = -u'' + (tan · u)' - 6u` is the angular part of the elliptic operator of the
straightened Elgindi coordinates.  For a function which is `C^∞` on the *open* interval
`(0, π/2)`, continuous on `[0, π/2]` and vanishes at both endpoints, with `(u'')² σ`
integrable (`σ = sin(2θ)^{-η}`, `η = 99/100`), the pointwise antiderivative identity

  `F' = Lzero1 u · u - (u')² - (1/2) (u/cos)² + 6 u²`,   `F θ = -u'(θ) u(θ) + (1/2) tan θ · u(θ)²`

integrates over `(0, π/2)` to the quadratic form, because `F → 0` at both endpoints and
`Lzero1 u · u` is integrable there.  The endpoint behaviour is not free: the hypothesis
`(u'')² σ ∈ L¹` (with `σ ≥ 1` on `(0,π/2)`) is what forces `u'` to be bounded and hence
`u = O(θ) = O(π/2 - θ)` near the ends.

The file contains, before the target, two private helpers for the integrability of
`Lzero1 u · u`, proved from scratch (the remaining information comes from the shared
modules `HonSliceBounds`, `HonAntiderivTendsto`, `HonSelfDeriv` and
`sliceLimitLeftExists`).
-/

/-! ## Integrability of `Lzero1 u · u` on the open interval -/




/-! ## The target -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.LzeroSelfFormHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


/-! ## Auxiliary slice estimates -/







/-! ## The target -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SliceIbpTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory

/-- A function with an *everywhere* derivative `deriv φ` on the open interval `(a,b)` whose
derivative is integrable there is bounded on `(a,b)`: the total variation
`∫_{(a,b)} |φ'|` is finite, so `φ` is absolutely continuous and extends continuously to the
closed interval.  (Nothing is assumed off `(a,b)`: only the values of `deriv φ` on `(a,b)`
enter the hypotheses and the conclusion.) -/
theorem bdd_of_integrableOn_deriv {a b : ℝ} (hab : a < b) {φ : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt φ (deriv φ x) x)
    (hint : MeasureTheory.IntegrableOn (deriv φ) (Set.Ioo a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo a b, |φ θ| ≤ C := by
  -- A reference point in the interior and the total variation of the derivative.
  set c : ℝ := (a + b) / 2 with hcdef
  have hac : a < c := by rw [hcdef]; linarith
  have hcb : c < b := by rw [hcdef]; linarith
  set M : ℝ := ∫ x in Set.Ioo a b, |deriv φ x| with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => abs_nonneg (deriv φ x))
  have hIntAbs : IntegrableOn (fun x => |deriv φ x|) (Set.Ioo a b) := by
    simpa only [Real.norm_eq_abs, IntegrableOn] using hint.abs
  -- On the whole interval, `φ` moves by at most the total variation of its derivative.
  have key : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, x ≤ y → |φ y - φ x| ≤ M := by
    intro x hx y hy hxy
    have hsubIcc : Set.uIcc x y ⊆ Set.Ioo a b := by
      rw [Set.uIcc_of_le hxy]
      intro t ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    have hsub1 : Set.Ioc x y ⊆ Set.Ioo a b := fun t ht =>
      ⟨lt_trans hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    have hsub2 : Set.Ioc y x ⊆ Set.Ioo a b := fun t ht =>
      ⟨lt_trans hy.1 ht.1, lt_of_le_of_lt ht.2 hx.2⟩
    have hInt : MeasureTheory.IntegrableOn (deriv φ) (Set.Ioc x y) := hint.mono_set hsub1
    have hInt' : MeasureTheory.IntegrableOn (deriv φ) (Set.Ioc y x) := hint.mono_set hsub2
    have hftc : ∫ t in x..y, deriv φ t = φ y - φ x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := φ)
        (fun t ht => hderiv t (hsubIcc ht)) ⟨hInt, hInt'⟩
    have hMI : ∫ t in x..y, |deriv φ t| ≤ M := by
      rw [hMdef, intervalIntegral.integral_of_le hxy]
      refine setIntegral_mono_set hIntAbs
        (Filter.Eventually.of_forall fun t => abs_nonneg (deriv φ t)) ?_
      filter_upwards with t ht
      exact ⟨lt_trans hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    calc |φ y - φ x| = |∫ t in x..y, deriv φ t| := by rw [hftc]
      _ ≤ ∫ t in x..y, |deriv φ t| := intervalIntegral.abs_integral_le_integral_abs hxy
      _ ≤ M := hMI
  have key' : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, |φ y - φ x| ≤ M := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · exact key x hx y hy hxy
    · rw [abs_sub_comm]
      exact key y hy x hx hyx
  refine ⟨|φ c| + M, add_nonneg (abs_nonneg (φ c)) hMnn, ?_⟩
  intro θ hθ
  have h1 : |φ θ - φ c| ≤ M := key' c ⟨hac, hcb⟩ θ hθ
  calc |φ θ| = |φ c + (φ θ - φ c)| := by rw [show φ c + (φ θ - φ c) = φ θ by ring]
    _ ≤ |φ c| + |φ θ - φ c| := abs_add_le _ _
    _ ≤ |φ c| + M := add_le_add le_rfl h1

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.psi_boundary_vanish =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

open Work.FTS.EllipticEst.TanTheta (psi wrho wrhoD wrho_eq_half_sin_rpow wrho_deriv)

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The angular interval `(0, π/2)` of the slice. -/
local notation "Iθ" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The exponent `η = 99/100` of the paper. -/
local notation "eη" => Work.Spaces.eta

/-! ## Elementary angular facts -/

private lemma pi_half_pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]

private lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Iθ) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sin_two_le_one_prv {θ : ℝ} (hθ : θ ∈ Iθ) : Real.sin (2 * θ) ≤ 1 :=
  Real.sin_le_one _

private lemma cos_pos {θ : ℝ} (hθ : θ ∈ Iθ) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

private lemma sig_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ AngSecond.sig θ :=
  AngSecond.sig_nonneg ⟨hθ.1.le, hθ.2.le⟩

private lemma sig_pos {θ : ℝ} (hθ : θ ∈ Iθ) : 0 < AngSecond.sig θ :=
  Real.rpow_pos_of_pos (sin_two_pos hθ) _

private lemma continuousOn_wrho : ContinuousOn (wrho eη) Iθ := by
  change ContinuousOn
    (fun θ : ℝ => Real.sin θ * Real.cos θ * (Real.sin (2 * θ)) ^ (-(eη))) Iθ
  refine (Real.continuous_sin.continuousOn.mul Real.continuous_cos.continuousOn).mul ?_
  exact ContinuousOn.rpow_const
    (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2))
    (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))

private lemma continuousOn_wrhoD : ContinuousOn (wrhoD eη) Iθ := by
  change ContinuousOn
    (fun θ : ℝ => (1 - eη) * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(eη))) Iθ
  refine (continuousOn_const.mul
    (Real.continuous_cos.comp_continuousOn (continuousOn_id.const_mul 2))).mul ?_
  exact ContinuousOn.rpow_const
    (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2))
    (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))

/-! ## The algebra of the weight `ρ` against `σ = sin(2θ)^{-η}` -/

/-- On the open interval, `ρ = ((1/2) sin 2θ) · σ`. -/
private lemma wrho_eq_half_sin_mul_sig {θ : ℝ} (hθ : θ ∈ Iθ) :
    wrho eη θ = (1 / 2 * Real.sin (2 * θ)) * AngSecond.sig θ := by
  rw [wrho_eq_half_sin_rpow _ hθ]
  have hs := sin_two_pos hθ
  have h1 : (Real.sin (2 * θ)) ^ (1 - eη)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(eη)) := by
    rw [show 1 - eη = 1 + (-(eη)) by ring, Real.rpow_add hs, Real.rpow_one]
  rw [h1, AngSecond.sig]
  ring

private lemma wrho_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ wrho eη θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (sin_two_pos hθ))) (sig_nonneg hθ)


/-- `ρ ≤ σ` on the open interval. -/
private lemma wrho_le_sig {θ : ℝ} (hθ : θ ∈ Iθ) : wrho eη θ ≤ AngSecond.sig θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  have hsig := sig_nonneg hθ
  have h : (1 / 2 * Real.sin (2 * θ)) ≤ 1 := by
    have := sin_two_le_one_prv hθ; linarith
  calc (1 / 2 * Real.sin (2 * θ)) * AngSecond.sig θ ≤ 1 * AngSecond.sig θ :=
        mul_le_mul_of_nonneg_right h hsig
    _ = AngSecond.sig θ := one_mul _

/-- `ρ ≤ θ · σ` on the open interval (used as `θ → 0⁺`). -/
private lemma wrho_le_mul_sig_right {θ : ℝ} (hθ : θ ∈ Iθ) :
    wrho eη θ ≤ θ * AngSecond.sig θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  refine mul_le_mul_of_nonneg_right ?_ (sig_nonneg hθ)
  have h2 := Real.sin_le (show (0 : ℝ) ≤ 2 * θ by linarith [hθ.1])
  linarith

/-- `ρ ≤ (π/2 - θ) · σ` on the open interval (used as `θ → π/2⁻`). -/
private lemma wrho_le_mul_sig_left {θ : ℝ} (hθ : θ ∈ Iθ) :
    wrho eη θ ≤ (Real.pi / 2 - θ) * AngSecond.sig θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  refine mul_le_mul_of_nonneg_right ?_ (sig_nonneg hθ)
  have h0 : (0 : ℝ) ≤ Real.pi - 2 * θ := by linarith [hθ.2]
  have h2 := Real.sin_le h0
  rw [Real.sin_pi_sub] at h2
  linarith

/-- `ρ · tan θ ≤ σ` on the open interval. -/
private lemma wrho_mul_tan_le_sig {θ : ℝ} (hθ : θ ∈ Iθ) :
    wrho eη θ * (Real.sin θ / Real.cos θ) ≤ AngSecond.sig θ := by
  rw [wrho_eq_half_sin_mul_sig hθ]
  have hsig := sig_pos hθ
  have hc : Real.cos θ ≠ 0 := ne_of_gt (cos_pos hθ)
  have hkey : (1 / 2 * Real.sin (2 * θ)) * (Real.sin θ / Real.cos θ) = (Real.sin θ) ^ 2 := by
    rw [Real.sin_two_mul]
    field_simp
  calc ((1 / 2 * Real.sin (2 * θ)) * AngSecond.sig θ) * (Real.sin θ / Real.cos θ)
      = ((1 / 2 * Real.sin (2 * θ)) * (Real.sin θ / Real.cos θ)) * AngSecond.sig θ := by ring
    _ = (Real.sin θ) ^ 2 * AngSecond.sig θ := by rw [hkey]
    _ ≤ 1 * AngSecond.sig θ :=
        mul_le_mul_of_nonneg_right (Real.sin_sq_le_one θ) hsig.le
    _ = AngSecond.sig θ := one_mul _

/-- `|ρ'| ≤ (1-η) σ`. -/
private lemma abs_wrhoD_le_sig {θ : ℝ} (hθ : θ ∈ Iθ) :
    |wrhoD eη θ| ≤ (1 - eη) * AngSecond.sig θ := by
  change |(1 - eη) * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(eη))|
      ≤ (1 - eη) * AngSecond.sig θ
  rw [AngSecond.sig]
  have h1 : 0 ≤ 1 - eη := by linarith [Work.Spaces.eta_lt_one]
  have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(eη)) :=
    (Real.rpow_pos_of_pos (sin_two_pos hθ) _).le
  rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
  have h3 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  calc (1 - eη) * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(eη))
      ≤ (1 - eη) * 1 * (Real.sin (2 * θ)) ^ (-(eη)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 h1) h2
    _ = (1 - eη) * (Real.sin (2 * θ)) ^ (-(eη)) := by ring

/-- `sin(2θ)^{2-η} = sin(2θ)² σ`. -/
private lemma sin_two_pow_two_sub_eta_eq {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ)) ^ (2 - eη)
      = (Real.sin (2 * θ)) ^ 2 * AngSecond.sig θ := by
  have hs := sin_two_pos hθ
  rw [show (2 : ℝ) - eη = 2 + (-(eη)) by ring, Real.rpow_add hs, Real.rpow_two, pow_two,
    AngSecond.sig]

/-- `sin(2θ)^{2-η} / cos²θ ≤ 4 σ` on the open interval. -/
private lemma sin_two_pow_two_sub_eta_div_cos_sq_le {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ)) ^ (2 - eη) / (Real.cos θ) ^ 2 ≤ 4 * AngSecond.sig θ := by
  rw [sin_two_pow_two_sub_eta_eq hθ]
  have hc := cos_pos hθ
  have hcs : 0 < (Real.cos θ) ^ 2 := sq_pos_of_pos hc
  rw [div_le_iff₀ hcs]
  have hsig := sig_nonneg hθ
  have hs2 : (Real.sin (2 * θ)) ^ 2 = 4 * (Real.sin θ) ^ 2 * (Real.cos θ) ^ 2 := by
    rw [Real.sin_two_mul]; ring
  rw [hs2]
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hX : 0 ≤ (Real.cos θ) ^ 2 * AngSecond.sig θ := mul_nonneg hcs.le hsig
  calc 4 * (Real.sin θ) ^ 2 * (Real.cos θ) ^ 2 * AngSecond.sig θ
      = 4 * ((Real.cos θ) ^ 2 * AngSecond.sig θ) * (Real.sin θ) ^ 2 := by ring
    _ ≤ 4 * ((Real.cos θ) ^ 2 * AngSecond.sig θ) * 1 :=
        mul_le_mul_of_nonneg_left hsin (by linarith)
    _ = 4 * AngSecond.sig θ * (Real.cos θ) ^ 2 := by ring

/-- The weighted AM–GM inequality for the mixed term `2ρ|A|(|B|/cos θ)`. -/
private lemma two_wrho_mul_le {θ : ℝ} (hθ : θ ∈ Iθ) (A B : ℝ) :
    2 * wrho eη θ * |A| * (|B| / Real.cos θ)
      ≤ (1 / 2) * (AngSecond.sig θ * A ^ 2) + 2 * (AngSecond.sig θ * B ^ 2) := by
  have hs := sin_two_pos hθ
  have hρ := wrho_eq_half_sin_mul_sig hθ
  set X : ℝ := (Real.sin (2 * θ)) ^ (-(eη) / 2) * |A| with hX
  set Y : ℝ := (Real.sin (2 * θ)) ^ ((2 - eη) / 2) * (|B| / Real.cos θ) with hY
  have hsq : (Real.sin (2 * θ)) ^ (-(eη) / 2) * (Real.sin (2 * θ)) ^ ((2 - eη) / 2)
      = Real.sin (2 * θ) * AngSecond.sig θ := by
    rw [← Real.rpow_add hs, show -(eη) / 2 + (2 - eη) / 2 = 1 - eη by ring,
      show (1 : ℝ) - eη = 1 + (-(eη)) by ring, Real.rpow_add hs, Real.rpow_one]
    rfl
  have hLHS : 2 * wrho eη θ * |A| * (|B| / Real.cos θ) = X * Y := by
    rw [hX, hY, hρ]
    calc 2 * ((1 / 2 * Real.sin (2 * θ)) * AngSecond.sig θ) * |A| * (|B| / Real.cos θ)
        = ((Real.sin (2 * θ)) ^ (-(eη) / 2) * (Real.sin (2 * θ)) ^ ((2 - eη) / 2)) * |A|
            * (|B| / Real.cos θ) := by rw [hsq]; ring
      _ = ((Real.sin (2 * θ)) ^ (-(eη) / 2) * |A|)
            * ((Real.sin (2 * θ)) ^ ((2 - eη) / 2) * (|B| / Real.cos θ)) := by ring
  have hXs : X ^ 2 = AngSecond.sig θ * A ^ 2 := by
    rw [hX, mul_pow]
    have h1 : ((Real.sin (2 * θ)) ^ (-(eη) / 2)) ^ 2 = AngSecond.sig θ := by
      rw [pow_two, ← Real.rpow_add hs, show -(eη) / 2 + -(eη) / 2 = -(eη) by ring]
      rfl
    rw [h1, sq_abs]
  have hYs : Y ^ 2 ≤ 4 * (AngSecond.sig θ * B ^ 2) := by
    rw [hY, mul_pow]
    have h1 : ((Real.sin (2 * θ)) ^ ((2 - eη) / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (2 - eη) := by
      rw [pow_two, ← Real.rpow_add hs, show (2 - eη) / 2 + (2 - eη) / 2 = 2 - eη by ring]
    rw [h1]
    have hd : (|B| / Real.cos θ) ^ 2 = B ^ 2 / (Real.cos θ) ^ 2 := by
      rw [div_pow, sq_abs]
    rw [hd]
    calc (Real.sin (2 * θ)) ^ (2 - eη) * (B ^ 2 / (Real.cos θ) ^ 2)
        = ((Real.sin (2 * θ)) ^ (2 - eη) / (Real.cos θ) ^ 2) * B ^ 2 := by ring
      _ ≤ (4 * AngSecond.sig θ) * B ^ 2 :=
          mul_le_mul_of_nonneg_right (sin_two_pow_two_sub_eta_div_cos_sq_le hθ) (sq_nonneg B)
      _ = 4 * (AngSecond.sig θ * B ^ 2) := by ring
  have h2 : 2 * X * Y ≤ X ^ 2 + Y ^ 2 := two_mul_le_add_sq X Y
  have h2' : 2 * X * Y = 2 * (2 * wrho eη θ * |A| * (|B| / Real.cos θ)) := by
    rw [show 2 * X * Y = 2 * (X * Y) by ring, hLHS]
  rw [hLHS]
  linarith [h2, h2', hXs, hYs]

/-- `2|a||b| ≤ a² + b²`. -/
private lemma two_mul_abs_mul_le_prv (a b : ℝ) : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
  have h := two_mul_le_add_sq |a| |b|
  rwa [sq_abs, sq_abs] at h

/-! ## The second derivative of the slice variable -/

/-- **Leibniz for the slice variable.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then
`u''(θ) = ψ''(θ) cos θ - 2 ψ'(θ) sin θ - ψ(θ) cos θ` with `ψ = u / cos`.
(Copy of the private companion of `Work.FTS.EllipticEst.TanTheta.psi_second_deriv`, stated for
`ContDiffAt` so that it applies to the honest hypotheses on the open interval.) -/
private lemma deriv_deriv_eq_div_cos_at (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    deriv (deriv u) θ
      = deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ * Real.cos θ
        - 2 * deriv (fun t : ℝ => u t / Real.cos t) θ * Real.sin θ
        - (u θ / Real.cos θ) * Real.cos θ := by
  obtain ⟨s, hs_mem, hs_reg⟩ := hu.contDiffOn le_rfl (by simp)
  have hmem : interior s ∈ 𝓝 θ :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs_mem)
  have hreg : ContDiffOn ℝ 2 u (interior s) := hs_reg.mono interior_subset
  have hdiff : ∀ t ∈ interior s, DifferentiableAt ℝ u t := fun t ht =>
    (hreg.differentiableOn (by simp)).differentiableAt (isOpen_interior.mem_nhds ht)
  have hcos_nhds : ∀ᶠ t in 𝓝 θ, Real.cos t ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hcos
  have heq_deriv : deriv u =ᶠ[𝓝 θ]
      fun t : ℝ =>
        deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t - (u t / Real.cos t) * Real.sin t := by
    filter_upwards [hcos_nhds, hmem] with t ht hts
    have heqt : u =ᶠ[𝓝 t] fun s : ℝ => (u s / Real.cos s) * Real.cos s := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne ht] with s hs
      exact (div_mul_cancel₀ (u s) hs).symm
    have hd : deriv (fun s : ℝ => (u s / Real.cos s) * Real.cos s) t
        = deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
          + (u t / Real.cos t) * (-Real.sin t) := by
      have hVt : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) t :=
        (hdiff t hts).div Real.differentiableAt_cos ht
      have h3 : HasDerivAt (fun s : ℝ => (u s / Real.cos s) * Real.cos s)
          (deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
            + (u t / Real.cos t) * (-Real.sin t)) t :=
        hVt.hasDerivAt.mul (Real.hasDerivAt_cos t)
      exact h3.deriv
    rw [heqt.deriv_eq, hd]
    ring
  rw [heq_deriv.deriv_eq]
  have hVd : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) θ :=
    (hu.div (Real.contDiff_cos.contDiffAt) hcos).differentiableAt (by simp)
  have hDd : DifferentiableAt ℝ (deriv (fun s : ℝ => u s / Real.cos s)) θ :=
    ((hu.div (Real.contDiff_cos.contDiffAt) hcos).derivWithin (m := 1) (by norm_num)
      ).differentiableAt (by simp)
  have h1 : HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t)
      (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
        + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ)) θ :=
    hDd.hasDerivAt.mul (Real.hasDerivAt_cos θ)
  have h2 : HasDerivAt (fun t : ℝ => (u t / Real.cos t) * Real.sin t)
      (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
        + (u θ / Real.cos θ) * Real.cos θ) θ :=
    hVd.hasDerivAt.mul (Real.hasDerivAt_sin θ)
  have h3 := h1.sub h2
  have h4 : deriv (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
        - (u t / Real.cos t) * Real.sin t) θ
      = (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
          + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ))
        - (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
            + (u θ / Real.cos θ) * Real.cos θ) := h3.deriv
  rw [h4]
  ring

/-- **The Leibniz identity for `ψ = u / cos`**, in the form used below:
`cos θ · ψ'' θ = u''(θ) + 2 sin θ · ψ' θ + cos θ · ψ θ`. -/
private lemma psi_second_deriv_Ioo (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u Iθ) {θ : ℝ}
    (hθ : θ ∈ Iθ) :
    Real.cos θ * deriv (deriv (psi u)) θ
      = deriv (deriv u) θ + 2 * deriv (psi u) θ * Real.sin θ + psi u θ * Real.cos θ := by
  have hc : Real.cos θ ≠ 0 := ne_of_gt (cos_pos hθ)
  have h := deriv_deriv_eq_div_cos_at u (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)) hc
  change Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
      = deriv (deriv u) θ + 2 * deriv (fun t : ℝ => u t / Real.cos t) θ * Real.sin θ
        + (u θ / Real.cos θ) * Real.cos θ
  rw [h]; ring

/-! ## The divergence of `∫ dt / t` at the right endpoint -/

/-- **`c/(π/2 - θ)` is not integrable near `π/2`.**  Obtained from the divergence of `∫ dt/t`
at `0` (`Work.FTS.EllipticEst.Honest.not_integrableOn_div_of_ge_const`) by the reflection
`θ ↦ π/2 - θ` (`IntervalIntegrable.comp_sub_left_iff`). -/
private lemma not_integrableOn_right {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ¬ IntegrableOn (fun θ : ℝ => c / (Real.pi / 2 - θ))
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
  have hleft : ¬ IntegrableOn (fun u : ℝ => c / u) (Set.Ioo (0 : ℝ) δ) := by
    have h := not_integrableOn_div_of_ge_const (F := fun _ : ℝ => c) hc hδ
      (fun t _ => le_refl c)
    simpa using h
  intro hI
  have hle : Real.pi / 2 - δ ≤ Real.pi / 2 := by linarith
  have hII : IntervalIntegrable (fun θ : ℝ => c / (Real.pi / 2 - θ)) volume
      (Real.pi / 2 - δ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mpr hI
  have hiff := (IntervalIntegrable.comp_sub_left_iff (f := fun u : ℝ => c / u)
    (a := δ) (b := 0) (Real.pi / 2) (by simp)).mp
  have hII' : IntervalIntegrable (fun u : ℝ => c / u) volume δ 0 := by
    apply hiff
    simpa using hII
  have hII'' : IntervalIntegrable (fun u : ℝ => c / u) volume (0 : ℝ) δ := hII'.symm
  exact hleft ((intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).mp hII'')

/-! ## A positive limit is impossible -/

/-- If `F = ρ W² ≥ 0` on `(0, π/2)` with `∫ σ W² < ∞`, then a limit of `F` at `0⁺` must be
`0`: a positive limit forces `σ W² ≥ c/t`, whose integral diverges. -/
private lemma eq_zero_of_tendsto_right {F W : ℝ → ℝ} {L : ℝ}
    (hL : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hFnn : ∀ x ∈ Iθ, 0 ≤ F x)
    (hFW : ∀ x ∈ Iθ, F x = wrho eη x * (W x) ^ 2)
    (hWint : IntegrableOn (fun x => AngSecond.sig x * (W x) ^ 2) Iθ) : L = 0 := by
  have hLnn : 0 ≤ L :=
    ge_of_tendsto hL (by
      filter_upwards [Ioo_mem_nhdsGT pi_half_pos] with x hx
      exact hFnn x hx)
  by_contra hne
  have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hne)
  have hm : Set.Ioi (L / 2) ∈ 𝓝 L := Ioi_mem_nhds (by linarith)
  have hev : {x : ℝ | L / 2 < F x} ∈ 𝓝[>] (0 : ℝ) := hL hm
  obtain ⟨b, hb, hbsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hbpos : (0 : ℝ) < b := hb
  set δ : ℝ := min b (Real.pi / 2) with hδ
  have hδpos : 0 < δ := lt_min hbpos pi_half_pos
  have hδle : δ ≤ Real.pi / 2 := min_le_right _ _
  have hδsub : Set.Ioo (0 : ℝ) δ ⊆ Iθ := fun x hx =>
    ⟨hx.1, lt_of_lt_of_le hx.2 hδle⟩
  have hkey : ∀ t ∈ Set.Ioo (0 : ℝ) δ, L / 2 ≤ t * (AngSecond.sig t * (W t) ^ 2) := by
    intro t ht
    have htI : t ∈ Iθ := hδsub ht
    have htb : t ∈ Set.Ioo (0 : ℝ) b := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    have hFt : L / 2 < F t := hbsub htb
    rw [hFW t htI] at hFt
    have hρle : wrho eη t ≤ t * AngSecond.sig t := wrho_le_mul_sig_right htI
    calc L / 2 ≤ wrho eη t * (W t) ^ 2 := le_of_lt hFt
      _ ≤ (t * AngSecond.sig t) * (W t) ^ 2 :=
          mul_le_mul_of_nonneg_right hρle (sq_nonneg _)
      _ = t * (AngSecond.sig t * (W t) ^ 2) := by ring
  have hnot := not_integrableOn_div_of_ge_const
    (F := fun t : ℝ => t * (AngSecond.sig t * (W t) ^ 2)) (by linarith : 0 < L / 2) hδpos hkey
  have heq : Set.EqOn (fun t : ℝ => (t * (AngSecond.sig t * (W t) ^ 2)) / t)
      (fun t => AngSecond.sig t * (W t) ^ 2) (Set.Ioo (0 : ℝ) δ) := by
    intro t ht
    rw [div_eq_iff (ne_of_gt ht.1)]
    ring
  have hnot' : ¬ IntegrableOn (fun t => AngSecond.sig t * (W t) ^ 2)
      (Set.Ioo (0 : ℝ) δ) := by
    intro h
    exact hnot (h.congr_fun heq.symm measurableSet_Ioo)
  exact hnot' (hWint.mono_set hδsub)

/-- If `F = ρ W² ≥ 0` on `(0, π/2)` with `∫ σ W² < ∞`, then a limit of `F` at `π/2⁻` must be
`0`. -/
private lemma eq_zero_of_tendsto_left {F W : ℝ → ℝ} {L : ℝ}
    (hL : Tendsto F (𝓝[<] (Real.pi / 2)) (𝓝 L))
    (hFnn : ∀ x ∈ Iθ, 0 ≤ F x)
    (hFW : ∀ x ∈ Iθ, F x = wrho eη x * (W x) ^ 2)
    (hWint : IntegrableOn (fun x => AngSecond.sig x * (W x) ^ 2) Iθ) : L = 0 := by
  have hLnn : 0 ≤ L :=
    ge_of_tendsto hL (by
      filter_upwards [Ioo_mem_nhdsLT pi_half_pos] with x hx
      exact hFnn x hx)
  by_contra hne
  have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hne)
  have hm : Set.Ioi (L / 2) ∈ 𝓝 L := Ioi_mem_nhds (by linarith)
  have hev : {x : ℝ | L / 2 < F x} ∈ 𝓝[<] (Real.pi / 2) := hL hm
  obtain ⟨b, hb, hbsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  have hblt : b < Real.pi / 2 := hb
  set δ : ℝ := min (Real.pi / 2 - b) (Real.pi / 2) with hδ
  have hδle1 : δ ≤ Real.pi / 2 - b := min_le_left _ _
  have hδle2 : δ ≤ Real.pi / 2 := min_le_right _ _
  have hδpos : 0 < δ := lt_min (by linarith) pi_half_pos
  have hδsub : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Iθ := by
    intro x hx
    exact ⟨by linarith [hx.1, hδle2], hx.2⟩
  have hkey : ∀ t ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
      L / 2 ≤ (Real.pi / 2 - t) * (AngSecond.sig t * (W t) ^ 2) := by
    intro t ht
    have htI : t ∈ Iθ := hδsub ht
    have htb : t ∈ Set.Ioo b (Real.pi / 2) := by
      exact ⟨by linarith [ht.1, hδle1], ht.2⟩
    have hFt : L / 2 < F t := hbsub htb
    rw [hFW t htI] at hFt
    have hρle : wrho eη t ≤ (Real.pi / 2 - t) * AngSecond.sig t :=
      wrho_le_mul_sig_left htI
    calc L / 2 ≤ wrho eη t * (W t) ^ 2 := le_of_lt hFt
      _ ≤ ((Real.pi / 2 - t) * AngSecond.sig t) * (W t) ^ 2 :=
          mul_le_mul_of_nonneg_right hρle (sq_nonneg _)
      _ = (Real.pi / 2 - t) * (AngSecond.sig t * (W t) ^ 2) := by ring
  have hcomp : IntegrableOn (fun t : ℝ => (L / 2) / (Real.pi / 2 - t))
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
    refine Integrable.mono' (hWint.mono_set hδsub) ?_ ?_
    · have hcont : ContinuousOn (fun t : ℝ => (L / 2) / (Real.pi / 2 - t))
          (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
        refine continuousOn_const.div (continuousOn_const.sub continuousOn_id) ?_
        intro t ht
        linarith [ht.2]
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hpos : 0 < Real.pi / 2 - t := by linarith [ht.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hpos.le)]
      rw [div_le_iff₀ hpos]
      calc L / 2 ≤ (Real.pi / 2 - t) * (AngSecond.sig t * (W t) ^ 2) := hkey t ht
        _ = (AngSecond.sig t * (W t) ^ 2) * (Real.pi / 2 - t) := by ring
  exact not_integrableOn_right (by linarith : 0 < L / 2) hδpos hcomp

/-! ## The main theorem -/

set_option maxHeartbeats 1600000 in
theorem psi_boundary_vanish (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hB : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA' : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (u θ / Real.cos θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (u θ / Real.cos θ) ^ 2) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  -- ## Smoothness of the slice variable and its derivatives
  have hψcd : ContDiffOn ℝ 2 (psi u) Iθ :=
    hu.div Real.contDiff_cos.contDiffOn (fun θ hθ => ne_of_gt (cos_pos hθ))
  have hψcont : ContinuousOn (psi u) Iθ := hψcd.continuousOn
  have hψ1d : ∀ θ ∈ Iθ, HasDerivAt (psi u) (deriv (psi u) θ) θ := fun θ hθ =>
    ((hψcd.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hψ1cd : ContDiffOn ℝ 1 (deriv (psi u)) Iθ :=
    hψcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hψ1cont : ContinuousOn (deriv (psi u)) Iθ := hψ1cd.continuousOn
  have hψ2cd : ContDiffOn ℝ 0 (deriv (deriv (psi u))) Iθ :=
    hψ1cd.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
  have hψ2cont : ContinuousOn (deriv (deriv (psi u))) Iθ := hψ2cd.continuousOn
  have hψ2d : ∀ θ ∈ Iθ, HasDerivAt (deriv (psi u)) (deriv (deriv (psi u)) θ) θ := fun θ hθ =>
    ((hψ1cd.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  -- ## Lebesgue integrability of the three basic weights
  have hSg : IntegrableOn (fun θ => AngSecond.sig θ * (psi u θ) ^ 2) Iθ := by
    change IntegrableOn (fun θ => AngSecond.sig θ * (u θ / Real.cos θ) ^ 2) Iθ
    exact hA.congr_fun (fun θ _ => by ring) measurableSet_Ioo
  have hSg1 : IntegrableOn (fun θ => AngSecond.sig θ * (deriv (psi u) θ) ^ 2) Iθ := by
    change IntegrableOn
      (fun θ => AngSecond.sig θ * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2) Iθ
    exact hA'.congr_fun (fun θ _ => by ring) measurableSet_Ioo
  have hSgu : IntegrableOn (fun θ => AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) Iθ :=
    hX.congr_fun (fun θ _ => by ring) measurableSet_Ioo
  have hRho : IntegrableOn (fun θ => wrho eη θ * (psi u θ) ^ 2) Iθ := by
    refine Integrable.mono' hSg ?_ ?_
    · exact (continuousOn_wrho.mul (hψcont.pow 2)).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wrho_nonneg hθ) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _)
  have hRho1 : IntegrableOn (fun θ => wrho eη θ * (deriv (psi u) θ) ^ 2) Iθ := by
    refine Integrable.mono' hSg1 ?_ ?_
    · exact (continuousOn_wrho.mul (hψ1cont.pow 2)).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wrho_nonneg hθ) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _)
  -- ## The two derivative functions
  have hF1d : ∀ θ ∈ Iθ, HasDerivAt (fun t => wrho eη t * (psi u t) ^ 2)
      (wrhoD eη θ * (psi u θ) ^ 2 + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)) θ := by
    intro θ hθ
    have h1 := wrho_deriv eη hθ
    have h2 : HasDerivAt (fun t => (psi u t) ^ 2) (2 * psi u θ * deriv (psi u) θ) θ := by
      have hp := (hψ1d θ hθ).pow 2
      refine hp.congr_deriv ?_
      push_cast
      ring
    have h3 := h1.mul h2
    convert h3 using 1
  have hF2d : ∀ θ ∈ Iθ, HasDerivAt (fun t => wrho eη t * (deriv (psi u) t) ^ 2)
      (wrhoD eη θ * (deriv (psi u) θ) ^ 2
        + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)) θ := by
    intro θ hθ
    have h1 := wrho_deriv eη hθ
    have h2 : HasDerivAt (fun t => (deriv (psi u) t) ^ 2)
        (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ) θ := by
      have hp := (hψ2d θ hθ).pow 2
      refine hp.congr_deriv ?_
      push_cast
      ring
    have h3 := h1.mul h2
    convert h3 using 1
  -- ## The dominating integrable function
  have hDm : IntegrableOn (fun θ => AngSecond.sig θ * (psi u θ) ^ 2
      + AngSecond.sig θ * (deriv (psi u) θ) ^ 2
      + AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) Iθ :=
    (hSg.add hSg1).add hSgu
  -- ## Integrability of the derivative of `ρψ²`
  have hG1int : IntegrableOn (fun θ => wrhoD eη θ * (psi u θ) ^ 2
      + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)) Iθ := by
    refine Integrable.mono' (hDm.const_mul 10) ?_ ?_
    · refine ((continuousOn_wrhoD.mul (hψcont.pow 2)).add
        (continuousOn_wrho.mul ((continuousOn_const.mul hψcont).mul hψ1cont))).aestronglyMeasurable
        measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hsig := sig_nonneg hθ
      have hρ0 := wrho_nonneg hθ
      have hS1 : 0 ≤ AngSecond.sig θ * (psi u θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hS2 : 0 ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hS3 : 0 ≤ AngSecond.sig θ * (deriv (deriv u) θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hA1 : |wrhoD eη θ| * (psi u θ) ^ 2
          ≤ (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2) := by
        calc |wrhoD eη θ| * (psi u θ) ^ 2
            ≤ ((1 - eη) * AngSecond.sig θ) * (psi u θ) ^ 2 :=
              mul_le_mul_of_nonneg_right (abs_wrhoD_le_sig hθ) (sq_nonneg _)
          _ = (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2) := by ring
      have hA2 : wrho eη θ * (2 * |psi u θ| * |deriv (psi u) θ|)
          ≤ wrho eη θ * ((psi u θ) ^ 2 + (deriv (psi u) θ) ^ 2) :=
        mul_le_mul_of_nonneg_left (two_mul_abs_mul_le_prv _ _) hρ0
      have hA3 : wrho eη θ * ((psi u θ) ^ 2 + (deriv (psi u) θ) ^ 2)
          ≤ AngSecond.sig θ * (psi u θ) ^ 2 + AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _))
      have htri : |wrhoD eη θ * (psi u θ) ^ 2 + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)|
          ≤ |wrhoD eη θ| * (psi u θ) ^ 2
            + wrho eη θ * (2 * |psi u θ| * |deriv (psi u) θ|) := by
        calc |wrhoD eη θ * (psi u θ) ^ 2 + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)|
            ≤ |wrhoD eη θ * (psi u θ) ^ 2|
              + |wrho eη θ * (2 * psi u θ * deriv (psi u) θ)| := abs_add_le _ _
          _ = |wrhoD eη θ| * (psi u θ) ^ 2
              + wrho eη θ * (2 * |psi u θ| * |deriv (psi u) θ|) := by
                rw [abs_mul, abs_mul, abs_of_nonneg hρ0,
                  abs_of_nonneg (sq_nonneg (psi u θ)), abs_mul, abs_mul,
                  abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hstep : (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2)
          ≤ AngSecond.sig θ * (psi u θ) ^ 2 := by
        calc (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2)
            ≤ 1 * (AngSecond.sig θ * (psi u θ) ^ 2) :=
              mul_le_mul_of_nonneg_right
                (by linarith [Work.Spaces.eta_lt_one, Work.Spaces.eta_nonneg]) hS1
          _ = AngSecond.sig θ * (psi u θ) ^ 2 := one_mul _
      rw [Real.norm_eq_abs]
      calc |wrhoD eη θ * (psi u θ) ^ 2 + wrho eη θ * (2 * psi u θ * deriv (psi u) θ)|
          ≤ |wrhoD eη θ| * (psi u θ) ^ 2
            + wrho eη θ * (2 * |psi u θ| * |deriv (psi u) θ|) := htri
        _ ≤ (1 - eη) * (AngSecond.sig θ * (psi u θ) ^ 2)
            + wrho eη θ * ((psi u θ) ^ 2 + (deriv (psi u) θ) ^ 2) := add_le_add hA1 hA2
        _ ≤ AngSecond.sig θ * (psi u θ) ^ 2
            + (AngSecond.sig θ * (psi u θ) ^ 2 + AngSecond.sig θ * (deriv (psi u) θ) ^ 2) :=
              add_le_add hstep hA3
        _ ≤ 10 * (AngSecond.sig θ * (psi u θ) ^ 2 + AngSecond.sig θ * (deriv (psi u) θ) ^ 2
            + AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) := by
              nlinarith [hS1, hS2, hS3]
  -- ## Integrability of the derivative of `ρψ'²`
  have hG2int : IntegrableOn (fun θ => wrhoD eη θ * (deriv (psi u) θ) ^ 2
      + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)) Iθ := by
    refine Integrable.mono' (hDm.const_mul 10) ?_ ?_
    · refine ((continuousOn_wrhoD.mul (hψ1cont.pow 2)).add
        (continuousOn_wrho.mul ((continuousOn_const.mul hψ1cont).mul hψ2cont))).aestronglyMeasurable
        measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hsig := sig_nonneg hθ
      have hρ0 := wrho_nonneg hθ
      have hcos := cos_pos hθ
      have hsin : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, Real.pi_pos])
      have hS1 : 0 ≤ AngSecond.sig θ * (psi u θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hS2 : 0 ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      have hS3 : 0 ≤ AngSecond.sig θ * (deriv (deriv u) θ) ^ 2 := mul_nonneg hsig (sq_nonneg _)
      -- Leibniz: `ψ'' cos θ = u'' + 2 sin θ ψ' + ψ cos θ`
      have hid := psi_second_deriv_Ioo u hu hθ
      have hW2 : deriv (deriv (psi u)) θ * Real.cos θ
          = deriv (deriv u) θ + 2 * deriv (psi u) θ * Real.sin θ + psi u θ * Real.cos θ := by
        rw [mul_comm]; exact hid
      have hnum : |deriv (deriv (psi u)) θ| * Real.cos θ
          ≤ |deriv (deriv u) θ| + 2 * |deriv (psi u) θ| * Real.sin θ
            + |psi u θ| * Real.cos θ := by
        have habs : |deriv (deriv (psi u)) θ| * Real.cos θ
            = |deriv (deriv (psi u)) θ * Real.cos θ| := by
          rw [abs_mul, abs_of_pos hcos]
        rw [habs, hW2]
        calc |deriv (deriv u) θ + 2 * deriv (psi u) θ * Real.sin θ + psi u θ * Real.cos θ|
            ≤ |deriv (deriv u) θ + 2 * deriv (psi u) θ * Real.sin θ|
              + |psi u θ * Real.cos θ| := abs_add_le _ _
          _ ≤ (|deriv (deriv u) θ| + |2 * deriv (psi u) θ * Real.sin θ|)
              + |psi u θ| * Real.cos θ :=
                add_le_add (abs_add_le _ _) (by rw [abs_mul, abs_of_pos hcos])
          _ = |deriv (deriv u) θ| + 2 * |deriv (psi u) θ| * Real.sin θ
              + |psi u θ| * Real.cos θ := by
                rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                  abs_of_nonneg hsin]
      have hW2le : |deriv (deriv (psi u)) θ| ≤ |deriv (deriv u) θ| / Real.cos θ
          + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ| := by
        calc |deriv (deriv (psi u)) θ|
            = (|deriv (deriv (psi u)) θ| * Real.cos θ) / Real.cos θ := by
              field_simp
          _ ≤ (|deriv (deriv u) θ| + 2 * |deriv (psi u) θ| * Real.sin θ
                + |psi u θ| * Real.cos θ) / Real.cos θ :=
              div_le_div_of_nonneg_right hnum hcos.le
          _ = |deriv (deriv u) θ| / Real.cos θ
              + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ| := by
              field_simp
      -- the three pieces
      have hT1 : wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ))
          ≤ (1 / 2) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
            + 2 * (AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) := by
        have h := two_wrho_mul_le hθ (deriv (psi u) θ) (deriv (deriv u) θ)
        have h' : wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ))
            = 2 * wrho eη θ * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ) := by
          ring
        linarith [h, h']
      have hT2 : wrho eη θ * (4 * (|deriv (psi u) θ| * |deriv (psi u) θ|)
          * (Real.sin θ / Real.cos θ)) ≤ 4 * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) := by
        have htan := wrho_mul_tan_le_sig hθ
        have hsq : |deriv (psi u) θ| * |deriv (psi u) θ| = (deriv (psi u) θ) ^ 2 := by
          rw [← sq_abs]; ring
        calc wrho eη θ * (4 * (|deriv (psi u) θ| * |deriv (psi u) θ|)
              * (Real.sin θ / Real.cos θ))
            = 4 * (wrho eη θ * (Real.sin θ / Real.cos θ)) * (deriv (psi u) θ) ^ 2 := by
              rw [hsq]; ring
          _ ≤ 4 * AngSecond.sig θ * (deriv (psi u) θ) ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htan (by norm_num))
                (sq_nonneg _)
          _ = 4 * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) := by ring
      have hT3 : wrho eη θ * (2 * |deriv (psi u) θ| * |psi u θ|)
          ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 + AngSecond.sig θ * (psi u θ) ^ 2 := by
        have h := two_mul_abs_mul_le_prv (deriv (psi u) θ) (psi u θ)
        have h2 := mul_le_mul_of_nonneg_left h hρ0
        calc wrho eη θ * (2 * |deriv (psi u) θ| * |psi u θ|)
            ≤ wrho eη θ * ((deriv (psi u) θ) ^ 2 + (psi u θ) ^ 2) := h2
          _ = wrho eη θ * (deriv (psi u) θ) ^ 2 + wrho eη θ * (psi u θ) ^ 2 := by ring
          _ ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 + AngSecond.sig θ * (psi u θ) ^ 2 :=
              add_le_add (mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _))
                (mul_le_mul_of_nonneg_right (wrho_le_sig hθ) (sq_nonneg _))
      have hA1 : |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
          ≤ (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) := by
        calc |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
            ≤ ((1 - eη) * AngSecond.sig θ) * (deriv (psi u) θ) ^ 2 :=
              mul_le_mul_of_nonneg_right (abs_wrhoD_le_sig hθ) (sq_nonneg _)
          _ = (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) := by ring
      -- assemble
      have htri : |wrhoD eη θ * (deriv (psi u) θ) ^ 2
          + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)|
          ≤ |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
            + wrho eη θ * (2 * |deriv (psi u) θ| * |deriv (deriv (psi u)) θ|) := by
        calc |wrhoD eη θ * (deriv (psi u) θ) ^ 2
            + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)|
            ≤ |wrhoD eη θ * (deriv (psi u) θ) ^ 2|
              + |wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)| := abs_add_le _ _
          _ = |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
              + wrho eη θ * (2 * |deriv (psi u) θ| * |deriv (deriv (psi u)) θ|) := by
                rw [abs_mul, abs_mul, abs_of_nonneg hρ0,
                  abs_of_nonneg (sq_nonneg (deriv (psi u) θ)), abs_mul, abs_mul,
                  abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hmid : wrho eη θ * (2 * |deriv (psi u) θ| * |deriv (deriv (psi u)) θ|)
          ≤ wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ
              + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hW2le (by positivity)) hρ0
      have hdist : wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ
          + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ|))
          = wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ))
            + wrho eη θ * (4 * (|deriv (psi u) θ| * |deriv (psi u) θ|)
                * (Real.sin θ / Real.cos θ))
            + wrho eη θ * (2 * |deriv (psi u) θ| * |psi u θ|) := by
        ring
      rw [Real.norm_eq_abs]
      calc |wrhoD eη θ * (deriv (psi u) θ) ^ 2
          + wrho eη θ * (2 * deriv (psi u) θ * deriv (deriv (psi u)) θ)|
          ≤ |wrhoD eη θ| * (deriv (psi u) θ) ^ 2
            + wrho eη θ * (2 * |deriv (psi u) θ| * |deriv (deriv (psi u)) θ|) := htri
        _ ≤ (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
            + wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ
              + 2 * |deriv (psi u) θ| * (Real.sin θ / Real.cos θ) + |psi u θ|)) :=
              add_le_add hA1 hmid
        _ = (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
            + (wrho eη θ * (2 * |deriv (psi u) θ| * (|deriv (deriv u) θ| / Real.cos θ))
              + wrho eη θ * (4 * (|deriv (psi u) θ| * |deriv (psi u) θ|)
                  * (Real.sin θ / Real.cos θ))
              + wrho eη θ * (2 * |deriv (psi u) θ| * |psi u θ|)) := by
              rw [hdist]
        _ ≤ (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
            + (((1 / 2) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
                + 2 * (AngSecond.sig θ * (deriv (deriv u) θ) ^ 2))
              + 4 * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
              + (AngSecond.sig θ * (deriv (psi u) θ) ^ 2
                + AngSecond.sig θ * (psi u θ) ^ 2)) := by
              refine add_le_add le_rfl ?_
              exact add_le_add (add_le_add hT1 hT2) hT3
        _ ≤ 10 * (AngSecond.sig θ * (psi u θ) ^ 2 + AngSecond.sig θ * (deriv (psi u) θ) ^ 2
            + AngSecond.sig θ * (deriv (deriv u) θ) ^ 2) := by
              have h1 : (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
                  ≤ AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := by
                calc (1 - eη) * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2)
                    ≤ 1 * (AngSecond.sig θ * (deriv (psi u) θ) ^ 2) :=
                      mul_le_mul_of_nonneg_right
                        (by linarith [Work.Spaces.eta_lt_one, Work.Spaces.eta_nonneg]) hS2
                  _ = AngSecond.sig θ * (deriv (psi u) θ) ^ 2 := one_mul _
              linarith [h1, hS1, hS2, hS3]
  -- ## The four limits
  obtain ⟨L1, hL1⟩ := exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    pi_half_pos hF1d hG1int
  obtain ⟨L2, hL2⟩ := exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    pi_half_pos hF2d hG2int
  obtain ⟨M1, hM1⟩ := exists_tendsto_nhdsLT_of_integrableOn_deriv
    pi_half_pos hF1d hG1int
  obtain ⟨M2, hM2⟩ := exists_tendsto_nhdsLT_of_integrableOn_deriv
    pi_half_pos hF2d hG2int
  have hL1z : L1 = 0 := eq_zero_of_tendsto_right hL1
    (fun θ hθ => mul_nonneg (wrho_nonneg hθ) (sq_nonneg _)) (fun θ _ => rfl) hSg
  have hL2z : L2 = 0 := eq_zero_of_tendsto_right hL2
    (fun θ hθ => mul_nonneg (wrho_nonneg hθ) (sq_nonneg _)) (fun θ _ => rfl) hSg1
  have hM1z : M1 = 0 := eq_zero_of_tendsto_left hM1
    (fun θ hθ => mul_nonneg (wrho_nonneg hθ) (sq_nonneg _)) (fun θ _ => rfl) hSg
  have hM2z : M2 = 0 := eq_zero_of_tendsto_left hM2
    (fun θ hθ => mul_nonneg (wrho_nonneg hθ) (sq_nonneg _)) (fun θ _ => rfl) hSg1
  rw [hL1z] at hL1
  rw [hL2z] at hL2
  rw [hM1z] at hM1
  rw [hM2z] at hM2
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Filter.Tendsto (fun t : ℝ => wrho eη t * (psi u t) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
    exact hL1
  · change Filter.Tendsto (fun t : ℝ => wrho eη t * (psi u t) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
    exact hM1
  · change Filter.Tendsto (fun t : ℝ => wrho eη t * (deriv (psi u) t) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
    exact hL2
  · change Filter.Tendsto (fun t : ℝ => wrho eη t * (deriv (psi u) t) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
    exact hM2

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.slice_ident_honest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Elementary integrability helpers -/

/-- An integrable function on `(0, π/2)` times an a.e.-measurable function bounded by `c` is
integrable. -/
private theorem integrableOn_mul_of_bound {f g : ℝ → ℝ} {c : ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo 0 (Real.pi / 2)))
    (hg : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ c) :
    MeasureTheory.IntegrableOn (fun θ => f θ * g θ) (Set.Ioo 0 (Real.pi / 2)) :=
  hf.mul_bdd hg (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hb)

/-- An integrable function on `(0, π/2)` times a continuous function bounded by `1` is
integrable. -/
private theorem integrableOn_mul_continuous_of_norm_le_one {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo 0 (Real.pi / 2)))
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ => f θ * g θ) (Set.Ioo 0 (Real.pi / 2)) :=
  integrableOn_mul_of_bound hf (hg.aemeasurable measurableSet_Ioo).aestronglyMeasurable hb

/-- The factor `(1 - η)·cos 2θ` of the derivative `wrhoD` of the integration weight is bounded
by `1` (here `η = 99/100`). -/
private theorem norm_one_sub_eta_mul_cos_two_le_one {θ : ℝ} :
    ‖(1 - Work.Spaces.eta) * Real.cos (2 * θ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_mul]
  have hη : |1 - Work.Spaces.eta| ≤ 1 := by
    have h : (1 : ℝ) - Work.Spaces.eta = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [h]; norm_num
  have hc : |Real.cos (2 * θ)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  calc |1 - Work.Spaces.eta| * |Real.cos (2 * θ)| ≤ 1 * 1 :=
        mul_le_mul hη hc (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- The cosine square factor `cos²θ` is bounded by `1`. -/
private theorem norm_cos_sq_le_one (θ : ℝ) : ‖(Real.cos θ) ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Real.cos_sq_le_one θ

/-! ## The integrability inputs of the two integrations by parts -/

/-- `∫_θ wrhoD η θ · ψ(θ)²` is honest, given `∫ ψ² σ`. -/
private theorem integrableOn_wrhoD_mul_divCos_sq (u : ℝ → ℝ)
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta θ
      * (u θ / Real.cos θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
  have hfac : ContinuousOn (fun θ : ℝ => (1 - Work.Spaces.eta) * Real.cos (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have h := integrableOn_mul_continuous_of_norm_le_one hA hfac
    (fun θ _ => norm_one_sub_eta_mul_cos_two_le_one)
  refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioo
  simp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- `∫_θ wrhoD η θ · ψ'(θ)²` is honest, given `∫ (ψ')² σ`. -/
private theorem integrableOn_wrhoD_mul_deriv_divCos_sq (u : ℝ → ℝ)
    (hA' : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta θ
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hfac : ContinuousOn (fun θ : ℝ => (1 - Work.Spaces.eta) * Real.cos (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have h := integrableOn_mul_continuous_of_norm_le_one hA' hfac
    (fun θ _ => norm_one_sub_eta_mul_cos_two_le_one)
  refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioo
  simp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- `∫_θ cos 2θ · ψ'(θ)² · σ` is honest, given `∫ (ψ')² σ`. -/
private theorem integrableOn_cos_two_mul_deriv_divCos_sq (u : ℝ → ℝ)
    (hA' : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Real.cos (2 * θ)
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hfac : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have h := integrableOn_mul_continuous_of_norm_le_one hA' hfac (fun θ _ => by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioo
  ring

/-- **`∫_θ ρ ψ ψ'` is honest**, where `ρ = wrho η`: `ψ ψ' σ` is in `L¹` by
Cauchy--Schwarz (`sin²θ (ψ')² σ` is hypothesised) and the factor `sin θ cos θ` is bounded. -/
private theorem integrableOn_wrho_mul_divCos_mul_deriv (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
      * (u θ / Real.cos θ) * deriv (fun θ => u θ / Real.cos θ) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hcos_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hψcd : ContDiffOn ℝ 2 (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div (Real.contDiff_cos.contDiffOn.of_le le_top) hcos_ne
  have hψcont : ContinuousOn (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hψcd.continuousOn
  have hψ'cont : ContinuousOn (deriv (fun θ : ℝ => u θ / Real.cos θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hψcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hf_meas : AEMeasurable (fun θ : ℝ => Real.cos θ * (u θ / Real.cos θ))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (Real.continuous_cos.continuousOn.mul hψcont).aemeasurable measurableSet_Ioo
  have hg_meas : AEMeasurable (fun θ : ℝ => Real.sin θ
      * deriv (fun θ => u θ / Real.cos θ) θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (Real.continuous_sin.continuousOn.mul hψ'cont).aemeasurable measurableSet_Ioo
  have hf2 : MeasureTheory.IntegrableOn (fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)) := by
    have hfac : ContinuousOn (fun θ : ℝ => (Real.cos θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have h := integrableOn_mul_continuous_of_norm_le_one hA hfac
      (fun θ _ => norm_cos_sq_le_one θ)
    refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioo
    simp only [Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hg2 : MeasureTheory.IntegrableOn (fun θ =>
      (Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)) := by
    refine hY.congr_fun (fun θ _ => ?_) measurableSet_Ioo
    simp only [Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hAB := Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable
    Work.Spaces.eta hf_meas hg_meas hf2 hg2
  refine hAB.congr_fun (fun θ _ => ?_) measurableSet_Ioo
  simp only [Work.FTS.EllipticEst.TanTheta.wrho, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-! ## The slice identity -/

theorem slice_ident_honest (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hB : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA' : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hv1 : Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (u θ / Real.cos θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hv2 : Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (u θ / Real.cos θ) ^ 2) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hv3 : Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hv4 : Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
        * deriv (deriv u) θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2),
            Work.FTS.EllipticEst.AngSecond.acoef θ
              * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig θ := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcos_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  -- ## `ψ = u / cos θ` is `C²` on the open interval, and the pointwise chain rule
  have hψcd : ContDiffOn ℝ 2 (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div (Real.contDiff_cos.contDiffOn.of_le le_top) hcos_ne
  have hψD : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => u t / Real.cos t)
        (deriv (fun t => u t / Real.cos t) θ) θ := fun θ hθ =>
    ((hψcd.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hψ'D : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv (fun t : ℝ => u t / Real.cos t))
        (deriv (deriv (fun t => u t / Real.cos t)) θ) θ := fun θ hθ =>
    (((hψcd.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := 1) (by norm_num)
      ).differentiableAt (by norm_num)).hasDerivAt
  have hchain : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
        = deriv (deriv u) θ + Real.cos θ * (u θ / Real.cos θ)
          + 2 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ := fun θ hθ =>
    cos_mul_derivDeriv_divCos u (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)) (hcos_ne θ hθ)
  -- ## the integrability inputs of the two integrations by parts
  have hintA : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta θ * (u θ / Real.cos θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := integrableOn_wrhoD_mul_divCos_sq u hA
  have hintA' : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_wrhoD_mul_deriv_divCos_sq u hA'
  have hintJ1 : MeasureTheory.IntegrableOn (fun θ => Real.cos (2 * θ)
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_cos_two_mul_deriv_divCos_sq u hA'
  have hintP3 : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ * (u θ / Real.cos θ)
        * deriv (fun θ => u θ / Real.cos θ) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_wrho_mul_divCos_mul_deriv u hu hY hA
  have hintP2 : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * deriv (fun θ => u θ / Real.cos θ) θ
        * deriv (deriv (fun θ => u θ / Real.cos θ)) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_wrho_mul_psiDeriv_mul_psiSecond u hu hX hY hA
  -- ## the two integrations by parts
  have hP1 := integral_Ioo_mul_deriv_eq_neg_half (a := (0 : ℝ)) (b := Real.pi / 2) hpi2
    (ρ := Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta)
    (ρ' := Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta)
    (f := fun t : ℝ => u t / Real.cos t)
    (f' := fun t : ℝ => deriv (fun s => u s / Real.cos s) t)
    (fun θ hθ => Work.FTS.EllipticEst.TanTheta.wrho_deriv Work.Spaces.eta hθ)
    hψD hintA hintP3 hv1 hv2
  have hP2 := integral_Ioo_mul_deriv_eq_neg_half (a := (0 : ℝ)) (b := Real.pi / 2) hpi2
    (ρ := Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta)
    (ρ' := Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta)
    (f := fun t : ℝ => deriv (fun s => u s / Real.cos s) t)
    (f' := fun t : ℝ => deriv (deriv (fun s => u s / Real.cos s)) t)
    (fun θ hθ => Work.FTS.EllipticEst.TanTheta.wrho_deriv Work.Spaces.eta hθ)
    hψ'D hintA' hintP2 hv3 hv4
  have hP1r : (∫ x in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta x * (u x / Real.cos x)
          * deriv (fun t : ℝ => u t / Real.cos t) x)
      = -(1 / 2) * (∫ x in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x * (u x / Real.cos x) ^ 2) := by
    simpa only [] using hP1
  have hP2r : (∫ x in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta x
          * deriv (fun t : ℝ => u t / Real.cos t) x
          * deriv (deriv (fun t : ℝ => u t / Real.cos t)) x)
      = -(1 / 2) * (∫ x in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x
            * (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2) := by
    simpa only [] using hP2
  -- ## the two derived integrals, in terms of `cos 2θ · ψ² · σ`
  have hP1c : (∫ x in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x * (u x / Real.cos x) ^ 2)
      = (1 - Work.Spaces.eta) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [show (∫ x in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x * (u x / Real.cos x) ^ 2)
        = ∫ x in Set.Ioo 0 (Real.pi / 2), (1 - Work.Spaces.eta)
            * (Real.cos (2 * x) * (u x / Real.cos x) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig x) from
      setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
        simp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
        ring)]
    rw [integral_const_mul]
  have hP2c : (∫ x in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x
          * (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2)
      = (1 - Work.Spaces.eta) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.cos (2 * θ) * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [show (∫ x in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x
            * (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2)
        = ∫ x in Set.Ioo 0 (Real.pi / 2), (1 - Work.Spaces.eta)
            * (Real.cos (2 * x) * (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig x) from
      setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
        simp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
        ring)]
    rw [integral_const_mul]
  -- ## the left-hand integrand, rewritten
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Real.sin θ * deriv (fun t : ℝ => u t / Real.cos t) θ * deriv (deriv u) θ
        * Work.FTS.EllipticEst.AngSecond.sig θ
      = Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
            * deriv (fun t : ℝ => u t / Real.cos t) θ
            * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
        - (2 * ((Real.sin θ) ^ 2 * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)
          + Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ * (u θ / Real.cos θ)
            * deriv (fun t : ℝ => u t / Real.cos t) θ) := by
    intro θ hθ
    have h := hchain θ hθ
    have huu : deriv (deriv u) θ
        = Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
          - Real.cos θ * (u θ / Real.cos θ)
          - 2 * Real.sin θ * deriv (fun t : ℝ => u t / Real.cos t) θ := by linarith [h]
    rw [huu]
    simp only [Work.FTS.EllipticEst.TanTheta.wrho, Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hY2C : MeasureTheory.IntegrableOn (fun θ => 2 * ((Real.sin θ) ^ 2
        * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      + Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ * (u θ / Real.cos θ)
        * deriv (fun t : ℝ => u t / Real.cos t) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hY.const_mul 2).add hintP3
  have hLHS : (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
        * deriv (fun t : ℝ => u t / Real.cos t) θ * deriv (deriv u) θ
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
            * deriv (fun t : ℝ => u t / Real.cos t) θ
            * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ)
        - (2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
            * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)
          + ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
            * (u θ / Real.cos θ) * deriv (fun t : ℝ => u t / Real.cos t) θ) := by
    rw [setIntegral_congr_fun measurableSet_Ioo hpt]
    rw [integral_sub hintP2 hY2C]
    rw [integral_add (hY.const_mul 2) hintP3, integral_const_mul]
  -- ## the `acoef`-integral, split along `acoef θ = ((1-η)/2) cos 2θ + 2 sin²θ`
  have hpt2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.AngSecond.acoef θ
          * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ
      = ((1 - Work.Spaces.eta) / 2) * (Real.cos (2 * θ)
            * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 2 * ((Real.sin θ) ^ 2 * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    intro θ _
    simp only [Work.FTS.EllipticEst.AngSecond.acoef]
    ring
  have hacoef : (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AngSecond.acoef θ
        * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
            * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
            * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [setIntegral_congr_fun measurableSet_Ioo hpt2]
    rw [integral_add (hintJ1.const_mul ((1 - Work.Spaces.eta) / 2)) (hY.const_mul 2),
      integral_const_mul, integral_const_mul]
  -- ## assemble
  rw [hLHS, hP2r, hP2c, hP1r, hP1c, hacoef]
  ring

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.sliceSharpFts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

theorem sliceSharpFts {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∃ M : ℝ, 0 ≤ M ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + (2 * Work.Spaces.eta) * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  -- The two ingredients are the weak-class integration by parts for the angular slice
  -- (`sliceIbpSigmaWeakFts`) and the sharp `cos²(2θ)`-weighted Hardy inequality
  -- (`cosSqHardyWeakFts`), both with the weight `σ = sin(2θ)^{-η}`, `η = 99/100`:
  --   `∫ (f')²σ = -∫ f f''σ + 2η∫ f²σ + 2η(1+η)∫ f²cos²(2θ)σ/sin²(2θ)`,
  --   `∫ f²cos²(2θ)σ/sin²(2θ) ≤ (1+η)^{-2} ∫ (f')²σ`.
  -- Combining them: `∫ f f''σ ≤ -(1 - 2η/(1+η))∫(f')²σ + 2η∫f²σ` and
  -- `1 - 2η/(1+η) = (1-η)/(1+η)`, which is the claim.
  obtain ⟨M, hM0, hMf, hMd⟩ := hb
  have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have hhardy := Work.FTS.EllipticEst.AngAWeak.cosSqHardyWeakFts Work.Spaces.eta hη0 hη1 f hf
    ⟨M, hM0, hMf, hMd⟩
  have hibp := Work.FTS.EllipticEst.AngAWeak.sliceIbpSigmaWeakFts Work.Spaces.eta hη0 hη1 f M hM0
    hf hMf hMd h2
  set D : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hD
  set G : ℝ := ∫ θ in Work.Spaces.Iθ,
    f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hG
  set H : ℝ := ∫ θ in Work.Spaces.Iθ,
    (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hH
  set E : ℝ := ∫ θ in Work.Spaces.Iθ,
    (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) with hE
  have hid : D = -G + 2 * Work.Spaces.eta * H + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * E :=
    hibp
  have hc0 : (0 : ℝ) ≤ 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) := by
    norm_num [Work.Spaces.eta]
  -- the sharp Hardy inequality with the coefficient `2η(1+η)`
  have hEbound : 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * E
      ≤ (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * D := by
    have h1 : 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * E
        ≤ 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (1 / (1 + Work.Spaces.eta) ^ 2 * D) :=
      mul_le_mul_of_nonneg_left hhardy hc0
    have h2 : 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
          * (1 / (1 + Work.Spaces.eta) ^ 2 * D)
        = (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * D := by
      rw [show 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
            * (1 / (1 + Work.Spaces.eta) ^ 2 * D)
          = (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
              * (1 / (1 + Work.Spaces.eta) ^ 2)) * D from by ring]
      rw [show 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
            * (1 / (1 + Work.Spaces.eta) ^ 2)
          = 2 * Work.Spaces.eta / (1 + Work.Spaces.eta) from by
        norm_num [Work.Spaces.eta]]
    exact le_trans h1 (le_of_eq h2)
  have hkey : -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      = -1 + 2 * Work.Spaces.eta / (1 + Work.Spaces.eta) := by
    norm_num [Work.Spaces.eta]
  have hGle : G ≤ (-1 + 2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * D
      + 2 * Work.Spaces.eta * H := by
    linarith [hid, hEbound]
  rw [hkey]
  simpa only [hG, hD, hH] using hGle

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ZCuts.zCut_exists =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped ContDiff Topology
open Set Filter

namespace Work.FTS.EllipticEst.ZCuts



end Work.FTS.EllipticEst.ZCuts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ZCuts.zCut_props =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.ZCuts

/-- For `k ≥ 2` the real number `k` is `> 1` (so that `log k > 0`). -/
lemma one_lt_natCast_of_two_le {k : ℕ} (hk : 2 ≤ k) : (1 : ℝ) < (k : ℝ) := by
  exact_mod_cast (by omega : 1 < k)

/-- `y ↦ log y / log k` is `C^∞` on `(0,∞)` for `k ≥ 2`. -/
lemma contDiffOn_log_div {k : ℕ} (hk : 2 ≤ k) :
    ContDiffOn ℝ smoothOrder (fun y : ℝ => Real.log y / Real.log (k : ℝ)) (Set.Ioi 0) := by
  apply ContDiffOn.div
  · exact Real.contDiffOn_log.mono (fun x hx => hx.ne')
  · exact contDiffOn_const
  · intro y hy
    exact ne_of_gt (Real.log_pos (one_lt_natCast_of_two_le hk))

/-- `ψ_k = φ(log z / log k)` is `C^∞` on `(0,∞)`. -/
lemma psiFun_contDiffOn {φ : ℝ → ℝ} {k : ℕ} (hφ : ContDiff ℝ smoothOrder φ) (hk : 2 ≤ k) :
    ContDiffOn ℝ smoothOrder (Work.FTS.EllipticEst.psiFun φ k) (Set.Ioi 0) :=
  hφ.comp_contDiffOn (contDiffOn_log_div hk)

/-- For `k ≥ 2` and `0 < z ≤ 1/k²`, `log z / log k ≤ -2`. -/
lemma log_div_le_neg_two {k : ℕ} (hk : 2 ≤ k) {z : ℝ} (hz : 0 < z)
    (h : z ≤ 1 / (k : ℝ) ^ 2) : Real.log z / Real.log (k : ℝ) ≤ -2 := by
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (one_lt_natCast_of_two_le hk)
  have h1 : Real.log z ≤ Real.log (1 / (k : ℝ) ^ 2) := Real.log_le_log hz h
  have h2 : Real.log (1 / (k : ℝ) ^ 2) = -(2 * Real.log (k : ℝ)) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  rw [div_le_iff₀ hlogk]
  linarith [h1, h2.le]

/-- For `k ≥ 2` and `k² ≤ z`, `2 ≤ log z / log k`. -/
lemma two_le_log_div {k : ℕ} (hk : 2 ≤ k) {z : ℝ} (h : (k : ℝ) ^ 2 ≤ z) :
    (2 : ℝ) ≤ Real.log z / Real.log (k : ℝ) := by
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (one_lt_natCast_of_two_le hk)
  have h1 : Real.log ((k : ℝ) ^ 2) ≤ Real.log z :=
    Real.log_le_log (by positivity) h
  have h2 : Real.log ((k : ℝ) ^ 2) = 2 * Real.log (k : ℝ) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [le_div_iff₀ hlogk]
  linarith [h1, h2.le]


/-- On `(0,1/k²] ∪ [k²,∞)` the cutoff vanishes: there `|log z / log k| ≥ 2`. -/
lemma psiFun_eq_zero {φ : ℝ → ℝ} {k : ℕ} (hφ0 : ∀ t, 2 ≤ |t| → φ t = 0) (hk : 2 ≤ k)
    {z : ℝ} (hz : 0 < z) (h : z ≤ 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 ≤ z) :
    Work.FTS.EllipticEst.psiFun φ k z = 0 := by
  have key : 2 ≤ |Real.log z / Real.log (k : ℝ)| := by
    rcases h with h | h
    · have hq := log_div_le_neg_two hk hz h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hq := two_le_log_div hk h
      rw [abs_of_nonneg (by linarith)]
      linarith
  simp only [Work.FTS.EllipticEst.psiFun]
  exact hφ0 _ key


/-- `ψ_k` takes values in `[0,1]` everywhere. -/
lemma psiFun_mem_Icc {φ : ℝ → ℝ} {k : ℕ} (hbdd : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (z : ℝ) :
    0 ≤ Work.FTS.EllipticEst.psiFun φ k z ∧ Work.FTS.EllipticEst.psiFun φ k z ≤ 1 := by
  simp only [Work.FTS.EllipticEst.psiFun]
  exact hbdd _

/-- The commutator bound `|z ψ_k'(z)| ≤ K / log k`: differentiating the composition
`ψ_k = φ ∘ (log z / log k)` gives `z ψ_k'(z) = φ'(log z / log k) / log k`, and
`|φ'| ≤ K`. -/
lemma abs_mul_deriv_psiFun_le {φ : ℝ → ℝ} {K : ℝ} {k : ℕ} (hφcd : ContDiff ℝ smoothOrder φ)
    (hφd : ∀ t, |deriv φ t| ≤ K) (hk : 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    |z * deriv (Work.FTS.EllipticEst.psiFun φ k) z| ≤ K / Real.log (k : ℝ) := by
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (one_lt_natCast_of_two_le hk)
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hφdiff : DifferentiableAt ℝ φ (Real.log z / Real.log (k : ℝ)) :=
    (hφcd.differentiable (by simp)).differentiableAt
  -- the chain rule for `ψ_k = φ ∘ (log · / log k)`
  have hderiv : deriv (Work.FTS.EllipticEst.psiFun φ k) z
      = deriv φ (Real.log z / Real.log (k : ℝ)) * (z⁻¹ / Real.log (k : ℝ)) := by
    have h2 : HasDerivAt (fun y : ℝ => Real.log y / Real.log (k : ℝ))
        (z⁻¹ / Real.log (k : ℝ)) z := (Real.hasDerivAt_log hz0).div_const _
    have h1 : HasDerivAt φ (deriv φ (Real.log z / Real.log (k : ℝ)))
        (Real.log z / Real.log (k : ℝ)) := hφdiff.hasDerivAt
    have hcomp : HasDerivAt (fun y : ℝ => φ (Real.log y / Real.log (k : ℝ)))
        (deriv φ (Real.log z / Real.log (k : ℝ)) * (z⁻¹ / Real.log (k : ℝ))) z :=
      h1.comp z h2
    change deriv (fun y : ℝ => φ (Real.log y / Real.log (k : ℝ))) z = _
    exact hcomp.deriv
  have hzψ : z * deriv (Work.FTS.EllipticEst.psiFun φ k) z
      = deriv φ (Real.log z / Real.log (k : ℝ)) / Real.log (k : ℝ) := by
    rw [hderiv]
    field_simp
  calc |z * deriv (Work.FTS.EllipticEst.psiFun φ k) z|
      = |deriv φ (Real.log z / Real.log (k : ℝ))| / Real.log (k : ℝ) := by
        rw [hzψ, abs_div, abs_of_pos hlogk]
    _ ≤ K / Real.log (k : ℝ) := div_le_div_of_nonneg_right (hφd _) hlogk.le


end Work.FTS.EllipticEst.ZCuts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.EllFarTopDiv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top-order reflected divided-derivative slot (independent proof)

`∫_0^{π/8} ((U/x)^{(k+1)})² sin(2x)^{2k-γ} ≤ C·FarR k γ u g`, `U = shiftU u` — the `i = k+1`
slot of `TopCoreB/far_vBound.lean` (whose `i ≤ k` case is
`TopCoreB.integrableOn_sinWeight_xDivX` / `TopCoreB.xTerm_le`).

Route: with the Leibniz identity `x·(U/x)^{(k+1)} = U^{(k+1)} - (k+1)(U/x)^{(k)}`, the factor
`sin(2x)²/x² ≤ 4` on `(0, π/8]` gives the pointwise bound

`((U/x)^{(k+1)})² sin(2x)^e ≤ 8 ((U^{(k+1)})² + (k+1)² ((U/x)^{(k)})²) sin(2x)^{e-2}`,

and both terms on the right are controlled by `FarR`: the first is the `j = k+1` slot of `FarR`
itself, the second by the weighted Hardy division `TopCoreB.hardyDiv_int_r` at
`(j, γ') = (k, γ+2)`, whose output `∫ x^{e-2} (U^{(k+1)})²` is again the `j = k+1` slot (after
`x ≤ sin 2x`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.EllFarTopDiv

open Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `sin (2x) ^ e = sin (2x) ^ (e - 2) · sin (2x)²`. -/
private lemma rpow_sin_two_split {x e : ℝ} (hs : 0 < Real.sin (2 * x)) :
    (Real.sin (2 * x)) ^ e = (Real.sin (2 * x)) ^ (e - 2) * (Real.sin (2 * x)) ^ 2 := by
  have h2 : (Real.sin (2 * x)) ^ (2 : ℝ) = (Real.sin (2 * x)) ^ 2 := by
    rw [Real.rpow_two, pow_two]
  have h1 : (Real.sin (2 * x)) ^ e = (Real.sin (2 * x)) ^ ((e - 2) + 2) := by
    congr 1
    ring
  rw [h1, Real.rpow_add hs, h2]

/-- `(A/x)² sin(2x)^e ≤ 4 A² sin(2x)^{e-2}` on `(0, π/8]`. -/
private lemma div_sq_rpow_le {A x e : ℝ} (hx : 0 < x) (hs : 0 < Real.sin (2 * x))
    (hle : Real.sin (2 * x) ≤ 2 * x) :
    (A / x) ^ 2 * (Real.sin (2 * x)) ^ e
      ≤ 4 * A ^ 2 * (Real.sin (2 * x)) ^ (e - 2) := by
  rw [rpow_sin_two_split hs]
  have hsnn : 0 ≤ (Real.sin (2 * x)) ^ (e - 2) := Real.rpow_nonneg hs.le _
  have hxne : x ≠ 0 := ne_of_gt hx
  have habs : |(A / x) * Real.sin (2 * x)| ≤ |(A / x) * (2 * x)| := by
    rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos (by positivity : 0 < 2 * x)]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  have h3 : ((A / x) * Real.sin (2 * x)) ^ 2 ≤ ((A / x) * (2 * x)) ^ 2 :=
    (sq_le_sq).mpr habs
  have h4 : ((A / x) * (2 * x)) ^ 2 = (2 * A) ^ 2 := by
    field_simp
  have h5 : (A / x) ^ 2 * (Real.sin (2 * x)) ^ 2 = ((A / x) * Real.sin (2 * x)) ^ 2 := by
    ring
  have key : (A / x) ^ 2 * (Real.sin (2 * x)) ^ 2 ≤ (2 * A) ^ 2 :=
    h5.le.trans (h3.trans h4.le)
  calc (A / x) ^ 2 * ((Real.sin (2 * x)) ^ (e - 2) * (Real.sin (2 * x)) ^ 2)
      = ((A / x) ^ 2 * (Real.sin (2 * x)) ^ 2) * (Real.sin (2 * x)) ^ (e - 2) := by ring
    _ ≤ (2 * A) ^ 2 * (Real.sin (2 * x)) ^ (e - 2) :=
        mul_le_mul_of_nonneg_right key hsnn
    _ = 4 * A ^ 2 * (Real.sin (2 * x)) ^ (e - 2) := by ring

/-- `sin (2x) ≤ 2x` for `x ≥ 0`. -/
private lemma sin_two_le_two_mul {x : ℝ} (hx : 0 ≤ x) : Real.sin (2 * x) ≤ 2 * x :=
  Real.sin_le (x := 2 * x) (by linarith)

/-- `2^{E-2} ≤ 4^k` when `E - 2 ≤ 2k`. -/
private lemma two_rpow_sub_le (k : ℕ) {E : ℝ} (hE : E - 2 ≤ 2 * (k : ℝ)) :
    Real.rpow (2 : ℝ) (E - 2) ≤ (4 : ℝ) ^ k := by
  have h1 : Real.rpow (2 : ℝ) (E - 2) ≤ Real.rpow (2 : ℝ) (2 * (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
  have h2 : Real.rpow (2 : ℝ) (2 * (k : ℝ)) = (4 : ℝ) ^ k := by
    rw [Real.rpow_eq_pow]
    rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_natCast]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  calc Real.rpow (2 : ℝ) (E - 2) ≤ Real.rpow (2 : ℝ) (2 * (k : ℝ)) := h1
    _ = (4 : ℝ) ^ k := h2

/-- The Leibniz identity `x·(U/x)^{(n+1)} = U^{(n+1)} - (n+1)(U/x)^{(n)}`. -/
private theorem x_mul_iteratedDeriv_div (n : ℕ) {a b : ℝ} {U : ℝ → ℝ}
    (hU : ContDiffOn ℝ (n + 1) U (Set.Ioo a b)) (ha : 0 ≤ a) :
    ∀ x ∈ Set.Ioo a b,
      x * iteratedDeriv (n + 1) (fun y : ℝ => U y / y) x
        = iteratedDeriv (n + 1) U x - (n + 1) * iteratedDeriv n (fun y : ℝ => U y / y) x := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_le_of_lt ha hx.1)
  have hUat : ContDiffAt ℝ (n + 1) U x := hU.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hgn : ContDiffAt ℝ (n + 1) (fun y : ℝ => U y / y) x := hUat.div contDiffAt_id hx0
  have hev : U =ᶠ[𝓝 x] fun y : ℝ => y * (U y / y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have hy0 : y ≠ 0 := ne_of_gt (lt_of_le_of_lt ha hy.1)
    field_simp
  have hmul := iteratedDeriv_mul (n := n + 1) (x := x)
    (f := fun y : ℝ => y) (g := fun y : ℝ => U y / y) contDiffAt_id hgn
  have hid1 : iteratedDeriv 1 (fun y : ℝ => y) x = 1 := by
    have hfun : (fun y : ℝ => y) = id := rfl
    rw [hfun, iteratedDeriv_id]
    rw [if_neg (by norm_num : ¬ ((1 : ℕ) = 0)), if_pos rfl]
  have hid0 : iteratedDeriv 0 (fun y : ℝ => y) x = x := by
    rw [iteratedDeriv_zero]
  have hsplit : (∑ i ∈ Finset.range (n + 2),
        ((n + 1).choose i : ℝ) * iteratedDeriv i (fun y : ℝ => y) x
          * iteratedDeriv (n + 1 - i) (fun y : ℝ => U y / y) x)
      = x * iteratedDeriv (n + 1) (fun y : ℝ => U y / y) x
        + ((n + 1 : ℕ) : ℝ) * iteratedDeriv n (fun y : ℝ => U y / y) x := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_range_succ']
    have htail : (∑ k ∈ Finset.range n,
        ((n + 1).choose (k + 1 + 1) : ℝ) * iteratedDeriv (k + 1 + 1) (fun y : ℝ => y) x
          * iteratedDeriv (n + 1 - (k + 1 + 1)) (fun y : ℝ => U y / y) x) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have h0 : iteratedDeriv (k + 1 + 1) (fun y : ℝ => y) x = 0 := by
        have hfun : (fun y : ℝ => y) = id := rfl
        rw [hfun, iteratedDeriv_id,
          if_neg (by omega : ¬ (k + 1 + 1 = 0)), if_neg (by omega : ¬ (k + 1 + 1 = 1))]
      rw [h0, mul_zero, zero_mul]
    rw [htail]
    rw [Nat.zero_add]
    simp only [hid1, hid0, Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one,
      Nat.cast_add, one_mul, mul_one, Nat.add_sub_cancel, Nat.sub_zero]
    ring
  have hU_eq : iteratedDeriv (n + 1) U x
      = ∑ i ∈ Finset.range (n + 2),
          ((n + 1).choose i : ℝ) * iteratedDeriv i (fun y : ℝ => y) x
            * iteratedDeriv (n + 1 - i) (fun y : ℝ => U y / y) x :=
    (Filter.EventuallyEq.iteratedDeriv_eq (n + 1) hev).trans hmul
  rw [hU_eq, hsplit]
  push_cast
  ring

/-- **The `i = k+1` reflected divided-derivative slot.** -/
theorem sinWeight_xDivX_top_le' (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      TopCoreB.FarHyp k γ u g →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (Set.Ioc 0 TopCoreB.xEnd) ∧
      (∫ x in (0 : ℝ)..TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ C * TopCoreB.FarR k γ u g := by
  refine ⟨8 * (1 + (((k : ℝ) + 1) ^ 2 * (2 * (4 : ℝ) ^ k))) + 1, by positivity, ?_⟩
  intro γ u g h
  set E : ℝ := 2 * (k : ℝ) - γ with hEdef
  set WK : ℝ → ℝ := fun x => iteratedDeriv k (fun y : ℝ => TopCoreB.shiftU u y / y) x with hWKdef
  set WL : ℝ → ℝ := fun x => iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x
    with hWLdef
  set UU : ℝ → ℝ := fun x => iteratedDeriv (k + 1) (TopCoreB.shiftU u) x with hUUdef
  have hE2 : E - 2 = 2 * ((k + 1 : ℕ) : ℝ) - 4 - γ := by rw [hEdef]; push_cast; ring
  have hE2nn : 0 ≤ E - 2 := by
    rw [hE2]
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith [h.hγ2]
  -- a.e. only the interior matters
  have haeIoo : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)),
      x ∈ Set.Ioo 0 TopCoreB.xEnd := by
    have h1 : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) TopCoreB.xEnd)),
        x ∈ Set.Ioo 0 TopCoreB.xEnd := ae_restrict_mem measurableSet_Ioo
    rwa [Measure.restrict_congr_set
      (Ioo_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := TopCoreB.xEnd))] at h1
  -- the Leibniz identity
  have hUU_C : ContDiffOn ℝ (k + 1) (TopCoreB.shiftU u) (Set.Ioo 0 TopCoreB.xEnd) :=
    TopCoreB.contDiffOn_shiftU (n := k + 1)
      (h.huC.of_le (by exact_mod_cast (by omega : k + 1 ≤ k + 2)))
  have hid : ∀ x ∈ Set.Ioo (0:ℝ) TopCoreB.xEnd,
      x * WL x = UU x - ((k : ℝ) + 1) * WK x := by
    intro x hx
    have hmain := x_mul_iteratedDeriv_div k (U := TopCoreB.shiftU u) hUU_C le_rfl x hx
    simpa only [hWLdef, hUUdef, hWKdef, Nat.cast_add, Nat.cast_one] using hmain
  -- the pointwise bound
  have hP : ∀ x ∈ Set.Ioo (0:ℝ) TopCoreB.xEnd,
      (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E
        ≤ 8 * ((UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
            + ((k : ℝ) + 1) ^ 2 * ((WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hsin : 0 < Real.sin (2 * x) := TopCoreB.sin_two_pos_Ioc ⟨hx.1, le_of_lt hx.2⟩
    have hle : Real.sin (2 * x) ≤ 2 * x := sin_two_le_two_mul hx0.le
    have hWL : WL x = (UU x - ((k : ℝ) + 1) * WK x) / x := by
      have h := hid x hx
      rw [eq_div_iff (ne_of_gt hx0), mul_comm]
      exact h
    rw [hWL]
    have hstep := div_sq_rpow_le (A := UU x - ((k : ℝ) + 1) * WK x) (x := x) (e := E)
      hx0 hsin hle
    have hsq : (UU x - ((k : ℝ) + 1) * WK x) ^ 2
        ≤ 2 * ((UU x) ^ 2 + (((k : ℝ) + 1) * WK x) ^ 2) := by
      nlinarith [sq_nonneg (UU x + ((k : ℝ) + 1) * WK x),
        sq_nonneg (UU x - ((k : ℝ) + 1) * WK x)]
    have hrnn : 0 ≤ Real.rpow (Real.sin (2 * x)) (E - 2) := Real.rpow_nonneg hsin.le _
    calc ((UU x - ((k : ℝ) + 1) * WK x) / x) ^ 2 * Real.rpow (Real.sin (2 * x)) E
        ≤ 4 * (UU x - ((k : ℝ) + 1) * WK x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (E - 2) := hstep
      _ ≤ 4 * (2 * ((UU x) ^ 2 + (((k : ℝ) + 1) * WK x) ^ 2))
            * Real.rpow (Real.sin (2 * x)) (E - 2) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hrnn
      _ = 8 * ((UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
            + ((k : ℝ) + 1) ^ 2 * ((WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))) := by
          ring
  -- integrability of the pieces
  have hAint' : MeasureTheory.IntegrableOn
      (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftU u) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * ((k + 1 : ℕ) : ℝ) - 4 - γ))
      (Set.Ioc 0 TopCoreB.xEnd) :=
    TopCoreB.integrableOn_shift_slot_Ioc (k + 1) (2 * ((k + 1 : ℕ) : ℝ) - 4 - γ) u
      (h.hH3 (k + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
  have hAint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
      (Set.Ioc 0 TopCoreB.xEnd) := by
    rw [hE2, hUUdef]
    exact hAint'
  have hassUU : AEStronglyMeasurable
      (fun x : ℝ => Real.rpow x (E - 2) * (UU x) ^ 2)
      (volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)) := by
    refine TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn ?_
    have hc : ContinuousOn (UU) (Set.Ioo 0 TopCoreB.xEnd) := by
      rw [hUUdef]
      exact TopCoreB.continuousOn_shiftU_iteratedDeriv h (j := k + 1) (by omega)
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul (hc.pow 2)
  have hGUint : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.rpow x (E - 2) * (UU x) ^ 2) (Set.Ioc 0 TopCoreB.xEnd) := by
    refine Integrable.mono' (f := fun x : ℝ => Real.rpow x (E - 2) * (UU x) ^ 2)
      (g := fun x : ℝ => (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)) hAint hassUU ?_
    filter_upwards [haeIoo] with x hx
    rw [Real.rpow_eq_pow]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg (UU x)))]
    have hxle : x ≤ Real.sin (2 * x) := TopCoreB.self_le_sin_two ⟨hx.1, le_of_lt hx.2⟩
    have h1 : x ^ (E - 2) ≤ (Real.sin (2 * x)) ^ (E - 2) :=
      Real.rpow_le_rpow hx.1.le hxle hE2nn
    calc x ^ (E - 2) * (UU x) ^ 2 = (UU x) ^ 2 * x ^ (E - 2) := by ring
      _ ≤ (UU x) ^ 2 * (Real.sin (2 * x)) ^ (E - 2) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg (UU x))
  have hE2' : E - 2 = 2 * (k : ℝ) - (γ + 2) := by rw [hEdef]; ring
  have hEk : E - 2 ≤ 2 * (k : ℝ) := by
    rw [hEdef]
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [h.hγ1]
  have hGKint : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.rpow x (E - 2) * (WK x) ^ 2) (Set.Ioc 0 TopCoreB.xEnd) := by
    obtain ⟨_Chd, _hChdpos, hdiv⟩ :=
      hardyDiv_fin k (γ + 2) (by linarith [h.hγ1]) TopCoreB.xEnd TopCoreB.xEnd_pos
    have hmain := (hdiv (TopCoreB.shiftU u) (TopCoreB.contDiffOn_shiftU_Ioc (N := k + 2) h.huC)
      (TopCoreB.tendsto_shiftU h.hucont h.hupi)
      (by simpa only [Real.rpow_eq_pow, hE2'] using hGUint)).1
    simpa only [Real.rpow_eq_pow, hE2', hWKdef] using hmain
  have hassWK : AEStronglyMeasurable
      (fun x : ℝ => (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
      (volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)) := by
    refine TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn ?_
    have hc : ContinuousOn (WK) (Set.Ioo 0 TopCoreB.xEnd) := by
      rw [hWKdef]
      exact TopCoreB.continuousOn_divXDeriv (N := k + 1) h.huC (by omega)
    exact (hc.pow 2).mul (TopCoreB.continuousOn_sin_rpow (p := E - 2))
  have hBint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
      (Set.Ioc 0 TopCoreB.xEnd) := by
    refine TopCoreB.integrableOn_of_le_const_mul (C := Real.rpow (2 : ℝ) (E - 2))
      (Real.rpow_nonneg (by norm_num) _) hGKint hassWK ?_ ?_
    · intro x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc hx) _)
    · intro x hx
      have hx0 : 0 ≤ x := hx.1.le
      have hsin0 : 0 ≤ Real.sin (2 * x) := TopCoreB.sin_two_nonneg_Ioc hx
      have hle : Real.sin (2 * x) ≤ 2 * x := sin_two_le_two_mul hx0
      have h1 : Real.rpow (Real.sin (2 * x)) (E - 2) ≤ Real.rpow (2 * x) (E - 2) :=
        Real.rpow_le_rpow hsin0 hle hE2nn
      have h2 : Real.rpow (2 * x) (E - 2)
          = Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2) :=
        Real.mul_rpow (x := (2 : ℝ)) (y := x) (z := E - 2) (by norm_num) hx0
      rw [h2] at h1
      calc (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
          ≤ (WK x) ^ 2 * (Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2)) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg (WK x))
        _ = Real.rpow (2 : ℝ) (E - 2) * (Real.rpow x (E - 2) * (WK x) ^ 2) := by ring
  -- integral comparisons
  have hUb : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)) ≤ TopCoreB.FarR k γ u g := by
    have h1 : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
        = ∫ θ in TopCoreB.farSet, (iteratedDeriv (k + 1) u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * ((k + 1 : ℕ) : ℝ) - 4 - γ) := by
      rw [hE2, hUUdef]
      rw [← intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le]
      rw [← TopCoreB.integral_farSet_slot_eq (k + 1) (2 * ((k + 1 : ℕ) : ℝ) - 4 - γ) u]
    rw [h1]
    exact TopCoreB.farSet_slot_le_FarR hk h (j := k + 1) (by omega) le_rfl
  have hGUb : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, Real.rpow x (E - 2) * (UU x) ^ 2)
      ≤ ∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2) := by
    refine integral_mono_of_nonneg ?_ hAint ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg _)
    · filter_upwards [haeIoo] with x hx
      have hxle : x ≤ Real.sin (2 * x) := TopCoreB.self_le_sin_two ⟨hx.1, le_of_lt hx.2⟩
      have h1 : Real.rpow x (E - 2) ≤ Real.rpow (Real.sin (2 * x)) (E - 2) :=
        Real.rpow_le_rpow hx.1.le hxle hE2nn
      calc Real.rpow x (E - 2) * (UU x) ^ 2
          ≤ Real.rpow (Real.sin (2 * x)) (E - 2) * (UU x) ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2) := by ring
  have hGKb : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, Real.rpow x (E - 2) * (WK x) ^ 2)
      ≤ 2 * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, Real.rpow x (E - 2) * (UU x) ^ 2) := by
    have hmain := TopCoreB.hardyDiv_int_r (j := k) (by omega) (γ := γ + 2)
      (by linarith [h.hγ1]) (x₁ := TopCoreB.xEnd) TopCoreB.xEnd_pos
      (f := TopCoreB.shiftU u) (TopCoreB.contDiffOn_shiftU_Ioc (N := k + 2) h.huC)
      (TopCoreB.tendsto_shiftU h.hucont h.hupi)
      (by simpa only [Real.rpow_eq_pow, hE2'] using hGUint)
    have hconv : ∀ f : ℝ → ℝ, (∫ x in (0 : ℝ)..TopCoreB.xEnd, f x)
        = ∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, f x := fun f =>
      intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le
    rw [hconv, hconv] at hmain
    simpa only [Real.rpow_eq_pow, hE2', hWKdef, hUUdef] using hmain
  have hBb : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
      ≤ (4 : ℝ) ^ k * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          Real.rpow x (E - 2) * (WK x) ^ 2) := by
    have hmaj : Integrable
        (fun x : ℝ => (4 : ℝ) ^ k * (Real.rpow x (E - 2) * (WK x) ^ 2))
        (volume.restrict (Set.Ioc (0 : ℝ) TopCoreB.xEnd)) := hGKint.const_mul _
    refine (integral_mono_of_nonneg ?_ hmaj ?_).trans (le_of_eq ?_)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc hx) _)
    · filter_upwards [haeIoo] with x hx
      have hx0 : 0 < x := hx.1
      have hsin : 0 < Real.sin (2 * x) := TopCoreB.sin_two_pos_Ioc ⟨hx.1, le_of_lt hx.2⟩
      have hle : Real.sin (2 * x) ≤ 2 * x := sin_two_le_two_mul hx0.le
      have h1 : Real.rpow (Real.sin (2 * x)) (E - 2) ≤ Real.rpow (2 * x) (E - 2) :=
        Real.rpow_le_rpow hsin.le hle hE2nn
      have h2 : Real.rpow (2 * x) (E - 2)
          = Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2) :=
        Real.mul_rpow (x := (2 : ℝ)) (y := x) (z := E - 2) (by norm_num) hx0.le
      have h3 : Real.rpow (2 : ℝ) (E - 2) ≤ (4 : ℝ) ^ k := two_rpow_sub_le k hEk
      rw [h2] at h1
      have h6 : Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2)
          ≤ (4 : ℝ) ^ k * Real.rpow x (E - 2) :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hx0.le _)
      calc (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
          ≤ (WK x) ^ 2 * (Real.rpow (2 : ℝ) (E - 2) * Real.rpow x (E - 2)) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg (WK x))
        _ ≤ (WK x) ^ 2 * ((4 : ℝ) ^ k * Real.rpow x (E - 2)) :=
            mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
        _ = (4 : ℝ) ^ k * (Real.rpow x (E - 2) * (WK x) ^ 2) := by ring
    · exact integral_const_mul _ _
  -- the main integral bound
  have hassL : AEStronglyMeasurable
      (fun x : ℝ => (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
      (volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)) := by
    refine TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn ?_
    have hc : ContinuousOn (WL) (Set.Ioo 0 TopCoreB.xEnd) := by
      rw [hWLdef]
      exact TopCoreB.continuousOn_divXDeriv (N := k + 1) h.huC (by omega)
    exact (hc.pow 2).mul (TopCoreB.continuousOn_sin_rpow (p := E))
  have hLHSint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
      (Set.Ioc 0 TopCoreB.xEnd) := by
    have hmaj : Integrable
        (fun x : ℝ => 8 * ((UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
            + ((k : ℝ) + 1) ^ 2 * ((WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))))
        (volume.restrict (Set.Ioc (0 : ℝ) TopCoreB.xEnd)) :=
      ((hAint.add (hBint.const_mul _)).const_mul 8)
    refine hmaj.mono' hassL ?_
    filter_upwards [haeIoo] with x hx
    rw [Real.rpow_eq_pow]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg (WL x))
      (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩) _))]
    exact hP x hx
  have hPint : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
      ≤ 8 * ((∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
            (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
          + ((k : ℝ) + 1) ^ 2 * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))) := by
    have hmaj : Integrable
        (fun x : ℝ => 8 * ((UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2)
            + ((k : ℝ) + 1) ^ 2 * ((WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))))
        (volume.restrict (Set.Ioc (0 : ℝ) TopCoreB.xEnd)) :=
      ((hAint.add (hBint.const_mul _)).const_mul 8)
    refine (integral_mono_of_nonneg ?_ hmaj ?_).trans (le_of_eq ?_)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc hx) _)
    · filter_upwards [haeIoo] with x hx
      exact hP x hx
    · rw [integral_const_mul, integral_add hAint (hBint.const_mul _), integral_const_mul]
  -- conclusion
  have hFarRnn : 0 ≤ TopCoreB.FarR k γ u g := TopCoreB.FarR_nonneg hk h
  have h4k : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  have hbound : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
      ≤ (8 * (1 + (((k : ℝ) + 1) ^ 2 * (2 * (4 : ℝ) ^ k))) + 1)
        * TopCoreB.FarR k γ u g := by
    have hBK : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
        ≤ (2 * (4 : ℝ) ^ k) * TopCoreB.FarR k γ u g := by
      calc (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
            (WK x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))
          ≤ (4 : ℝ) ^ k * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              Real.rpow x (E - 2) * (WK x) ^ 2) := hBb
        _ ≤ (4 : ℝ) ^ k * (2 * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              Real.rpow x (E - 2) * (UU x) ^ 2)) :=
            mul_le_mul_of_nonneg_left hGKb h4k.le
        _ ≤ (4 : ℝ) ^ k * (2 * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              (UU x) ^ 2 * Real.rpow (Real.sin (2 * x)) (E - 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGUb (by norm_num)) h4k.le
        _ ≤ (4 : ℝ) ^ k * (2 * TopCoreB.FarR k γ u g) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUb (by norm_num)) h4k.le
        _ = (2 * (4 : ℝ) ^ k) * TopCoreB.FarR k γ u g := by ring
    have hstep : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (WL x) ^ 2 * Real.rpow (Real.sin (2 * x)) E)
        ≤ 8 * (TopCoreB.FarR k γ u g
            + ((k : ℝ) + 1) ^ 2 * ((2 * (4 : ℝ) ^ k) * TopCoreB.FarR k γ u g)) := by
      refine hPint.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact add_le_add hUb (mul_le_mul_of_nonneg_left hBK (sq_nonneg ((k : ℝ) + 1)))
    refine hstep.trans ?_
    nlinarith [hFarRnn, h4k, sq_nonneg ((k : ℝ) + 1)]
  refine ⟨?_, ?_⟩
  · simpa only [hWLdef, hEdef] using hLHSint
  · rw [intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le]
    simpa only [hWLdef, hEdef] using hbound

end Work.FTS.EllipticEst.remov.EllFarTopDiv
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.farVIntLow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the low-order `v`-slots on the far window

For `k ≥ 2`, `γ ≥ 1` and `u`, `g` satisfying `FarHyp k γ u g`, the weighted square of every
low slot `∂^m (u / cos θ)`, `m ≤ k`, is integrable on the far window `[3π/8, π/2]` against
`qW k γ θ = sin(2θ)^{2k-γ}`.

This is the *integrability* half of the far-window estimate (`far_vBound`), separated out so
that the far slots can be fed to the dominated-convergence arguments of the angular estimate.

Route (the reflected variable `x = π/2 - θ ∈ [0, π/8]`, `shiftV u x = u(π/2-x)/sin x`,
`shiftU u x = u(π/2-x)`, `secH x = x/sin x`):

* `shiftV u = (shiftU u / ·) * secH` near the interior of `(0, π/8)`, so Leibniz
  (`shiftV_deriv_sq_le`) bounds `(∂^m (shiftV u))²` pointwise by a constant times
  `∑_{i ≤ m} (∂^i (shiftU u / ·))²`, the `secH`-derivatives being bounded by `K`
  (`sinDivDerivBounds`);
* each summand, multiplied by `sin(2x)^{2k-γ}`, is integrable on `(0, π/8]`
  (`integrableOn_sinWeight_xDivX`, i.e. the weighted Hardy division followed by the slots `H1`,
  `H3`, `H4` of `FarHyp`);
* `a.e.`-monotonicity (`Integrable.mono'`) and the reflection transfer
  (`MeasurePreserving.integrableOn_comp_preimage`) give the claim on `farSet`.
-/

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

theorem farVIntLow (k : ℕ) (hk : 2 ≤ k) :
    ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.TopCoreB.FarHyp k γ u g →
      ∀ m : ℕ, m ≤ k →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (iteratedDeriv m (Work.FTS.EllipticEst.remov.TopCoreB.vF u) θ) ^ 2
            * Work.FTS.EllipticEst.remov.TopCoreB.qW k γ θ)
          Work.FTS.EllipticEst.remov.TopCoreB.farSet := by
  intro γ u g hF m hm
  obtain ⟨K, hKpos, hKb⟩ := TopCoreB.sinDivDerivBounds k
  have hK : ∀ i ≤ m, ∀ y ∈ Set.Ioc 0 TopCoreB.xEnd, |iteratedDeriv i TopCoreB.secH y| ≤ K :=
    fun i hi y hy => hKb i (le_trans hi hm) y hy
  have huC : ContDiffOn ℝ m u (Set.Ioo 0 (Real.pi / 2)) :=
    hF.huC.of_le (by exact_mod_cast (by omega : m ≤ k + 2))
  set A : ℝ := ((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set G : ℝ → ℝ := fun x => A * ∑ i ∈ Finset.range (m + 1),
      ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) with hG
  have hGint : IntegrableOn G (Set.Ioc 0 TopCoreB.xEnd) := by
    rw [hG]
    exact (MeasureTheory.integrable_finsetSum (Finset.range (m + 1))
      (fun i hi => TopCoreB.integrableOn_sinWeight_xDivX hk hF
        (le_trans (by simpa [Finset.mem_range] using hi) hm))).const_mul A
  -- smoothness of the reflected `v` on the interior of `(0, π/8)`
  have hsv : ContDiffOn ℝ m (TopCoreB.shiftV u) (Set.Ioo 0 TopCoreB.xEnd) := by
    have h1 : ContDiffOn ℝ m (TopCoreB.shiftU u) (Set.Ioo 0 TopCoreB.xEnd) :=
      TopCoreB.contDiffOn_shiftU huC
    have h2 : ContDiffOn ℝ m (fun x : ℝ => Real.sin x) (Set.Ioo 0 TopCoreB.xEnd) :=
      Real.contDiff_sin.contDiffOn
    have h3 : ContDiffOn ℝ m (TopCoreB.shiftU u / fun x : ℝ => Real.sin x)
        (Set.Ioo 0 TopCoreB.xEnd) :=
      h1.div h2 (fun x hx => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1
        (by linarith [hx.2, TopCoreB.xEnd_lt_pi_half, Real.pi_pos])))
    have hfun : (TopCoreB.shiftU u / fun x : ℝ => Real.sin x) = TopCoreB.shiftV u := by
      funext x; simp [TopCoreB.shiftV, Pi.div_apply]
    rw [hfun] at h3
    exact h3
  -- the shifted integrand is integrable on `(0, π/8]`
  have hshift : IntegrableOn (fun x => (iteratedDeriv m (TopCoreB.shiftV u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Ioc 0 TopCoreB.xEnd) := by
    have hsm : AEStronglyMeasurable (fun x => (iteratedDeriv m (TopCoreB.shiftV u) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (volume.restrict (Set.Ioc 0 TopCoreB.xEnd)) :=
      TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn
        (((HardyFin.continuousOn_iteratedDeriv_Ioo_fin' hsv le_rfl).pow 2).mul
          (TopCoreB.continuousOn_sin_rpow (p := 2 * (k : ℝ) - γ)))
    refine hGint.mono' hsm ?_
    have hsub : ∀ᵐ x ∂(volume.restrict (Set.Ioc 0 TopCoreB.xEnd)),
        x ∈ Set.Ioo 0 TopCoreB.xEnd := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ))
        (b := TopCoreB.xEnd))]
      exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => hx)
    filter_upwards [hsub] with x hx
    have hw_nn : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
      Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw_nn)]
    have h1 := TopCoreB.shiftV_deriv_sq_le (u := u) (m := m) (K := K) hK huC hx
    calc (iteratedDeriv m (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ (((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ)
            * ∑ i ∈ Finset.range (m + 1),
                (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2)
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
          mul_le_mul_of_nonneg_right h1 hw_nn
      _ = G x := by
          simp only [hG, hA]
          rw [← Finset.sum_mul]
          ring
  -- pass from `(0, π/8]` to `[0, π/8]`
  have hIcc : IntegrableOn (fun x => (iteratedDeriv m (TopCoreB.shiftV u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Icc 0 TopCoreB.xEnd) :=
    (integrableOn_congr_set_ae (Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
      (b := TopCoreB.xEnd))).mp hshift
  -- reflect back to the far window
  refine (MeasurePreserving.integrableOn_comp_preimage (μ := volume) (ν := volume)
    TopCoreB.measurePreserving_reflectC TopCoreB.measurableEmbedding_reflectC
    (s := TopCoreB.farSet)).mp ?_
  rw [TopCoreB.preimage_reflectC_farSet]
  refine hIcc.congr_fun (fun x _ => ?_) measurableSet_Icc
  exact (TopCoreB.farSet_integrand_eq k γ m u x).symm

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.sliceV2Uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The `(v'')²σ`-coercivity bound, `v = u/cos θ`, `σ = sin(2θ)^{2-γ}`, `1 ≤ γ ≤ 3/2`. -/
theorem sliceV2Uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  -- the two halves: the interval estimate on `(π/4, b)` and the bound on `[0, π/4]`
  obtain ⟨CI, hCIpos, hCI⟩ := sliceV2IntervalUniform
  obtain ⟨CL, hCLpos, hCL⟩ := sliceLeftUniform
  refine ⟨CL + CI + 1, by linarith, ?_⟩
  intro γ u g hγ1 hγ2 hu huc hu0 hupi hg hint2 hint1 hint0 hintg
  -- notational abbreviations (all `let`-definitions, hence definitionally equal to their bodies)
  let F : ℝ → ℝ := fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ)
  let D : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
  let B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  let C1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2
  let C0 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2
  let R : ℝ := D + B + C1 + C0
  change MeasureTheory.IntegrableOn F Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, F θ) ≤ (CL + CI + 1) * R
  -- nonnegativity of the four data integrals
  have hDnn : 0 ≤ D := by
    change 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
    rw [Work.Spaces.Iθ]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    rw [Set.mem_Icc] at hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩) _)
  have hBnn : 0 ≤ B := by
    change 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [Work.Spaces.Iθ]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    rw [Set.mem_Icc] at hθ
    refine mul_nonneg (sq_nonneg _) ?_
    rw [Work.FTS.EllipticEst.sEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩) _
  have hC1nn : 0 ≤ C1 := by
    change 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hC0nn : 0 ≤ C0 := by
    change 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hRnn : 0 ≤ R := by
    change 0 ≤ D + B + C1 + C0
    linarith
  -- the interval estimate, transported to `F`
  have hintv2 : ∀ b ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (∫ θ in (Real.pi / 4)..b, F θ) ≤ CI * R := by
    intro b hb
    exact hCI γ u g hγ1 hγ2 hu huc hu0 hupi hg hint2 hint1 hint0 hintg b hb
  -- `F` is continuous on the whole open interval
  have hcos_ne : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), Real.cos x ≠ 0 := by
    intro x hx
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  have hv2c : ContinuousOn (fun θ => deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hv : ContDiffOn ℝ 3 (fun s => u s / Real.cos s) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.div ((Real.contDiff_cos (n := 3)).contDiffOn) hcos_ne
    have h1 : ContDiffOn ℝ 2 (deriv (fun s => u s / Real.cos s)) (Set.Ioo 0 (Real.pi / 2)) :=
      hv.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)
    have h2 : ContDiffOn ℝ 1 (deriv (deriv (fun s => u s / Real.cos s)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    exact h2.continuousOn
  have hσcont : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
    (Real.continuous_rpow_const (q := 2 - γ) (by linarith)).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hcontBig : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)) := by
    change ContinuousOn (fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Ioo 0 (Real.pi / 2))
    exact (hv2c.pow 2).mul hσcont.continuousOn
  have hnnF : ∀ x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), 0 ≤ F x := by
    intro x hx
    change 0 ≤ (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) (2 - γ)
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩) _)
  have hcont : ContinuousOn F (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hcontBig.mono (Set.Ioo_subset_Ioo (by linarith [Real.pi_pos]) le_rfl)
  have hintF : ∀ b ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      MeasureTheory.IntegrableOn F (Set.Ioo (Real.pi / 4) b) := by
    intro b hb
    have hsub : Set.Icc (Real.pi / 4) b ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro x hx
      rw [Set.mem_Icc] at hx
      exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hb.2]⟩
    exact ((hcontBig.mono hsub).integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  -- pass to the open interval `(π/4, π/2)`
  obtain ⟨hintIoo, hbdIoo⟩ :=
    interval_integral_mono_limit (a := Real.pi / 4) (β := Real.pi / 2) (f := F) (K := CI * R)
      (by linarith [Real.pi_pos]) hcont hnnF hintF (fun b hb => hintv2 b hb)
  -- the left half
  obtain ⟨hLint, hLbd⟩ := hCL γ u g hγ1 hγ2 hu huc hu0 hupi hg hint2 hint1 hint0
  have hleftInt : MeasureTheory.IntegrableOn F (Set.Icc 0 (Real.pi / 4)) := hLint
  have hleftBd : (∫ θ in Set.Icc 0 (Real.pi / 4), F θ) ≤ CL * R := by
    have h : (∫ θ in Set.Icc 0 (Real.pi / 4), F θ) ≤ CL * (B + C1 + C0) := hLbd
    calc (∫ θ in Set.Icc 0 (Real.pi / 4), F θ) ≤ CL * (B + C1 + C0) := h
      _ ≤ CL * R := by
          change CL * (B + C1 + C0) ≤ CL * (D + B + C1 + C0)
          exact mul_le_mul_of_nonneg_left (by linarith) hCLpos.le
  -- split `Iθ` at `π/4`
  have hDisj : Disjoint (Set.Icc 0 (Real.pi / 4)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt_of_ge hx1.2))
  have hSsub : (Set.Icc 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)) ⊆
      Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    rcases (Set.mem_union x _ _).mp hx with hx | hx
    · rw [Set.mem_Icc] at hx
      exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    · rw [Set.mem_Ioo] at hx
      exact ⟨by linarith [hx.1, Real.pi_pos], le_of_lt hx.2⟩
  have hsub1 : Work.Spaces.Iθ \
        (Set.Icc 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)) ⊆
      ({Real.pi / 2} : Set ℝ) := by
    intro x hx
    rw [Set.mem_sdiff] at hx
    obtain ⟨hxIθ, hxS⟩ := hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hxIθ
    simp only [Set.mem_singleton_iff]
    by_contra hne
    have hxq : Real.pi / 4 < x := by
      rcases le_or_gt x (Real.pi / 4) with h | h
      · exact absurd ((Set.mem_union x (Set.Icc 0 (Real.pi / 4))
          (Set.Ioo (Real.pi / 4) (Real.pi / 2))).mpr (Or.inl ⟨hxIθ.1, h⟩)) hxS
      · exact h
    exact hxS ((Set.mem_union x (Set.Icc 0 (Real.pi / 4))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2))).mpr
        (Or.inr ⟨hxq, lt_of_le_of_ne hxIθ.2 hne⟩))
  have hSae : (Set.Icc 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2))
      =ᵐ[volume] Work.Spaces.Iθ := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, MeasureTheory.measure_mono_null hsub1 Real.volume_singleton⟩
    rw [Set.sdiff_eq_empty.mpr hSsub]
    exact MeasureTheory.measure_empty
  refine ⟨(hleftInt.union hintIoo).congr_set_ae hSae.symm, ?_⟩
  calc (∫ θ in Work.Spaces.Iθ, F θ)
      = ∫ θ in (Set.Icc 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)), F θ :=
          (MeasureTheory.setIntegral_congr_set hSae).symm
    _ = (∫ θ in Set.Icc 0 (Real.pi / 4), F θ)
          + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ) :=
          MeasureTheory.setIntegral_union hDisj measurableSet_Ioo hleftInt hintIoo
    _ ≤ CL * R + CI * R := add_le_add hleftBd hbdIoo
    _ ≤ (CL + CI + 1) * R := by nlinarith [hCLpos, hCIpos, hRnn]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_V2_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.H2.STSigma =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Congruence and linearity of the `D_z`-iterates on an open set -/

theorem Dz_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz u)) (Function.uncurry (Work.Spaces.Dz v)) V := by
  intro p hp
  show p.1 * Work.Spaces.pz u p.1 p.2 = p.1 * Work.Spaces.pz v p.1 p.2
  rw [Work.Spaces.pz_congr_of_isOpen hV h hp]

theorem DzIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j u))
      (Function.uncurry (Work.Spaces.DzIter j v)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro p hp
    show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j u) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j v) p.1 p.2
    rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

/-- `D_z` acts termwise on a finite sum with `θ`-dependent coefficients. -/
theorem Dz_sum_const_mul_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (F : ι → ℝ → ℝ → ℝ)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ⊤ (Function.uncurry (F i)) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.Dz (F i) z θ)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => F i z' θ) z := fun i hi => by
    have h1 : DifferentiableAt ℝ (Function.uncurry (F i)) (z, θ) :=
      ((hF i hi).contDiffAt (hV.mem_nhds hp)).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
      (hasFDerivAt_prodMk_left z θ).differentiableAt
    have h3 : DifferentiableAt ℝ ((Function.uncurry (F i)) ∘ (fun e : ℝ => (e, θ))) z :=
      h1.comp z h2
    simpa [Function.comp_def, Function.uncurry] using h3
  have h1 : Work.Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ) z θ
      = ∑ i ∈ s, c i θ * Work.Spaces.pz (F i) z θ := by
    show deriv (fun z' => ∑ i ∈ s, c i θ * F i z' θ) z = _
    have hfun : (fun z' => ∑ i ∈ s, c i θ * F i z' θ)
        = ∑ i ∈ s, (fun z' => c i θ * F i z' θ) := by
      funext z'; rw [Finset.sum_apply]
    rw [hfun, deriv_sum (fun i hi => (hdiff i hi).const_mul (c i θ))]
    exact Finset.sum_congr rfl fun i hi =>
      deriv_const_mul_field (c i θ)
  show z * Work.Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ) z θ
      = ∑ i ∈ s, c i θ * (z * Work.Spaces.pz (F i) z θ)
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => by ring

/-- The `pz`-form of the same termwise identity. -/
theorem pz_sum_const_mul_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (F : ι → ℝ → ℝ → ℝ)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ⊤ (Function.uncurry (F i)) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.pz (F i) z θ)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => F i z' θ) z := fun i hi => by
    have h1 : DifferentiableAt ℝ (Function.uncurry (F i)) (z, θ) :=
      ((hF i hi).contDiffAt (hV.mem_nhds hp)).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
      (hasFDerivAt_prodMk_left z θ).differentiableAt
    have h3 : DifferentiableAt ℝ ((Function.uncurry (F i)) ∘ (fun e : ℝ => (e, θ))) z :=
      h1.comp z h2
    simpa [Function.comp_def, Function.uncurry] using h3
  show deriv (fun z' => ∑ i ∈ s, c i θ * F i z' θ) z
      = ∑ i ∈ s, c i θ * Work.Spaces.pz (F i) z θ
  have hfun : (fun z' => ∑ i ∈ s, c i θ * F i z' θ)
      = ∑ i ∈ s, (fun z' => c i θ * F i z' θ) := by
    funext z'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun i hi => (hdiff i hi).const_mul (c i θ))]
  exact Finset.sum_congr rfl fun i hi =>
    deriv_const_mul_field (c i θ)

theorem DzIter_sum_const_mul_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (F : ι → ℝ → ℝ → ℝ)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ⊤ (Function.uncurry (F i)) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (F i) z θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    have hFs : ∀ i ∈ s, ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter j (F i))) V :=
      fun i hi => Work.Spaces.DzIterSmoothOn hV (hF i hi) j
    have hstep := Dz_sum_const_mul_eqOn s c (fun i => Work.Spaces.DzIter j (F i)) hV hFs
    have hstep' := pz_sum_const_mul_eqOn s c (fun i => Work.Spaces.DzIter j (F i)) hV hFs
    intro p hp
    have hcongr : Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ))
          p.1 p.2
        = Work.Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (F i) z θ) p.1 p.2 :=
      Work.Spaces.pz_congr_of_isOpen hV ih hp
    have hstep'' := hstep' hp
    simp only [Function.uncurry] at hstep''
    show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) p.1 p.2
        = ∑ i ∈ s, c i p.2 * (p.1 * Work.Spaces.pz (Work.Spaces.DzIter j (F i)) p.1 p.2)
    rw [show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ))
            p.1 p.2
          = p.1 * Work.Spaces.pz
              (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) p.1 p.2 from rfl,
      hcongr, hstep'', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring

/-! ## `D_θ` preserves `z`-independence -/

theorem Dth_zindep {u : ℝ → ℝ → ℝ} (h : ∀ z θ, u z θ = u 0 θ) (z θ : ℝ) :
    Work.Spaces.Dth u z θ = Work.Spaces.Dth u 0 θ := by
  show Real.sin (2 * θ) * Work.Spaces.pth u z θ = Real.sin (2 * θ) * Work.Spaces.pth u 0 θ
  congr 1
  show deriv (fun θ' => u z θ') θ = deriv (fun θ' => u 0 θ') θ
  congr 1
  funext θ'
  exact h z θ'


/-! ## The Leibniz identity in `θ` on `nbhU`, with a `θ`-only coefficient -/




/-! ## The iterated commutator bound -/

/-- The constants of the iteration of `mixed_succ_expansion`:
`B n = 1 + ∑_{r<n} C(n,r+1)·A_{r+1}·B_{n-r-1}`. -/
def Bz : ℕ → ℝ
  | 0 => 1
  | 1 => 3
  | 2 => 17
  | _ => 187







end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.GoodThetaDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option autoImplicit false


/-- The `(i,b)`-th `D_z`-slot Leibniz summand of `H4PairInt α (f · D_θ g) g`:
`binom(i,b) · D_z^b f · D_z^{i-b}(D_θ g) · D_z^i g · Whz²`. -/
def xD (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) : ℝ :=
  (i.choose b : ℝ) * (Work.Spaces.DzIter b f z θ * Work.Spaces.mixed (i - b) 1 g z θ
    * Work.Spaces.DzIter i g z θ * (Whz z θ) ^ 2)

/-- The `(i,j,a,b)`-th mixed-slot Leibniz summand of `H4PairInt α (f · D_θ g) g`:
`binom(i,a) binom(j,b) · D_z^b D_θ^a f · D_z^{j-b} D_θ^{i-a+1} g · D_z^j D_θ^i g · Wm²`. -/
def yM (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (z θ : ℝ) : ℝ :=
  ((i.choose a : ℝ) * (j.choose b : ℝ)) *
    (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a + 1) g z θ
      * Work.Spaces.mixed j i g z θ * (Wm α z θ) ^ 2)


/-- The pointwise majorant of `GoodInt`: the sum of the absolute values of the Leibniz
summands appearing in `EasySum`. -/
def EasyMajor (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
      if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|)
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
          else 0)

/-! ## Elementary rewriting and comparison lemmas

The lemmas below are the small facts that the expansion of `GoodInt` (in which the
`D_θ`-derivative hidden in `xD`, `yM` has to commute with the `D_z`-iterates) and the
term-by-term bound of `EasySum` (in which the `η`-weight `Whz` has to be compared with
the `γ`-weight `Wm`) repeatedly need. -/

/-- The `D_θ`-iterate of `D_θ g` is the next iterate of `g`: `D_z^jD_θ^i(D_θ g) =
D_z^jD_θ^{i+1} g`. -/
theorem mixed_Dth (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth g) = Work.Spaces.mixed j (i + 1) g := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dth g))
      = Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) g)
  rw [show Work.Spaces.Dth g = Work.Spaces.DthIter 1 g from rfl,
    Work.Spaces.DthIter_add_right i 1 g]



/-- On the closed quadrant the `η`-weight is dominated by the `γ`-weight:
`Whz z θ ≤ Wm α z θ`. -/
theorem Whz_le_Wm {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Whz z θ ≤ Wm α z θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hγη : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    have h1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
    have h2 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
    linarith
  have hw : 0 ≤ Work.Spaces.w z := by simp only [Work.Spaces.w]; positivity
  have hWhz : Whz z θ = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [Whz, div_eq_mul_inv, Real.rpow_neg hs0]
  have hWm : Wm α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Wm, Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [hWhz, hWm]
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs, Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta / 2) ≠ 0),
      Real.zero_rpow (by
        intro hh
        have := Work.Spaces.gam_pos hα
        linarith)]
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)) hw


/-! ## The `g`-slot bounds -/







end Work.FTS.H2.Transport3Aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.DthIter_five_Sfun_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The derivative of the quartic profile occurring in `D_θ^4(sin 2·)`. -/
theorem deriv_five_Sfun_aux (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')
        * (16 * Real.cos (2 * θ') ^ 4 - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
          + 80 * Real.sin (2 * θ') ^ 4)) θ
      = 2 * Real.cos (2 * θ)
          * (16 * Real.cos (2 * θ) ^ 4 - 288 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2
            + 80 * Real.sin (2 * θ) ^ 4)
        + Real.sin (2 * θ)
          * (-1280 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ)
            + 1792 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 3) := by
  have hA : HasDerivAt (fun θ' : ℝ => 16 * Real.cos (2 * θ') ^ 4)
      (-128 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ)) θ := by
    convert ((Work.FTS.H2.hasDerivAt_cos_two θ).pow 4).const_mul (16 : ℝ) using 1
    ring
  have hB : HasDerivAt
      (fun θ' : ℝ => 288 * (Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2))
      (288 * (-4 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 3
        + 4 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ))) θ := by
    have h := (((Work.FTS.H2.hasDerivAt_cos_two θ).pow 2).mul
      ((Work.FTS.H2.hasDerivAt_sin_two θ).pow 2)).const_mul (288 : ℝ)
    convert h using 1 <;>
      (try funext θ') <;> (try simp only [Pi.pow_apply, Pi.mul_apply]) <;> ring_nf
  have hC : HasDerivAt (fun θ' : ℝ => 80 * Real.sin (2 * θ') ^ 4)
      (640 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 3) θ := by
    convert ((Work.FTS.H2.hasDerivAt_sin_two θ).pow 4).const_mul (80 : ℝ) using 1
    ring
  have hQ : HasDerivAt (fun θ' : ℝ => 16 * Real.cos (2 * θ') ^ 4
      - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
      + 80 * Real.sin (2 * θ') ^ 4)
      (-1280 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ)
        + 1792 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 3) θ := by
    have h := (hA.sub hB).add hC
    convert h using 1 <;>
      (try funext θ') <;>
      (try simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]) <;> ring_nf
  have hS := Work.FTS.H2.hasDerivAt_sin_two θ
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ')
        * (16 * Real.cos (2 * θ') ^ 4 - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
          + 80 * Real.sin (2 * θ') ^ 4))
      = (fun θ' : ℝ => Real.sin (2 * θ')) * (fun θ' : ℝ => 16 * Real.cos (2 * θ') ^ 4
          - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
          + 80 * Real.sin (2 * θ') ^ 4) := rfl
  rw [hfun, (hS.mul hQ).deriv]

/-- `D_θ^5 (sin 2·)`, explicitly. -/
theorem DthIter_five_Sfun :
    Work.Spaces.DthIter 5 Work.FTS.H2.Sfun
      = fun _ θ => Real.sin (2 * θ)
          * (32 * Real.cos (2 * θ) ^ 5
              - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
              + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4) := by
  funext z θ
  rw [show Work.Spaces.DthIter 5 Work.FTS.H2.Sfun
      = Work.Spaces.Dth (Work.Spaces.DthIter 4 Work.FTS.H2.Sfun) from rfl,
    Work.FTS.H2.DthIter_four_Sfun]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => Real.sin (2 * θ')
      * (16 * Real.cos (2 * θ') ^ 4 - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
        + 80 * Real.sin (2 * θ') ^ 4)) θ
      = Real.sin (2 * θ)
          * (32 * Real.cos (2 * θ) ^ 5
              - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
              + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4)
  rw [deriv_five_Sfun_aux θ]
  ring

/-- The fifth `D_θ`-iterate of `sin(2·)` is bounded by `3840` on the open quadrant. -/
theorem abs_DthIter_five_Sfun_le (z θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |Work.Spaces.DthIter 5 Work.FTS.H2.Sfun z θ| ≤ 3840 := by
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hc5 : |Real.cos (2 * θ) ^ 5| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc
  have hc3 : |Real.cos (2 * θ) ^ 3| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc
  have hs2 : |Real.sin (2 * θ) ^ 2| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs
  have hs4 : |Real.sin (2 * θ) ^ 4| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs
  have e1 : |(32 : ℝ) * Real.cos (2 * θ) ^ 5| ≤ 32 := by
    rw [abs_mul, show |(32 : ℝ)| = 32 by norm_num]
    nlinarith [hc5]
  have h32 : |Real.cos (2 * θ) ^ 3| * |Real.sin (2 * θ) ^ 2| ≤ 1 := by
    calc |Real.cos (2 * θ) ^ 3| * |Real.sin (2 * θ) ^ 2| ≤ 1 * 1 :=
          mul_le_mul hc3 hs2 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have e2 : |(1856 : ℝ) * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2| ≤ 1856 := by
    rw [show (1856 : ℝ) * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
        = 1856 * (Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2) from by ring,
      abs_mul, show |(1856 : ℝ)| = 1856 by norm_num, abs_mul]
    have h := mul_le_mul_of_nonneg_left h32 (by norm_num : (0:ℝ) ≤ 1856)
    linarith
  have h19 : |Real.cos (2 * θ)| * |Real.sin (2 * θ) ^ 4| ≤ 1 := by
    calc |Real.cos (2 * θ)| * |Real.sin (2 * θ) ^ 4| ≤ 1 * 1 :=
          mul_le_mul hc hs4 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have e3 : |(1952 : ℝ) * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4| ≤ 1952 := by
    rw [show (1952 : ℝ) * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4
        = 1952 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4) from by ring,
      abs_mul, show |(1952 : ℝ)| = 1952 by norm_num, abs_mul]
    have h := mul_le_mul_of_nonneg_left h19 (by norm_num : (0:ℝ) ≤ 1952)
    linarith
  have e4 := Work.FTS.H2.abs_sub_le_abs_add ((32 : ℝ) * Real.cos (2 * θ) ^ 5)
    ((1856 : ℝ) * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2)
  have e5 := abs_add_le (((32 : ℝ) * Real.cos (2 * θ) ^ 5
      - (1856 : ℝ) * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2))
    ((1952 : ℝ) * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4)
  have hpoly : |32 * Real.cos (2 * θ) ^ 5
      - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
      + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4| ≤ 3840 := by
    linarith
  have hval : Work.Spaces.DthIter 5 Work.FTS.H2.Sfun z θ
      = Real.sin (2 * θ)
          * (32 * Real.cos (2 * θ) ^ 5
              - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
              + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4) := by
    rw [DthIter_five_Sfun]
  rw [hval, abs_mul]
  calc |Real.sin (2 * θ)| * |32 * Real.cos (2 * θ) ^ 5
        - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
        + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4|
      ≤ 1 * 3840 :=
        mul_le_mul hs hpoly (abs_nonneg _) (by norm_num)
    _ = 3840 := by norm_num

theorem DthIter_five_Sfun_bound : ∃ M : ℝ, 0 < M ∧ ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → |Work.Spaces.DthIter 5 Work.FTS.H2.Sfun z θ| ≤ M := by
  exact ⟨3840, by norm_num, fun z θ hθ hθ' => abs_DthIter_five_Sfun_le z θ hθ hθ'⟩

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.DzBoundR2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

namespace Work.FTS.StrongEps.ClassCRHS

set_option autoImplicit false

/-- The substitution `x = z/(1+z)` transporting `D_z = z ∂_z` into `x(1-x) ∂_x`. -/
def xtR2 (z : ℝ) : ℝ := z / (1 + z)

/-- The `i`-th `D_z`-iterate of `SR2` in the variable `x = z/(1+z)`: the `i`-fold
application of `x(1-x) ∂_x` to `2x²(1-x)(1-2x)`. -/
def polyR2 : ℕ → ℝ → ℝ
  | 0 => fun x => 2 * x ^ 2 - 6 * x ^ 3 + 4 * x ^ 4
  | 1 => fun x => 4 * x ^ 2 - 22 * x ^ 3 + 34 * x ^ 4 - 16 * x ^ 5
  | 2 => fun x => 8 * x ^ 2 - 74 * x ^ 3 + 202 * x ^ 4 - 216 * x ^ 5 + 80 * x ^ 6
  | 3 => fun x => 16 * x ^ 2 - 238 * x ^ 3 + 1030 * x ^ 4 - 1888 * x ^ 5 + 1560 * x ^ 6
                - 480 * x ^ 7
  | 4 => fun x => 32 * x ^ 2 - 746 * x ^ 3 + 4834 * x ^ 4 - 13560 * x ^ 5 + 18800 * x ^ 6
                - 12720 * x ^ 7 + 3360 * x ^ 8
  | _ => fun _ => 0

/-- The ordinary derivative of `polyR2 k`, for `k ≤ 3`. -/
def dpolyR2 : ℕ → ℝ → ℝ
  | 0 => fun x => 4 * x - 18 * x ^ 2 + 16 * x ^ 3
  | 1 => fun x => 8 * x - 66 * x ^ 2 + 136 * x ^ 3 - 80 * x ^ 4
  | 2 => fun x => 16 * x - 222 * x ^ 2 + 808 * x ^ 3 - 1080 * x ^ 4 + 480 * x ^ 5
  | 3 => fun x => 32 * x - 714 * x ^ 2 + 4120 * x ^ 3 - 9440 * x ^ 4 + 9360 * x ^ 5
                - 3360 * x ^ 6
  | _ => fun _ => 0

/-- The polynomial cofactor of `polyR2 i`: `polyR2 i x = x²(1-x)·AR2 i x`. -/
def AR2 : ℕ → ℝ → ℝ
  | 0 => fun x => 2 - 4 * x
  | 1 => fun x => 4 - 18 * x + 16 * x ^ 2
  | 2 => fun x => 8 - 66 * x + 136 * x ^ 2 - 80 * x ^ 3
  | 3 => fun x => 16 - 222 * x + 808 * x ^ 2 - 1080 * x ^ 3 + 480 * x ^ 4
  | 4 => fun x => 32 - 714 * x + 4120 * x ^ 2 - 9440 * x ^ 3 + 9360 * x ^ 4 - 3360 * x ^ 5
  | _ => fun _ => 0

/-- The explicit derivative of `polyR2 k` for `k ≤ 3`. -/
lemma hasDerivAt_polyR2 : ∀ k : ℕ, k ≤ 3 → ∀ x : ℝ,
    HasDerivAt (polyR2 k) (dpolyR2 k x) x := by
  intro k hk x
  interval_cases k
  · exact (by
      have h2 : HasDerivAt (fun y : ℝ => 2 * y ^ 2 - 6 * y ^ 3 + 4 * y ^ 4)
          (4 * x - 18 * x ^ 2 + 16 * x ^ 3) x := by
        have hc := (((hasDerivAt_pow 2 x).const_mul 2).sub
          ((hasDerivAt_pow 3 x).const_mul 6)).add ((hasDerivAt_pow 4 x).const_mul 4)
        convert hc using 1
        norm_num
        ring
      exact h2)
  · exact (by
      have h2 : HasDerivAt (fun y : ℝ => 4 * y ^ 2 - 22 * y ^ 3 + 34 * y ^ 4 - 16 * y ^ 5)
          (8 * x - 66 * x ^ 2 + 136 * x ^ 3 - 80 * x ^ 4) x := by
        have hc := ((((hasDerivAt_pow 2 x).const_mul 4).sub
          ((hasDerivAt_pow 3 x).const_mul 22)).add
          ((hasDerivAt_pow 4 x).const_mul 34)).sub ((hasDerivAt_pow 5 x).const_mul 16)
        convert hc using 1
        norm_num
        ring
      exact h2)
  · exact (by
      have h2 : HasDerivAt
          (fun y : ℝ => 8 * y ^ 2 - 74 * y ^ 3 + 202 * y ^ 4 - 216 * y ^ 5 + 80 * y ^ 6)
          (16 * x - 222 * x ^ 2 + 808 * x ^ 3 - 1080 * x ^ 4 + 480 * x ^ 5) x := by
        have hc := (((((hasDerivAt_pow 2 x).const_mul 8).sub
          ((hasDerivAt_pow 3 x).const_mul 74)).add
          ((hasDerivAt_pow 4 x).const_mul 202)).sub
          ((hasDerivAt_pow 5 x).const_mul 216)).add ((hasDerivAt_pow 6 x).const_mul 80)
        convert hc using 1
        norm_num
        ring
      exact h2)
  · exact (by
      have h2 : HasDerivAt
          (fun y : ℝ => 16 * y ^ 2 - 238 * y ^ 3 + 1030 * y ^ 4 - 1888 * y ^ 5
            + 1560 * y ^ 6 - 480 * y ^ 7)
          (32 * x - 714 * x ^ 2 + 4120 * x ^ 3 - 9440 * x ^ 4 + 9360 * x ^ 5
            - 3360 * x ^ 6) x := by
        have hc := ((((((hasDerivAt_pow 2 x).const_mul 16).sub
          ((hasDerivAt_pow 3 x).const_mul 238)).add
          ((hasDerivAt_pow 4 x).const_mul 1030)).sub
          ((hasDerivAt_pow 5 x).const_mul 1888)).add
          ((hasDerivAt_pow 6 x).const_mul 1560)).sub ((hasDerivAt_pow 7 x).const_mul 480)
        convert hc using 1
        norm_num
        ring
      exact h2)

/-- The recursion `polyR2 (k+1) x = x(1-x)·(polyR2 k)' x`, for `k ≤ 3`. -/
lemma step_polyR2 : ∀ k : ℕ, k ≤ 3 → ∀ x : ℝ,
    x * (1 - x) * dpolyR2 k x = polyR2 (k + 1) x := by
  intro k hk x
  interval_cases k <;> (simp only [dpolyR2, polyR2]; ring)

/-- `polyR2 i` is `x²(1-x)` times the polynomial `AR2 i`. -/
lemma factor_polyR2 : ∀ i : ℕ, i ≤ 4 → ∀ x : ℝ,
    polyR2 i x = x ^ 2 * (1 - x) * AR2 i x := by
  intro i hi x
  interval_cases i <;> (simp only [polyR2, AR2]; ring)

/-- The cofactors `AR2 i`, `i ≤ 4`, are bounded by `30000` on `[0,1]` (their coefficient
`ℓ¹`-norms are `6, 38, 290, 2606, 27026`). -/
lemma cof_bound : ∀ i : ℕ, i ≤ 4 → ∀ x : ℝ, 0 ≤ x → x ≤ 1 → |AR2 i x| ≤ 30000 := by
  intro i hi x hx0 hx1
  interval_cases i
  all_goals
    simp only [AR2]
    refine abs_le.mpr ⟨?_, ?_⟩ <;>
      nlinarith [hx0, hx1, pow_le_one₀ (n := 2) hx0 hx1, pow_le_one₀ (n := 3) hx0 hx1,
        pow_le_one₀ (n := 4) hx0 hx1, pow_le_one₀ (n := 5) hx0 hx1,
        pow_nonneg hx0 2, pow_nonneg hx0 3, pow_nonneg hx0 4, pow_nonneg hx0 5]

/-- `x ↦ z/(1+z)` has derivative `1/(1+z)²` at `z ≠ -1`. -/
lemma hasDerivAt_xtR2 (z : ℝ) (hz : 1 + z ≠ 0) :
    HasDerivAt xtR2 (1 / (1 + z) ^ 2) z := by
  have hden : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    convert ((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)) using 1
    · funext w; simp
    · simp
  have h2 : HasDerivAt (fun w : ℝ => w / (1 + w)) (1 / (1 + z) ^ 2) z := by
    have h := (hasDerivAt_id z).div hden (by simpa using hz)
    convert h using 1
    · funext w
      simp [Pi.div_apply]
    · simp only [id_eq]
      field_simp
      ring
  exact h2

/-- `z·(1+z)^{-2} = x(1-x)` for `x = z/(1+z)`. -/
lemma mul_xtR2 (z : ℝ) (hz : 1 + z ≠ 0) : z * (1 / (1 + z) ^ 2) = xtR2 z * (1 - xtR2 z) := by
  simp only [xtR2]
  field_simp
  ring

/-- `x²(1-x) = z²/(1+z)³` for `x = z/(1+z)`. -/
lemma sq_xtR2 (z : ℝ) (hz : 1 + z ≠ 0) : (xtR2 z) ^ 2 * (1 - xtR2 z) = z ^ 2 / (1 + z) ^ 3 := by
  simp only [xtR2]
  field_simp
  ring

/-- `SR2` in the variable `x = z/(1+z)`. -/
lemma SR2_eq_polyR2 (z : ℝ) (hz : 1 + z ≠ 0) : SR2 z = polyR2 0 (xtR2 z) := by
  simp only [SR2, xtR2, polyR2]
  field_simp
  ring

/-- The `D_z`-iterates of `SR2`, expressed through the substitution `x = z/(1+z)`. -/
lemma DzdIter_SR2_eq (i : ℕ) (hi : i ≤ 4) : ∀ z : ℝ, 1 + z ≠ 0 →
    Work.Elliptic.DzdIter i SR2 z = polyR2 i (xtR2 z) := by
  induction i with
  | zero =>
      intro z hz
      simpa only [Work.Elliptic.DzdIter_zero, polyR2] using SR2_eq_polyR2 z hz
  | succ k ih =>
      intro z hz
      have hk4 : k ≤ 4 := le_trans (Nat.le_succ k) hi
      have hk3 : k ≤ 3 := by omega
      have hev : Work.Elliptic.DzdIter k SR2 =ᶠ[nhds z] fun w => polyR2 k (xtR2 w) := by
        filter_upwards [eventually_ne_nhds (show z ≠ -1 by intro h; exact hz (by linarith))]
          with w hw
        exact ih hk4 w (by intro h; exact hw (by linarith))
      have hcomp : deriv (fun w => polyR2 k (xtR2 w)) z
          = dpolyR2 k (xtR2 z) * (1 / (1 + z) ^ 2) := by
        have hX := hasDerivAt_xtR2 z hz
        have hp := hasDerivAt_polyR2 k hk3 (xtR2 z)
        exact (hp.comp z hX).deriv
      rw [show Work.Elliptic.DzdIter (k + 1) SR2 z
            = z * deriv (Work.Elliptic.DzdIter k SR2) z from rfl,
        hev.deriv_eq, hcomp]
      rw [show z * (dpolyR2 k (xtR2 z) * (1 / (1 + z) ^ 2))
            = xtR2 z * (1 - xtR2 z) * dpolyR2 k (xtR2 z) from by
          calc z * (dpolyR2 k (xtR2 z) * (1 / (1 + z) ^ 2))
              = (z * (1 / (1 + z) ^ 2)) * dpolyR2 k (xtR2 z) := by ring
            _ = (xtR2 z * (1 - xtR2 z)) * dpolyR2 k (xtR2 z) := by rw [mul_xtR2 z hz]]
      rw [step_polyR2 k hk3 (xtR2 z)]

/-- `|DzdIter i SR2 z| ≤ 30000 z²/(1+z)³` for `i ≤ 4` and `z ≥ 0`. -/
theorem DzdIter_SR2_bound (i : ℕ) (hi : i ≤ 4) (z : ℝ) (hz0 : 0 ≤ z) :
    |Work.Elliptic.DzdIter i SR2 z| ≤ 30000 * z ^ 2 / (1 + z) ^ 3 := by
  have hz : 1 + z ≠ 0 := by positivity
  rw [DzdIter_SR2_eq i hi z hz, factor_polyR2 i hi (xtR2 z)]
  have hx0 : 0 ≤ xtR2 z := by simp only [xtR2]; positivity
  have hx1 : xtR2 z ≤ 1 := by
    simp only [xtR2]
    rw [div_le_one (by linarith : (0 : ℝ) < 1 + z)]
    linarith
  have hnn : 0 ≤ (xtR2 z) ^ 2 * (1 - xtR2 z) := by
    nlinarith [sq_nonneg (xtR2 z), hx1]
  have hcof := cof_bound i hi (xtR2 z) hx0 hx1
  calc |(xtR2 z) ^ 2 * (1 - xtR2 z) * AR2 i (xtR2 z)|
      = (xtR2 z) ^ 2 * (1 - xtR2 z) * |AR2 i (xtR2 z)| := by
        rw [abs_mul, abs_of_nonneg hnn]
    _ ≤ (xtR2 z) ^ 2 * (1 - xtR2 z) * 30000 := mul_le_mul_of_nonneg_left hcof hnn
    _ = 30000 * z ^ 2 / (1 + z) ^ 3 := by rw [sq_xtR2 z hz]; ring

theorem DzBoundR2 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 4 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR2 z|
      ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  exact ⟨30000, by norm_num, fun i hi z hz0 => DzdIter_SR2_bound i hi z hz0⟩

end Work.FTS.StrongEps.ClassCRHS
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.RadProfiles =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Polynomial

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The substitution `x = z/(1+z)`

Under `x = z/(1+z)` the operator `D_z = z ∂_z` becomes `x(1-x) ∂_x`: the chain rule gives
`∂_z (F ∘ Xd) = (1+z)^{-2} · (F' ∘ Xd)` and `z (1+z)^{-2} = x(1-x)`.

All three profiles have the shape `z² p(x)/(1+z)³` with `p` a polynomial in `x`, i.e.
`f z = x²(1-x)·r(x)`.  Since `x²(1-x) = z²/(1+z)³`, the whole problem reduces to iterating
the purely polynomial operator `Red r = (2-3x)·r + x(1-x)·r'` on the cofactor `r`, together
with a bound for the (polynomial) cofactors on the compact interval `[0,1]`.
-/

/-- The substitution `x = z/(1+z)`. -/
def Xd (z : ℝ) : ℝ := z / (1 + z)







/-! ## The polynomial operator `Red` -/

/-- The operator on the cofactor: if `p = X²(1-X)·r`, then `X(1-X)·p' = X²(1-X)·Red r`. -/
def Red (r : ℝ[X]) : ℝ[X] := (C 2 - C 3 * X) * r + X * (1 - X) * r.derivative

/-- The iterates of `Red`. -/
def RedIter : ℕ → ℝ[X] → ℝ[X]
  | 0, r => r
  | k + 1, r => Red (RedIter k r)

@[simp] lemma RedIter_zero (r : ℝ[X]) : RedIter 0 r = r := rfl

@[simp] lemma RedIter_succ (k : ℕ) (r : ℝ[X]) : RedIter (k + 1) r = Red (RedIter k r) := rfl




/-! ## Congruence of `D_z`-iterates on open sets -/

/-- The `D_z`-iterates agree on an open set on which the functions agree. -/
lemma DzdIter_congr_of_eqOn {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (h : Set.EqOn f g U)
    (i : ℕ) : Set.EqOn (Work.Elliptic.DzdIter i f) (Work.Elliptic.DzdIter i g) U := by
  induction i with
  | zero => simpa using h
  | succ k ih =>
      intro z hz
      have hev : Work.Elliptic.DzdIter k f =ᶠ[𝓝 z] Work.Elliptic.DzdIter k g := by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact ih hw
      simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
      rw [hev.deriv_eq]

/-! ## The three profiles in the variable `x = z/(1+z)`

* `SR0 z = 2z²/(1+z)³ = x²(1-x)·2`,
* `SR2 z = 2z²(1-z)/(1+z)⁴ = x²(1-x)·(2-4x)`,
* `hKer z ^ 2 = z²/(1+z)⁴ = x²(1-x)·(1-x)`. -/




/-! ## The cofactors are bounded on `[0,1]` -/



/-! ## The main theorem -/


end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

set_option maxHeartbeats 1000000

/-! ## The `D_z`-jets of `L₁₂(F_*) = 2α/(1+z)`

Self-contained version of the (private) `NonlinRows.NRow7.DzdIter_L12Fstar_le`, in the
two-variable `Spaces.DzIter` form needed by the `theta_part_jets` assembly. -/

/-- `∂_z^k` of a radial function. -/
theorem pzIter_radial' (r : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => r z) z θ = deriv^[k] r z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      have hfun : (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) = deriv^[k] r :=
        funext fun z' => ih z'
      show deriv (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) z = deriv^[k + 1] r z
      rw [hfun, Function.iterate_succ_apply']

/-- `2α/(1+z)` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_invH' (α : ℝ) :
    ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi (-1)) := by
  have h : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z)⁻¹) (Set.Ioi (-1)) := by
    refine ContDiffOn.inv (by fun_prop) ?_
    intro z hz
    simp only [Set.mem_Ioi] at hz
    linarith
  have h2 : ContDiffOn ℝ ⊤ (fun z : ℝ => (2 * α) * (1 + z)⁻¹) (Set.Ioi (-1)) :=
    contDiffOn_const.mul h
  refine h2.congr ?_
  intro z _
  simp only [div_eq_mul_inv]

/-- `|z^j ∂_z^j (2α/(1+z))| ≤ 48α` for `z ≥ 0`, `j ≤ 4`. -/
theorem pzIter_invH_bound' (α : ℝ) (hα : 0 < α) (j : ℕ) (hj : j ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ j * Work.Spaces.pzIter j (fun z _ => 2 * α / (1 + z)) z θ| ≤ 48 * α := by
  intro z hzIz θ _
  have hz0 : (0 : ℝ) ≤ z := hzIz
  rw [pzIter_radial' (fun z => 2 * α / (1 + z)) j z θ]
  rw [show (fun z : ℝ => 2 * α / (1 + z)) = fun z => (2 * α) * (1 + z)⁻¹ from by
    funext z; rw [div_eq_mul_inv]]
  rw [Work.FTS.Nonlinear.FstarPkg.deriv_iter_const_mul (2 * α) (fun z : ℝ => (1 + z)⁻¹) j]
  simp only
  rw [Work.FTS.Nonlinear.FstarPkg.iter_deriv_nInvClosed j z (by linarith)]
  have hw := Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted j z hz0
  have habs : z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|
      ≤ |(z + 1) ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) j)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 (by linarith) j) (abs_nonneg _)
  have hkey : z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| ≤ (j.factorial : ℝ) :=
    le_trans habs hw
  have hfact : (j.factorial : ℝ) ≤ 24 := by interval_cases j <;> norm_num
  have h2α : (0 : ℝ) < 2 * α := by linarith
  rw [show z ^ j * ((2 * α) * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z)
      = (2 * α) * (z ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z) from by ring]
  rw [abs_mul, abs_of_nonneg h2α.le]
  calc (2 * α) * |z ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|
      = (2 * α) * (z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
    _ ≤ (2 * α) * (j.factorial : ℝ) := mul_le_mul_of_nonneg_left hkey h2α.le
    _ ≤ (2 * α) * 24 := mul_le_mul_of_nonneg_left hfact h2α.le
    _ = 48 * α := by ring

/-- **The `D_z`-jets of `L₁₂(F_*)` are bounded by `4800α`.** -/
theorem L12Fstar_jets' : ∃ C : ℝ, 0 < C ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter k (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z)
        z 0| ≤ C * α := by
  refine ⟨4800, by norm_num, ?_⟩
  intro α hα hα1 k hk z hz
  have hcongr : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Fstar α) w = 2 * α / (1 + w) :=
    fun w hw => Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1
      (by have hw' : (0 : ℝ) < w := hw; linarith)
  have h1 : Work.Spaces.DzIter k (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z)
        z 0 = Work.Spaces.DzIter k (fun z _ => 2 * α / (1 + z)) z 0 :=
    Work.FTS_RegExport.RXT.SysAux.DzIter_congr_of_isOpen (isOpen_Ioi.prod isOpen_univ)
      (by rintro ⟨a, b⟩ ⟨ha, -⟩; exact hcongr a ha) k z 0 ⟨hz, trivial⟩
  rw [h1]
  have hmain := Work.Spaces.DzIter_le_of_pzIter (h := fun z _ => 2 * α / (1 + z)) (M := 48 * α)
    (by positivity)
    (fun θ _ => contDiffOn_invH' α)
    (fun j hj z' hz' θ hθ => pzIter_invH_bound' α hα j hj z' hz' θ hθ)
    k (by omega) z (le_of_lt hz) 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
  linarith [hmain]

end

end Work.FTS_StreamBdry.Inputs
end
