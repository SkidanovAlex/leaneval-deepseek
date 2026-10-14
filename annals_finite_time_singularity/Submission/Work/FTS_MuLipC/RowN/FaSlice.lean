import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound
import Submission.Work.FTS.BSSwirl.lintegral_inv_norm_mul_ball_indicator_le
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Filter
open scoped Topology
open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-- **Reduction of the Hölder exponent.**  If `ω` is bounded by `M ≥ 0` and Hölder of exponent
`c > 0`, then it is Hölder with the (smaller) exponent `min c (1/2) < 1` and the (larger)
constant `max C (2M)`.  The estimates of the difference quotient need the exponent strictly
below `1`. -/
theorem holder_reduce {ω : R3 → R3} {M C c : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) :
    ∃ c' C' : ℝ, 0 < c' ∧ c' < 1 ∧ 0 ≤ C' ∧
      ∀ a b : R3, ‖ω a - ω b‖ ≤ C' * ‖a - b‖ ^ c' := by
  refine ⟨min c (1 / 2), max C (2 * M), lt_min hc (by norm_num),
    min_lt_of_right_lt (by norm_num), le_trans (by linarith : (0:ℝ) ≤ 2 * M) (le_max_right _ _),
    ?_⟩
  have hc' : (0:ℝ) < min c (1 / 2) := lt_min hc (by norm_num)
  have hC'nn : (0:ℝ) ≤ max C (2 * M) :=
    le_trans (by linarith : (0:ℝ) ≤ 2 * M) (le_max_right _ _)
  intro a b
  by_cases hab : a = b
  · subst hab
    rw [sub_self, norm_zero, sub_self, norm_zero]
    exact mul_nonneg hC'nn (Real.rpow_nonneg le_rfl _)
  have hx0 : (0:ℝ) < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have h1 : ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c := hhold a b
  by_cases hle : ‖a - b‖ ≤ 1
  · have hpow : ‖a - b‖ ^ c ≤ ‖a - b‖ ^ (min c (1 / 2)) := by
      have hsplit : ‖a - b‖ ^ c
          = ‖a - b‖ ^ (min c (1/2)) * ‖a - b‖ ^ (c - min c (1/2)) := by
        rw [← Real.rpow_add hx0, show min c (1/2) + (c - min c (1/2)) = c by ring]
      have hle1 : ‖a - b‖ ^ (c - min c (1/2)) ≤ 1 :=
        Real.rpow_le_one hx0.le hle (by linarith [min_le_left c (1/2)])
      rw [hsplit]
      nlinarith [Real.rpow_nonneg hx0.le (min c (1/2)), hle1]
    by_cases hC : 0 ≤ C
    · calc ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c := h1
        _ ≤ (max C (2 * M)) * ‖a - b‖ ^ c :=
            mul_le_mul_of_nonneg_right (le_max_left C (2 * M)) (Real.rpow_nonneg hx0.le c)
        _ ≤ (max C (2 * M)) * ‖a - b‖ ^ (min c (1 / 2)) :=
            mul_le_mul_of_nonneg_left hpow hC'nn
    · have hneg : C * ‖a - b‖ ^ c ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hC)) (Real.rpow_nonneg hx0.le c)
      calc ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c := h1
        _ ≤ 0 := hneg
        _ ≤ (max C (2 * M)) * ‖a - b‖ ^ (min c (1 / 2)) :=
            mul_nonneg hC'nn (Real.rpow_nonneg hx0.le _)
  · have hx1 : (1:ℝ) ≤ ‖a - b‖ := le_of_lt (not_le.mp hle)
    have h2M : ‖ω a - ω b‖ ≤ 2 * M := by
      calc ‖ω a - ω b‖ ≤ ‖ω a‖ + ‖ω b‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hbdd a) (hbdd b)
        _ = 2 * M := by ring
    have hone : (1:ℝ) ≤ ‖a - b‖ ^ (min c (1/2)) :=
      Real.one_le_rpow hx1 (le_min hc.le (by norm_num))
    calc ‖ω a - ω b‖ ≤ 2 * M := h2M
      _ ≤ (max C (2 * M)) * ‖a - b‖ ^ (min c (1 / 2)) := by
          have h3 : (2:ℝ) * M * 1 ≤ (2:ℝ) * M * ‖a - b‖ ^ (min c (1/2)) :=
            mul_le_mul_of_nonneg_left hone (by linarith)
          have h4 : (2:ℝ) * M ≤ max C (2 * M) := by
            rw [show (2:ℝ) * M = 2 * M from rfl]; exact le_max_right _ _
          nlinarith [h4, Real.rpow_nonneg (norm_nonneg (a - b)) (min c (1/2))]

/-- **Little-o relation** `‖h‖^{1+c} = o(‖h‖)` at `h = 0` for `c > 0`, the form in which the
difference-quotient bound feeds `HasFDerivAt`. -/
theorem isLittleO_norm_rpow {c : ℝ} (hc : 0 < c) :
    (fun h : R3 => ‖h‖ ^ (1 + c)) =o[𝓝 (0 : R3)] (fun h : R3 => h) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hεc : (0:ℝ) < ε ^ (1 / c) := Real.rpow_pos_of_pos hε _
  filter_upwards [Metric.ball_mem_nhds (0 : R3) hεc] with h hh
  have hnorm : ‖h‖ < ε ^ (1 / c) := by simpa [dist_eq_norm] using hh
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg h) _)]
  change ‖h‖ ^ (1 + c) ≤ ε * ‖h‖
  rcases eq_or_lt_of_le (norm_nonneg h) with h0 | h0
  · rw [← h0, Real.zero_rpow (by linarith : (1:ℝ) + c ≠ 0), mul_zero]
  · have hpow : ‖h‖ ^ c ≤ ε := by
      have h1 : ‖h‖ ^ c ≤ (ε ^ (1 / c)) ^ c := Real.rpow_le_rpow h0.le hnorm.le hc.le
      rwa [← Real.rpow_mul hε.le, one_div, inv_mul_cancel₀ (ne_of_gt hc), Real.rpow_one] at h1
    rw [Real.rpow_add h0, Real.rpow_one]
    nlinarith [hpow, h0]

/-- **`bsField ω ρ` is differentiable wherever the ball does not touch the support.**  The
difference-quotient bound `norm_bsField_diff_bound` gives an error of order `‖h‖^{1+c}`, and
`‖h‖^{1+c} = o(‖h‖)` (`isLittleO_norm_rpow`). -/
theorem hasFDerivAt_bsField {ω : R3 → R3} {R M C c : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hc : 0 < c)
    (hc1 : c < 1) (hC : 0 ≤ C) (hbdd : ∀ a, ‖ω a‖ ≤ M)
    (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    {ρ : ℝ} {x : R3} (hρ : R + ‖x‖ < ρ) :
    HasFDerivAt (bsField ω ρ) (bsDerivCLM ω ρ x) x := by
  obtain ⟨K, hK0, hK⟩ := norm_bsField_diff_bound hR hM hc hc1 hC hbdd hs hm hhold
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.trans_isLittleO ?_ (isLittleO_norm_rpow hc))
  refine Asymptotics.isBigO_iff.2 ⟨K, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : R3) (sub_pos.mpr hρ)] with h hh
  have hhρ : R + ‖x‖ + ‖h‖ < ρ := by
    have h2 : ‖h‖ < ρ - (R + ‖x‖) := by simpa [dist_eq_norm] using hh
    linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg h) _)]
  exact hK ρ x h hhρ

/-- **`C¹` of the Biot–Savart field (the Calderón–Zygmund chapter).**  For a vorticity `ω` that is
bounded, supported in `closedBall 0 R`, ae-strongly-measurable and Hölder of some positive exponent
`c` (the classical setting: `ω ∈ L^∞ ∩ C^{0,c}` compactly supported), the Newtonian-potential
Biot–Savart field is `C¹` on all of `ℝ³`.

The singularity at `x = y` is handled by the standard regularisation: since the kernel `bsK ω x a` is
odd about `a = x`, one may replace `ω` by `ω - ω x` and restrict the integral to the ball
`B(x, ρ)`, `ρ ≥ R + ‖x‖` (`biotSavart_centered`, `constant_vec_integral_ball_bsK_eq_zero`);
the resulting integrand is then dominated by `C‖x-a‖^{c-3}`, whose `a`-integral is finite and whose
`x`-derivative is dominated by `C'‖x-a‖^{c-3}`, integrable for `c > 0`.  Differentiating under the
integral sign then gives differentiability everywhere with a continuous derivative. -/
theorem biotSavart_contDiff_one {ω : Work.LWP.R3 → Work.LWP.R3} {R M C c : ℝ} (hR : 0 < R)
    (hM : 0 ≤ M) (hc : 0 < c) (hbdd : ∀ a, ‖ω a‖ ≤ M)
    (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) :
    ContDiff ℝ 1 (Work.LWP.biotSavart ω) := by
  obtain ⟨c', C', hc'0, hc'1, hC'0, hhold'⟩ := holder_reduce hc hM hbdd hhold
  rw [contDiff_iff_contDiffAt]
  intro x₀
  obtain ⟨K, hK0, hK⟩ := norm_bsField_diff_bound hR hM hc'0 hc'1 hC'0 hbdd hs hm hhold'
  set ρ : ℝ := R + ‖x₀‖ + 2 with hρdef
  have hρ' : R + ‖x₀‖ < ρ := by rw [hρdef]; linarith
  set U : Set R3 := Metric.ball x₀ 1 with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hx₀U : x₀ ∈ U := Metric.mem_ball_self one_pos
  have hUρ : ∀ x ∈ U, R + ‖x‖ < ρ := by
    intro x hx
    have h1 : ‖x - x₀‖ < 1 := by simpa [hU, dist_eq_norm] using hx
    have h2 : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
      have h := dist_triangle x x₀ 0
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero] at h
      linarith
    rw [hρdef]; linarith
  have hcont : ContinuousOn (fun x => (4 * Real.pi)⁻¹ • bsDerivCLM ω ρ x) U :=
    ((continuous_bsDerivCLM hc'0 hbdd hhold' ρ).continuousOn (s := U)).const_smul
      ((4 * Real.pi)⁻¹)
  have key : ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1)
      (fun x => (4 * Real.pi)⁻¹ • bsField ω ρ x) U := by
    rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUopen.uniqueDiffOn]
    refine ⟨fun h => absurd h (by simp), fun x => (4 * Real.pi)⁻¹ • bsDerivCLM ω ρ x, ?_, ?_⟩
    · exact contDiffOn_zero.mpr hcont
    · intro x hx
      exact ((hasFDerivAt_bsField hR hM hc'0 hc'1 hC'0 hbdd hs hm hhold'
        (hUρ x hx)).const_smul ((4 * Real.pi)⁻¹)).hasFDerivWithinAt
  have hEq : ∀ x ∈ U, Work.LWP.biotSavart ω x = (4 * Real.pi)⁻¹ • bsField ω ρ x := by
    intro x hx
    exact biotSavart_ball_integral hM hbdd hs hm (le_of_lt (hUρ x hx))
  have hkey : ContDiffOn ℝ 1 (fun x => (4 * Real.pi)⁻¹ • bsField ω ρ x) U := by
    simpa using key
  exact (hkey.congr hEq).contDiffAt (Metric.ball_mem_nhds x₀ one_pos)

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.continuousAt_biotSavart_param =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Filter
open scoped Topology
open Work.StabilityFar.Decay (crossL kf)

/-- **Continuity of the parametrised Biot–Savart integral.**

For a spacetime vorticity `ω` bounded by `M ≥ 0` on the time window `|t - t₀| < δ`, supported in
the fixed ball `B(0,R)`, with ae-strongly-measurable slices and continuous in `t` at `t₀` for every
fixed `y`, the reconstructed velocity `(x,t) ↦ BS(ω(·,t)) x` is continuous at `(x₀,t₀)`.

Suggested proof: since `hρ : R + ‖x₀‖ + 1 < ρ`, for `x ∈ B(x₀,1)` the field is the integral over
the *fixed* ball `B(0,ρ)` (`biotSavart_ball_integral`):
`(4π)⁻¹ • ∫_{B(0,ρ)} crossL (ω a t) (kf (x-a)) da`.  Split that integral at the fixed centre `x₀`
with radius `Δ > 0`: on `B(0,ρ) ∩ B(x₀,Δ)` its norm is bounded by
`M ∫_{B(x,3Δ/2)} ‖x-a‖⁻² da = 4π M (3Δ/2)`, uniformly in `x ∈ B(x₀,Δ/2)` and in `t`; on the
fixed set `B(0,ρ) \ B(x₀,Δ)` it is continuous at `(x₀,t₀)` by dominated convergence
(`MeasureTheory.continuousWithinAt_of_dominated`) with the *constant* dominating function
`M (Δ/2)⁻²` on the finite-measure set `B(0,ρ)` — for fixed `a` the integrand
`(x,t) ↦ ‖x-a‖⁻³ • (ω a t × (x-a))` is continuous away from `a = x`, and `htcont a` gives
continuity in `t`. -/
theorem continuousAt_biotSavart_param {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {δ R M ρ : ℝ} {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hρ : R + ‖x₀‖ + 1 < ρ)
    (hbdd : ∀ t : ℝ, |t - t₀| < δ → ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hsupp : ∀ t : ℝ, |t - t₀| < δ → ∀ y : Work.LWP.R3,
      ω y t ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : ∀ t : ℝ, |t - t₀| < δ →
      MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume)
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      Work.LWP.biotSavart (fun y => ω y q.2) q.1) (x₀, t₀) := by
  -- ## Step 1.  On a neighbourhood of `(x₀,t₀)` the field is the integral over the fixed ball.
  have hmem : {q : Work.LWP.R3 × ℝ | ‖q.1 - x₀‖ < 1 ∧ |q.2 - t₀| < δ} ∈ 𝓝 (x₀, t₀) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (x₀, t₀) (lt_min one_pos hδ)) ?_
    intro q hq
    rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at hq
    exact ⟨lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hq (min_le_left _ _)),
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hq (min_le_right _ _))⟩
  have hrepr : (fun q : Work.LWP.R3 × ℝ => (4 * Real.pi)⁻¹ •
        ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a q.2) (kf (q.1 - a)))
      =ᶠ[𝓝 (x₀, t₀)]
      (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1) := by
    refine Filter.mem_of_superset hmem (fun q hq => ?_)
    show (4 * Real.pi)⁻¹ • (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
        crossL (ω a q.2) (kf (q.1 - a))) = Work.LWP.biotSavart (fun y => ω y q.2) q.1
    have hR : R + ‖q.1‖ ≤ ρ := by
      have h1 : ‖q.1‖ ≤ ‖x₀‖ + 1 := by
        have h2 := norm_add_le (q.1 - x₀) x₀
        rw [sub_add_cancel] at h2
        linarith [h2, hq.1]
      linarith
    rw [biotSavart_ball_integral hM (hbdd q.2 hq.2) (hsupp q.2 hq.2) (hmeas q.2 hq.2) hR]
    simp only [bsField]
  -- ## Step 2.  The integral over the fixed ball `B(0,ρ)` is continuous at `(x₀,t₀)`.
  have hG : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
        ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a q.2) (kf (q.1 - a)))
      (x₀, t₀) := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    -- the radius of the fixed split
    set Δ : ℝ := min 1 (ε / (4 * (12 * Real.pi * M + 1))) with hΔdef
    have hden : 0 < 12 * Real.pi * M + 1 := by nlinarith [Real.pi_pos, hM]
    have hΔpos : 0 < Δ := by
      rw [hΔdef]
      exact lt_min one_pos (div_pos hε (by nlinarith [Real.pi_pos, hM]))
    have hΔsmall : 6 * Real.pi * M * Δ < ε / 8 := by
      have hden4 : 0 < 4 * (12 * Real.pi * M + 1) := by nlinarith [Real.pi_pos, hM]
      have hle : Δ ≤ ε / (4 * (12 * Real.pi * M + 1)) := by
        rw [hΔdef]; exact min_le_right _ _
      have h6 : 0 ≤ 6 * Real.pi * M := by nlinarith [Real.pi_pos, hM]
      have hstep : 6 * Real.pi * M * Δ
          ≤ 6 * Real.pi * M * (ε / (4 * (12 * Real.pi * M + 1))) :=
        mul_le_mul_of_nonneg_left hle h6
      have hcoef : 6 * Real.pi * M / (4 * (12 * Real.pi * M + 1)) < 1 / 8 := by
        rw [div_lt_iff₀ hden4]
        nlinarith [Real.pi_pos, hM]
      calc 6 * Real.pi * M * Δ
          ≤ 6 * Real.pi * M * (ε / (4 * (12 * Real.pi * M + 1))) := hstep
        _ = ε * (6 * Real.pi * M / (4 * (12 * Real.pi * M + 1))) := by ring
        _ < ε * (1 / 8) := mul_lt_mul_of_pos_left hcoef hε
        _ = ε / 8 := by ring
    -- the outer piece is continuous
    have hO : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
        ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
          crossL (ω a q.2) (kf (q.1 - a))) (x₀, t₀) :=
      continuousAt_integral_crossL_kf_diff hδ hM hΔpos hbdd hmeas htcont
    obtain ⟨r, hrpos, hr⟩ := Metric.continuousAt_iff.mp hO (ε / 2) (by linarith)
    refine ⟨min r (min (Δ / 2) δ), lt_min hrpos (lt_min (by linarith) hδ), fun q hq => ?_⟩
    have hqr : dist q (x₀, t₀) < r := lt_of_lt_of_le hq (min_le_left _ _)
    have hqΔ : ‖q.1 - x₀‖ ≤ Δ / 2 := by
      have h2 : dist q (x₀, t₀) < Δ / 2 :=
        lt_of_lt_of_le hq (le_trans (min_le_right _ _) (min_le_left _ _))
      rw [Prod.dist_eq] at h2
      have h3 : dist q.1 x₀ < Δ / 2 := lt_of_le_of_lt (le_max_left _ _) h2
      rw [dist_eq_norm] at h3
      exact le_of_lt h3
    have hqt : |q.2 - t₀| < δ := by
      have h2 : dist q (x₀, t₀) < δ :=
        lt_of_lt_of_le hq (le_trans (min_le_right _ _) (min_le_right _ _))
      rw [Prod.dist_eq, Real.dist_eq] at h2
      exact lt_of_le_of_lt (le_max_right _ _) h2
    -- the two splitting identities and the inner bound
    have hsplitq : (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a q.2) (kf (q.1 - a)))
        = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
              crossL (ω a q.2) (kf (q.1 - a)))
          + (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
              crossL (ω a q.2) (kf (q.1 - a))) :=
      integral_crossL_kf_split (ω := ω) hM (hbdd q.2 hqt) (hmeas q.2 hqt) hΔpos hqΔ
    have hsplit0 : (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a t₀) (kf (x₀ - a)))
        = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
              crossL (ω a t₀) (kf (x₀ - a)))
          + (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
              crossL (ω a t₀) (kf (x₀ - a))) :=
      integral_crossL_kf_split (ω := ω) (x := x₀) hM (hbdd t₀ (by simpa using hδ))
        (hmeas t₀ (by simpa using hδ)) hΔpos (by rw [sub_self, norm_zero]; linarith)
    rw [hsplitq, hsplit0]
    set A : Work.LWP.R3 := ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ), crossL (ω a q.2) (kf (q.1 - a)) with hA
    set B : Work.LWP.R3 := ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ), crossL (ω a q.2) (kf (q.1 - a)) with hB
    set C : Work.LWP.R3 := ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ), crossL (ω a t₀) (kf (x₀ - a)) with hC
    set D : Work.LWP.R3 := ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ), crossL (ω a t₀) (kf (x₀ - a)) with hD
    have hAb : ‖A‖ ≤ 6 * Real.pi * M * Δ := by
      rw [hA]
      refine le_trans ?_ (le_of_eq (by ring : M * (4 * Real.pi * (3 * Δ / 2)) = 6 * Real.pi * M * Δ))
      exact norm_setIntegral_crossL_kf_inter_le (ω := ω) hM (hbdd q.2 hqt) hΔpos hqΔ
    have hCb : ‖C‖ ≤ 6 * Real.pi * M * Δ := by
      rw [hC]
      refine le_trans ?_ (le_of_eq (by ring : M * (4 * Real.pi * (3 * Δ / 2)) = 6 * Real.pi * M * Δ))
      exact norm_setIntegral_crossL_kf_inter_le (ω := ω) (x := x₀) hM
        (hbdd t₀ (by simpa using hδ)) hΔpos (by rw [sub_self, norm_zero]; linarith)
    have hBd : ‖B - D‖ < ε / 2 := by
      rw [← dist_eq_norm, hB, hD]
      exact hr hqr
    have hfin : dist (A + B) (C + D) < ε := by
      rw [dist_eq_norm]
      have heq : (A + B) - (C + D) = (A - C) + (B - D) := by abel
      rw [heq]
      have h1 := norm_add_le (A - C) (B - D)
      have h2 := norm_sub_le A C
      linarith
    exact hfin
  -- ## Step 3.  Put the pieces together.
  have hΦ : ContinuousAt (fun q : Work.LWP.R3 × ℝ => (4 * Real.pi)⁻¹ •
        ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a q.2) (kf (q.1 - a)))
      (x₀, t₀) := hG.const_smul ((4 * Real.pi)⁻¹)
  exact hΦ.congr hrepr

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.TimeHolderDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-- **R4 at any element of the model-data class.**  The proof is the second-order computation of
`Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData` with the *explicit* profile
`F_*` (`g = 0`) and the affine modulation `λ̄(t) = 1 - t/2`. -/
theorem timeHolderDeriv_of_inhabitant {α : NNReal} (I : Inhabitant α) :
    TimeHolderDeriv I.P := by
  have hα : 0 < (α : ℝ) := I.P.hα
  have hα13 : (α : ℝ) ≤ 1 / 3 := I.P.hα13
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith
  refine Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData I.P ?_
    (Cg'' := 80) (K₂ := 0) ?_ ?_ ?_
  · intro z θ hz
    rw [I.hg]
    exact Work.ConstructionInstance.hasDerivAt_pz_profile_zeroPert
      (p := Work.ConstructionInstance.profExp α) hz
  · intro z θ hz hθ
    rw [I.hg]
    exact Work.ConstructionInstance.zsq_pz_pz_profile_zeroPert_abs_le hp hp1 z θ hz hθ
  · intro t _
    have hderiv : deriv I.P.lam = fun _ : ℝ => -(1 / 2) := funext fun s => model_deriv_lam I s
    rw [hderiv, deriv_const]
    exact hasDerivAt_const t (-(1 / 2))
  · intro t _
    have hderiv : deriv I.P.lam = fun _ : ℝ => -(1 / 2) := funext fun s => model_deriv_lam I s
    rw [hderiv, deriv_const]
    norm_num

/-- **The second-order time condition at the model data** (`TimeDerivLocallyLipschitz`), from the
*same* second-order data that proves R4: the explicit second time derivative of the cut
self-similar vorticity (`Work.ConstructionInstance.timeDeriv_timeDeriv_selfSimVort`) is bounded near
every time of the half-window, so `∂ₜω` is locally Lipschitz in `t`. -/
theorem timeDerivLocallyLipschitz_of_inhabitant {α : NNReal} (I : Inhabitant α) :
    TimeDerivLocallyLipschitz (solVort I.P) I.P.T := by
  have hα : 0 < (α : ℝ) := I.P.hα
  have hα13 : (α : ℝ) ≤ 1 / 3 := I.P.hα13
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith
  refine solVort_timeDeriv_lipschitz I.P ?_ (Cg'' := 80) (K₂ := 0) ?_ ?_ ?_
  · intro z θ hz
    rw [I.hg]
    exact Work.ConstructionInstance.hasDerivAt_pz_profile_zeroPert
      (p := Work.ConstructionInstance.profExp α) hz
  · intro z θ hz hθ
    rw [I.hg]
    exact Work.ConstructionInstance.zsq_pz_pz_profile_zeroPert_abs_le hp hp1 z θ hz hθ
  · intro t _
    have hderiv : deriv I.P.lam = fun _ : ℝ => -(1 / 2) := funext fun s => model_deriv_lam I s
    rw [hderiv, deriv_const]
    exact hasDerivAt_const t (-(1 / 2))
  · intro t _
    have hderiv : deriv I.P.lam = fun _ : ℝ => -(1 / 2) := funext fun s => model_deriv_lam I s
    rw [hderiv, deriv_const]
    norm_num

/-- **R4 at the model data.** -/
theorem timeHolderDeriv_model {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    TimeHolderDerivModel α := by
  obtain ⟨I⟩ := inhabitant_exists hα hα13
  exact ⟨I.P, inhabitant_isModelData I, timeHolderDeriv_of_inhabitant I⟩

end Work.CoreResiduals
end
end
-- ===== merged: Submission.Work.CoreResiduals.solVort_localHolder_preWindow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **Local `α`-Hölder regularity of the constructed vorticity around every time of the
half-window `preWindow P.T = Ioo (-2) P.T`.**  This is the local-`x`-Hölder clause of the
admissibility bundle `BSAdmissibleOnWindow` at `ω = solVort P`: near every `t₀ ∈ preWindow P.T`
there are `ε > 0`, an exponent `c > 0` and a constant `C` (all independent of `a, b`) with

  `‖solVort P a t - solVort P b t‖ ≤ C * ‖a - b‖ ^ c`   for all `t ∈ Ioo (t₀-ε) (t₀+ε)`.

The proof localises in time and then quotes the quantitative uniform-Hölder lemma.  Since
`preWindow P.T` is open, `exists_eps_min_lam` supplies `ε > 0` with `Icc (t₀-ε) (t₀+ε) ⊆
preWindow P.T` together with a *uniform* lower bound `m ≤ λ̄ s` on that interval
(`m = λ̄ t₀ / 2 > 0`, by continuity of `λ̄`, which is differentiable on `preWindow`).  The
uniformity of the Hölder constant in `t` is exactly the content of `solVort_holder_of_lam_ge`:
for every `δ > 0` a single constant works at *all* times with `λ̄ ≥ δ` — so `m ≤ λ̄ s` gives one
`H` valid at every `s ∈ Ioo (t₀-ε) (t₀+ε)`, regardless of whether the time is positive or negative
(this is where the restriction of `solVort_holder_strip` to the strip `Icc 0 S` would not suffice).
Writing the `dist`-inequality of `HolderWith.dist_le` as a norm inequality finishes the proof with
`c = α > 0` and `C = H`. -/
theorem solVort_localHolder_preWindow {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧
      ∃ C : ℝ, ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ a b : Work.CoreResiduals.R3,
        ‖Work.ConstructionInstance.solVort P a t - Work.ConstructionInstance.solVort P b t‖
          ≤ C * ‖a - b‖ ^ c := by
  intro t₀ ht₀
  -- a two-sided neighbourhood of `t₀` inside the half-window, on which `λ̄ ≥ m > 0` uniformly
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  -- a single Hölder constant for all times at which the modulation is at least `m`
  obtain ⟨H, hH⟩ := solVort_holder_of_lam_ge P (δ := m) hm
  refine ⟨ε, hε, (α : ℝ), P.hα, (H : ℝ), fun t ht a b => ?_⟩
  have hmem : t ∈ Set.Icc (t₀ - ε) (t₀ + ε) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  -- the slice at time `t` is `α`-Hölder with constant `H`, since `m ≤ λ̄ t`
  have h := (hH t (hmle t hmem)).dist_le a b
  rwa [dist_eq_norm, dist_eq_norm] at h

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.FTS.EpsEngine.StarRopLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-- **The star piece of the `Rop` slot.** -/
theorem star_Rop_le {α Cs : ℝ} {Φs : Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α * z / (1 + z) := by
  obtain ⟨hmem, hbd⟩ := hstar.R
  intro z θ hz hθ0 hθ1
  have hpt := Work.FTS.OpenPkg.WDMem_of_WDp_le (l := 4)
    (f := fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
    hmem hbd 0 0 (by norm_num) z θ hz hθ0 hθ1
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
    Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] at hpt
  -- `hpt : |(z+1)/z * X| ≤ Cs * α`, conclude `|X| ≤ Cs α · z/(1+z)`
  have hz1 : 0 < (z + 1) / z := div_pos (by linarith) hz
  have hfac : z / (1 + z) * ((z + 1) / z) = 1 := by
    field_simp
    ring
  calc |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
      = z / (1 + z)
          * |(z + 1) / z
              * Work.Construction.Rop α (Work.Construction.PhiTil α
                  (Work.Construction.Fstar α) Φs) z θ| := by
        rw [abs_mul, abs_of_pos hz1, ← mul_assoc, hfac, one_mul]
    _ ≤ z / (1 + z) * (Cs * α) := by
        refine mul_le_mul_of_nonneg_left hpt (by positivity)
    _ = Cs * α * z / (1 + z) := by ring

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.star_Uop_div_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

/-- **The star piece of the `Uop/sin 2θ` slot.**  This is the extraction of the field
`StarPkgo2.UsW` (`WlInfMem α 4 (Uop α (PhiTil α F_* Φs)/sin 2θ) ∧ WlInf α 4 (…) ≤ Cs α`): the
`k = 0` summand of `WlInf` is `supAbs` of the function itself, and `WlInfMem` makes that supremum
honest, so the pointwise bound follows (there is a precedent extraction for the star `U`-field in
`Submission/Work/FTS/NonlinRows/...`, `WlInf_z_bound`).  Only the numerical constant matters
downstream. -/
theorem star_Uop_div_le {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ} (hα : 0 < α) (hCs : 0 ≤ Cs)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          / Work.Construction.s2 θ| ≤ Cs * α := by
  intro z θ hz hθ hθ2
  -- the domain memberships `z ∈ [0,∞)`, `θ ∈ [0,π/2]`
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
  -- the `𝒲^{4,∞}`-field is the `Uop/sin 2θ` slot of the star package
  set f : ℝ → ℝ → ℝ :=
    fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      / Work.Construction.s2 θ with hf
  have hmem : Work.Spaces.WlInfMem α 4 f := hstar.UsW.1
  have hb : Work.Spaces.WlInf α 4 f ≤ Cs * α := hstar.UsW.2
  -- the `k = 0` summand of `WlInf` is bounded by the whole norm
  have h0 := Work.Spaces.WlInf_z_bound α 4 f hmem 0 (Nat.zero_le 4) z θ hzI hθI
  have h1 : |f z θ| ≤ Work.Spaces.WlInf α 4 f := by
    simpa only [Work.Spaces.pzIter_zero, pow_zero, one_mul] using h0
  exact le_trans h1 hb

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row12 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row13 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Open2.Defs2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField coeffOf IsSolOn IsGalFam
  ConvLocUnif DenseSpan WeakDetermines IsDynWeakOn ProfileBdd EquicontSpace EquicontTau
  profileFam RegPkg prof Slab)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The row table with the relaxed row 16 -/

/-- **The per-piece table of §8, with row 16 at the rate `X³`.**

Field for field this is `Work.FTS.OpenPkg.RowInputs'`, except for `r16`, whose rate is the one
delivered by the row bundle `Work.FTS.Nonlinear.Open.n4Rows2`
(`Work.FTS.VocabO2.NRows2.r16 : |IP α (N3gg α g Φg) g| ≤ K·Xn α g ^ 3`).

The assembly consumes `r16` only through `X³ ≤ Pbd α X`, so nothing is lost: this is exactly the
"row-16 step replaced by `X³ ≤ α^{-3/2}X³`" of the design note. -/
structure RowInputs2' (IP : ℝ → Fn → Fn → ℝ) (α C : ℝ) (g Φs Φg : Fn) : Prop where
  /-- the perturbation is in the `ℋ⁴`-class of the frozen vocabulary -/
  reg4 : RegQ α 4 g
  r1 : Work.Spaces.HkMem α 4 (N0fix α) ∧ Xn α (N0fix α) ≤ C * α ^ 2
  r2 : Work.Spaces.HkMem α 4 (N03g α g) ∧
    Xn α (N03g α g) ≤ C * (α ^ (-(1 : ℝ)) * Xn α g ^ 2)
  r3 : Work.Spaces.HkMem α 4 (N04aF α g) ∧
    Xn α (N04aF α g) ≤ C * (Real.sqrt α * Xn α g)
  r4 : Work.Spaces.HkMem α 4 (N04bF α g) ∧
    |IP α (N04bF α g) g| ≤ C * (α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3)
  r5 : Work.Spaces.HkMem α 4 (N05aF α g) ∧
    Xn α (N05aF α g) ≤ C * (Real.sqrt α * Xn α g)
  r6 : Work.Spaces.HkMem α 4 (N05bF α g) ∧
    |IP α (N05bF α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r7 : Work.Spaces.HkMem α 4 (N06F α g) ∧
    |IP α (N06F α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r8 : Work.Spaces.HkMem α 4 (N1gg α g Φg) ∧
    Xn α (N1gg α g Φg) ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2)
  r9 : Work.Spaces.HkMem α 4 (N1gs α g Φg) ∧
    Xn α (N1gs α g Φg) ≤ C * (Real.sqrt α * Xn α g)
  r10 : Work.Spaces.HkMem α 4 (N1sg α Φs g) ∧
    Xn α (N1sg α Φs g) ≤ C * (Real.sqrt α * Xn α g)
  r11 : Work.Spaces.HkMem α 4 (N1ss α Φs) ∧ Xn α (N1ss α Φs) ≤ C * α ^ 2
  r12 : Work.Spaces.HkMem α 4 (N2gg α g Φg) ∧
    |IP α (N2gg α g Φg) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r13 : Work.Spaces.HkMem α 4 (N2gs α g Φg) ∧
    Xn α (N2gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r14 : Work.Spaces.HkMem α 4 (N2sg α Φs g) ∧
    |IP α (N2sg α Φs g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r15 : Work.Spaces.HkMem α 4 (N2ss α Φs) ∧ Xn α (N2ss α Φs) ≤ C * α ^ 2
  /-- **row 16, relaxed**: `|(N₃^{gg}, g)| ≤ C·X³` (was `C·√α·X³`) -/
  r16 : Work.Spaces.HkMem α 4 (N3gg α g Φg) ∧
    |IP α (N3gg α g Φg) g| ≤ C * Xn α g ^ 3
  r17 : Work.Spaces.HkMem α 4 (N3gs α g Φg) ∧
    Xn α (N3gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r18 : Work.Spaces.HkMem α 4 (N3sg α Φs g) ∧
    |IP α (N3sg α Φs g) g| ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g ^ 2)
  r19 : Work.Spaces.HkMem α 4 (N3ss α Φs) ∧ Xn α (N3ss α Φs) ≤ C * α ^ 3
  r20 : Work.Spaces.HkMem α 4 (N4gg α g) ∧
    |IP α (N4gg α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r21 : Work.Spaces.HkMem α 4 (N4gs α g) ∧
    Xn α (N4gs α g) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r22 : Work.Spaces.HkMem α 4 (N4sg α g) ∧
    |IP α (N4sg α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r23 : Work.Spaces.HkMem α 4 (N4ss α) ∧ Xn α (N4ss α) ≤ C * α ^ 3
  r24 : Work.Spaces.HkMem α 4 (N5gg g) ∧ Xn α (N5gg g) ≤ C * Xn α g ^ 2
  r25 : Work.Spaces.HkMem α 4 (N5gs α g) ∧ Work.Spaces.HkMem α 4 (N5sg α g) ∧
    Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * Xn α g)
  r26 : Work.Spaces.HkMem α 4 (N5ss α) ∧ Xn α (N5ss α) ≤ C * α ^ 2
  rak : Work.Spaces.HkMem α 4 (Work.Construction.AK α) ∧ Xn α (Work.Construction.AK α) ≤ C
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ C * Xn α g
  hN0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
          + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)
  hN : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
        + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
        + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
        + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
        + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)
  hNs : ∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ
  hkN0 : Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
  hkN : Work.Spaces.HkMem α 4
    (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
  hkDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g)

/-! ## The N4 output, the N5 fields and the N6 bundle over `StarPkgo2` -/

/-- **The output of `pairing_bound_open2`** (the `StarPkgo2` analogue of
`Work.FTS.OpenPkg.PairData'`). -/
structure PairData2 (IP : ℝ → Fn → Fn → ℝ) (CcN Ce Cs α₄ : ℝ) : Prop where
  hCcN : 0 < CcN
  hα₄ : 0 < α₄
  bound : ∀ α : ℝ, 0 < α → α ≤ α₄ → ∀ g Φs Φg : Fn,
    GalClass α g → Work.FTS.VocabO2.StarPkgo2 α Cs Φs → EllPkgGo α Ce g Φg →
    Xn α g ≤ α ^ (7 / 4 : ℝ) →
    |Work.FTS.Apriori.muOf α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * (α + α ^ (-(1 : ℝ)) * Xn α g + α ^ (-(5 / 2 : ℝ)) * Xn α g ^ 2)
      ∧ |Work.FTS.Apriori.muOf α g (fun z θ => Φs z θ + Φg z θ)| ≤ 1 / 2
      ∧ |Work.FTS.Apriori.rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * Pbd α (Xn α g)

/-- **The a-priori fields of N6, over `StarPkgo2`.**  This structure carries no star-package
field (only the perturbation `g₀`, the stream functions `Φs`/`EllSol` as *data*, the basis and
the open-quadrant limit bound), so it is field-for-field
`Work.FTS.OpenPkg.AprioriFields'`; the copy exists so that the whole new chain is stated in the
`Open2` vocabulary. -/
structure AprioriFields2 (IP : ℝ → Fn → Fn → ℝ) (α C₀ clo cc CcN Ce Cs : ℝ) (φ : ℕ → Fn)
    (Φs : Fn) (EllSol : Fn → Fn) (g₀ : Fn) : Prop where
  /-- **`hInit`**: the projected datum lies in the a-priori ball. -/
  hInit : ∀ n : ℕ, ∑ k : Fin n,
    (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ (Work.FTS.Apriori.Rstar clo C₀ α) ^ 2
  /-- **`hCoeffBound`**: every Galerkin solution stays in the a-priori ball. -/
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ (Work.FTS.Apriori.Rstar clo C₀ α) ^ 2
  /-- **`hProfileBdd`**: uniform local bounds on the Galerkin profiles. -/
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Work.FTS.Apriori.Rstar clo C₀ α) c →
    ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.Galerkin.Slab →
      ∃ Cb : ℝ, ∀ n : ℕ, ∀ p ∈ K, |Work.FTS.Galerkin.prof φ c n p| ≤ Cb
  /-- **`hLimBound`**: the limit of a convergent subsequence obeys the a-priori bound. -/
  hLimBound : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Work.FTS.Apriori.Rstar clo C₀ α) c →
    ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    (∀ τ : ℝ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice g τ)) →
    ∀ τ : ℝ, 0 ≤ τ → Xn α (slice g τ) ≤ C₀ * α ^ 2


/-- **The Galerkin (N6) bundle over `StarPkgo2`** — the `StarPkgo2` analogue of
`Work.FTS.OpenPkg.DynInputsOpen`. -/
structure DynInputsOpen2 (Law : Fn → Fn → Prop) (α : ℝ) (g₀ : Fn) (C₀ : ℝ) where
  /-- the fields shared with `DynCore` -/
  core : Work.FTS.OpenPkg.DynCore Law α g₀ C₀
  Cs : ℝ
  Ce : ℝ
  hΦs : Work.FTS.VocabO2.StarPkgo2 α Cs (core.Φs)
  hEllSol : ∀ g : Fn, GalClass α g → EllPkgGo α Ce g (core.EllSol g)


end Work.FTS.Open2
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarCoreAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.StarCoreInhabitant` — the analysis node `StarCore`

For every `0 < α ≤ 1/5` there is a stream function `Φ_* = Model α (GzProfile α) ψ + R` with

* `R = psiSeries α (RemSource α ψ)` the mode series solving the `O(α²)` remainder equation
  (`Series.psiSeries_solves_rem`),
* `Φ_*` presented in the zero-extension normal form (`ZeroOffWitness`) so that `PhiTs α Φ_*`
  vanishes off the open quadrant,
* and the flat bound `FlatW 7 (Ycheck α Φ_*) (Cs·α)` assembled from

  `Ycheck α Φ_* = ((z+1)/z)·Aprof α + α·(2/(1+z))·(ψ/sin 2θ) + ((z+1)/z)·R/sin 2θ`

  whose three pieces are bounded by `FlatW_aprof` (`O(α)`), `FlatW_psiDiv` transported along the
  radial factor `2/(1+z)` (`O(α)`), and `FlatW_psiSeries` (`O(α²)`) respectively
  (`FlatW_YcheckExpansion`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Classical

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `FlatW` is monotone in its constant. -/
theorem FlatW_mono {l : ℕ} {f : ℝ → ℝ → ℝ} {K K' : ℝ}
    (h : Work.FTS.VocabO2.FlatW l f K) (hle : K ≤ K') :
    Work.FTS.VocabO2.FlatW l f K' := by
  intro z θ hz hθ hθ2
  obtain ⟨h1, h2⟩ := h z θ hz hθ hθ2
  exact ⟨fun k hk => le_trans (h1 k hk) hle, fun k i hki => le_trans (h2 k i hki) hle⟩

/-- The explicit decomposition of `Ycheck`, as a definition. -/
def YcheckExpand (α : ℝ) (ψ : ℝ → ℝ) (R : Fn) : Fn :=
  fun z θ => (z + 1) / z * Aprof α z
    + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ)
    + (z + 1) / z * R z θ / Work.Construction.s2 θ

/-- **The pointwise identity behind the flat bound**: on the open quadrant, `Ycheck` of the
assembled witness is the sum of the explicit flat part, the separable model part and the
remainder. -/
theorem Ycheck_eq_expand {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ψ : ℝ → ℝ} {R : Fn}
    {Φs : Fn}
    (hs : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Φs z θ = Model α (GzProfile α) ψ z θ + R z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      YcheckExpand α ψ R z θ = Work.FTS.VocabO2.Ycheck α Φs z θ := by
  intro z θ hz hθ hθ2
  have hzp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ, hθ2⟩
  have hs2 : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [Real.pi_pos]))
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by positivity
  have hphi : (z + 1) / z * Work.FTS.VocabO.phiR z = 2 / (1 + z) := by
    rw [Work.FTS.VocabO.phiR]
    field_simp
    ring
  have hkey : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
      = Aprof α z * Work.Construction.s2 θ + α * Work.FTS.VocabO.phiR z * ψ θ + R z θ := by
    have hp : Φs z θ = Model α (GzProfile α) ψ z θ + R z θ := hs z θ hzp
    have hq : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        = Work.Construction.PhiTil α (Work.Construction.Fstar α)
            (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) z θ := by
      simp only [Work.Construction.PhiTil, hp]
    exact hq.trans (PhiTil_expansion_eq hα hα1 ψ R z θ (le_of_lt hz))
  show YcheckExpand α ψ R z θ = Work.FTS.VocabO2.Ycheck α Φs z θ
  unfold YcheckExpand Work.FTS.VocabO2.Ycheck
  rw [show Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ / Work.Construction.s2 θ
      = (Aprof α z * Work.Construction.s2 θ + α * Work.FTS.VocabO.phiR z * ψ θ + R z θ)
        / Work.Construction.s2 θ from by rw [hkey]]
  rw [← hphi]
  field_simp
  try ring

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

variable {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}

theorem RegPkg'.alpha_pos (h : RegPkg' α S A B g) : 0 < α := h.hα

theorem RegPkg'.pExp_pos (h : RegPkg' α S A B g) : 0 < pExp α :=
  Work.FTS.Regularity.pExp_pos h.hα
theorem RegPkg'.pExp_le_one (h : RegPkg' α S A B g) : pExp α ≤ 1 :=
  Work.FTS.Regularity.pExp_le_one h.hα13

/-- The `VanishTheta` data, as a `Prop` about the slice. -/
theorem RegPkg'.vanish (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Work.Spaces.VanishTheta (gSlice g τ) := h.hvt τ hτ



/-- **Pointwise boundedness of the perturbation**: `|g| ≤ Cv` on the domain, since `Γ ≤ 1`. -/
theorem RegPkg'.abs_le_Cv (h : RegPkg' α S A B g) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv := by
  obtain ⟨Cv, hCv0, hCv⟩ := h.hvan
  refine ⟨Cv, hCv0, fun τ hτ z θ hz hθ => ?_⟩
  refine le_trans (hCv τ hτ z θ hz hθ) ?_
  have hΓ1 : Gamma α θ ≤ 1 := Work.ConstructionInstance.Gamma_le_one h.hα.le hθ
  have hΓ0 : 0 ≤ Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  nlinarith





/-- **The radial modulus of the perturbation at a strip time** (`Lg` of the `St1`-class). -/
theorem RegPkg'.zmod (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ∃ Lg : ℝ, 0 ≤ Lg ∧ ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ τ - g z' θ τ| ≤ Lg * |z - z'| ^ α := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun z z' θ hz hz' hθ => hN.zmod hz hz' hθ hτ⟩

/-- **The angular modulus of the perturbation at a strip time** (`Lθ` of the `St1`-class). -/
theorem RegPkg'.thmod (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ τ - g z θ' τ| ≤ Lθ * |θ - θ'| ^ α := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun z θ θ' hz hθ hθ' => hN.thmod hz hθ hθ' hτ⟩



/-- The support data: the full profile vanishes for `z ≥ L`. -/
theorem RegPkg'.supp (h : RegPkg' α S A B g) :
    ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → profFull α g z θ τ = 0 :=
  h.hsupp



/-- The joint `C¹` smoothness of `(z,τ) ↦ g z θ τ` at every fixed angle `θ ∈ Iθ`. -/
theorem RegPkg'.cont (h : RegPkg' α S A B g) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) := h.hcont θ hθ

/-! ## Elementary consequences of the corrected Taylor clause -/


end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.L12fDensBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

theorem L12fDensBound {α S N Kl Lf : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      |F z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → F z θ τ = 0) :
    (∀ τ ∈ Set.Icc 0 S, ∀ s : ℝ, 0 < s →
        |Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s| ≤ 6 * max Kl N) ∧
    (∀ τ ∈ Set.Icc 0 S, ∀ s : ℝ, Lf ≤ s →
        Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s = 0) := by
  have hKl0 : 0 ≤ Kl := hlin.1
  have hN0 : 0 ≤ N := hJ.nonneg
  refine ⟨?_, ?_⟩
  · intro τ hτ s hs
    -- the pointwise bound on the integrand, uniformly in `θ ∈ Iθ`
    have hpt : ∀ θ ∈ Work.Spaces.Iθ,
        ‖Work.Spaces.K θ * Work.FTS.Regularity.gSlice F τ s θ / s‖ ≤ 3 * max Kl N := by
      intro θ hθ
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul]
      have hK : |Work.Spaces.K θ| ≤ 3 := abs_K_le_three hθ
      rcases lt_or_ge s 1 with hlt | hge
      · -- `s < 1`: linearity of the profile near the axis
        have hF : |Work.FTS.Regularity.gSlice F τ s θ| ≤ Kl * s :=
          hlin.2 τ hτ θ hθ s ⟨hs, hlt⟩
        have h1 : |Work.Spaces.K θ| * |Work.FTS.Regularity.gSlice F τ s θ| / s
            ≤ 3 * (Kl * s) / s := by
          apply div_le_div_of_nonneg_right _ hs.le
          exact mul_le_mul hK hF (abs_nonneg _) (by norm_num)
        have h2 : 3 * (Kl * s) / s = 3 * Kl := by
          rw [mul_div_assoc, mul_div_cancel_right₀ Kl (ne_of_gt hs)]
        have h3 : 3 * Kl ≤ 3 * max Kl N := by linarith [le_max_left Kl N]
        linarith
      · -- `s ≥ 1`: the uniform `Jet` bound
        have hF : |Work.FTS.Regularity.gSlice F τ s θ| ≤ N :=
          hJ.abs_le (le_of_lt hs) hθ hτ
        have h1 : |Work.Spaces.K θ| * |Work.FTS.Regularity.gSlice F τ s θ| / s
            ≤ 3 * N / s := by
          apply div_le_div_of_nonneg_right _ hs.le
          exact mul_le_mul hK hF (abs_nonneg _) (by norm_num)
        have h2 : 3 * N / s ≤ 3 * N := by
          rw [div_le_iff₀ hs]; nlinarith [hN0, hge]
        have h3 : 3 * N ≤ 3 * max Kl N := by linarith [le_max_right Kl N]
        linarith
    -- integrate the pointwise bound over the finite measure `volume ↾ Iθ`
    have hmain : |∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.FTS.Regularity.gSlice F τ s θ / s|
        ≤ (3 * max Kl N) * (Real.pi / 2) := by
      rw [← Work.Spaces.volume_real_Iθ, ← Real.norm_eq_abs]
      exact MeasureTheory.norm_setIntegral_le_of_norm_le_const Work.Spaces.volume_Iθ_lt_top hpt
    have hfin : (3 * max Kl N) * (Real.pi / 2) ≤ 6 * max Kl N := by
      have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
      calc (3 * max Kl N) * (Real.pi / 2) = 3 * (Real.pi / 2) * max Kl N := by ring
        _ ≤ 3 * 2 * max Kl N := by
            have h0 : (0 : ℝ) ≤ max Kl N := le_trans hKl0 (le_max_left Kl N)
            have hm : 3 * (Real.pi / 2) ≤ 3 * 2 := by linarith
            exact mul_le_mul_of_nonneg_right hm h0
        _ = 6 * max Kl N := by ring
    rw [Work.FM.L12dens]
    exact le_trans hmain hfin
  · intro τ hτ s hs
    -- the slice vanishes identically beyond `Lf`, so the density is `0`
    rw [Work.FM.L12dens]
    have hzero : (fun θ : ℝ =>
        Work.Spaces.K θ * (Work.FTS.Regularity.gSlice F τ) s θ / s) = fun _ => (0 : ℝ) := by
      funext θ
      rw [Work.FTS.Regularity.gSlice_apply, hsupp.2 τ hτ s θ hs]
      ring
    rw [hzero, integral_zero]

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.L12fDensDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-! ## Elementary angular facts -/

/-- `K(θ) = 3 sin θ cos²θ` is continuous on `ℝ`. -/
theorem continuous_K : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
  simp only [Work.Spaces.K]
  exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)

/-- **The angular slice of a `Jet` is continuous.**  For `z ≥ 0` and `τ ∈ [0,S]` the `θ`-Hölder
modulus of `Jet.thmod` makes `θ ↦ K(θ)·F z θ τ` continuous on `Iθ`. -/
theorem continuousOn_K_mul_jet_slice {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hJ : Work.FTS.Regularity.Jet α S N F) {z τ : ℝ} (hz : 0 ≤ z)
    (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun θ => Work.Spaces.K θ * F z θ τ) (Set.Icc 0 (Real.pi / 2)) :=
  continuous_K.continuousOn.mul
    (continuousOn_of_holder hJ.nonneg hα fun θ hθ θ' hθ' => by
      simpa using hJ.thmod hz hθ hθ' hτ)

/-- **The angular slice is integrable.**  A continuous function on the compact interval `Iθ` is
`L¹` for the Lebesgue measure; this is the integrability that lets the difference of the two
`L12dens`-integrals be written as the integral of the difference. -/
theorem integrableOn_K_mul_jet_slice {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hJ : Work.FTS.Regularity.Jet α S N F) {z τ : ℝ} (hz : 0 ≤ z)
    (hτ : τ ∈ Set.Icc 0 S) :
    IntegrableOn (fun θ => Work.Spaces.K θ * F z θ τ) (Set.Icc 0 (Real.pi / 2)) :=
  (continuousOn_K_mul_jet_slice hα hJ hz hτ).integrableOn_Icc

/-! ## The `τ`-modulus of the density -/

/-- **The time-Hölder modulus of the angular density of `L₁₂^K`.**  If the profile family `F` is a
`Jet` and its `τ`-increments obey the *uniform in `z`* bound `|ΔF| ≤ Nt·z·|Δτ|^α`, then the
density `s ↦ L12dens K (gSlice F τ) s` is `α`-Hölder in `τ` with the same modulus, uniformly in
`s > 0`:

  `|L12dens K (gSlice F τ) s - L12dens K (gSlice F τ') s| ≤ 6·Nt·|τ - τ'|^α`.

The proof uses only `|K| ≤ 3` on `Iθ` and the angular mass `π/2 < 2`. -/
theorem L12fDensDiff {α S N Nt : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (htau : 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ici (0 : ℝ), |F z θ τ - F z θ τ'| ≤ Nt * z * |τ - τ'| ^ α) :
    ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ s : ℝ, 0 < s →
      |Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s
        - Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ') s|
      ≤ 6 * Nt * |τ - τ'| ^ α := by
  intro τ hτ τ' hτ' s hs
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
  have hne : s ≠ 0 := ne_of_gt hs
  -- integrability of the two angular slices at the radial value `s > 0`
  have hIntτ : IntegrableOn (fun θ => Work.Spaces.K θ * F s θ τ) (Set.Icc 0 (Real.pi / 2)) :=
    integrableOn_K_mul_jet_slice hα hJ hs0 hτ
  have hIntτ' : IntegrableOn (fun θ => Work.Spaces.K θ * F s θ τ') (Set.Icc 0 (Real.pi / 2)) :=
    integrableOn_K_mul_jet_slice hα hJ hs0 hτ'
  -- the difference of the integrals is the integral of the difference, divided by `s`
  have hsplit : (∫ θ in Set.Icc 0 (Real.pi / 2), Work.Spaces.K θ * F s θ τ) / s
      - (∫ θ in Set.Icc 0 (Real.pi / 2), Work.Spaces.K θ * F s θ τ') / s
      = ∫ θ in Set.Icc 0 (Real.pi / 2),
          (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s := by
    rw [← sub_div, ← MeasureTheory.integral_sub hIntτ hIntτ', ← MeasureTheory.integral_div]
  -- unfold the density (`L12dens_eq`: the factor `1/s` may be pulled out of the integral)
  rw [Work.FM.L12dens_eq hne, Work.FM.L12dens_eq hne]
  simp only [Work.FTS.Regularity.gSlice_apply]
  rw [hsplit]
  -- pointwise bound: `|K θ| ≤ 3`, and the factor `s` cancels
  have hpt : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      |(Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s|
        ≤ 3 * (Nt * |τ - τ'| ^ α) := by
    intro θ hθ
    have h1 : |F s θ τ - F s θ τ'| ≤ Nt * s * |τ - τ'| ^ α :=
      htau.2 τ hτ τ' hτ' θ hθ s (le_of_lt hs)
    have hK : |Work.Spaces.K θ| ≤ 3 := abs_K_le_three hθ
    have hnum_eq : Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ'
        = Work.Spaces.K θ * (F s θ τ - F s θ τ') := by ring
    rw [hnum_eq, abs_div, abs_of_pos hs, abs_mul]
    have hnum : |Work.Spaces.K θ| * |F s θ τ - F s θ τ'| ≤ 3 * (Nt * s * |τ - τ'| ^ α) :=
      mul_le_mul hK h1 (abs_nonneg _) (by norm_num)
    have hstep := div_le_div_of_nonneg_right hnum hs0
    have hfin : 3 * (Nt * s * |τ - τ'| ^ α) / s = 3 * (Nt * |τ - τ'| ^ α) := by
      have hre : 3 * (Nt * s * |τ - τ'| ^ α) = (3 * (Nt * |τ - τ'| ^ α)) * s := by ring
      rw [hre, mul_div_cancel_right₀ _ hne]
    rw [hfin] at hstep
    exact hstep
  -- the norm of the integral is bounded by the integral of the norm
  have h1 : |∫ θ in Set.Icc 0 (Real.pi / 2),
        (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s|
      ≤ ∫ θ in Set.Icc 0 (Real.pi / 2),
        |(Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s| := by
    have hb := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)))
      (fun θ => (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s θ τ') / s)
    simpa only [Real.norm_eq_abs] using hb
  -- the angular mass `π/2` and the final arithmetic
  refine le_trans h1 (le_trans (setIntegral_abs_le_of_bound hpt) ?_)
  have hX : 0 ≤ Nt * |τ - τ'| ^ α :=
    mul_nonneg htau.1 (Real.rpow_nonneg (abs_nonneg _) _)
  have hpi2 : Real.pi / 2 ≤ 2 := le_of_lt (by linarith [Real.pi_lt_four])
  have h3 : (3 * (Nt * |τ - τ'| ^ α)) * (Real.pi / 2)
      ≤ (3 * (Nt * |τ - τ'| ^ α)) * 2 :=
    mul_le_mul_of_nonneg_left hpi2 (by linarith)
  have h4 : (3 * (Nt * |τ - τ'| ^ α)) * 2 = 6 * Nt * |τ - τ'| ^ α := by ring
  linarith [h3, h4]

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.L12fDensUnif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

theorem L12fDensUnif {α S N Kl : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      |F z θ τ| ≤ Kl * z) :
    ∀ τ ∈ Set.Icc 0 S, ∀ s : ℝ, 0 < s →
      |Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s| ≤ 6 * max Kl N := by
  have hKl0 : 0 ≤ Kl := hlin.1
  have hN0 : 0 ≤ N := hJ.nonneg
  intro τ hτ s hs
  -- the pointwise bound on the integrand, uniformly in `θ ∈ Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.Spaces.K θ * Work.FTS.Regularity.gSlice F τ s θ / s‖ ≤ 3 * max Kl N := by
    intro θ hθ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul]
    have hK : |Work.Spaces.K θ| ≤ 3 := abs_K_le_three hθ
    rcases lt_or_ge s 1 with hlt | hge
    · -- `s < 1`: linearity of the profile near the axis
      have hF : |Work.FTS.Regularity.gSlice F τ s θ| ≤ Kl * s :=
        hlin.2 τ hτ θ hθ s ⟨hs, hlt⟩
      have h1 : |Work.Spaces.K θ| * |Work.FTS.Regularity.gSlice F τ s θ| / s
          ≤ 3 * (Kl * s) / s := by
        apply div_le_div_of_nonneg_right _ hs.le
        exact mul_le_mul hK hF (abs_nonneg _) (by norm_num)
      have h2 : 3 * (Kl * s) / s = 3 * Kl := by
        rw [mul_div_assoc, mul_div_cancel_right₀ Kl (ne_of_gt hs)]
      have h3 : 3 * Kl ≤ 3 * max Kl N := by linarith [le_max_left Kl N]
      linarith
    · -- `s ≥ 1`: the uniform `Jet` bound
      have hF : |Work.FTS.Regularity.gSlice F τ s θ| ≤ N :=
        hJ.abs_le (le_of_lt hs) hθ hτ
      have h1 : |Work.Spaces.K θ| * |Work.FTS.Regularity.gSlice F τ s θ| / s
          ≤ 3 * N / s := by
        apply div_le_div_of_nonneg_right _ hs.le
        exact mul_le_mul hK hF (abs_nonneg _) (by norm_num)
      have h2 : 3 * N / s ≤ 3 * N := by
        rw [div_le_iff₀ hs]; nlinarith [hN0, hge]
      have h3 : 3 * N ≤ 3 * max Kl N := by linarith [le_max_right Kl N]
      linarith
  -- integrate the pointwise bound over the finite measure `volume ↾ Iθ`
  have hmain : |∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.FTS.Regularity.gSlice F τ s θ / s|
      ≤ (3 * max Kl N) * (Real.pi / 2) := by
    rw [← Work.Spaces.volume_real_Iθ, ← Real.norm_eq_abs]
    exact MeasureTheory.norm_setIntegral_le_of_norm_le_const Work.Spaces.volume_Iθ_lt_top hpt
  have hfin : (3 * max Kl N) * (Real.pi / 2) ≤ 6 * max Kl N := by
    have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
    calc (3 * max Kl N) * (Real.pi / 2) = 3 * (Real.pi / 2) * max Kl N := by ring
      _ ≤ 3 * 2 * max Kl N := by
          have h0 : (0 : ℝ) ≤ max Kl N := le_trans hKl0 (le_max_left Kl N)
          have hm : 3 * (Real.pi / 2) ≤ 3 * 2 := by linarith
          exact mul_le_mul_of_nonneg_right hm h0
      _ = 6 * max Kl N := by ring
  rw [Work.FM.L12dens]
  exact le_trans hmain hfin

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.far_of_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

theorem far_of_support {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hsupp : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z →
      Work.FTS.Regularity.profFull α (Work.FTS.RegPkgGal.extG g) z θ τ = 0) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Cf ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.RegPkgGal.extG g z θ τ| ≤ Cf * Work.FTS.Regularity.Gamma α θ := by
  -- Beyond the support radius `L` the extension `g̃` coincides with `g` (for `τ ≥ 0`, `z > 0`)
  -- and the full profile `F = F_* + g̃` vanishes, so `g = -F_*` there; and `F_*` obeys the
  -- angular bound `|F_*| ≤ 20·(3α)·Γ`.
  obtain ⟨L, hLpos, hL⟩ := hsupp
  refine ⟨max L 20, le_trans hLpos.le (le_max_left L 20), ?_⟩
  intro τ hτ z θ hz hθ
  have hzL : L ≤ z := le_trans (le_max_left L 20) hz
  have hzpos : 0 < z := lt_of_lt_of_le hLpos hzL
  have hτ0 : 0 ≤ τ := hτ.1
  have hext : Work.FTS.RegPkgGal.extG g z θ τ = g z θ τ :=
    Work.FTS.RegPkgGal.extG_of_pos hzpos hτ0
  have hzero : Work.FTS.Regularity.profFull α (Work.FTS.RegPkgGal.extG g) z θ τ = 0 :=
    hL τ hτ z θ hzL
  rw [Work.FTS.Regularity.profFull_apply, hext] at hzero
  have hg : g z θ τ = -Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ := by
    linarith
  rw [hext, hg, abs_neg]
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hF := Work.ConstructionInstance.Fstar_abs_le (p := Work.FTS.Regularity.pExp α) hp0 hp1
    hzpos.le hθ
  have hp3 : Work.FTS.Regularity.pExp α / 3 = α := by rw [Work.FTS.Regularity.pExp]; ring
  rw [hp3] at hF
  have hGam0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
    Work.ConstructionInstance.Gamma_nonneg hθ
  calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
      ≤ 20 * Work.FTS.Regularity.pExp α * Work.FTS.Regularity.Gamma α θ := hF
    _ ≤ 20 * Work.FTS.Regularity.Gamma α θ := by
        have h := mul_le_mul_of_nonneg_right hp1 hGam0
        linarith
    _ ≤ max L 20 * Work.FTS.Regularity.Gamma α θ :=
        mul_le_mul_of_nonneg_right (le_max_right L 20) hGam0

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.integrableOn_Ioi_of_bound_of_eventually_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

theorem integrableOn_Ioi_of_bound_of_eventually_zero {f : ℝ → ℝ} {c L : ℝ}
    (hL : 0 < L)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hb : ∀ s : ℝ, 0 < s → |f s| ≤ c)
    (hz : ∀ s : ℝ, L ≤ s → f s = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  -- Split `Ioi 0` into the bounded piece `Ioo 0 L`, where `f` is continuous and
  -- bounded, and `Ici L`, where `f` vanishes.
  have hIoo : MeasureTheory.IntegrableOn f (Set.Ioo (0 : ℝ) L) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ c ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact (hcont.mono Set.Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with x hx
      rw [Real.norm_eq_abs]
      exact hb x hx.1
  have hIci : MeasureTheory.IntegrableOn f (Set.Ici L) := by
    refine (MeasureTheory.integrableOn_zero (s := Set.Ici L)).congr_fun ?_ measurableSet_Ici
    intro x hx
    exact (hz x hx).symm
  have hset : Set.Ioo (0 : ℝ) L ∪ Set.Ici L = Set.Ioi 0 := by
    ext x
    constructor
    · rintro (⟨h0, _⟩ | hLx)
      · exact h0
      · exact lt_of_lt_of_le hL hLx
    · intro hx
      rcases lt_or_ge x L with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
  rw [← hset]
  exact hIoo.union hIci

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.jet_coeff_all =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.jet_coeff_all`

The six explicit coefficient functions of the fake-time right-hand side of the modulation
(`Work.FTS.RegPkgGal.Der.rhs_jet_of_parts`) are `Jet`s on the strip `z ≥ 0`, `θ ∈ Iθ`,
`τ ∈ [0,S]`:

* `z ↦ 2z/(1+z)²` and `θ ↦ Γ(θ)/c` — the two factors of the profile `F_*`;
* `z ↦ 2/(1+z)`, `z ↦ 3/(1+z)` — the two radial factors of `L₁₂(F_*)` and of `N₀`;
* the products `2z Γ(θ)/(c(1+z)²)` and `AK = (Γ(θ)/c)·2z²/(1+z)³`.

None of the six depends on `τ`, so the only content is that each is *bounded* on
`[0,∞) × Iθ` and `α`-Hölder there for the metric `|Δz| + |Δθ|`; the `τ`-modulus is the trivial
one (the exponent `α ∈ (0,1]` is monotone).

The proof is a single general principle, `jet_of_zθ`: a function `A z θ` of `(z,θ)` alone which
is bounded by `M` and `α`-Hölder with constant `K` for `|Δz| + |Δθ|` is a `Jet` with any constant
`N ≥ K` and `N ≥ 2M` — because two points at distance `≥ 1` in the metric are handled by the sup
bound and two points at distance `≤ 1` by the Hölder bound.  The explicit functions are then
bounded and Hölder by elementary calculus: three rational functions of `z`
(`jca_z_facts`), the angular factor `Γ/c` (`jca_gam_div_c_bdd` + the already available
`rhsJet_gam_div_c_holder`), and the two products (`jca_zgam_facts`, `rhsJet_ak_bounds`).

All constants are the displayed ones (generous, but explicit).
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The general `Jet`-closure principle -/

/-- **A function of `(z,θ)` alone which is bounded and `α`-Hölder is a `Jet`.**  If
`|A z θ| ≤ M` on `z ≥ 0`, `θ ∈ Iθ` and `|A z θ - A z' θ'| ≤ K (|Δz| + |Δθ|)^α`, then
`(z,θ,τ) ↦ A z θ` is a `Jet` with any constant `N ≥ K`, `N ≥ 2M`. -/
theorem jet_of_zθ {α S N M K : ℝ} {A : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hN : 0 ≤ N) (hKN : K ≤ N) (hMN : 2 * M ≤ N)
    (hbdd : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ, |A z θ| ≤ M)
    (hhld : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |A z θ - A z' θ'| ≤ K * (|z - z'| + |θ - θ'|) ^ α) :
    Work.FTS.Regularity.Jet α S N (fun z θ _ => A z θ) := by
  have hMN' : M ≤ N := by linarith
  refine ⟨hN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (hbdd z hz θ hθ) hMN'
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have he : (0 : ℝ) ≤ |z - z'| + |θ - θ'| := by positivity
    have hd : (0 : ℝ) ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by positivity
    have hmono : (|z - z'| + |θ - θ'|) ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow he (by linarith [abs_nonneg (τ - τ')]) hα.le
    have h0 : (0 : ℝ) ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := Real.rpow_nonneg hd α
    calc |A z θ - A z' θ'| ≤ K * (|z - z'| + |θ - θ'|) ^ α := hhld z z' hz hz' θ hθ θ' hθ'
      _ ≤ K * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := mul_le_mul_of_nonneg_left hmono hK
      _ ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := mul_le_mul_of_nonneg_right hKN h0

/-- The radial special case of `jet_of_zθ`: a function of `z` alone. -/
theorem jet_of_z {α S N M K : ℝ} {f : ℝ → ℝ} (hα : 0 < α)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hN : 0 ≤ N) (hKN : K ≤ N) (hMN : 2 * M ≤ N)
    (hbdd : ∀ z : ℝ, 0 ≤ z → |f z| ≤ M)
    (hhld : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ K * |z - z'| ^ α) :
    Work.FTS.Regularity.Jet α S N (fun z _ _ => f z) := by
  refine jet_of_zθ (A := fun z _ => f z) hα hM hK hN hKN hMN ?_ ?_
  · intro z hz θ hθ
    exact hbdd z hz
  · intro z z' hz hz' θ hθ θ' hθ'
    refine le_trans (hhld z z' hz hz') (mul_le_mul_of_nonneg_left ?_ hK)
    exact Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (θ - θ')]) hα.le

/-- The angular special case of `jet_of_zθ`: a function of `θ` alone. -/
theorem jet_of_θ {α S N M K : ℝ} {g : ℝ → ℝ} (hα : 0 < α)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hN : 0 ≤ N) (hKN : K ≤ N) (hMN : 2 * M ≤ N)
    (hbdd : ∀ θ ∈ Work.Spaces.Iθ, |g θ| ≤ M)
    (hhld : ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ, |g θ - g θ'| ≤ K * |θ - θ'| ^ α) :
    Work.FTS.Regularity.Jet α S N (fun _ θ _ => g θ) := by
  refine jet_of_zθ (A := fun _ θ => g θ) hα hM hK hN hKN hMN ?_ ?_
  · intro z hz θ hθ
    exact hbdd θ hθ
  · intro z z' hz hz' θ hθ θ' hθ'
    refine le_trans (hhld θ hθ θ' hθ') (mul_le_mul_of_nonneg_left ?_ hK)
    exact Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (z - z')]) hα.le

/-! ## The three radial coefficients -/

/-- Bounds and Lipschitz constants of the three rational coefficients
`2z/(1+z)²`, `2/(1+z)`, `3/(1+z)` on `[0,∞)`.  (The parameters `α ≤ 1` are the ambient ones of
the `Jet`-conversion; they are not used here.) -/
theorem jca_z_facts {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ z : ℝ, 0 ≤ z → |2 * z / (1 + z) ^ 2| ≤ 1) ∧
    (∀ z : ℝ, 0 ≤ z → |2 / (1 + z)| ≤ 2) ∧
    (∀ z : ℝ, 0 ≤ z → |3 / (1 + z)| ≤ 3) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2| ≤ 2 * |z - z'|) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |2 / (1 + z) - 2 / (1 + z')| ≤ 2 * |z - z'|) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |3 / (1 + z) - 3 / (1 + z')| ≤ 3 * |z - z'|) := by
  have hb1 : ∀ z : ℝ, 0 ≤ z → |2 * z / (1 + z) ^ 2| ≤ 1 := by
    intro z hz
    have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * z := by positivity
    rw [abs_of_nonneg (div_nonneg h2 h1.le), div_le_iff₀ h1]
    nlinarith [hz, sq_nonneg z]
  have hb2 : ∀ z : ℝ, 0 ≤ z → |2 / (1 + z)| ≤ 2 := by
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith
    rw [abs_of_nonneg (div_nonneg (by norm_num) h1.le), div_le_iff₀ h1]
    linarith
  have hb3 : ∀ z : ℝ, 0 ≤ z → |3 / (1 + z)| ≤ 3 := by
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith
    rw [abs_of_nonneg (div_nonneg (by norm_num) h1.le), div_le_iff₀ h1]
    linarith
  have hlip1 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2| ≤ 2 * |z - z'| := by
    intro z z' hz hz'
    have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    have h2 : (0 : ℝ) < (1 + z') ^ 2 := by positivity
    have hden : (0 : ℝ) < (1 + z) ^ 2 * (1 + z') ^ 2 := mul_pos h1 h2
    have hfac : 2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2
        = 2 * (z - z') * (1 - z * z') / ((1 + z) ^ 2 * (1 + z') ^ 2) := by
      field_simp
      ring
    have hb : |1 - z * z'| ≤ (1 + z) * (1 + z') := by
      rw [abs_le]
      constructor <;> nlinarith [hz, hz', mul_nonneg hz hz']
    have hb2 : (1 + z) * (1 + z') ≤ (1 + z) ^ 2 * (1 + z') ^ 2 := by
      nlinarith [hz, hz', sq_nonneg z, sq_nonneg z']
    rw [hfac, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have h2n : (0 : ℝ) ≤ 2 * |z - z'| := by positivity
    calc |2 * (z - z') * (1 - z * z')|
        = 2 * |z - z'| * |1 - z * z'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * |z - z'| * ((1 + z) * (1 + z')) := mul_le_mul_of_nonneg_left hb h2n
      _ ≤ 2 * |z - z'| * ((1 + z) ^ 2 * (1 + z') ^ 2) := mul_le_mul_of_nonneg_left hb2 h2n
  have hlip2 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |2 / (1 + z) - 2 / (1 + z')| ≤ 2 * |z - z'| := by
    intro z z' hz hz'
    have h1 : (0 : ℝ) < 1 + z := by linarith
    have h2 : (0 : ℝ) < 1 + z' := by linarith
    have hden : (0 : ℝ) < (1 + z) * (1 + z') := mul_pos h1 h2
    have hfac : 2 / (1 + z) - 2 / (1 + z') = 2 * (z' - z) / ((1 + z) * (1 + z')) := by
      field_simp
      ring
    have hge : (1 : ℝ) ≤ (1 + z) * (1 + z') := by nlinarith [hz, hz']
    rw [hfac, abs_div, abs_of_pos hden, div_le_iff₀ hden, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_sub_comm z' z]
    have h2n : (0 : ℝ) ≤ 2 * |z - z'| := by positivity
    calc 2 * |z - z'| = 2 * |z - z'| * 1 := by ring
      _ ≤ 2 * |z - z'| * ((1 + z) * (1 + z')) := mul_le_mul_of_nonneg_left hge h2n
  have hlip3 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |3 / (1 + z) - 3 / (1 + z')| ≤ 3 * |z - z'| := by
    intro z z' hz hz'
    have h1 : (0 : ℝ) < 1 + z := by linarith
    have h2 : (0 : ℝ) < 1 + z' := by linarith
    have hden : (0 : ℝ) < (1 + z) * (1 + z') := mul_pos h1 h2
    have hfac : 3 / (1 + z) - 3 / (1 + z') = 3 * (z' - z) / ((1 + z) * (1 + z')) := by
      field_simp
      ring
    have hge : (1 : ℝ) ≤ (1 + z) * (1 + z') := by nlinarith [hz, hz']
    rw [hfac, abs_div, abs_of_pos hden, div_le_iff₀ hden, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_sub_comm z' z]
    have h2n : (0 : ℝ) ≤ 3 * |z - z'| := by positivity
    calc 3 * |z - z'| = 3 * |z - z'| * 1 := by ring
      _ ≤ 3 * |z - z'| * ((1 + z) * (1 + z')) := mul_le_mul_of_nonneg_left hge h2n
  exact ⟨hb1, hb2, hb3, hlip1, hlip2, hlip3⟩

/-! ## The angular coefficient `Γ/c` -/

/-- The bound `|Γ(θ)/c| ≤ 10` on `Iθ`: `Γ ≤ 1` and `c ≥ 1/10`. -/
theorem jca_gam_div_c_bdd {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)| ≤ 10 := by
  have hP : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hP1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨hc1, hc10⟩ := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hP hP1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith
  intro θ hθ
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hP hθ
  rw [abs_of_nonneg (div_nonneg hG0 hcpos.le), div_le_iff₀ hcpos]
  nlinarith [hG1, hc1]

/-- The `α`-Hölder modulus `40` of `Γ/c` on `Iθ` (from `rhsJet_gam_div_c_holder`). -/
theorem jca_gam_div_c_holder {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)
        - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)| ≤ 40 * |θ - θ'| ^ α :=
  fun θ hθ θ' hθ' => rhsJet_gam_div_c_holder hα hα13 hθ hθ'

/-! ## The product `2z Γ(θ)/(c(1+z)²)` -/

/-- Bounds and `α`-Hölder modulus of `(z,θ) ↦ 2z Γ(θ)/(c(1+z)²)`: bounded by `10` and
`α`-Hölder with constant `60` for the metric `|Δz| + |Δθ|`. -/
theorem jca_zgam_facts {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    (∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)| ≤ 10) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)
        - 2 * z' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
          / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z') ^ 2)|
      ≤ 60 * (|z - z'| + |θ - θ'|) ^ α) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨hb1, -, -, hlip1, -, -⟩ := jca_z_facts hα hα1
  have hh1 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2| ≤ 2 * |z - z'| ^ α := by
    intro z z' hz hz'
    have h := Lib.holder_of_lipschitz_of_bounded (f := fun w : ℝ => 2 * w / (1 + w) ^ 2)
      hα hα1 (by norm_num) (by norm_num) hlip1 hb1 z z' hz hz'
    have hmax : max (2 : ℝ) (2 * 1) = 2 := by norm_num
    rwa [hmax] at h
  have hFb := jca_gam_div_c_bdd hα hα13
  have hFh := jca_gam_div_c_holder hα hα13
  constructor
  · intro z hz θ hθ
    have heq : 2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)
        = (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)) := by
      field_simp
    rw [heq, abs_mul]
    calc |2 * z / (1 + z) ^ 2| * |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        ≤ 1 * 10 := mul_le_mul (hb1 z hz) (hFb θ hθ) (abs_nonneg _) (by norm_num)
      _ = 10 := by norm_num
  · intro z z' hz hz' θ hθ θ' hθ'
    have heq : 2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)
          - 2 * z' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z') ^ 2)
        = (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          - (2 * z' / (1 + z') ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)) := by
      field_simp
    have hsplit : (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          - (2 * z' / (1 + z') ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        = (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          + (2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2)
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)) := by
      ring
    rw [heq, hsplit]
    have hA : |(2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)
          - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))| ≤ 1 * (40 * |θ - θ'| ^ α) := by
      rw [abs_mul]
      exact mul_le_mul (hb1 z hz) (hFh θ hθ θ' hθ') (abs_nonneg _) (by norm_num)
    have hB : |(2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2)
          * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))| ≤ (2 * |z - z'| ^ α) * 10 := by
      rw [abs_mul]
      exact mul_le_mul (hh1 z z' hz hz') (hFb θ' hθ') (abs_nonneg _) (by positivity)
    have hd0 : (0 : ℝ) ≤ |z - z'| + |θ - θ'| := by positivity
    have hzd : |z - z'| ^ α ≤ (|z - z'| + |θ - θ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (θ - θ')]) hα.le
    have hθd : |θ - θ'| ^ α ≤ (|z - z'| + |θ - θ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (z - z')]) hα.le
    calc |(2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          + (2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2)
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))|
        ≤ |(2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))|
          + |(2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2)
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))| := abs_add_le _ _
      _ ≤ 1 * (40 * |θ - θ'| ^ α) + (2 * |z - z'| ^ α) * 10 := add_le_add hA hB
      _ = 40 * |θ - θ'| ^ α + 20 * |z - z'| ^ α := by ring
      _ ≤ 40 * (|z - z'| + |θ - θ'|) ^ α + 20 * (|z - z'| + |θ - θ'|) ^ α :=
          add_le_add (mul_le_mul_of_nonneg_left hθd (by norm_num))
            (mul_le_mul_of_nonneg_left hzd (by norm_num))
      _ = 60 * (|z - z'| + |θ - θ'|) ^ α := by ring

/-! ## The main statement -/

theorem jet_coeff_all {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    Work.FTS.Regularity.Jet α S 2 (fun z θ _ => 2 * z / (1 + z) ^ 2) ∧
    Work.FTS.Regularity.Jet α S 4 (fun z θ _ => 2 / (1 + z)) ∧
    Work.FTS.Regularity.Jet α S 6 (fun z θ _ => 3 / (1 + z)) ∧
    Work.FTS.Regularity.Jet α S 40
      (fun z θ _ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)) ∧
    Work.FTS.Regularity.Jet α S 160
      (fun z θ _ => 2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)) ∧
    Work.FTS.Regularity.Jet α S 100
      (fun z θ _ => Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨hb1, hb2, hb3, hlip1, hlip2, hlip3⟩ := jca_z_facts hα hα1
  -- the three radial coefficients, converted to `α`-Hölder
  have hh1 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2| ≤ 2 * |z - z'| ^ α := by
    intro z z' hz hz'
    have h := Lib.holder_of_lipschitz_of_bounded (f := fun w : ℝ => 2 * w / (1 + w) ^ 2)
      hα hα1 (by norm_num) (by norm_num) hlip1 hb1 z z' hz hz'
    have hmax : max (2 : ℝ) (2 * 1) = 2 := by norm_num
    rwa [hmax] at h
  have hh2 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 / (1 + z) - 2 / (1 + z')| ≤ 4 * |z - z'| ^ α := by
    intro z z' hz hz'
    have h := Lib.holder_of_lipschitz_of_bounded (f := fun w : ℝ => 2 / (1 + w))
      hα hα1 (by norm_num) (by norm_num) hlip2 hb2 z z' hz hz'
    have hmax : max (2 : ℝ) (2 * 2) = 4 := by norm_num
    rwa [hmax] at h
  have hh3 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |3 / (1 + z) - 3 / (1 + z')| ≤ 6 * |z - z'| ^ α := by
    intro z z' hz hz'
    have h := Lib.holder_of_lipschitz_of_bounded (f := fun w : ℝ => 3 / (1 + w))
      hα hα1 (by norm_num) (by norm_num) hlip3 hb3 z z' hz hz'
    have hmax : max (3 : ℝ) (2 * 3) = 6 := by norm_num
    rwa [hmax] at h
  have hFb := jca_gam_div_c_bdd hα hα13
  have hFh := jca_gam_div_c_holder hα hα13
  obtain ⟨hAb, hAh⟩ := jca_zgam_facts hα hα13
  obtain ⟨hAKb, hAKh⟩ := rhsJet_ak_bounds hα hα13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jet_of_z (f := fun z : ℝ => 2 * z / (1 + z) ^ 2) (N := 2) (M := 1) (K := 2)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb1 hh1
  · exact jet_of_z (f := fun z : ℝ => 2 / (1 + z)) (N := 4) (M := 2) (K := 4)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb2 hh2
  · exact jet_of_z (f := fun z : ℝ => 3 / (1 + z)) (N := 6) (M := 3) (K := 6)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb3 hh3
  · exact jet_of_θ (g := fun θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)) (N := 40) (M := 10) (K := 40)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hFb hFh
  · exact jet_of_zθ (A := fun z θ => 2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2))
      (N := 160) (M := 10) (K := 60)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAb hAh
  · exact jet_of_zθ (A := fun z θ => Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ)
      (N := 100) (M := 10) (K := 100)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAKb hAKh

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R1b.Locals =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R1b

open Set Filter Topology MeasureTheory
open scoped Topology Real

set_option autoImplicit false

/-! ## The local objects -/

/-- The `θ`-slice of the family, as a function on the `(z,τ)`-plane. -/
noncomputable def baseFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ := fun q => g q.1 θ q.2

/-- The `τ`-derivative of the family at `τ = 0`, as a function of `z`. -/
noncomputable def tauDer (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ → ℝ :=
  fun z => deriv (fun s => g z θ s) 0

/-- `tauDer`, viewed as a function on the `(z,τ)`-plane (constant in `τ`). -/
noncomputable def tauDerFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ := fun q => tauDer g θ q.1

/-- The first-order Taylor jet of the family in `τ` at `τ = 0`: the `τ < 0` branch of `extG`. -/
noncomputable def jetFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun q => g q.1 θ 0 + q.2 * tauDer g θ q.1

/-- The extension `extG g · θ ·`, as a function on the `(z,τ)`-plane. -/
noncomputable def extFun (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun q => Work.FTS.RegPkgGal.extG g q.1 θ q.2

/-- The candidate derivative of the extension.  For `z ≤ 0` the extension vanishes identically
nearby, so the derivative is `0`; for `z > 0` it is the Fréchet derivative of the branch
(`jetFn` for `τ < 0`, `baseFn` for `τ ≥ 0`), written in terms of the two partial derivatives. -/
noncomputable def extDeriv (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun q =>
    if q.1 ≤ 0 then 0
    else if q.2 < 0 then
      (deriv (fun z => jetFn g θ (z, q.2)) q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun t => jetFn g θ (q.1, t)) q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ
    else
      (deriv (fun z => baseFn g θ (z, q.2)) q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun t => baseFn g θ (q.1, t)) q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem baseFn_apply (g : ℝ → ℝ → ℝ → ℝ) (θ z τ : ℝ) :
    baseFn g θ (z, τ) = g z θ τ := rfl

@[simp] theorem tauDerFn_apply (g : ℝ → ℝ → ℝ → ℝ) (θ z τ : ℝ) :
    tauDerFn g θ (z, τ) = tauDer g θ z := rfl

@[simp] theorem jetFn_apply (g : ℝ → ℝ → ℝ → ℝ) (θ z τ : ℝ) :
    jetFn g θ (z, τ) = g z θ 0 + τ * tauDer g θ z := rfl

@[simp] theorem extFun_apply (g : ℝ → ℝ → ℝ → ℝ) (θ z τ : ℝ) :
    extFun g θ (z, τ) = Work.FTS.RegPkgGal.extG g z θ τ := rfl

@[simp] theorem extDeriv_of_nonpos (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z : ℝ} (hz : z ≤ 0) (τ : ℝ) :
    extDeriv g θ (z, τ) = 0 := by
  simp only [extDeriv]
  rw [if_pos hz]

theorem extDeriv_of_pos_of_neg (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z) (hτ : τ < 0) :
    extDeriv g θ (z, τ)
      = (deriv (fun z' => jetFn g θ (z', τ)) z) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun t => jetFn g θ (z, t)) τ) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  simp only [extDeriv]
  rw [if_neg (not_le.mpr hz), if_pos hτ]

theorem extDeriv_of_pos_of_nonneg (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : 0 ≤ τ) :
    extDeriv g θ (z, τ)
      = (deriv (fun z' => baseFn g θ (z', τ)) z) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun t => baseFn g θ (z, t)) τ) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  simp only [extDeriv]
  rw [if_neg (not_le.mpr hz), if_neg (not_lt.mpr hτ)]

/-! ## The extension as a piecewise function -/

theorem extFun_of_nonpos (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : z ≤ 0) :
    extFun g θ (z, τ) = 0 := by
  simp only [extFun_apply]
  exact extG_of_nonpos hz

theorem extFun_of_pos_of_nonneg (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : 0 ≤ τ) : extFun g θ (z, τ) = baseFn g θ (z, τ) := by
  simp only [extFun_apply, baseFn_apply]
  exact extG_of_pos hz hτ

theorem extFun_of_pos_of_neg (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z) (hτ : τ < 0) :
    extFun g θ (z, τ) = jetFn g θ (z, τ) := by
  simp only [extFun_apply, jetFn_apply]
  rw [extG_of_neg hz hτ]
  simp only [tauDer]

/-- At `τ = 0` the jet agrees with the family. -/
theorem jetFn_eq_baseFn_at_zero (g : ℝ → ℝ → ℝ → ℝ) (θ z : ℝ) :
    jetFn g θ (z, 0) = baseFn g θ (z, 0) := by
  simp only [jetFn_apply, baseFn_apply]
  ring


noncomputable def jetBranch (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun q => (deriv (fun z => jetFn g θ (z, q.2)) q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
    + (deriv (fun t => jetFn g θ (q.1, t)) q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The `τ ≥ 0` branch of the candidate derivative. -/
noncomputable def baseBranch (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun q => (deriv (fun z => baseFn g θ (z, q.2)) q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
    + (deriv (fun t => baseFn g θ (q.1, t)) q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem extDeriv_of_pos_of_neg' (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : τ < 0) : extDeriv g θ (z, τ) = jetBranch g θ (z, τ) :=
  extDeriv_of_pos_of_neg g θ hz hτ

theorem extDeriv_of_pos_of_nonneg' (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : 0 ≤ τ) : extDeriv g θ (z, τ) = baseBranch g θ (z, τ) :=
  extDeriv_of_pos_of_nonneg g θ hz hτ

end Work.FTS.RegPkgGal.R1b
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R2.Repair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The repaired Taylor packages

Two versions of the repaired statement, both conditional on the single analytic input `hA`
(the angular integral bound `Work.FTS.RegPkgGal.R2.angIntegral_le`):

* `tay_clauses_nbhd_aux` — the shape adopted by the repaired interface (`R2b`): the joint
  smoothness is taken on a neighbourhood of the closed angular range;
* `tay_clauses_of_continuous_aux` — the version with the minimal extra hypothesis (continuity of
  the angular slices on `Iθ`), which additionally needs `hE`
  (`Work.FTS.RegPkgGal.R2.integrableOn_pth_slice`).
-/

open MeasureTheory Set Filter Topology
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R2

/-! ## The two repaired packages

Both are stated with the single analytic input `hA` (the angular integral bound, proved as
`Work.FTS.RegPkgGal.R2.angIntegral_le`) as a hypothesis; the unconditional versions are added
below once `angIntegral_le` is available. -/


/-- **The repaired Taylor clauses, with the minimal extra hypothesis of continuity of the
angular slices on `Iθ`** (the weakest repair: the smoothness hypothesis `hsm` is left as in the
requested statement, and one adds exactly the information that the counterexample above
violates). -/
theorem tay_clauses_of_continuous_aux {α S Cθ K Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hCθ : 0 ≤ Cθ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |g z θ τ| ≤ K * z ^ 2)
    (hlinz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Q * z)
    (hcontθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 < z → z ≤ 2 →
      ContinuousOn (fun θ => g z θ τ) Work.Spaces.Iθ)
    (hA : ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      IntervalIntegrable
          (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          volume a b ∧
        (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          ≤ M * (b - a) ^ α)
    (hE : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 < z → IntegrableOn
      (fun s : ℝ => Work.Spaces.pth (fun z θ => g z θ τ) z s)
      (Set.Icc 0 (Real.pi / 2)) volume) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K' * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K' * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K' * z ^ 2 * |θ - θ'| ^ α) := by
  obtain ⟨M, hM0, hA'⟩ := hA
  refine ⟨max K (max Q (Cθ * M)), le_trans hK (le_max_left _ _), ?_⟩
  intro τ hτ θ hθ
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hz2
    exact le_trans (hquad τ hτ θ hθ z hz hz2)
      (mul_le_mul_of_nonneg_right (le_max_left K (max Q (Cθ * M))) (sq_nonneg z))
  · have hsmw : ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) := hsm τ hτ
    have hQK : max Q K ≤ max K (max Q (Cθ * M)) :=
      max_le (le_trans (le_max_left Q (Cθ * M)) (le_max_right K (max Q (Cθ * M))))
        (le_max_left K (max Q (Cθ * M)))
    have hB2 : ∀ {z θ' : ℝ}, 0 < z → θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
        HasDerivAt (fun s : ℝ => (fun z θ => g z θ τ) s θ')
          (Work.Spaces.pz (fun z θ => g z θ τ) z θ') z :=
      fun hz hθ' => hasDerivAt_slice_pz (f := fun z θ => g z θ τ) hsmw hz hθ'
    exact zClause_aux hQ hQK hsmw (hvt τ hτ) (hquad τ hτ) (hlinz τ hτ) hB2 θ hθ
  · intro z hz hz2 θ' hθ'
    rcases eq_or_lt_of_le hz with hz0 | hzpos
    · subst hz0
      have h1 : g 0 θ τ = 0 := by
        have h := hquad τ hτ θ hθ 0 le_rfl (by norm_num : (0:ℝ) ≤ 2)
        have h' : |g 0 θ τ| ≤ 0 := by simpa using h
        exact abs_eq_zero.mp (le_antisymm h' (abs_nonneg _))
      have h2 : g 0 θ' τ = 0 := by
        have h := hquad τ hτ θ' hθ' 0 le_rfl (by norm_num : (0:ℝ) ≤ 2)
        have h' : |g 0 θ' τ| ≤ 0 := by simpa using h
        exact abs_eq_zero.mp (le_antisymm h' (abs_nonneg _))
      rw [h1, h2, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg (le_trans hK (le_max_left _ _)) (sq_nonneg 0))
        (Real.rpow_nonneg (abs_nonneg _) _)
    · have hM : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
          (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
            ≤ M * (b - a) ^ α := fun a b ha hab hb => (hA' a b ha hab hb).2
      have hIntγ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
          IntervalIntegrable (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
            volume a b := fun a b ha hab hb => (hA' a b ha hab hb).1
      have hE' : ∀ z : ℝ, 0 < z → IntegrableOn
          (fun s : ℝ => Work.Spaces.pth (fun z θ => g z θ τ) z s)
          (Set.Icc 0 (Real.pi / 2)) volume := fun z hz => hE τ hτ z hz
      have hd' : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
          |Work.Spaces.Dth (fun z θ => g z θ τ) z θ|
            ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α :=
        fun z θ hz hθ => hd τ hτ z θ hz hθ
      have hcontθ' : ∀ z : ℝ, 0 < z → z ≤ 2 →
          ContinuousOn (fun θ => (fun z θ => g z θ τ) z θ) Work.Spaces.Iθ :=
        fun z hz hz2 => hcontθ τ hτ z hz hz2
      have hB1 : ∀ {z θ' : ℝ}, 0 < z → θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
          HasDerivAt (fun s : ℝ => (fun z θ => g z θ τ) z s)
            (Work.Spaces.pth (fun z θ => g z θ τ) z θ') θ' :=
        fun hz hθ' => hasDerivAt_slice_pth (f := fun z θ => g z θ τ) (hsm τ hτ) hz hθ'
      have hcl := angClause_aux hα hα1 hCθ hM0 hM hIntγ hE' (hsm τ hτ) hd' hcontθ' hB1
        z θ θ' hzpos hz2 hθ hθ'
      calc |g z θ τ - g z θ' τ| ≤ Cθ * M * z ^ 2 * |θ - θ'| ^ α := hcl
        _ ≤ max K (max Q (Cθ * M)) * z ^ 2 * |θ - θ'| ^ α := by
            have hCM : Cθ * M ≤ max K (max Q (Cθ * M)) :=
              le_trans (le_max_right Q (Cθ * M)) (le_max_right K (max Q (Cθ * M)))
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM (sq_nonneg z))
              (Real.rpow_nonneg (abs_nonneg _) _)

end Work.FTS.RegPkgGal.R2
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Congruence of the derived operators on an open set -/

private lemma pz_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hz)
  have hslice : (fun z' => Function.uncurry f (z', θ)) =ᶠ[𝓝 z]
      (fun z' => Function.uncurry f' (z', θ)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  have := hslice.deriv_eq
  simpa only [Work.Spaces.pz, Function.uncurry] using this

private lemma pth_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (Continuous.prodMk_right z).continuousAt.eventually (hV.mem_nhds hz)
  have hslice : (fun θ' => Function.uncurry f (z, θ')) =ᶠ[𝓝 θ]
      (fun θ' => Function.uncurry f' (z, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have := hslice.deriv_eq
  simpa only [Work.Spaces.pth, Function.uncurry] using this

/-- Congruence of `DzIter` on an open set. -/
lemma DzIter_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (j : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j f')) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro y hy
      have hp := pz_congr_of_isOpen hV ih hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter j f) y.1 y.2
        = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j f') y.1 y.2
      rw [hp]

/-- Congruence of `mixed` on an open set. -/
lemma mixed_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (j i : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.mixed j i f))
      (Function.uncurry (Work.Spaces.mixed j i f')) V := by
  have hth : EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i f')) V := by
    induction i with
    | zero => exact h
    | succ i ih =>
        intro y hy
        have hp := pth_congr_of_isOpen hV ih hy
        show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter i f) y.1 y.2
          = Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter i f') y.1 y.2
        rw [hp]
  exact DzIter_congr_of_isOpen hV hth j

/-! ## R8: the `ℋ⁴`-membership of the extended slice -/

/-- On `Iz ×ˢ univ` the `ℋ⁴`-integrand of the extended slice agrees with that of the original
slice, at every `τ ≥ 0`.  For `z > 0` this is the congruence of the derived operators on the open
set `Ioi 0`; at `z = 0` both integrands vanish because of the factor `w 0 = 0`. -/
lemma HkIntegrand_extG_eq {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ}
    (hz : 0 ≤ z) :
    Work.Spaces.HkIntegrand (pExp α) 4 (fun z θ => extG g z θ τ) z θ
      = Work.Spaces.HkIntegrand (pExp α) 4 (fun z θ => g z θ τ) z θ := by
  by_cases hz0 : z = 0
  · subst hz0
    have hw : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
    simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, hw]
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hagree : EqOn (Function.uncurry (fun z θ => extG g z θ τ))
        (Function.uncurry (fun z θ => g z θ τ)) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
      rintro ⟨z', θ'⟩ ⟨hz', -⟩
      simp only [Function.uncurry]
      exact extG_of_pos hz' hτ
    have hmem : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := ⟨hzpos, trivial⟩
    simp only [Work.Spaces.HkIntegrand]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      have h := DzIter_congr_of_isOpen hV hagree i hmem
      simp only [Function.uncurry] at h
      rw [h]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hij : 1 ≤ i ∧ i + j ≤ 4
      · simp only [hij]
        have h := mixed_congr_of_isOpen hV hagree j i hmem
        simp only [Function.uncurry] at h
        rw [h]
      · simp only [hij, ite_false]

/-- **R8.** The `ℋ⁴`-membership of the extended slice, for every `τ` in the strip: this is
`RegPkgMin.mem4` transported along `HkIntegrand_extG_eq`. -/
theorem mem4_extG {α : ℝ} {S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hmin : RegPkgMin (pExp α) g) :
    ∀ τ ∈ Set.Icc 0 S, Work.Spaces.HkMem (pExp α) 4 (fun z θ => extG g z θ τ) := by
  intro τ hτ
  obtain ⟨h1, h2⟩ := hmin.mem4 τ hτ.1
  refine ⟨fun z hz => ?_, ?_⟩
  · refine IntegrableOn.congr_fun (h1 z hz) (fun θ _ => ?_) measurableSet_Icc
    exact (HkIntegrand_extG_eq (α := α) (g := g) (τ := τ) hτ.1 (z := z) (θ := θ) hz).symm
  · refine IntegrableOn.congr_fun h2 (fun z hz => ?_) measurableSet_Ici
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun θ => (HkIntegrand_extG_eq (α := α) (g := g) (τ := τ) hτ.1 (z := z) (θ := θ) hz).symm))

end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.Regularity.gammaFstarModuli =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FTS.Regularity

/-! ## The one-variable profile `F_*(z) = 2z/(1+z)²` -/

/-- `2z/(1+z)² ≥ 0` for `z ≥ 0`. -/
theorem fmFstar_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Work.FM.Fstar z := by
  rw [Work.FM.Fstar]
  exact div_nonneg (by linarith) (by positivity)

/-- `2z/(1+z)² ≤ 1/2` for `z ≥ 0` (`(1-z)² ≥ 0`). -/
theorem fmFstar_le_half {z : ℝ} (hz : 0 ≤ z) : Work.FM.Fstar z ≤ 1 / 2 := by
  rw [Work.FM.Fstar, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z)]

/-- `|2z/(1+z)²| ≤ 1/2` for `z ≥ 0`. -/
theorem fmFstar_abs_le_half {z : ℝ} (hz : 0 ≤ z) : |Work.FM.Fstar z| ≤ 1 / 2 := by
  rw [abs_of_nonneg (fmFstar_nonneg hz)]
  exact fmFstar_le_half hz


/-! ## The coefficient `3α/c(3α)` -/

/-- The coefficient of the profile is bounded: `|3α/c(3α)| ≤ 10` for `0 < α ≤ 1/3`, since
`3α ≤ 1` and `c(3α) ≥ 1/10`. -/
theorem threeAlpha_div_c_abs_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    |3 * α / Work.Spaces.c (3 * α)| ≤ 10 := by
  have h3a : 0 < 3 * α := by linarith
  have h3a1 : 3 * α ≤ 1 := by linarith
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c (3 * α) :=
    (Work.Spaces.c_bounds (3 * α) h3a h3a1).1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by linarith
  rw [abs_of_nonneg (div_nonneg (by linarith) hcpos.le), div_le_iff₀ hcpos]
  nlinarith

/-! ## Two elementary exponent inequalities -/

/-- For `0 ≤ d ≤ 1` and `0 < α ≤ 1`: `d ≤ d ^ α` (the map `x ↦ x ^ α` is `≥` the identity on
`[0,1]`).  The case `d = 0` is the null exponent case of `Real.zero_rpow`. -/
theorem self_le_rpow_of_le_one {α d : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) : d ≤ d ^ α := by
  rcases eq_or_lt_of_le hd0 with h | h
  · rw [← h, Real.zero_rpow hα0.ne']
  · have hle := Real.rpow_le_rpow_of_exponent_ge h hd1 hα1
    simpa [Real.rpow_one] using hle

/-- **The join inequality.**  If a nonnegative quantity `x` is bounded both by a constant `M`
and by a combination `A·t + B·s^α` of two nonnegative variables `t, s`, then it is bounded by
`max M (A + B)·(t + s)^α` — the standard way of merging a `C⁰` bound with a "Hölder-type" one
into a single modulus for the metric `t + s`.

Below the level `t + s ≤ 1` the linear term is dominated by `(t+s)^α` (`t ≤ (t+s) ≤ (t+s)^α`) and
so is `s^α`; above the level `1` the constant bound `M` is, since `(t+s)^α ≥ 1`. -/
theorem join_rpow_le {α M A B t s x : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hxM : x ≤ M) (hxAB : x ≤ A * t + B * s ^ α) :
    x ≤ max M (A + B) * (t + s) ^ α := by
  have hD : 0 ≤ t + s := by linarith
  have hmax0 : 0 ≤ max M (A + B) := le_trans hM (le_max_left M (A + B))
  by_cases hle : t + s ≤ 1
  · have hself : t + s ≤ (t + s) ^ α := self_le_rpow_of_le_one hα0 hα1 hD hle
    have hDα : 0 ≤ (t + s) ^ α := Real.rpow_nonneg hD α
    have htD : t ≤ (t + s) ^ α := le_trans (by linarith) hself
    have hAt : A * t ≤ A * (t + s) ^ α := mul_le_mul_of_nonneg_left htD hA
    have hBs : B * s ^ α ≤ B * (t + s) ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs (by linarith) hα0.le) hB
    have hsum : A * t + B * s ^ α ≤ (A + B) * (t + s) ^ α := by
      rw [add_mul]
      linarith
    exact le_trans hxAB
      (le_trans hsum (mul_le_mul_of_nonneg_right (le_max_right M (A + B)) hDα))
  · have hgt : 1 ≤ t + s := le_of_lt (not_le.mp hle)
    have hDα1 : 1 ≤ (t + s) ^ α := Real.one_le_rpow hgt hα0.le
    calc x ≤ M := hxM
      _ ≤ max M (A + B) := le_max_left M (A + B)
      _ = max M (A + B) * 1 := (mul_one _).symm
      _ ≤ max M (A + B) * (t + s) ^ α := mul_le_mul_of_nonneg_left hDα1 hmax0

/-! ## The angular vanishing of the profile and its `Γ`-bound -/

/-- `|F_*(z,θ)| ≤ 20·Γ(θ)` for `z ≥ 0`, `θ ∈ Iθ` and `0 < α ≤ 1/3`: the coefficient
`20·(3α) ≤ 20` of `Work.ConstructionInstance.Fstar_abs_le` (which is `≤ 20·p·Γ(p/3)`) has
`p = 3α`. -/
theorem fstar_abs_le_gamma {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (3 * α) z θ| ≤ 20 * Gamma α θ := by
  have h := Work.ConstructionInstance.Fstar_abs_le (p := 3 * α) (by linarith) (by linarith) hz hθ
  have h3 : (3 * α) / 3 = α := by ring
  rw [h3] at h
  refine le_trans h ?_
  have hG0 : 0 ≤ Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  have h20 : 20 * (3 * α) ≤ 20 := by linarith
  exact mul_le_mul_of_nonneg_right h20 hG0

/-! ## The angular modulus of a fixed `z`-slice -/

/-- **The angular modulus of `F_*` at fixed `z`**: for `z ≥ 0` and `θ, θ' ∈ Iθ`,

  `|F_*(z,θ) - F_*(z,θ')| ≤ 5·3^α·|θ-θ'|^α`.

The profile factors as `((3α/c(3α))·2z/(1+z)²)·Γ(θ)`; the first factor is bounded by
`10·(1/2) = 5` and the second difference by the angular modulus `3^α|θ-θ'|^α` of `Γ`. -/
theorem fstar_theta_modulus {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z θ θ' : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z θ'|
      ≤ 5 * 3 ^ α * |θ - θ'| ^ α := by
  have hkey : Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z θ'
      = ((3 * α / Work.Spaces.c (3 * α)) * Work.FM.Fstar z)
        * (Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ') := by
    simp only [Work.Construction.Fstar]
    ring
  have hK : |(3 * α / Work.Spaces.c (3 * α)) * Work.FM.Fstar z| ≤ 5 := by
    rw [abs_mul]
    calc |3 * α / Work.Spaces.c (3 * α)| * |Work.FM.Fstar z|
        ≤ 10 * (1 / 2) :=
          mul_le_mul (threeAlpha_div_c_abs_le hα hα13) (fmFstar_abs_le_half hz) (abs_nonneg _)
            (by norm_num)
      _ = 5 := by norm_num
  have hG : |Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'| ≤ 3 ^ α * |θ - θ'| ^ α := by
    rw [gam_three α θ, gam_three α θ']
    exact gammaModulus (α := α) hα hα13 θ θ' hθ hθ'
  rw [hkey, abs_mul]
  calc |(3 * α / Work.Spaces.c (3 * α)) * Work.FM.Fstar z|
        * |Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'|
      ≤ 5 * (3 ^ α * |θ - θ'| ^ α) :=
        mul_le_mul hK hG (abs_nonneg _) (by norm_num)
    _ = 5 * 3 ^ α * |θ - θ'| ^ α := by ring

/-! ## The split bound and the joint modulus -/

/-- **The split bound**: splitting the joint difference at the intermediate point `(z',θ)`, the
radial part is `fstarModulus` (`≤ 20|z-z'|`) and the angular part is `fstar_theta_modulus`
(`≤ 5·3^α|θ-θ'|^α`). -/
theorem fstar_diff_le_split {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z z' θ θ' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ'|
      ≤ 20 * |z - z'| + 5 * 3 ^ α * |θ - θ'| ^ α := by
  have h1 : |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ|
      ≤ 20 * |z - z'| := fstarModulus (α := α) hα hα13 z z' θ hz hz' hθ
  have h2 : |Work.Construction.Fstar (3 * α) z' θ - Work.Construction.Fstar (3 * α) z' θ'|
      ≤ 5 * 3 ^ α * |θ - θ'| ^ α := fstar_theta_modulus hα hα13 hz' hθ hθ'
  exact le_trans (abs_sub_le _ _ _) (add_le_add h1 h2)

/-- **The joint `α`-Hölder modulus of the profile `F_*(3α)`** for the metric
`|Δz| + |Δθ|` on `[0,∞) × Iθ`, with the structural constant `100`. -/
theorem fstar_joint_modulus {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z z' θ θ' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ'|
      ≤ 100 * (|z - z'| + |θ - θ'|) ^ α := by
  have hsplit := fstar_diff_le_split hα hα13 hz hz' hθ hθ'
  -- the global (`C⁰`) bound `|F_*| ≤ 20Γ ≤ 20`
  have hglob : |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ'|
      ≤ 40 := by
    have hz1 : |Work.Construction.Fstar (3 * α) z θ| ≤ 20 * Gamma α θ :=
      fstar_abs_le_gamma hα hα13 hz hθ
    have hz2 : |Work.Construction.Fstar (3 * α) z' θ'| ≤ 20 * Gamma α θ' :=
      fstar_abs_le_gamma hα hα13 hz' hθ'
    have hG1 : Gamma α θ ≤ 1 := Work.ConstructionInstance.Gamma_le_one hα.le hθ
    have hG2 : Gamma α θ' ≤ 1 := Work.ConstructionInstance.Gamma_le_one hα.le hθ'
    calc |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ'|
        ≤ |Work.Construction.Fstar (3 * α) z θ| + |Work.Construction.Fstar (3 * α) z' θ'| := by
          have := abs_sub_le (Work.Construction.Fstar (3 * α) z θ) 0
            (Work.Construction.Fstar (3 * α) z' θ')
          simpa using this
      _ ≤ 20 * Gamma α θ + 20 * Gamma α θ' := add_le_add hz1 hz2
      _ ≤ 40 := by nlinarith
  have hjoin := join_rpow_le (M := 40) (A := 20) (B := 5 * 3 ^ α) hα (by linarith)
    (by norm_num) (by norm_num) (by positivity) (abs_nonneg _) (abs_nonneg _) hglob hsplit
  have hmax : max (40 : ℝ) (20 + 5 * 3 ^ α) ≤ 100 := by
    refine max_le (by norm_num) ?_
    have h3 : (3 : ℝ) ^ α ≤ 3 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by linarith : α ≤ 1)
      simpa [Real.rpow_one] using this
    linarith
  exact le_trans hjoin (mul_le_mul_of_nonneg_right hmax (Real.rpow_nonneg (by positivity) α))

/-! ## The packaged statement -/


end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.starPkg_mono =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Decay3Aux

theorem starPkg_mono {α Cs Cs' : ℝ} (hα : 0 < α) (h : Cs ≤ Cs') {Φs : Work.FTS.Galerkin.Fn}
    (hp : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) : Work.FTS.VocabO2.StarPkgo2 α Cs' Φs := by
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have hmul : ∀ x : ℝ, x ≤ Cs * α → x ≤ Cs' * α := fun x hx =>
    le_trans hx (mul_le_mul_of_nonneg_right h hα0)
  exact ⟨{ sol := hp.sol
           smooth := hp.smooth
           R := ⟨hp.R.1, hmul _ hp.R.2⟩
           dU := ⟨hp.dU.1, hmul _ hp.dU.2⟩
           V := ⟨hp.V.1, hmul _ hp.V.2⟩
           vanishU := hp.vanishU
           Vth := ⟨hp.Vth.1, hmul _ hp.Vth.2⟩ },
    ⟨hp.RW.1, hmul _ hp.RW.2⟩,
    ⟨hp.VW.1, hmul _ hp.VW.2⟩,
    ⟨hp.VzW.1, hmul _ hp.VzW.2⟩,
    ⟨hp.UsW.1, hmul _ hp.UsW.2⟩,
    ⟨hp.UszW.1, hmul _ hp.UszW.2⟩⟩

end Work.FTS.StrongEps.E4R3.Decay3Aux
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN.FaSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

set_option autoImplicit false

/-- **A.e. slice integrability from the finiteness of `Fa`.**  If `uncurry f` is a.e. strongly
measurable for `volume.restrict (Ioi 0) × volume.restrict Iθ` and `Fa f < ⊤`, then for almost
every `r > 0` the angular slice `θ ↦ K θ · f r θ` is integrable on `Iθ`. -/
theorem FaSlice {f : ℝ → ℝ → ℝ}
    (haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hfa : Work.FTS.Nonlinear.Pieces.Fa f < ⊤) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ := by
  -- ## the a.e. strong measurability of the slices
  have hslice : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.AEStronglyMeasurable (fun θ => f r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    simpa only [Function.uncurry_apply_pair] using haesm.prodMk_left
  -- ## the a.e. finiteness of the angular lintegral
  have hB : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f r θ|) < ⊤ := by
    have hmeas1 : AEMeasurable (Function.uncurry f)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := haesm.aemeasurable
    have hKp : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
      unfold Work.Spaces.K; fun_prop
    have hprod : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry f p)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      hKp.aemeasurable.mul hmeas1
    have habs : AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal |Work.Spaces.K p.2 * Function.uncurry f p|)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      hprod.abs.ennreal_ofReal
    have hB_aem : AEMeasurable (fun r : ℝ =>
        ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f r θ|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      simpa only [Function.uncurry_apply_pair] using habs.lintegral_prod_right'
    have hFinv_aem : AEMeasurable (fun r : ℝ => ENNReal.ofReal r⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ENNReal.measurable_ofReal.comp measurable_inv).aemeasurable
    have hF_aem : AEMeasurable (fun r : ℝ => ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f r θ|))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      hFinv_aem.mul hB_aem
    have hlt : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f r θ|)) < ⊤ := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hfa
    filter_upwards [MeasureTheory.ae_lt_top' hF_aem (ne_of_lt hlt),
      MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr hrI
    by_contra hBtop
    have hBeq : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * f r θ|) = ⊤ :=
      le_antisymm le_top (not_lt.mp hBtop)
    have hne : ENNReal.ofReal r⁻¹ ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hrI))
    have hthis : ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * f r θ|) = ⊤ := by
      rw [hBeq, ENNReal.mul_eq_top]
      exact Or.inl ⟨hne, rfl⟩
    exact absurd hr (by rw [hthis]; exact not_lt.mpr le_top)
  -- ## assembly: `Integrable = AEStronglyMeasurable ∧ HasFiniteIntegral`
  have hKmeas : Measurable Work.Spaces.K := by unfold Work.Spaces.K; fun_prop
  filter_upwards [hslice, hB] with r hr hm
  refine ⟨?_, ?_⟩
  · exact hKmeas.aestronglyMeasurable.mul hr
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs] using hm

end Work.FTS_MuLipC.RowN
end
end
