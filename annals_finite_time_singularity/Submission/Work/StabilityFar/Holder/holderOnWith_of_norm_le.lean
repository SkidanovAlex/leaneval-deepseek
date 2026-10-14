import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Defs
-- ===== merged: Submission.Work.Spaces.Slots.lintegral_mixed_gamma_le_HkSq_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Spaces.Slots

set_option autoImplicit false

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])



end Work.Spaces.Slots
end
end
-- ===== merged: Submission.Work.StabilityFar.BKM.bkm_tendsto_atTop_of_linf_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter Topology MeasureTheory
open scoped Topology

namespace Work.StabilityFar.BKM

/-- `bkm u` is the interval integral of `vortLInf u` — the two definitions in
`Submission/Work/LWP/Defs.lean` unfold to the same expression. -/
theorem bkm_eq_intervalIntegral_vortLInf (u : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3) :
    Work.LWP.bkm u = fun t => ∫ s in (0:ℝ)..t, Work.LWP.vortLInf u s := by
  funext t
  rfl

/-- The elementary integral `∫₀ᵗ c/(T-s) ds = c · log (T/(T-t))` for `0 ≤ t < T`, `0 < T`. -/
theorem integral_div_sub_eq (c T t : ℝ) (hT : 0 < T) (ht : t ∈ Set.Ico 0 T) :
    (∫ s in (0:ℝ)..t, c / (T - s)) = c * Real.log (T / (T - t)) := by
  have hTt : 0 < T - t := by linarith [ht.2]
  have hsub : (∫ s in (0:ℝ)..t, (1:ℝ) / (T - s)) = Real.log (T / (T - t)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => (1:ℝ) / u) T]
    simp only [sub_zero]
    exact integral_one_div_of_pos hTt hT
  have h1 : (∫ s in (0:ℝ)..t, c / (T - s)) = c * ∫ s in (0:ℝ)..t, (1:ℝ) / (T - s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    show c / (T - s) = c * (1 / (T - s))
    exact div_eq_mul_one_div c (T - s)
  rw [h1, hsub]

/-- The comparison function `t ↦ c · log (T/(T-t))` tends to `+∞` along `t → T⁻` (for
`T > 0`, `c > 0`). -/
theorem tendsto_log_div_sub_atTop (c T : ℝ) (hT : 0 < T) (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => c * Real.log (T / (T - t))) (𝓝[<] T) Filter.atTop := by
  have h1 : Filter.Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Filter.Tendsto (fun t : ℝ => T - t) (𝓝 T) (𝓝 (T - T)) :=
        tendsto_const_nhds.sub tendsto_id
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ioi, Set.mem_Iio] at ht ⊢
      linarith
  have h3 : Filter.Tendsto (fun t : ℝ => (T - t)⁻¹) (𝓝[<] T) Filter.atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h4 : Filter.Tendsto (fun t : ℝ => T * (T - t)⁻¹) (𝓝[<] T) Filter.atTop := by
    have h := (Filter.Tendsto.const_mul_atTop hT tendsto_id).comp h3
    simpa only [Function.comp_def, id_eq] using h
  have h4' : Filter.Tendsto (fun t : ℝ => T / (T - t)) (𝓝[<] T) Filter.atTop := by
    simpa only [div_eq_mul_inv] using h4
  have h5 : Filter.Tendsto (fun t : ℝ => Real.log (T / (T - t))) (𝓝[<] T) Filter.atTop :=
    Real.tendsto_log_atTop.comp h4'
  exact Filter.Tendsto.const_mul_atTop hc h5

/-- `[0,T) = Ico 0 T` is an eventual condition at `T` from the left, for `T > 0`. -/
theorem eventually_mem_Ico_nhdsLT (T : ℝ) (hT : 0 < T) :
    ∀ᶠ t in 𝓝[<] T, t ∈ Set.Ico 0 T := by
  have hIoo : Set.Ioo (0:ℝ) T ∈ 𝓝[<] T := by
    have h1 : Set.Ioi (0:ℝ) ∈ 𝓝[<] T := nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hT)
    have h2 : Set.Iio T ∈ 𝓝[<] T := self_mem_nhdsWithin
    have h3 := Filter.inter_mem h1 h2
    rwa [Set.Ioi_inter_Iio] at h3
  exact Filter.mem_of_superset hIoo (fun t ht => ⟨le_of_lt ht.1, ht.2⟩)

theorem bkm_tendsto_atTop_of_linf_lower {u : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {T c : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hlower : ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf u t)
    (hint : ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf u) volume 0 t) :
    Filter.Tendsto (Work.LWP.bkm u) (nhdsWithin T (Set.Iio T)) Filter.atTop := by
  have hbkm : ∀ t : ℝ, Work.LWP.bkm u t = ∫ s in (0:ℝ)..t, Work.LWP.vortLInf u s :=
    fun t => rfl
  rw [Filter.tendsto_atTop]
  intro a
  have hL : Filter.Tendsto (fun t : ℝ => c * Real.log (T / (T - t))) (𝓝[<] T) Filter.atTop :=
    tendsto_log_div_sub_atTop c T hT hc
  have hevL : ∀ᶠ t in 𝓝[<] T, a ≤ c * Real.log (T / (T - t)) :=
    hL.eventually (eventually_ge_atTop a)
  have hevIco : ∀ᶠ t in 𝓝[<] T, t ∈ Set.Ico 0 T := eventually_mem_Ico_nhdsLT T hT
  filter_upwards [hevL, hevIco] with t haL ht
  rw [hbkm t]
  calc a ≤ c * Real.log (T / (T - t)) := haL
    _ = ∫ s in (0:ℝ)..t, c / (T - s) := (integral_div_sub_eq c T t hT ht).symm
    _ ≤ ∫ s in (0:ℝ)..t, Work.LWP.vortLInf u s := by
        apply intervalIntegral.integral_mono_on ht.1
        · apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div
          · exact continuousOn_const
          · exact continuousOn_const.sub continuousOn_id
          · intro s hs
            have hsle : s ≤ t := by
              rw [Set.uIcc_of_le ht.1] at hs; exact hs.2
            linarith [ht.2]
        · exact hint t ht
        · intro s hs
          exact hlower s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩

end Work.StabilityFar.BKM
end
-- ===== merged: Submission.Work.StabilityFar.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-! ## The regions -/

theorem isOpen_farRegion (ρ : ℝ) : IsOpen (farRegion ρ) :=
  isOpen_lt continuous_const continuous_norm

theorem isClosed_coreRegion (ρ : ℝ) : IsClosed (coreRegion ρ) :=
  isClosed_le continuous_norm continuous_const


/-- Every point of a closed interval `[0,T]`, `T > 0`, is uniquely differentiable within it.
(For `T > 0` the interval is convex with non-empty interior, so
`uniqueDiffWithinAt_convex` applies at every point of its closure.) -/
theorem uniqueDiffWithinAt_Icc {T t : ℝ} (hT : 0 < T) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) T) t :=
  uniqueDiffWithinAt_convex (convex_Icc 0 T)
    ⟨T / 2, by rw [interior_Icc]; exact ⟨by linarith, by linarith⟩⟩ (subset_closure ht)

/-! ## Support transport -/


/-! ## The support of the time derivative -/

/-- If a slice of `ω` vanishes in a neighbourhood of `t`, then so does `∂ₜω` at `t`: the time
derivative of a function that is identically zero on a neighbourhood is zero. -/
theorem timeDeriv_eq_zero_of_eventuallyEq_zero {ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, ω x s = 0) : timeDeriv ω x t = 0 := by
  have h1 : (fun s => ω x s) =ᶠ[𝓝 t] (fun _ => (0 : R3)) := h
  have h2 : deriv (fun s => ω x s) t = deriv (fun _ : ℝ => (0 : R3)) t := h1.deriv_eq
  simpa [timeDeriv] using h2

/-- **A one-sided vanishing criterion for `deriv`.**  If `s ↦ ω x s` vanishes on `[t, t+ε)`, then
its derivative at `t` is `0`: either `ω x` is not differentiable at `t` (and `deriv` defaults to
`0`), or it is, and then its derivative equals the right-hand (within-`Ioi t`) derivative, which
is the derivative of the zero function. -/
theorem timeDeriv_eq_zero_of_eq_zero_on_Ico {ω : R3 → ℝ → R3} {x : R3} {t ε : ℝ} (hε : 0 < ε)
    (h : ∀ s ∈ Set.Ico t (t + ε), ω x s = 0) : timeDeriv ω x t = 0 := by
  show deriv (fun s => ω x s) t = 0
  by_cases hd : DifferentiableAt ℝ (fun s => ω x s) t
  · have h1 : HasDerivWithinAt (fun s => ω x s) (deriv (fun s => ω x s) t) (Set.Ioi t) t :=
      hd.hasDerivAt.hasDerivWithinAt
    have hev : (fun s => ω x s) =ᶠ[𝓝[Set.Ioi t] t] (fun _ => (0 : R3)) := by
      have hmem : (Set.Ioi t ∩ Set.Iio (t + ε)) ∈ 𝓝[Set.Ioi t] t :=
        Filter.inter_mem self_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds ((isOpen_Iio (a := t + ε)).mem_nhds
            (by simp only [Set.mem_Iio]; linarith)))
      exact Filter.mem_of_superset hmem (fun s hs => h s ⟨hs.1.le, hs.2⟩)
    have h2 : derivWithin (fun s => ω x s) (Set.Ioi t) t = 0 := by
      rw [Filter.EventuallyEq.derivWithin_eq hev (h t ⟨le_refl t, by linarith⟩)]
      exact congrFun (derivWithin_zero (𝕜 := ℝ) (F := R3) (s := Set.Ioi t)) t
    rw [← h1.derivWithin (uniqueDiffWithinAt_Ioi t), h2]
  · exact deriv_zero_of_not_differentiableAt hd

/-- The mirror image of `timeDeriv_eq_zero_of_eq_zero_on_Ico`: vanishing on `(t-ε, t]` forces
`deriv ω x t = 0`. -/
theorem timeDeriv_eq_zero_of_eq_zero_on_Ioc {ω : R3 → ℝ → R3} {x : R3} {t ε : ℝ} (hε : 0 < ε)
    (h : ∀ s ∈ Set.Ioc (t - ε) t, ω x s = 0) : timeDeriv ω x t = 0 := by
  show deriv (fun s => ω x s) t = 0
  by_cases hd : DifferentiableAt ℝ (fun s => ω x s) t
  · have h1 : HasDerivWithinAt (fun s => ω x s) (deriv (fun s => ω x s) t) (Set.Iio t) t :=
      hd.hasDerivAt.hasDerivWithinAt
    have hev : (fun s => ω x s) =ᶠ[𝓝[Set.Iio t] t] (fun _ => (0 : R3)) := by
      have hmem : (Set.Iio t ∩ Set.Ioi (t - ε)) ∈ 𝓝[Set.Iio t] t :=
        Filter.inter_mem self_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds ((isOpen_Ioi (a := t - ε)).mem_nhds
            (by simp only [Set.mem_Ioi]; linarith)))
      exact Filter.mem_of_superset hmem (fun s hs => h s ⟨hs.2, hs.1.le⟩)
    have h2 : derivWithin (fun s => ω x s) (Set.Iio t) t = 0 := by
      rw [Filter.EventuallyEq.derivWithin_eq hev (h t ⟨by linarith, le_refl t⟩)]
      exact congrFun (derivWithin_zero (𝕜 := ℝ) (F := R3) (s := Set.Iio t)) t
    rw [← h1.derivWithin (uniqueDiffWithinAt_Iio t), h2]
  · exact deriv_zero_of_not_differentiableAt hd



/-! ## The two blocks of `fderiv u.uncurry` -/



/-! ## The mean value inequality along a segment -/


end Work.StabilityFar
end
-- ===== merged: Submission.Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open MeasureTheory Filter Topology Set

/-- **The time derivative of a slice is almost everywhere strongly measurable.**

If `ω y ·` is differentiable at every time `s` in a two-sided window around `t` (with derivative
`timeDeriv ω y s`, which is how `∂ₜω` is defined), and every time slice `ω · s` in that window is
almost everywhere strongly measurable, then the slice of the time derivative `∂ₜω(·,t)` is almost
everywhere strongly measurable as well.

The proof is the elementary slope argument: `∂ₜω(y,t) = deriv (ω y) t` is the limit of the slopes
`s ↦ s⁻¹ • (ω y (t+s) - ω y t)` along any sequence in the window converging to `0`, and each of
those slopes is a measurable (in fact strongly measurable) function of `y`.  The null sequence
`τ n = ε/2 · 1/(n+1)` is chosen so that `t + τ n` always lies in the window `(t-ε, t+ε)`. -/
theorem aestronglyMeasurable_timeDeriv_slice {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {t ε : ℝ} (hε : 0 < ε)
    (hdc : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      HasDerivAt (fun s' => ω y s') (FiniteTimeSingularity.timeDeriv ω y s) s)
    (hmeas : ∀ s ∈ Set.Ioo (t - ε) (t + ε),
      MeasureTheory.AEStronglyMeasurable (ω · s) MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (fun y => FiniteTimeSingularity.timeDeriv ω y t)
      MeasureTheory.volume := by
  -- The null sequence of time steps: `τ n = ε/2 · 1/(n+1)`, so `0 < τ n < ε`.
  let τ : ℕ → ℝ := fun n => (ε / 2) * (1 / ((n : ℝ) + 1))
  have hτpos : ∀ n, 0 < τ n := by
    intro n
    have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      apply div_pos one_pos
      positivity
    have h2 : (0 : ℝ) < ε / 2 := by linarith
    simpa only [τ] using mul_pos h2 h1
  have hτlt : ∀ n, τ n < ε := by
    intro n
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      calc 1 / ((n : ℝ) + 1) ≤ 1 / (1 : ℝ) := one_div_le_one_div_of_le (by norm_num) h1
        _ = 1 := by norm_num
    have h3 : τ n ≤ (ε / 2) * 1 := by
      simp only [τ]
      exact mul_le_mul_of_nonneg_left hle (by linarith)
    linarith
  have hmem : ∀ n, t + τ n ∈ Set.Ioo (t - ε) (t + ε) := by
    intro n
    have hp := hτpos n
    have hl := hτlt n
    exact ⟨by linarith, by linarith⟩
  have ht : t ∈ Set.Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  -- Each slope is strongly measurable in `y`.
  have hf : ∀ n, AEStronglyMeasurable (fun y => (τ n)⁻¹ • (ω y (t + τ n) - ω y t)) volume := by
    intro n
    exact ((hmeas (t + τ n) (hmem n)).sub (hmeas t ht)).const_smul ((τ n)⁻¹)
  -- The slopes converge, for every `y`, to the time derivative at `t`.
  have hlim : ∀ᵐ y ∂volume, Tendsto (fun n => (τ n)⁻¹ • (ω y (t + τ n) - ω y t)) atTop
      (𝓝 (FiniteTimeSingularity.timeDeriv ω y t)) := by
    refine Eventually.of_forall (fun y => ?_)
    have hd := hdc t ht y
    have hτtend : Tendsto τ atTop (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall (fun n => ?_)⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 2)
        simpa only [τ, mul_zero] using h
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (hτpos n)
    exact hd.tendsto_slope_zero.comp hτtend
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hf hlim

end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.Decay.integrable_indicator_inv_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open MeasureTheory

/-- The singular weight `‖x-y‖⁻²` has finite integral over the closed ball `B(0,R)`, with the
explicit bound `4π(‖x‖+R)`: enlarge `B(0,R)` to the ball `B(x, ‖x‖+R)` centred at `x`, which
contains it (because `‖y‖ ≤ R` gives `‖y-x‖ ≤ R + ‖x‖`), and apply the radial computation
`∫_{B(x,r)}‖y-x‖⁻² = 4πr` of `Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le`. -/
lemma lintegral_inv_sq_closedBall_le {R : ℝ} (hR : 0 ≤ R) (x : R3) :
    ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) := by
  have hsub : Metric.closedBall (0 : R3) R ⊆ Metric.closedBall x (‖x‖ + R) := by
    intro y hy
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    simp only [Metric.mem_closedBall, dist_eq_norm]
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := by linarith
      _ = ‖x‖ + R := by ring
  calc ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ∫⁻ y in Metric.closedBall x (‖x‖ + R), ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ y in Metric.closedBall x (‖x‖ + R), ENNReal.ofReal ((‖y - x‖ ^ (2 : ℕ))⁻¹) := by
        apply lintegral_congr
        intro y
        rw [norm_sub_rev]
    _ ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) :=
        Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le x (by positivity)

theorem integrable_indicator_inv_sq (x : Work.StabilityFar.R3) {R C : ℝ} (hC : 0 ≤ C) :
    MeasureTheory.Integrable (fun y : Work.StabilityFar.R3 =>
      (Metric.closedBall (0 : Work.StabilityFar.R3) R).indicator
        (fun y => C * ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y) MeasureTheory.volume := by
  classical
  rcases lt_or_ge R 0 with hR | hR
  · have hempty : Metric.closedBall (0 : R3) R = ∅ := Metric.closedBall_eq_empty.mpr hR
    rw [hempty, Set.indicator_empty']
    exact integrable_zero R3 ℝ MeasureTheory.volume
  rw [MeasureTheory.integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  rw [MeasureTheory.IntegrableOn]
  refine ⟨?_, ?_⟩
  · apply Measurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have hbound := lintegral_inv_sq_closedBall_le (R := R) hR x
    calc ∫⁻ y in Metric.closedBall (0 : R3) R,
            ENNReal.ofReal ‖C * ((‖x - y‖ ^ (2 : ℕ))⁻¹)‖
        = ∫⁻ y in Metric.closedBall (0 : R3) R,
            ENNReal.ofReal C * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) := by
          apply lintegral_congr
          intro y
          rw [Real.norm_of_nonneg (mul_nonneg hC (by positivity)), ENNReal.ofReal_mul hC]
      _ = ENNReal.ofReal C *
            ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.Decay.norm_bsK_le_indicator =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

/-- Pointwise bound on the Biot–Savart integrand: if `‖ω‖ ≤ C` and `ω` is supported in
`closedBall 0 R`, then the integrand `bsK ω x y` is bounded by the `closedBall 0 R`-indicator
of `C * ‖x - y‖⁻²`. -/
theorem norm_bsK_le_indicator {ω : Work.StabilityFar.R3 → Work.StabilityFar.R3} {R C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ y, ‖ω y‖ ≤ C)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) (x y : Work.StabilityFar.R3) :
    ‖Work.LWP.BiotSavart.bsK ω x y‖ ≤
      (Metric.closedBall (0 : Work.StabilityFar.R3) R).indicator
        (fun y => C * ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
  by_cases h0 : ω y = 0
  · rw [Work.LWP.BiotSavart.bsK_eq_zero h0, norm_zero]
    exact Set.indicator_nonneg (fun z _ => mul_nonneg hC (inv_nonneg.mpr (by positivity))) y
  · have hyR : y ∈ Metric.closedBall (0 : Work.StabilityFar.R3) R := hsupp y h0
    rw [Set.indicator_of_mem hyR]
    have h1 := Work.LWP.BiotSavart.norm_bsK_le ω x y
    have hkey : (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ = (‖x - y‖ ^ (2 : ℕ))⁻¹ := by
      rcases eq_or_ne ‖x - y‖ 0 with h | h
      · rw [h]; simp
      · have h3 : (‖x - y‖) ^ (3 : ℕ) = ‖x - y‖ ^ (2 : ℕ) * ‖x - y‖ := by ring
        rw [h3, mul_inv, mul_assoc, inv_mul_cancel₀ h, mul_one]
    calc ‖Work.LWP.BiotSavart.bsK ω x y‖
        ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖ω y‖ * ‖x - y‖ := h1
      _ ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * C * ‖x - y‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left (hb y) (inv_nonneg.mpr (by positivity))
      _ = C * (‖x - y‖ ^ (2 : ℕ))⁻¹ := by
            rw [show (‖x - y‖ ^ (3 : ℕ))⁻¹ * C * ‖x - y‖
                  = C * ((‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖) by ring, hkey]

end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The derivative of `u.uncurry` splits into its spatial and temporal blocks

If `(x,t) ↦ u x t` is differentiable at `(x,t)` with derivative `L`, then applying `L` to a
pair `(v,s)` splits as the spatial derivative `D_xu(x,t) v` plus `s` times the time derivative
`∂ₜu(x,t)`.  This is the pointwise form of `Work.StabilityFar.blockDeriv`.  The two blocks are
computed by composing `h` with the two coordinate embeddings `x ↦ (x,t)` and `t ↦ (x,t)`.
-/

open FiniteTimeSingularity

namespace Work.StabilityFar.Deriv

theorem hasFDerivAt_uncurry_apply {u : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {L : (Work.StabilityFar.R3 × ℝ) →L[ℝ] Work.StabilityFar.R3}
    {x : Work.StabilityFar.R3} {t : ℝ}
    (h : HasFDerivAt (Function.uncurry u) L (x, t)) (v : Work.StabilityFar.R3) (s : ℝ) :
    L (v, s) = fderiv ℝ (u · t) x v + s • FiniteTimeSingularity.timeDeriv u x t := by
  have hsl := h.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) (E := Work.StabilityFar.R3) (F := ℝ) x t)
  have htt := h.comp t (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := Work.StabilityFar.R3) (F := ℝ) x t)
  have e1 : fderiv ℝ (u · t) x = L.comp (ContinuousLinearMap.inl ℝ Work.StabilityFar.R3 ℝ) := by
    simpa [Function.comp_def] using hsl.fderiv
  have e2 : FiniteTimeSingularity.timeDeriv u x t = L (0, 1) := by
    rw [FiniteTimeSingularity.timeDeriv, deriv]
    have := htt.fderiv
    change fderiv ℝ (u x) t = _ at this
    rw [this]
    rfl
  rw [e1, e2]
  rw [show (v, s) = (v, (0:ℝ)) + ((0:Work.StabilityFar.R3), s) by ext <;> simp]
  rw [map_add]
  rw [show ((0:Work.StabilityFar.R3), s) = s • ((0:Work.StabilityFar.R3), (1:ℝ)) by ext <;> simp]
  rw [map_smul]
  simp [ContinuousLinearMap.comp_apply]

end Work.StabilityFar.Deriv
end
-- ===== merged: Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Holder

/-- The norm-coordinate form of the Hölder condition implies the `edist`-coordinate form
used by `HolderOnWith`.  Since `edist` on a (pseudo)metric space is `ENNReal.ofReal` of the
distance, this is just `ENNReal.ofReal` applied to the hypothesis, together with
`ENNReal.ofReal_mul` and `ENNReal.ofReal_rpow_of_nonneg`. -/
theorem holderOnWith_of_norm_le {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {C r : NNReal} {f : X → Y} {s : Set X}
    (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (r : ℝ)) :
    HolderOnWith C r f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, dist_eq_norm]
  calc ENNReal.ofReal ‖f x - f y‖
      ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (r : ℝ)) := ENNReal.ofReal_le_ofReal (h x hx y hy)
    _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (dist x y ^ (r : ℝ)) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ↑C * ENNReal.ofReal (dist x y) ^ (r : ℝ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity), ENNReal.ofReal_coe_nnreal]

end Work.StabilityFar.Holder
end
