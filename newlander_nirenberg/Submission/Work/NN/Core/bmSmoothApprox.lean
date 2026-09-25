/-
# Smooth approximation of a bounded Hölder function on `ℂⁿ` by a mollifier

This file proves `Work.NN.Core.bmSmoothApprox`: a function `g : (Fin n → ℂ) → ℂ` which is
bounded by `A`, Hölder with exponent `α` and constant `K`, and whose support lies in the
polydisc `{z | ∀ i, ‖z i - c i‖ < s i}` (more precisely, `g z = 0` whenever
`‖z i - c i‖ ≥ s i` for some `i`), can be approximated pointwise by a sequence of functions
`G m` which are

* smooth (`ContDiff ℝ ∞`),
* bounded by the same constant `A`,
* Hölder with the same constant `K` and exponent `α`,
* supported in the strictly larger polydisc `{z | ∀ i, ‖z i - c i‖ < r i}` when `s i < r i`,

and which converge pointwise to `g`.

The construction is the classical mollification `G m = ρ m ⋆ g`, where `ρ m` is a smooth
nonnegative bump function with integral `1` and support `rOut m → 0`.  Two features make the
construction work exactly as stated:

* convolution with a probability density does not increase the sup norm nor the Hölder
  constant (both are convexity-type estimates),
* the support of the mollification is contained in the `rOut`-neighbourhood of the support
  of `g`, which is contained in the polydisc of radii `r i` as long as `rOut m < r i - s i`
  for all `i`.

The helper lemma `convolution_holder_le_of_probDensity` is the second point's invariant part;
it is stated for a general finite-dimensional real normed space since the argument never uses
anything specific to `ℂⁿ`.
-/
import Mathlib

namespace Work.NN.Core

open MeasureTheory Filter
open scoped Convolution ContDiff Topology

/-- Convolution with a probability density `ρ ≥ 0`, `∫ ρ = 1`, preserves the Hölder seminorm:
if `‖f x - f y‖ ≤ K ‖x - y‖ ^ α` for all `x y`, then the same bound holds for `ρ ⋆ f`.

This is the elementary "mollification does not increase the Hölder constant" step.  Writing
`(ρ ⋆ f) x = ∫ t, ρ t • f (x - t)`, the difference of two translates is bounded pointwise by
`ρ t * (K ‖x - y‖ ^ α)`, and `∫ t, ρ t * c = c` by `∫ ρ = 1`. -/
theorem convolution_holder_le_of_probDensity {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    [SFinite μ]
    {ρ : G → ℝ} {f : G → ℂ} {M K α : ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρint : ∫ x, ρ x ∂μ = 1) (hρi : Integrable ρ μ)
    (hfa : AEStronglyMeasurable f μ) (hfM : ∀ z, ‖f z‖ ≤ M)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) :
    ∀ x y, ‖MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
        - MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) μ y‖
          ≤ K * ‖x - y‖ ^ α := by
  intro x y
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hfM 0)
  -- The convolution integrand at a fixed point is integrable: it is dominated by `M * ρ`.
  have hint : ∀ z : G, Integrable (fun t => ρ t • f (z - t)) μ := by
    intro z
    refine Integrable.mono' (hρi.const_mul M) ?_ ?_
    · exact hρi.aestronglyMeasurable.smul
        (hfa.comp_measurePreserving (Measure.measurePreserving_sub_left μ z))
    · filter_upwards with t
      rw [norm_smul, Real.norm_of_nonneg (hρ0 t), mul_comm M (ρ t)]
      exact mul_le_mul_of_nonneg_left (hfM (z - t)) (hρ0 t)
  -- Unfold the convolution as the corresponding integral.
  have hconv : ∀ z, MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) μ z
      = ∫ t, ρ t • f (z - t) ∂μ := by
    intro z
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
  have hInt : Integrable (fun t => ‖ρ t • f (x - t) - ρ t • f (y - t)‖) μ :=
    ((hint x).sub (hint y)).norm
  -- The pointwise bound, integrated against the probability density `ρ`.
  have hbound : ∫ t, ‖ρ t • f (x - t) - ρ t • f (y - t)‖ ∂μ ≤ K * ‖x - y‖ ^ α := by
    calc ∫ t, ‖ρ t • f (x - t) - ρ t • f (y - t)‖ ∂μ
        ≤ ∫ t, ρ t * (K * ‖x - y‖ ^ α) ∂μ := by
          refine integral_mono_ae hInt (hρi.mul_const _) ?_
          filter_upwards with t
          have h1 : ρ t • f (x - t) - ρ t • f (y - t) = ρ t • (f (x - t) - f (y - t)) := by
            rw [smul_sub]
          rw [h1, norm_smul, Real.norm_of_nonneg (hρ0 t)]
          have h2 : ‖f (x - t) - f (y - t)‖ ≤ K * ‖x - y‖ ^ α := by
            have := hholder (x - t) (y - t)
            rwa [show (x - t) - (y - t) = x - y by abel] at this
          exact mul_le_mul_of_nonneg_left h2 (hρ0 t)
      _ = (∫ t, ρ t ∂μ) * (K * ‖x - y‖ ^ α) := integral_mul_const _ _
      _ = K * ‖x - y‖ ^ α := by rw [hρint, one_mul]
  calc ‖MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
        - MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) μ y‖
      = ‖∫ t, (ρ t • f (x - t) - ρ t • f (y - t)) ∂μ‖ := by
        rw [hconv x, hconv y, ← integral_sub (hint x) (hint y)]
    _ ≤ ∫ t, ‖ρ t • f (x - t) - ρ t • f (y - t)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ K * ‖x - y‖ ^ α := hbound

theorem bmSmoothApprox {n : ℕ} {g : (Fin n → ℂ) → ℂ} {A K α : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    {c : Fin n → ℂ} {s r : Fin n → ℝ} (hst : ∀ j, s j < r j)
    (hA : ∀ x, ‖g x‖ ≤ A) (hH : ∀ x y, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, (∃ i, s i ≤ ‖z i - c i‖) → g z = 0) :
    ∃ G : ℕ → (Fin n → ℂ) → ℂ,
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (G m)) ∧
      (∀ m x, ‖G m x‖ ≤ A) ∧
      (∀ m x y, ‖G m x - G m y‖ ≤ K * ‖x - y‖ ^ α) ∧
      (∀ m z, (∃ i, r i ≤ ‖z i - c i‖) → G m z = 0) ∧
      (∀ z, Filter.Tendsto (fun m => G m z) Filter.atTop (nhds (g z))) := by
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA 0)
  -- `g` is continuous because it is Hölder with a positive exponent.
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have h2 : Tendsto (fun y : Fin n → ℂ => ‖y - x‖) (𝓝 x) (𝓝 0) := by
      have hcont : ContinuousAt (fun y : Fin n → ℂ => y - x) x := by
        apply ContinuousAt.sub
        · exact continuousAt_id
        · exact continuousAt_const
      have := hcont.tendsto.norm
      simpa using this
    have hcont : ContinuousAt (fun t : ℝ => K * t ^ α) 0 :=
      ((Real.continuous_rpow_const hα.le).continuousAt).const_mul K
    have h4 : Tendsto (fun y : Fin n → ℂ => K * ‖y - x‖ ^ α) (𝓝 x) (𝓝 (K * (0 : ℝ) ^ α)) :=
      hcont.tendsto.comp h2
    rw [Real.zero_rpow hα.ne', mul_zero] at h4
    refine squeeze_zero_norm' (a := fun y : Fin n → ℂ => K * ‖y - x‖ ^ α) ?_ h4
    filter_upwards with y
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hH y x
  -- A positive radius `δ` which keeps the polydisc of radii `s` strictly inside that of radii `r`.
  have hδ : ∃ δ > 0, ∀ i, δ < r i - s i := by
    by_cases hn : Nonempty (Fin n)
    · have hn' : Finset.univ.Nonempty := Finset.univ_nonempty_iff.mpr hn
      refine ⟨(Finset.univ.inf' hn' (fun i => r i - s i)) / 2, ?_, ?_⟩
      · have hpos : 0 < Finset.univ.inf' hn' (fun i => r i - s i) := by
          rw [Finset.lt_inf'_iff]
          intro i _
          exact sub_pos.mpr (hst i)
        linarith
      · intro i
        have h1 : Finset.univ.inf' hn' (fun i => r i - s i) ≤ r i - s i :=
          Finset.inf'_le _ (Finset.mem_univ i)
        have hpos : 0 < Finset.univ.inf' hn' (fun i => r i - s i) := by
          rw [Finset.lt_inf'_iff]
          intro j _
          exact sub_pos.mpr (hst j)
        linarith
    · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hn⟩
  obtain ⟨δ, hδpos, hδlt⟩ := hδ
  let R : ℕ → ℝ := fun m => min (((m : ℝ) + 2)⁻¹) δ
  have hRpos : ∀ m, 0 < R m := fun m => lt_min (by positivity) hδpos
  have hRlt : ∀ m i, R m < r i - s i := by
    intro m i
    have h : R m ≤ δ := min_le_right _ _
    linarith [hδlt i]
  -- The family of bump functions whose outer radius is `R m`.
  let φ : ℕ → ContDiffBump (0 : Fin n → ℂ) := fun m =>
    ⟨R m / 2, R m, half_pos (hRpos m), by linarith [hRpos m]⟩
  have hRlim : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (((m : ℝ) + 2)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
      have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)
      refine h2.congr' (Eventually.of_forall fun m => ?_)
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    have h3 : Tendsto (fun m : ℕ => min (((m : ℝ) + 2)⁻¹) δ) atTop (𝓝 (min 0 δ)) :=
      h1.min tendsto_const_nhds
    rw [min_eq_left hδpos.le] at h3
    exact h3
  refine ⟨fun m => (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro m
    exact (φ m).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ m).contDiff_normed hgcont.locallyIntegrable
  · -- sup norm bound
    intro m x
    have h := MeasureTheory.dist_convolution_le (f := (φ m).normed volume) (g := g)
      (x₀ := x) (R := R m) (ε := A) (z₀ := 0) hA0
      (by rw [(φ m).support_normed_eq])
      (fun y => (φ m).nonneg_normed y) (φ m).integral_normed hgcont.aestronglyMeasurable
      (fun y _ => by rw [dist_zero_right]; exact hA y)
    simpa only [dist_zero_right] using h
  · -- Hölder bound
    intro m x y
    exact convolution_holder_le_of_probDensity (φ m).nonneg_normed (φ m).integral_normed
      (φ m).integrable_normed hgcont.aestronglyMeasurable hA hH x y
  · -- support in the enlarged polydisc
    intro m z hz
    obtain ⟨i0, hi0⟩ := hz
    have hzero : (fun t => (φ m).normed volume t • g (z - t)) = 0 := by
      funext t
      by_cases ht : (φ m).normed volume t = 0
      · simp only [ht, zero_smul, Pi.zero_apply]
      · have htmem : t ∈ Function.support ((φ m).normed volume) := ht
        rw [(φ m).support_normed_eq, Metric.mem_ball, dist_zero_right] at htmem
        have htnorm : ‖t‖ < R m := htmem
        have hgi : g (z - t) = 0 := by
          apply hsupp (z - t)
          refine ⟨i0, ?_⟩
          have h2 : ‖t i0‖ ≤ ‖t‖ := norm_le_pi_norm t i0
          have h3 : R m < r i0 - s i0 := hRlt m i0
          have hge : ‖z i0 - c i0‖ - ‖t i0‖ ≤ ‖(z - t) i0 - c i0‖ := by
            have hh := norm_add_le ((z - t) i0 - c i0) (t i0)
            have heq : (z - t) i0 - c i0 + t i0 = z i0 - c i0 := by
              simp only [Pi.sub_apply]; abel
            linarith [heq ▸ hh]
          linarith
        simp only [hgi, smul_zero, Pi.zero_apply]
    dsimp only
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
    rw [hzero]
    simp
  · -- pointwise convergence
    intro z
    exact ContDiffBump.convolution_tendsto_right_of_continuous hRlim hgcont z

end Work.NN.Core
