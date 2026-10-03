import Mathlib
import Submission.Work.Pert.small_of_nearOn

namespace Work.PertCrux

open Filter Metric
open scoped Topology

/-!
# `‖α n‖ → 0` and `‖u n 0 - 1‖ → 0` for a sequence of parabolic perturbations

This is a direct corollary of `Work.Pert.small_of_nearOn`: the near-parabolic sequence `f n`
(close to `f₀` on the *fixed* compact `closedBall 0 (16π/Ξ')` with `δ n → 0`, of the normal form
`z + z (z - σ n) u n z` on `ball 0 (rr n)`, with `1/2 ≤ ‖u n‖ ≤ 2` and `rr n` bounded below by
`1/(4(Ξ'+1))`) satisfies, for a constant `C` depending only on the germ `f₀` and a fixed radius
`ρ > 0`,

  `‖u n 0 - 1‖ ≤ C (δ n / ρ² + δ n / (ρ rr n))`,  `‖rotOf (f n)‖ ≤ C δ n / ρ`,

and the right-hand sides are `O(δ n)` because `rr n` is bounded below.  This is Shishikura
§4.2/(4.2.x): the derivative of a parabolic perturbation converges to `1`, so the rotation
number converges to `0`.
-/

/-- `NearOn` is monotone in the compact set. -/
private lemma nearOn_mono {f₀ f : ℂ → ℂ} {Df L L' : Set ℂ} {δ : ℝ} (hL : L' ⊆ L)
    (h : MandelDim.NearOn f₀ f Df L δ) : MandelDim.NearOn f₀ f Df L' δ :=
  ⟨h.1, fun _ hz => h.2.1 (hL hz), h.2.2.1, fun z hz => h.2.2.2 z (hL hz)⟩

theorem alpha_u0_tendsto_zero_seq {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {Ξ' : ℝ} (hΞ' : 0 < Ξ')
    {δ : ℕ → ℝ} (hδpos : ∀ n, 0 < δ n) (hδ0 : Filter.Tendsto δ Filter.atTop (nhds 0))
    {f : ℕ → ℂ → ℂ} {Df : ℕ → Set ℂ} {rr : ℕ → ℝ} {u : ℕ → ℂ → ℂ} {σ α : ℕ → ℂ}
    (hNear : ∀ n, MandelDim.NearOn f₀ (f n) (Df n)
      (Metric.closedBall (0 : ℂ) (16 * Real.pi / Ξ')) (δ n))
    (hf0 : ∀ n, f n 0 = 0)
    (hαeq : ∀ n, α n = MandelDim.rotOf (f n))
    (hrrpos : ∀ n, 0 < rr n)
    (hrrlb : ∀ n, 1 / (4 * (Ξ' + 1)) ≤ rr n)
    (hudiff : ∀ n, DifferentiableOn ℂ (u n) (Metric.ball 0 (rr n)))
    (hubnd : ∀ n z, z ∈ Metric.ball 0 (rr n) → 1 / 2 ≤ ‖u n z‖ ∧ ‖u n z‖ ≤ 2)
    (hform : ∀ n z, z ∈ Metric.ball 0 (rr n) → f n z = z + z * (z - σ n) * u n z) :
    Filter.Tendsto (fun n => ‖α n‖) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ‖u n 0 - 1‖) Filter.atTop (nhds 0) := by
  -- the quantitative germ data
  obtain ⟨r₀, hr₀pos, _hr₀sub, C, hCpos, hsmall⟩ := Work.Pert.small_of_nearOn hd
  have hLpos : (0 : ℝ) < 16 * Real.pi / Ξ' := by positivity
  -- the fixed working radius
  set ρ : ℝ := min r₀ (16 * Real.pi / Ξ') with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hr₀pos hLpos
  have hρr₀ : ρ ≤ r₀ := by rw [hρdef]; exact min_le_left _ _
  have hρL : ρ ≤ 16 * Real.pi / Ξ' := by rw [hρdef]; exact min_le_right _ _
  -- the lower bound for `rr`
  set c : ℝ := 1 / (4 * (Ξ' + 1)) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcrr : ∀ n, c ≤ rr n := by intro n; rw [hcdef]; exact hrrlb n
  -- closeness on the smaller compact
  have hnear' : ∀ n, MandelDim.NearOn f₀ (f n) (Df n) (Metric.closedBall (0 : ℂ) ρ) (δ n) :=
    fun n => nearOn_mono (Metric.closedBall_subset_closedBall hρL) (hNear n)
  -- eventual smallness of `δ`
  have hδsmall : ∀ᶠ n in Filter.atTop, 2 * δ n ≤ ρ := by
    have hlt : ∀ᶠ n in Filter.atTop, δ n < ρ / 2 :=
      (tendsto_order.1 hδ0).2 (ρ / 2) (by linarith)
    filter_upwards [hlt] with n hn
    linarith
  -- the per-`n` quantitative bounds
  have hbound : ∀ n, 2 * δ n ≤ ρ →
      (‖u n 0 - 1‖ ≤ C * (δ n / ρ ^ 2 + δ n / (ρ * c))) ∧ (‖α n‖ ≤ C * δ n / ρ) := by
    intro n hn2
    obtain ⟨h1, _h2, h3⟩ :=
      hsmall (f := f n) (Df := Df n) (ρ := ρ) (δ₀ := δ n) (rr := rr n) (u := u n) (σ := σ n)
        hρpos hρr₀ (hδpos n) hn2 (hrrpos n) (hnear' n) (hf0 n) (hudiff n) (hubnd n) (hform n)
    refine ⟨?_, ?_⟩
    · refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hCpos.le)
      have hden : ρ * c ≤ ρ * rr n := mul_le_mul_of_nonneg_left (hcrr n) hρpos.le
      have hmono : δ n / (ρ * rr n) ≤ δ n / (ρ * c) :=
        div_le_div_of_nonneg_left (hδpos n).le (mul_pos hρpos hcpos) hden
      linarith
    · rw [hαeq n]; exact h3
  -- both comparison sequences tend to `0`
  have hCδ : Filter.Tendsto (fun n => C * δ n / ρ) Filter.atTop (nhds 0) := by
    have h := (hδ0.const_mul C).div_const ρ
    simpa using h
  have hCδ2 : Filter.Tendsto (fun n => C * (δ n / ρ ^ 2 + δ n / (ρ * c)))
      Filter.atTop (nhds 0) := by
    have h := ((hδ0.div_const (ρ ^ 2)).add (hδ0.div_const (ρ * c))).const_mul C
    simpa using h
  refine ⟨?_, ?_⟩
  · refine squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ hCδ
    filter_upwards [hδsmall] with n hn
    exact (hbound n hn).2
  · refine squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ hCδ2
    filter_upwards [hδsmall] with n hn
    exact (hbound n hn).1

end Work.PertCrux
