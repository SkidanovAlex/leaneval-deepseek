import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.coerc.not_integrableOn_of_le_div_sub_pow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.SliceA

open MeasureTheory Set Filter
open scoped Real Topology

/-!
## Non-integrability of `sin θ · cos²θ · |g θ|` at the right endpoint `θ = π/2`

For `N ≥ 2` and `c ≠ 0`, if `θ ↦ (π/2 - θ)^(N+2) · g θ` tends to `c` as `θ → (π/2)⁻`, then
`g` blows up like `c · (π/2 - θ)^{-(N+2)}` near `π/2`.  Since `sin θ → 1` and
`cos²θ = sin²(π/2 - θ) ~ (π/2 - θ)²` there, the integrand behaves like
`|c| · (π/2 - θ)^{-N}`, whose integral diverges at `π/2` for `N ≥ 1`.  Hence it is not
integrable on `Iθ = [0, π/2]`.

The quantitative pointwise bound used below is, for `θ ∈ (π/2 - δ, π/2)`,

`sin θ · cos²θ · |g θ| ≥ (|c| / π²) / (π/2 - θ)^N`,

obtained from `sin θ ≥ 1/2` (for `θ ∈ (π/2 - 1, π/2)`),
`cos²θ ≥ (4/π²)(π/2 - θ)²` (`cos θ = sin(π/2 - θ) ≥ (2/π)(π/2 - θ)`) and
`|g θ| ≥ (|c|/2) / (π/2 - θ)^(N+2)` (from the limit).  The divergence is then supplied by
`Work.FTS.EllipticEst.remov.coerc.not_integrableOn_of_le_div_sub_pow`.
-/

/-- `1/2 ≤ sin θ` for `θ` in the (right) half of the interval `(π/6, π/2]`. -/
private lemma sin_ge_half_of_mem {θ : ℝ} (h1 : Real.pi / 2 - 1 < θ) (h2 : θ ≤ Real.pi / 2) :
    (1 : ℝ) / 2 ≤ Real.sin θ := by
  have h3 : Real.pi / 6 ≤ θ := by have := Real.pi_gt_three; linarith
  have h4 : Real.sin (Real.pi / 6) ≤ Real.sin θ :=
    Real.strictMonoOn_sin.monotoneOn (by constructor <;> linarith [Real.pi_pos])
      (by constructor <;> linarith [Real.pi_pos]) h3
  rw [Real.sin_pi_div_six] at h4
  linarith

/-- The quadratic lower bound `cos²θ ≥ (4/π²)(π/2 - θ)²` on `(0, π/2)`. -/
private lemma cos_sq_ge (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (4 / Real.pi ^ 2) * (Real.pi / 2 - θ) ^ 2 ≤ Real.cos θ ^ 2 := by
  set a := Real.pi / 2 - θ with ha
  have ha0 : 0 ≤ a := by simp only [ha]; linarith [hθ.2]
  have ha1 : a ≤ Real.pi / 2 := by simp only [ha]; linarith [hθ.1]
  have hcos : Real.cos θ = Real.sin a := by
    rw [ha]; exact (Real.sin_pi_div_two_sub θ).symm
  rw [hcos]
  have hlow : 2 / Real.pi * a ≤ Real.sin a := Real.mul_le_sin ha0 ha1
  have hnn : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_pos])
  have hnonneg : 0 ≤ 2 / Real.pi * a := mul_nonneg (by positivity) ha0
  have hsq : (2 / Real.pi * a) ^ 2 ≤ (Real.sin a) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hnonneg, abs_of_nonneg hnn]
    exact hlow
  calc (4 / Real.pi ^ 2) * a ^ 2 = (2 / Real.pi * a) ^ 2 := by ring
    _ ≤ Real.sin a ^ 2 := hsq

theorem not_integrableOn_sinCos2_of_tendsto : ∀ (N : ℕ) (g : ℝ → ℝ) (c : ℝ), 2 ≤ N → c ≠ 0 →
    Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * g θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) →
    ¬ MeasureTheory.IntegrableOn
        (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * |g θ|) Work.Spaces.Iθ := by
  intro N g c hN hc htend hInt
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hbpos : (0 : ℝ) < Real.pi / 2 := by positivity
  -- The limit hypothesis, in absolute value and with the power unravelled.
  have hev_abs : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |c| / 2 < |(Real.pi / 2 - θ) ^ (N + 2) * g θ| :=
    (htend.abs).eventually (Ioi_mem_nhds (by linarith))
  have hev : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |c| / 2 < (Real.pi / 2 - θ) ^ (N + 2) * |g θ| := by
    filter_upwards [hev_abs, self_mem_nhdsWithin] with θ h1 h2
    have h2' : θ < Real.pi / 2 := h2
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ Real.pi / 2 - θ) _)] at h1
    exact h1
  -- Extract a one-sided neighbourhood on which it holds.
  obtain ⟨s, hs, hsP⟩ := Filter.eventually_iff_exists_mem.mp hev
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.mem_nhdsWithin_iff.mp hs
  set δ := min ε₀ (min 1 (Real.pi / 2)) with hδdef
  have hδpos : 0 < δ := lt_min hε₀pos (lt_min one_pos hbpos)
  have hδle₀ : δ ≤ ε₀ := min_le_left _ _
  have hδle1 : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδleb : δ ≤ Real.pi / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- The quantitative pointwise lower bound.
  have hkey : ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
      (|c| / Real.pi ^ 2) / (Real.pi / 2 - θ) ^ N
        ≤ Real.sin θ * Real.cos θ ^ 2 * |g θ| := by
    intro θ hθ
    have hθlt : θ < Real.pi / 2 := hθ.2
    have hθpos : 0 < θ := by linarith [hθ.1, hδleb, Real.pi_pos]
    have ha0 : 0 < Real.pi / 2 - θ := by linarith
    have haε : Real.pi / 2 - θ < ε₀ := by linarith [hθ.1, hδle₀]
    have ha1 : Real.pi / 2 - θ < 1 := by linarith [hθ.1, hδle1]
    have hmem : θ ∈ s := by
      apply hε₀sub
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      · exact hθ.2
    have hPa : |c| / 2 < (Real.pi / 2 - θ) ^ (N + 2) * |g θ| := hsP θ hmem
    -- `|g θ| ≥ (|c|/2) / (π/2 - θ)^(N+2)`, hence `(|c|/2)/(π/2 - θ)^N ≤ (π/2 - θ)²|g θ|`.
    have hg : (|c| / 2) / (Real.pi / 2 - θ) ^ N ≤ (Real.pi / 2 - θ) ^ 2 * |g θ| := by
      rw [div_le_iff₀ (pow_pos ha0 N)]
      rw [pow_add] at hPa
      exact le_of_lt (hPa.trans_eq (by ring))
    have hsin : (1 : ℝ) / 2 ≤ Real.sin θ :=
      sin_ge_half_of_mem (by linarith [hθ.1, hδle1]) (le_of_lt hθlt)
    have hcos : (4 / Real.pi ^ 2) * (Real.pi / 2 - θ) ^ 2 ≤ Real.cos θ ^ 2 :=
      cos_sq_ge θ ⟨hθpos, hθlt⟩
    calc (|c| / Real.pi ^ 2) / (Real.pi / 2 - θ) ^ N
        = (2 / Real.pi ^ 2) * ((|c| / 2) / (Real.pi / 2 - θ) ^ N) := by ring
      _ ≤ (2 / Real.pi ^ 2) * ((Real.pi / 2 - θ) ^ 2 * |g θ|) :=
            mul_le_mul_of_nonneg_left hg (by positivity)
      _ = (1 / 2) * ((4 / Real.pi ^ 2) * (Real.pi / 2 - θ) ^ 2) * |g θ| := by ring
      _ ≤ (1 / 2) * Real.cos θ ^ 2 * |g θ| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcos (by norm_num)) (abs_nonneg (g θ))
      _ ≤ Real.sin θ * Real.cos θ ^ 2 * |g θ| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsin (sq_nonneg (Real.cos θ))) (abs_nonneg (g θ))
  -- The interval of the lower bound sits inside `Iθ`.
  have hsub : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    change θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
    exact ⟨by linarith [hθ.1, hδleb, Real.pi_pos], le_of_lt hθ.2⟩
  have hnot := Work.FTS.EllipticEst.remov.coerc.not_integrableOn_of_le_div_sub_pow
    (f := fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * |g θ|)
    (c := |c| / Real.pi ^ 2) (b := Real.pi / 2) (ε := δ) (k := N)
    (div_pos hcpos (pow_pos Real.pi_pos 2)) hδpos hN hkey
  exact hnot (hInt.mono_set hsub)

end Work.FTS.EllipticEst.H2W.SliceA
