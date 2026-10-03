import Mathlib

namespace Work.KMTAreas.A5

open Filter Asymptotics
open scoped Topology

/-- Ultraviolet cut-off for the elementary growth comparison of §5 of Krause--Mirek--Tao:
below the linear growth `x ↦ x`, both a sublinear power `(x+2)^s` (`s < 1`) and a logarithm
`logb 2 (x+2)` are eventually negligible.  Concretely, for every `s < 1` and every `c d : ℝ`
there is `x₀` with `c (x+2)^s + d logb 2 (x+2) + 1 ≤ x` for all `x ≥ x₀`.

The proof bounds each of the two terms by `(x+2)/4` eventually (using
`tendsto_rpow_neg_atTop` for the power, and `isLittleO_log_rpow_atTop` for the logarithm) and
then compares with the linear term on the range `x + 2 ≥ 8`. -/
theorem pow_log_eventually_le {s : ℝ} (hs : s < 1) (c d : ℝ) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      c * (x + 2) ^ s + d * Real.logb 2 (x + 2) + 1 ≤ x := by
  -- the power term is eventually at most `t / 4`
  have h1 : ∀ᶠ t : ℝ in atTop, c * t ^ s ≤ t / 4 := by
    have hbase : Tendsto (fun t : ℝ => t ^ (-(1 - s))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have hc : Tendsto (fun t : ℝ => c * t ^ (-(1 - s))) atTop (𝓝 0) := by
      simpa using hbase.const_mul c
    have hpt : ∀ t : ℝ, 0 < t → c * t ^ s / t = c * t ^ (-(1 - s)) := by
      intro t ht
      have h2 : t ^ s / t = t ^ (-(1 - s)) := by
        have h := Real.rpow_sub ht s 1
        rw [Real.rpow_one] at h
        rw [← h]
        congr 1
        ring
      calc c * t ^ s / t = c * (t ^ s / t) := by ring
        _ = c * t ^ (-(1 - s)) := by rw [h2]
    have hcc : Tendsto (fun t : ℝ => c * t ^ s / t) atTop (𝓝 0) :=
      hc.congr' ((Filter.eventually_gt_atTop (0 : ℝ)).mono fun t ht => (hpt t ht).symm)
    have hlt : ∀ᶠ t : ℝ in atTop, c * t ^ s / t < 1 / 4 :=
      hcc.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    filter_upwards [hlt, Filter.eventually_gt_atTop (0 : ℝ)] with t ht hpos
    have := (div_le_iff₀ hpos).mp (le_of_lt ht)
    linarith
  -- the logarithmic term is eventually at most `t / 4`
  have h2 : ∀ᶠ t : ℝ in atTop, d * Real.logb 2 t ≤ t / 4 := by
    have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
      have h := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).tendsto_div_nhds_zero
      simpa [Real.rpow_one] using h
    have hlogb : Tendsto (fun t : ℝ => Real.logb 2 t / t) atTop (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => (1 / Real.log 2) * (Real.log t / t)) atTop (𝓝 0) := by
        simpa using hlog.const_mul (1 / Real.log 2)
      refine h.congr' ?_
      refine Eventually.of_forall fun t => ?_
      simp only [Real.logb]
      field_simp
    have hd : Tendsto (fun t : ℝ => d * Real.logb 2 t / t) atTop (𝓝 0) := by
      have h := hlogb.const_mul d
      simpa [mul_div_assoc] using h
    have hlt : ∀ᶠ t : ℝ in atTop, d * Real.logb 2 t / t < 1 / 4 :=
      hd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    filter_upwards [hlt, Filter.eventually_gt_atTop (0 : ℝ)] with t ht hpos
    have := (div_le_iff₀ hpos).mp (le_of_lt ht)
    linarith
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp
    (h1.and (h2.and (Filter.eventually_ge_atTop (8 : ℝ))))
  refine ⟨t₀ - 2, ?_⟩
  intro x hx
  obtain ⟨ha, hb, hc8⟩ := ht₀ (x + 2) (by linarith)
  have h3 : c * (x + 2) ^ s + d * Real.logb 2 (x + 2) + 1 ≤
      (x + 2) / 4 + (x + 2) / 4 + (x + 2) / 4 := by linarith
  have h4 : (x + 2) / 4 + (x + 2) / 4 + (x + 2) / 4 ≤ x := by linarith
  linarith

end Work.KMTAreas.A5
