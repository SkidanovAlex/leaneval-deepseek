import Mathlib

namespace Work.FatouCH.Ends

open Set Metric Complex Filter
open scoped Topology

/-- A vertically parametrised function whose increments over `[T₁,T₂]` (`T₀ ≤ T₁ ≤ T₂`) are bounded
by a quantity `Ψ` that is decreasing on `(0,∞)` and tends to `0` has a limit at `+∞`, with the same
quantitative bound. -/
theorem endsVerticalLimit {B : ℂ → ℂ} {x K κ T₀ : ℝ} (hT₀ : 1 ≤ T₀)
    (hseg : ∀ T₂ T₁ : ℝ, T₀ ≤ T₁ → T₁ ≤ T₂ →
      ‖B (x + (T₂ : ℂ) * Complex.I) - B (x + (T₁ : ℂ) * Complex.I)‖ ≤
        2 * K / T₁ + 16 * K / κ * Real.exp (-(κ * T₁ / 8)))
    (hmono : AntitoneOn (fun T : ℝ => 2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)))
      (Set.Ioi 0))
    (hzero : Tendsto (fun T : ℝ => 2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)))
      atTop (𝓝 0)) :
    ∃ c : ℂ, Tendsto (fun T : ℝ => B (x + (T : ℂ) * Complex.I)) atTop (𝓝 c) ∧
      ∀ T : ℝ, T₀ ≤ T → ‖B (x + (T : ℂ) * Complex.I) - c‖ ≤
        2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)) := by
  have hT₀pos : 0 < T₀ := lt_of_lt_of_le zero_lt_one hT₀
  -- Step 1: arbitrarily far out, the increment bound is arbitrarily small.
  have hex : ∀ ε : ℝ, 0 < ε → ∃ T₁ : ℝ, T₀ ≤ T₁ ∧
      (2 * K / T₁ + 16 * K / κ * Real.exp (-(κ * T₁ / 8))) < ε := by
    intro ε hε
    have h1 : ∀ᶠ T : ℝ in atTop,
        2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)) < ε :=
      hzero.eventually (isOpen_Iio.mem_nhds hε)
    have h2 : ∀ᶠ T : ℝ in atTop, T₀ ≤ T := Ici_mem_atTop T₀
    obtain ⟨T₁, hg, hge⟩ := (h1.and h2).exists
    exact ⟨T₁, hge, hg⟩
  -- Step 2: the vertical parametrisation is a Cauchy filter.
  have hCauchy : Cauchy (map (fun T : ℝ => B (x + (T : ℂ) * Complex.I)) atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨T₁, hT₁ge, hT₁lt⟩ := hex ε hε
    have hT₁pos : 0 < T₁ := lt_of_lt_of_le hT₀pos hT₁ge
    refine ⟨(fun T : ℝ => B (x + (T : ℂ) * Complex.I)) '' Set.Ici T₁, ?_, ?_⟩
    · rw [Filter.mem_map]
      filter_upwards [Ici_mem_atTop T₁] with T hT
      exact ⟨T, hT, rfl⟩
    · rintro u ⟨a, ha, rfl⟩ v ⟨b, hb, rfl⟩
      rw [dist_eq_norm]
      rcases le_total a b with hab | hba
      · have h1 := hseg b a (le_trans hT₁ge ha) hab
        have h2 : 2 * K / a + 16 * K / κ * Real.exp (-(κ * a / 8)) ≤
            2 * K / T₁ + 16 * K / κ * Real.exp (-(κ * T₁ / 8)) :=
          hmono (Set.mem_Ioi.mpr hT₁pos)
            (Set.mem_Ioi.mpr (lt_of_lt_of_le hT₁pos ha)) ha
        rw [norm_sub_rev]
        exact lt_of_le_of_lt (le_trans h1 h2) hT₁lt
      · have h1 := hseg a b (le_trans hT₁ge hb) hba
        have h2 : 2 * K / b + 16 * K / κ * Real.exp (-(κ * b / 8)) ≤
            2 * K / T₁ + 16 * K / κ * Real.exp (-(κ * T₁ / 8)) :=
          hmono (Set.mem_Ioi.mpr hT₁pos)
            (Set.mem_Ioi.mpr (lt_of_lt_of_le hT₁pos hb)) hb
        exact lt_of_le_of_lt (le_trans h1 h2) hT₁lt
  -- Step 3: completeness of `ℂ` yields the limit and the quantitative bound.
  obtain ⟨c, hc⟩ := CompleteSpace.complete hCauchy
  refine ⟨c, hc, ?_⟩
  intro T hT
  have hcont : Tendsto
      (fun T' : ℝ => dist (B (x + (T : ℂ) * Complex.I)) (B (x + (T' : ℂ) * Complex.I)))
      atTop (𝓝 (dist (B (x + (T : ℂ) * Complex.I)) c)) :=
    tendsto_const_nhds.dist hc
  have hev : ∀ᶠ T' : ℝ in atTop,
      dist (B (x + (T : ℂ) * Complex.I)) (B (x + (T' : ℂ) * Complex.I)) ≤
        2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)) := by
    filter_upwards [Ici_mem_atTop T] with T' hT'
    rw [dist_eq_norm, norm_sub_rev]
    exact hseg T' T hT hT'
  have hle : dist (B (x + (T : ℂ) * Complex.I)) c ≤
      2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)) := le_of_tendsto hcont hev
  rwa [dist_eq_norm] at hle

end Work.FatouCH.Ends
