/-
Copyright: work module for the Elgindi finite-time singularity project.

`Work.FTS.StrongEps.EpsE4Thr.tendsto_slope_interval_integral`

If `R σ → c` as `σ → τ` and `R` is (a.e.) measurable, then the mean of `R` over `[τ, s]`
converges to `c` as `s → τ`, `s ≠ τ`:

  `(s - τ)⁻¹ * ∫ σ in τ..s, R σ → c`.

This is the "derivative of the primitive at a point" statement with the *limit* hypothesis
`Tendsto R (𝓝 τ) (𝓝 c)` instead of continuity of `R` on a neighbourhood. It is proved by the
elementary `ε`-`δ` argument: for `σ` in `uIoc τ s` (with `|s - τ|` small) one has
`|σ - τ| ≤ |s - τ|`, so `|R σ - c| < ε/2`; the bound
`‖∫ σ in τ..s, (R σ - c)‖ ≤ (ε/2) * |s - τ|` then gives
`|(s - τ)⁻¹ * ∫ σ in τ..s, R σ - c| ≤ ε/2 < ε`. The only measure-theoretic input is that a
measurable function which is bounded near `τ` is interval-integrable there, which is needed to
split `∫ (R - c) = ∫ R - (s - τ) * c`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter Set
open scoped Topology

namespace Work.FTS.StrongEps.EpsE4Thr

theorem tendsto_slope_interval_integral {R : ℝ → ℝ} {τ c : ℝ}
    (hR : Filter.Tendsto R (nhds τ) (nhds c))
    (hm : AEMeasurable R MeasureTheory.volume) :
    Filter.Tendsto (fun s : ℝ => (s - τ)⁻¹ * ∫ σ in τ..s, R σ) (nhdsWithin τ {τ}ᶜ) (nhds c) := by
  -- `R` is bounded on a neighbourhood of `τ`.
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ σ, |σ - τ| < δ₁ → |R σ| ≤ |c| + 1 := by
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp ((Metric.tendsto_nhds.mp hR) 1 one_pos)
    refine ⟨δ₁, hδ₁pos, fun σ hσ => ?_⟩
    have h : dist (R σ) c < 1 := hδ₁ (y := σ) hσ
    rw [Real.dist_eq] at h
    calc |R σ| = |(R σ - c) + c| := by rw [sub_add_cancel]
      _ ≤ |R σ - c| + |c| := abs_add_le _ _
      _ ≤ 1 + |c| := by linarith
      _ = |c| + 1 := by ring
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  -- the `ε/2`-closeness of `R` to `c` near `τ`
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ σ, |σ - τ| < δ₂ → |R σ - c| < ε / 2 := by
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
      Metric.eventually_nhds_iff.mp ((Metric.tendsto_nhds.mp hR) (ε / 2) hε2)
    exact ⟨δ₂, hδ₂pos, fun σ hσ => by simpa [Real.dist_eq] using hδ₂ (y := σ) hσ⟩
  set δ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
  have hδ_le₁ : δ ≤ δ₁ := min_le_left _ _
  have hδ_le₂ : δ ≤ δ₂ := min_le_right _ _
  -- integrability of `R` near `τ`, from boundedness + measurability
  have hmeas : AEStronglyMeasurable R (volume.restrict (Icc (τ - δ / 2) (τ + δ / 2))) :=
    (hm.restrict).aestronglyMeasurable
  have hvol : volume (Icc (τ - δ / 2) (τ + δ / 2)) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hIntOn : IntegrableOn R (Icc (τ - δ / 2) (τ + δ / 2)) volume := by
    refine IntegrableOn.of_bound hvol hmeas (|c| + 1) ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall (fun σ hσ => ?_)
    have h1 : |σ - τ| ≤ δ / 2 := by
      rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
    exact hδ₁ σ (by linarith)
  have hII : IntervalIntegrable R volume (τ - δ / 2) (τ + δ / 2) := by
    refine intervalIntegrable_iff.mpr (hIntOn.mono_set ?_)
    rw [← uIcc_of_le (by linarith : τ - δ / 2 ≤ τ + δ / 2)]
    exact uIoc_subset_uIcc
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨δ / 2, by linarith, ?_⟩
  intro s hs hsne
  rw [Real.dist_eq] at hs
  have hsτ : s ≠ τ := by simpa using hsne
  have hsτne : s - τ ≠ 0 := sub_ne_zero.mpr hsτ
  have hs1 : -(δ / 2) < s - τ := (abs_lt.mp hs).1
  have hs2 : s - τ < δ / 2 := (abs_lt.mp hs).2
  -- `R` is interval integrable on `τ..s`
  have hsub : Set.uIcc τ s ⊆ Set.uIcc (τ - δ / 2) (τ + δ / 2) := by
    rw [uIcc_subset_uIcc_iff_le, min_eq_left (by linarith : τ - δ / 2 ≤ τ + δ / 2),
      max_eq_right (by linarith : τ - δ / 2 ≤ τ + δ / 2)]
    exact ⟨le_min (by linarith : τ - δ / 2 ≤ τ) (by linarith [hs1] : τ - δ / 2 ≤ s),
      max_le (by linarith : τ ≤ τ + δ / 2) (by linarith [hs2] : s ≤ τ + δ / 2)⟩
  have hIIs : IntervalIntegrable R volume τ s := hII.mono_set hsub
  -- split off the constant: `∫ (R - c) = ∫ R - (s - τ) * c`
  have hkey : ∫ σ in τ..s, (R σ - c) = (∫ σ in τ..s, R σ) - (s - τ) * c := by
    rw [intervalIntegral.integral_sub hIIs intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have hrewrite : ((s - τ)⁻¹ * ∫ σ in τ..s, R σ) - c
      = (s - τ)⁻¹ * ∫ σ in τ..s, (R σ - c) := by
    rw [hkey, mul_sub, ← mul_assoc, inv_mul_cancel₀ hsτne, one_mul]
  -- the mean of `R - c` is small
  have hbound : |∫ σ in τ..s, (R σ - c)| ≤ (ε / 2) * |s - τ| := by
    have h4 : ‖∫ σ in τ..s, (R σ - c)‖ ≤ (ε / 2) * |s - τ| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun σ hσ => ?_)
      have hmem : σ ∈ Set.uIcc τ s := uIoc_subset_uIcc hσ
      have h1 : |σ - τ| ≤ |s - τ| := abs_sub_left_of_mem_uIcc hmem
      have h2 : |σ - τ| < δ₂ := by linarith [hδpos, hδ_le₂]
      have h3 : |R σ - c| < ε / 2 := hδ₂ σ h2
      simpa [Real.norm_eq_abs] using h3.le
    simpa [Real.norm_eq_abs] using h4
  calc dist ((s - τ)⁻¹ * ∫ σ in τ..s, R σ) c
      = |((s - τ)⁻¹ * ∫ σ in τ..s, R σ) - c| := by rw [Real.dist_eq]
    _ = |(s - τ)⁻¹ * ∫ σ in τ..s, (R σ - c)| := by rw [hrewrite]
    _ = |(s - τ)⁻¹| * |∫ σ in τ..s, (R σ - c)| := by rw [abs_mul]
    _ ≤ |(s - τ)⁻¹| * ((ε / 2) * |s - τ|) :=
        mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = ε / 2 := by
        have hne : |s - τ| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hsτ)
        rw [abs_inv, mul_comm (ε / 2) |s - τ|, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ < ε := by linarith

end Work.FTS.StrongEps.EpsE4Thr
