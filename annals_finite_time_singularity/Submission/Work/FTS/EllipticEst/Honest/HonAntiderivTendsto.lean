import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real
open Filter

/-- If `|f| ≤ c` eventually along `l` and `c → 0`, then `f → 0`. -/
private lemma honZeroOfAbsLe {f c : ℝ → ℝ} {l : Filter ℝ}
    (hfc : ∀ᶠ s in l, |f s| ≤ c s) (hc : Filter.Tendsto c l (nhds 0)) :
    Filter.Tendsto f l (nhds 0) :=
  squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hfc) hc

/-- **The primitives of the solution vanish at the two endpoints of `(0, π/2)`.**

Near `0⁺` the first summand `-u' u` is bounded by `M |u| → 0` (the derivative is bounded
along the interval, `u → 0`), while the `tan`-weighted summand is a product of two
quantities with limit `0` (`tan θ → 0` and `u → 0`).

Near `π/2⁻` the first summand is bounded by `M |u| → 0` as before, and the `tan`-weighted one
is *not* estimated by `tan θ → 0` (which is false here): instead we use the hypothesis
`|u θ / cos θ| ≤ K` to the effect that `u = O(cos θ)`, and write

`½ tan θ · u² = ½ sin θ · (u / cos θ) · u`,

whose absolute value is at most `½ K |u θ| → 0`, since `|sin| ≤ 1`. -/
theorem HonAntiderivTendsto (u : ℝ → ℝ) {M K : ℝ} (hM0 : 0 ≤ M) (hK0 : 0 ≤ K)
    (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M)
    (hMu : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * θ)
    (hK : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ / Real.cos θ| ≤ K)
    (h0t : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hπt : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    Filter.Tendsto (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi : (0:ℝ) < Real.pi / 2 := by positivity
  -- eventually the variable is in the interior interval, at both endpoints
  have hiv0 : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), s ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (a := Real.pi / 2) (b := (0:ℝ)) hpi)]
      with s hs0 hslt
    exact ⟨hs0, hslt⟩
  have hivπ : ∀ᶠ s in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      s ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds (a := (0:ℝ)) (b := Real.pi / 2) hpi)]
      with s hslt hs0
    exact ⟨hs0, hslt⟩
  -- the `-u' u` summand at `0⁺`
  have hder0 : Filter.Tendsto (fun s => -(deriv u s) * u s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine honZeroOfAbsLe (c := fun s => M * |u s|) ?_ ?_
    · filter_upwards [hiv0] with s hs
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (hM s hs) (abs_nonneg _)
    · simpa using h0t.abs.const_mul M
  -- the `½ tan · u²` summand at `0⁺`: a product of two limits
  have htan0 : Filter.Tendsto (fun s => (1 / 2) * Real.tan s * (u s) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have htan : Filter.Tendsto Real.tan (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt Real.tan 0 :=
        Real.continuousAt_tan.mpr (by rw [Real.cos_zero]; norm_num)
      have h := hc.tendsto
      rw [Real.tan_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hsq : Filter.Tendsto (fun s => (u s) ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using h0t.pow 2
    simpa only [mul_zero, zero_mul] using (htan.const_mul (1 / 2)).mul hsq
  -- the `-u' u` summand at `π/2⁻`
  have hderπ : Filter.Tendsto (fun s => -(deriv u s) * u s)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine honZeroOfAbsLe (c := fun s => M * |u s|) ?_ ?_
    · filter_upwards [hivπ] with s hs
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (hM s hs) (abs_nonneg _)
    · simpa using hπt.abs.const_mul M
  -- the `½ tan · u²` summand at `π/2⁻`: `u = O(cos θ)` absorbs the singularity of `tan`
  have htanπ : Filter.Tendsto (fun s => (1 / 2) * Real.tan s * (u s) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine honZeroOfAbsLe (c := fun s => (1 / 2) * K * |u s|) ?_ ?_
    · filter_upwards [hivπ] with s hs
      have hsin : |Real.sin s| ≤ 1 := Real.abs_sin_le_one s
      have hKs : |u s / Real.cos s| ≤ K := hK s hs
      have hkey : (1 / 2 : ℝ) * (Real.sin s / Real.cos s) * (u s) ^ 2
          = (1 / 2 : ℝ) * Real.sin s * (u s / Real.cos s) * u s := by ring
      rw [Real.tan_eq_sin_div_cos, hkey]
      simp only [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
      have h1 : (1 / 2 : ℝ) * |Real.sin s| ≤ (1 / 2 : ℝ) * 1 := by nlinarith [hsin]
      calc (1 / 2 : ℝ) * |Real.sin s| * |u s / Real.cos s| * |u s|
          ≤ ((1 / 2 : ℝ) * 1 * K) * |u s| := by
            apply mul_le_mul
            · exact mul_le_mul h1 hKs (abs_nonneg _) (by norm_num)
            · exact le_rfl
            · exact abs_nonneg _
            · linarith
        _ = (1 / 2 : ℝ) * K * |u s| := by ring
    · simpa using hπt.abs.const_mul (1 / 2 * K)
  exact ⟨by simpa only [add_zero] using hder0.add htan0,
    by simpa only [add_zero] using hderπ.add htanπ⟩

end Work.FTS.EllipticEst.Honest
