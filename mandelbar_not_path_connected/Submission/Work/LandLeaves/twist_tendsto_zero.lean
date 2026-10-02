import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology

/-- For a unit vector `a` and a small perturbation `w` (with `‖w‖ ≤ 1/2`), the direction
`(a + w)/‖a + w‖` differs from `a` by at most `4‖w‖`. -/
lemma norm_div_norm_sub_le {a w : ℂ} (ha : ‖a‖ = 1) (hw : ‖w‖ ≤ 1/2) :
    ‖(a + w) / ‖a + w‖ - a‖ ≤ 4 * ‖w‖ := by
  have hnorm : (1:ℝ) / 2 ≤ ‖a + w‖ := by
    have h1 : ‖a‖ ≤ ‖a + w‖ + ‖w‖ := by
      calc ‖a‖ = ‖(a + w) - w‖ := by congr 1; ring
        _ ≤ ‖a + w‖ + ‖w‖ := norm_sub_le _ _
    linarith
  have hpos : (0:ℝ) < ‖a + w‖ := by linarith
  have hne : (‖a + w‖ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  have hnum : ‖(a + w) - (‖a + w‖ : ℂ) * a‖ ≤ 2 * ‖w‖ := by
    have h2 : (a + w) - (‖a + w‖ : ℂ) * a = w - a * ((‖a + w‖ : ℂ) - 1) := by ring
    rw [h2]
    calc ‖w - a * ((‖a + w‖ : ℂ) - 1)‖
        ≤ ‖w‖ + ‖a * ((‖a + w‖ : ℂ) - 1)‖ := norm_sub_le _ _
      _ = ‖w‖ + ‖a‖ * ‖(‖a + w‖ : ℂ) - 1‖ := by rw [norm_mul]
      _ = ‖w‖ + ‖(‖a + w‖ : ℂ) - 1‖ := by rw [ha, one_mul]
      _ = ‖w‖ + |‖a + w‖ - 1| := by
            congr 1
            rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖w‖ + ‖w‖ := by
            have h3 : |‖a + w‖ - 1| ≤ ‖w‖ := by
              have h4 := abs_norm_sub_norm_le a (a + w)
              rw [ha, show a - (a + w) = -w by ring, norm_neg] at h4
              rwa [abs_sub_comm] at h4
            linarith
      _ = 2 * ‖w‖ := by ring
  have hmain : ‖(a + w) / ‖a + w‖ - a‖ = ‖(a + w) - (‖a + w‖ : ℂ) * a‖ / ‖a + w‖ := by
    rw [div_sub' hne, norm_div]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hmain]
  calc ‖(a + w) - (‖a + w‖ : ℂ) * a‖ / ‖a + w‖
      ≤ (2 * ‖w‖) / ‖a + w‖ := div_le_div_of_nonneg_right hnum (le_of_lt hpos)
    _ ≤ (2 * ‖w‖) / ((1:ℝ)/2) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hnorm
    _ = 4 * ‖w‖ := by ring

/-- If `F z = lam * z + o(z)` at `0` with `‖lam‖ = 1`, then the direction of `F z` is asymptotic to
the direction of `lam * z`: this is the "twist" of the direction under the dynamics.
Hints: `F z = ‖z‖ • (lam * (z/‖z‖) + w)` with `‖w‖ = ‖F z - lam z‖/‖z‖ → 0`; for a unit vector `a`
one has `‖(a+w)/‖a+w‖ - a‖ ≤ 4‖w‖` for `‖w‖ ≤ 1/2`; also `F z ≠ 0` for `0 < ‖z‖ < r` (else
`‖z‖ = ‖F z - lam * z‖ = o(‖z‖)`), so the junk value `0 / 0` is never used. -/
theorem twist_tendsto_zero {F : ℂ → ℂ} {lam : ℂ} (hlam : ‖lam‖ = 1)
    (h : (fun z : ℂ => F z - lam * z) =o[𝓝 0] (fun z : ℂ => z)) :
    Filter.Tendsto (fun z : ℂ => F z / ‖F z‖ - lam * (z / ‖z‖)) (𝓝[≠] 0) (𝓝 0) := by
  set w : ℂ → ℂ := fun z => (F z - lam * z) / (‖z‖ : ℂ) with hwdef
  have hw_t : Tendsto (fun z => ‖w z‖) (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun z => ‖(F z - lam * z) / z‖) (𝓝[≠] 0) (𝓝 0) := by
      simpa using (h.tendsto_div_nhds_zero.norm).mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards with z
    simp only [hwdef]
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  have hF : ∀ᶠ z in 𝓝[≠] 0, F z ≠ 0 := by
    have hhalf : ∀ᶠ z in 𝓝[≠] 0, ‖F z - lam * z‖ ≤ (1/2) * ‖z‖ :=
      (h.def (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hhalf, self_mem_nhdsWithin] with z hz hz0
    intro hzF
    rw [hzF] at hz
    have hthis : ‖0 - lam * z‖ = ‖z‖ := by
      rw [zero_sub, norm_neg, norm_mul, hlam, one_mul]
    rw [hthis] at hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    linarith
  have hbound : ∀ᶠ z in 𝓝[≠] 0,
      ‖F z / ‖F z‖ - lam * (z / ‖z‖)‖ ≤ 4 * ‖w z‖ := by
    have hwsmall : ∀ᶠ z in 𝓝[≠] 0, ‖w z‖ ≤ 1/2 :=
      (hw_t.eventually (isOpen_Iio.mem_nhds (by norm_num : (0:ℝ) < 1/2))).mono
        (fun z hz => le_of_lt hz)
    filter_upwards [hF, self_mem_nhdsWithin, hwsmall] with z hzF hz0 hwle
    have hc : (‖z‖ : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hz0
    have ha : ‖lam * (z / ‖z‖)‖ = 1 := by
      rw [norm_mul, hlam, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz0)]
    have hFz : F z = (‖z‖ : ℂ) * (lam * (z / ‖z‖) + w z) := by
      simp only [hwdef]
      field_simp
      ring
    have hnormF : ‖F z‖ = ‖z‖ * ‖lam * (z / ‖z‖) + w z‖ := by
      rw [hFz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    have hdiv : F z / ‖F z‖ = (lam * (z / ‖z‖) + w z) / ‖lam * (z / ‖z‖) + w z‖ := by
      rw [hnormF, hFz, Complex.ofReal_mul, mul_div_mul_left _ _ hc]
    rw [hdiv]
    exact norm_div_norm_sub_le ha hwle
  have hlim : Tendsto (fun z => 4 * ‖w z‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hw_t.const_mul 4
  have hgn : Tendsto (fun z => ‖F z / ‖F z‖ - lam * (z / ‖z‖)‖) (𝓝[≠] 0) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun z => norm_nonneg _)) hbound hlim
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hgn

end Work.LandLeaves
