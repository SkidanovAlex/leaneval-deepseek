import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

set_option maxHeartbeats 800000

/-- Pointwise bound of the `L₁₂`-density of `F_* + u` on `(0,∞)`, from a weighted bound of `u`.

PROOF RECIPE.  `L12dens (F_*+u) s = ∫ θ in Iθ, Ktheta θ * ((F_* s θ + u s θ)/s)`; bound the
norm of the integral by the integral of the norm
(`MeasureTheory.norm_integral_le_integral_norm`, unconditional), then bound the integrand a.e. in
`θ` (`0 < θ < π/2`, the two endpoints of `Iθ` being null) by the constant
`3*(20/(1+s)² + Cw*(s^{1/2}/(1+s)²))` and use
`MeasureTheory.integral_mono_of_nonneg` against `MeasureTheory.integrable_const` (no
integrability/measurability hypothesis on the integrand is needed, and there is NO need to split
`L12dens (F_*+u)` into its two summands).  Ingredients:
* `|Ktheta θ| ≤ 3` (`Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three`);
* `|Fstar α s θ| ≤ 10 * |FM.Fstar s|` for `θ ∈ Iθ`, i.e. `≤ 20*s/(1+s)²`: unfold
  `Construction.Fstar α s θ = α*(Work.Spaces.Gam α θ / Work.Spaces.c α)*FM.Fstar s`,
  use `Work.Spaces.Gam_bounds` (`0 ≤ Γ ≤ 1`) and `Work.Spaces.c_bounds` (`1/10 ≤ c`), so
  `|α*(Γ/c)| ≤ 10*α ≤ 10` for `0 < α ≤ 1`;
* `s^{3/2}/(1+s)²/s = s^{1/2}/(1+s)²` for `s > 0` (`Real.rpow_sub`, cf. `L12Iter.Rwt_div`);
* `∫ θ in Iθ, c = c*(π/2)`, as in the proved `Work.FTS_RegExport.RXT.L12Iter.abs_Qang_zero_le`
  (`Work.Elliptic.integral_Iθ_eq_interval` + `intervalIntegral.integral_const`). -/
theorem abs_L12dens_Fstar_add_le {α Cw : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCw : 0 ≤ Cw)
    {u : ℝ → ℝ → ℝ}
    (hu : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |u z θ| ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + u z θ) s|
      ≤ 3 * (Real.pi / 2)
          * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
  set C0 : ℝ := 3 * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) with hC0def
  have hden : (0 : ℝ) < (1 + s) ^ 2 := by positivity
  have hC0nn : 0 ≤ C0 := by
    rw [hC0def]
    have h1 : 0 ≤ 20 / (1 + s) ^ 2 := div_nonneg (by norm_num) hden.le
    have h2 : 0 ≤ Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) :=
      mul_nonneg hCw (div_nonneg (Real.rpow_nonneg hs.le _) hden.le)
    nlinarith [Real.pi_pos]
  have hvol_lt : MeasureTheory.volume (Set.Icc (0:ℝ) (Real.pi / 2)) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hvol : MeasureTheory.volume.real (Set.Icc (0:ℝ) (Real.pi / 2)) = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  -- `K` vanishes at the two endpoints of `Iθ`, where `hu` does not apply
  have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K]; norm_num
  have hKpi : Work.Spaces.K (Real.pi / 2) = 0 := by
    rw [Work.Spaces.K, Real.cos_pi_div_two]; norm_num
  have hKab : ∀ θ, |Work.Spaces.K θ| ≤ 3 := fun θ =>
    (by simpa [Work.Spaces.K, Work.Elliptic.Ktheta] using
      Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three θ)
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  -- the pointwise bound on the reference profile
  have hFstar : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2),
      |Work.Construction.Fstar α s θ| ≤ 20 * s / (1 + s) ^ 2 := by
    intro θ hθ
    have hGam := Work.Spaces.Gam_bounds α θ hα hθ
    have hΓc : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
      have hle : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 1 / ((1 : ℝ) / 10) :=
        div_le_div₀ (by norm_num) hGam.2 (by norm_num) hc
      rw [abs_of_nonneg (div_nonneg hGam.1 hcpos.le)]
      norm_num at hle ⊢
      linarith
    have hfac : |α * (Work.Spaces.Gam α θ / Work.Spaces.c α)| ≤ 10 := by
      rw [abs_mul, abs_of_nonneg hα.le]
      calc α * |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 1 * 10 :=
            mul_le_mul hα1 hΓc (abs_nonneg _) (by norm_num)
        _ = 10 := by ring
    have hFstar_eq : Work.Construction.Fstar α s θ
        = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * s / (1 + s) ^ 2) := by
      rw [Work.Construction.Fstar, Work.FM.Fstar]
    rw [hFstar_eq, abs_mul]
    have hFnn : 0 ≤ 2 * s / (1 + s) ^ 2 := div_nonneg (by linarith) hden.le
    rw [abs_of_nonneg hFnn]
    calc |α * (Work.Spaces.Gam α θ / Work.Spaces.c α)| * (2 * s / (1 + s) ^ 2)
        ≤ 10 * (2 * s / (1 + s) ^ 2) := mul_le_mul_of_nonneg_right hfac hFnn
      _ = 20 * s / (1 + s) ^ 2 := by ring
  -- dividing the weight `Rwt s = s^{3/2}/(1+s)²` by `s`
  have hsplit : (20 * s / (1 + s) ^ 2 + Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt s) / s
      = 20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
    have hA : 20 * s / (1 + s) ^ 2 / s = 20 / (1 + s) ^ 2 := by
      rw [div_div]; field_simp
    have hB : Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt s / s
        = Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
      rw [mul_div_assoc, Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs]
    rw [add_div, hA, hB]
  -- the uniform pointwise bound on the whole of `Iθ`
  have hpt : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2),
      ‖Work.Spaces.K θ * (Work.Construction.Fstar α s θ + u s θ) / s‖ ≤ C0 := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [hK0, zero_mul, zero_div, norm_zero]
      exact hC0nn
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        rw [hKpi, zero_mul, zero_div, norm_zero]
        exact hC0nn
      · have hX : |Work.Construction.Fstar α s θ + u s θ|
            ≤ 20 * s / (1 + s) ^ 2 + Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt s :=
          calc |Work.Construction.Fstar α s θ + u s θ|
              ≤ |Work.Construction.Fstar α s θ| + |u s θ| := abs_add_le _ _
            _ ≤ 20 * s / (1 + s) ^ 2 + Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt s :=
                add_le_add (hFstar θ hθ) (by
                  simpa only [Work.FTS_RegExport.RXT.L12Iter.Rwt] using hu s θ hs h0 h1)
        have hXdiv : |Work.Construction.Fstar α s θ + u s θ| / s
            ≤ 20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
          have h := div_le_div_of_nonneg_right hX hs.le
          rwa [hsplit] at h
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul]
        calc |Work.Spaces.K θ| * |Work.Construction.Fstar α s θ + u s θ| / s
            = |Work.Spaces.K θ| * (|Work.Construction.Fstar α s θ + u s θ| / s) := by ring
          _ ≤ 3 * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) :=
              mul_le_mul (hKab θ) hXdiv (by positivity) (by norm_num)
          _ = C0 := by rw [hC0def]
  have hgoal : |Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + u z θ) s|
      = ‖∫ θ in Set.Icc (0:ℝ) (Real.pi / 2),
          Work.Spaces.K θ * (Work.Construction.Fstar α s θ + u s θ) / s‖ := by
    rw [Real.norm_eq_abs, Work.Construction.L12dens, Work.FM.L12dens]
  calc |Work.Construction.L12dens (fun z θ => Work.Construction.Fstar α z θ + u z θ) s|
      = ‖∫ θ in Set.Icc (0:ℝ) (Real.pi / 2),
          Work.Spaces.K θ * (Work.Construction.Fstar α s θ + u s θ) / s‖ := hgoal
    _ ≤ C0 * MeasureTheory.volume.real (Set.Icc (0:ℝ) (Real.pi / 2)) :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hvol_lt hpt
    _ = C0 * (Real.pi / 2) := by rw [hvol]
    _ = 3 * (Real.pi / 2) * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
        rw [hC0def]; ring

end Work.FTS_RegExport.RXT.Sys
