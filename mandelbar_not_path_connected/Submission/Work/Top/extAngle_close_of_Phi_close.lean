/-
# The external angle is continuous at the interior points of a parameter ray

For a parameter `θ ∈ (0,1)` the map `c ↦ extAngle Φ c` is continuous at the points of the
parameter ray of angle `θ`: if the Böttcher coordinate `Φ c` is close to the point
`rayPoint θ R` of the exterior disc, then the external angle of `c` is close to `θ`.

The proof is the standard one.  Writing `z = Φ c` and `z₀ = rayPoint θ R`, the ratio
`w = z / z₀` is close to `1`; the argument of `w` is then small.  Since `arg z` and
`arg w + 2πθ` differ by an integer multiple of `2π`, and since `θ + arg w / (2π)` stays in
the interval `(0,1)`, reducing `arg z / (2π)` modulo `1` gives exactly `θ + arg w / (2π)`.
-/
import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.Top

namespace NakaneData

/-- The argument of the point `rayPoint θ R` of the exterior disc, as an element of the circle
`ℝ/2πℤ`: it is the class of `2πθ`. -/
theorem arg_rayPoint_coe_angle {θ R : ℝ} (hR : 0 < R) :
    (Complex.arg (rayPoint θ R) : Real.Angle) = ((2 * Real.pi * θ : ℝ) : Real.Angle) := by
  have hpt : rayPoint θ R = (R : ℂ) * Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := by
    rw [rayPoint]
    push_cast
    ring
  rw [hpt, Complex.arg_real_mul _ hR, Complex.arg_exp_mul_I]
  exact Real.Angle.coe_toIocMod _ _

/-- The argument of a quotient, as an element of `ℝ/2πℤ`. -/
theorem arg_div_add_arg_coe_angle {z z₀ : ℂ} (hz : z ≠ 0) (hz₀ : z₀ ≠ 0) :
    (Complex.arg z : Real.Angle)
      = (Complex.arg (z / z₀) : Real.Angle) + (Complex.arg z₀ : Real.Angle) := by
  conv_lhs => rw [← div_mul_cancel₀ z hz₀]
  rw [Complex.arg_mul_coe_angle (div_ne_zero hz hz₀) hz₀]

/-- The arguments of `z` and of `z / z₀` differ, modulo `2π`, by the argument of `z₀`. -/
theorem exists_int_arg_sub_arg_div {z z₀ : ℂ} (hz : z ≠ 0) (hz₀ : z₀ ≠ 0) {θ : ℝ}
    (hθ : (Complex.arg z₀ : Real.Angle) = ((θ : ℝ) : Real.Angle)) :
    ∃ n : ℤ, Complex.arg z - Complex.arg (z / z₀) - θ = 2 * Real.pi * n := by
  have h : (Complex.arg z : Real.Angle)
      = (Complex.arg (z / z₀) : Real.Angle) + (Complex.arg z₀ : Real.Angle) :=
    arg_div_add_arg_coe_angle hz hz₀
  rw [hθ, ← Real.Angle.coe_add] at h
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
  exact ⟨n, by linarith⟩

end NakaneData

theorem extAngle_close_of_Phi_close {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {θ R : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hR : 1 < R) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ c : ℂ, c ∉ Mb → ‖Φ c - Work.Top.NakaneData.rayPoint θ R‖ < δ →
      |Work.Top.NakaneData.extAngle Φ c - θ| < η := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hθ1 : 0 < 1 - θ := by linarith
  -- a tolerance `ε`, smaller than `θ`, than `1 - θ` and than `η`
  set ε : ℝ := min θ (min (1 - θ) η) / 2 with hεdef
  have hmpos : 0 < min θ (min (1 - θ) η) := lt_min hθ₀ (lt_min hθ1 hη)
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεθ : ε < θ := by
    rw [hεdef]
    have := min_le_left θ (min (1 - θ) η)
    linarith
  have hε1θ : ε < 1 - θ := by
    rw [hεdef]
    have h1 := min_le_right θ (min (1 - θ) η)
    have h2 := min_le_left (1 - θ) η
    linarith
  have hεη : ε < η := by
    rw [hεdef]
    have h1 := min_le_right θ (min (1 - θ) η)
    have h2 := min_le_right (1 - θ) η
    linarith
  -- `arg` is continuous at `1`, where it vanishes
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧
      ∀ w : ℂ, ‖w - 1‖ < δ₁ → |Complex.arg w| < 2 * Real.pi * ε := by
    have h2πε : (0 : ℝ) < 2 * Real.pi * ε :=
      mul_pos (by positivity : (0 : ℝ) < 2 * Real.pi) hεpos
    have hmem : Complex.arg (1 : ℂ) ∈ Set.Ioo (-(2 * Real.pi * ε)) (2 * Real.pi * ε) := by
      simp only [Complex.arg_one]
      exact ⟨by linarith, h2πε⟩
    have h1slit : (1 : ℂ) ∈ Complex.slitPlane := by
      rw [← Complex.ofReal_one, Complex.ofReal_mem_slitPlane]
      norm_num
    have hev : ∀ᶠ w in 𝓝 (1 : ℂ), |Complex.arg w| < 2 * Real.pi * ε := by
      have h1 := (Complex.continuousAt_arg h1slit).preimage_mem_nhds (isOpen_Ioo.mem_nhds hmem)
      filter_upwards [h1] with w hw using abs_lt.mpr hw
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hev
    exact ⟨δ₁, hδ₁pos, fun w hw => hδ₁ (by simpa [dist_eq_norm] using hw)⟩
  refine ⟨R * δ₁, by positivity, ?_⟩
  intro c hc hdist
  have hz : Φ c ≠ 0 := hN.Phi_ne_zero hc
  have hz₀ : Work.Top.NakaneData.rayPoint θ R ≠ 0 := by
    intro h
    have h1 := Work.Top.NakaneData.norm_rayPoint θ R
    rw [h, norm_zero] at h1
    have h2 : |R| = 0 := h1.symm
    rw [abs_eq_zero] at h2
    linarith
  have hnorm : ‖Work.Top.NakaneData.rayPoint θ R‖ = R := by
    rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos hRpos]
  -- the normalized Böttcher coordinate of `c`: its ratio to the ray point
  set w : ℂ := Φ c / Work.Top.NakaneData.rayPoint θ R with hwdef
  have hwne : w ≠ 0 := by rw [hwdef]; exact div_ne_zero hz hz₀
  have hw1 : w - 1 = (Φ c - Work.Top.NakaneData.rayPoint θ R) / Work.Top.NakaneData.rayPoint θ R := by
    rw [hwdef, sub_div, div_self hz₀]
  have hwdist : ‖w - 1‖ < δ₁ := by
    rw [hw1, norm_div, hnorm, div_lt_iff₀ hRpos]
    linarith
  have hargw : |Complex.arg w| < 2 * Real.pi * ε := hδ₁ w hwdist
  have hargw2 : |Complex.arg w / (2 * Real.pi)| < ε := by
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [abs_div, abs_of_pos h2π, div_lt_iff₀ h2π]
    linarith [hargw]
  -- `θ + arg w / (2π)` lies in the fundamental interval `[0,1)`
  have hmem : θ + Complex.arg w / (2 * Real.pi) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    obtain ⟨h1, h2⟩ := abs_lt.mp hargw2
    exact ⟨by linarith, by linarith⟩
  have hargz0 : (Complex.arg (Work.Top.NakaneData.rayPoint θ R) : Real.Angle) =
      ((2 * Real.pi * θ : ℝ) : Real.Angle) :=
    Work.Top.NakaneData.arg_rayPoint_coe_angle hRpos
  -- the congruence of the arguments modulo `2π`
  obtain ⟨n, hn⟩ := Work.Top.NakaneData.exists_int_arg_sub_arg_div (z := Φ c)
    (z₀ := Work.Top.NakaneData.rayPoint θ R) hz hz₀ hargz0
  -- the external angle is exactly `θ + arg w / (2π)`
  have hkey : Work.Top.NakaneData.extAngle Φ c = θ + Complex.arg w / (2 * Real.pi) := by
    rw [Work.Top.NakaneData.extAngle, toIcoMod_eq_iff]
    refine ⟨hmem, n, ?_⟩
    rw [zsmul_eq_mul, mul_one]
    have h2πne : (2 * Real.pi) ≠ 0 := by positivity
    rw [div_eq_iff h2πne]
    rw [add_mul, add_mul, div_mul_cancel₀ _ h2πne]
    linarith
  rw [hkey]
  have : |θ + Complex.arg w / (2 * Real.pi) - θ| < η := by
    rw [add_sub_cancel_left]
    exact lt_trans hargw2 hεη
  exact this

end Work.Top
