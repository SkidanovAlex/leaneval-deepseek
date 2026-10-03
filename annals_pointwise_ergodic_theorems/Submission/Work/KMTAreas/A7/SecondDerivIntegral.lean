import Mathlib

/-!
# The second derivative of a function supported in `|θ| ≤ 1/R` costs `O(C₀ R)`

If `‖m''‖` is bounded by `C₀ R²` everywhere and `m` vanishes for `|θ| > 1/R`, then

  `∫ θ, ‖m''(θ)‖ ≤ 2 * C₀ * R`.

The reason is that `m` vanishes on the *open* set `{1/R < |θ|}`, and a function vanishing on an
open set has vanishing derivative there (`Filter.EventuallyEq.deriv_eq` applied to the two
functions `m` and `deriv m`, using that the open set is a neighbourhood of each of its points),
so also `m''` vanishes there.  Hence `m''` is supported in the interval
`[-1/R, 1/R]`, of measure `2/R`, and the trivial bound on the integral of a bounded function
over that interval gives `C₀ R² · (2/R) = 2 C₀ R`.

(Note that no integrability or measurability of `m` is assumed: if `m''` is not integrable the
Bochner integral is `0` by definition, and `norm_setIntegral_le_of_norm_le_const` already covers
that convention.)
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Work.KMTAreas.A7

set_option linter.unusedVariables false in
theorem SecondDerivIntegral {m : ℝ → ℂ} {C0 R : ℝ} (hR : 0 < R) (hC0 : 0 ≤ C0)
    (hb : ∀ θ, ‖deriv (deriv m) θ‖ ≤ C0 * R ^ 2)
    (hsupp : ∀ θ, 1 / R < |θ| → m θ = 0) :
    ∫ θ, ‖deriv (deriv m) θ‖ ≤ 2 * C0 * R := by
  have hRpos : 0 < 1 / R := one_div_pos.mpr hR
  -- `{1/R < |θ|}` is open, so it is a neighbourhood of each of its points; `m` vanishes on it.
  have hmem_of : ∀ θ, 1 / R < |θ| → {x : ℝ | 1 / R < |x|} ∈ 𝓝 θ := fun θ hθ =>
    (isOpen_lt continuous_const continuous_abs).mem_nhds hθ
  -- On that open set the derivative of `m` vanishes.
  have hderiv : ∀ θ, 1 / R < |θ| → deriv m θ = 0 := by
    intro θ hθ
    have hev : m =ᶠ[𝓝 θ] (fun _ => (0 : ℂ)) :=
      eventually_of_mem (hmem_of θ hθ) fun x hx => hsupp x hx
    rw [hev.deriv_eq, deriv_const]
  -- ... and so does the second derivative.
  have hderiv2 : ∀ θ, 1 / R < |θ| → deriv (deriv m) θ = 0 := by
    intro θ hθ
    have hev : deriv m =ᶠ[𝓝 θ] (fun _ => (0 : ℂ)) :=
      eventually_of_mem (hmem_of θ hθ) fun x hx => hderiv x hx
    rw [hev.deriv_eq, deriv_const]
  -- `m''` is thus supported in `s = [-1/R, 1/R]`.
  set s : Set ℝ := Icc (-(1 / R)) (1 / R) with hs
  have hcompl : ∀ θ, θ ∉ s → 1 / R < |θ| := by
    intro θ hθ
    rw [hs] at hθ
    simp only [mem_Icc, not_and_or, not_le] at hθ
    rcases hθ with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hzero_off : ∀ θ, θ ∉ s → ‖deriv (deriv m) θ‖ = 0 := by
    intro θ hθ
    rw [hderiv2 θ (hcompl θ hθ), norm_zero]
  have hfin : volume s < ⊤ := by
    rw [hs, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hbound : ∀ θ ∈ s, ‖(fun θ => ‖deriv (deriv m) θ‖) θ‖ ≤ C0 * R ^ 2 := by
    intro θ _
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hb θ
  have hnn : 0 ≤ ∫ θ in s, ‖deriv (deriv m) θ‖ :=
    setIntegral_nonneg_of_ae (Eventually.of_forall fun θ => norm_nonneg _)
  calc ∫ θ, ‖deriv (deriv m) θ‖
      = ∫ θ in s, ‖deriv (deriv m) θ‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (s := s) hzero_off).symm
    _ = ‖∫ θ in s, ‖deriv (deriv m) θ‖‖ := (Real.norm_of_nonneg hnn).symm
    _ ≤ (C0 * R ^ 2) * volume.real s := norm_setIntegral_le_of_norm_le_const hfin hbound
    _ = 2 * C0 * R := by
        rw [Measure.real_def, hs, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [hRpos])]
        field_simp
        ring

end Work.KMTAreas.A7
