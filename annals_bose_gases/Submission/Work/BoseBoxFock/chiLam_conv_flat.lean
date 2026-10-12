import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseBoxFock.AliasDefs
import Submission.Work.BoseFixB1.chi_boundary_taylor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Flatness of the two-point convolution of the corpus bump

`Work.BoseK15.corpusBox.chiLam ℓ` is FS's localisation function `χ_Λ(x) = χ(x/ℓ)` of the box
of side `ℓ`, supported in the closed ball of radius `ℓ/2` and smooth.  The target of this module,
`Work.BoseBoxFock.chiLam_conv_flat`, states that its two-point convolution

    `u ↦ ∫ x, χ_Λ(x) χ_Λ(x - u)`

vanishes *faster than any polynomial* as `‖u‖` tends to `ℓ` (the tangency of the two support
balls): for every `N` there is `C` with `∫ χ_Λ(x) χ_Λ(x-u) ≤ C (ℓ - ‖u‖)^N` for `‖u‖ ≤ ℓ`.

The mathematical input is exactly the superpolynomial boundary decay of the bump,
`Work.BoseFixB1.chi_boundary_taylor`: for every `N` there is `C₀ > 0` with

    `χ z ≤ C₀ (1/2 - ‖z‖)^N`   for `‖z‖ ≤ 1/2`.

The proof is then a pointwise estimate plus one integration:

* if `χ_Λ(x) ≠ 0` and `χ_Λ(x - u) ≠ 0`, then both `‖x‖ < ℓ/2` and `‖x - u‖ < ℓ/2`, so that
  `‖u‖ ≤ ‖x‖ + ‖x - u‖ < ℓ/2 + ‖x - u‖`, i.e. `ℓ/2 - ‖x - u‖ ≤ ℓ - ‖u‖`;
* the flatness bound at `x - u` therefore gives
  `χ_Λ(x - u) ≤ C₀ ℓ^{-N} (ℓ - ‖u‖)^N =: Mb`, and (as `χ_Λ ≥ 0`)
  `χ_Λ(x) χ_Λ(x - u) ≤ Mb χ_Λ(x)` for *every* `x`;
* integrating against the (integrable, nonnegative) `χ_Λ` and taking
  `C := C₀ ℓ^{-N} ∫ χ_Λ` gives the claim.

The scaling `‖ℓ⁻¹ • y‖ = ‖y‖/ℓ` turns `(1/2 - ‖y‖/ℓ)^N` into `ℓ^{-N} (ℓ/2 - ‖y‖)^N`, and the
translated factor is handled *without* translation invariance of Lebesgue measure: one always
integrates the factor centred at `0`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `χ_Λ = χ(·/ℓ)` expressed through the unit-cell localisation function. -/
lemma chiLam_eq_chi (ℓ : ℝ) (x : E3) :
    Work.BoseK15.corpusBox.chiLam ℓ x = Submission.BoseGases.chi (ℓ⁻¹ • x) := by
  rw [Work.BoseB4.BoxData.chiLam_apply, Work.BoseK15.corpusBox_chi]

/-- The scaled corpus bump vanishes outside the closed ball of radius `ℓ/2`. -/
lemma chiLam_eq_zero_of_half_le_norm {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ℓ / 2 ≤ ‖x‖) :
    Work.BoseK15.corpusBox.chiLam ℓ x = 0 := by
  rw [chiLam_eq_chi, Submission.BoseGases.chi]
  have h0 : Submission.BoseGases.chiBase (ℓ⁻¹ • x) = 0 := by
    refine Submission.BoseGases.chiBump.zero_of_le_dist ?_
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    have h2 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
    have hle := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hℓ))
    rw [h2] at hle
    exact hle
  rw [h0, zero_div]

/-- A non-vanishing value of the scaled bump forces `‖x‖ < ℓ/2`. -/
lemma norm_lt_half_of_chiLam_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : Work.BoseK15.corpusBox.chiLam ℓ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  by_contra hcon
  exact hx (chiLam_eq_zero_of_half_le_norm hℓ (not_lt.mp hcon))

/-- **Flatness of the scaled bump.**  The boundary decay `χ z ≤ C (1/2 - ‖z‖)^N` of the unit-cell
localisation function transported to `χ_Λ = χ(·/ℓ)`. -/
lemma chiLam_le_flat {ℓ C : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hC : ∀ z : E3, ‖z‖ ≤ 1 / 2 → Submission.BoseGases.chi z ≤ C * (1 / 2 - ‖z‖) ^ N)
    {x : E3} (hx : ‖x‖ < ℓ / 2) :
    Work.BoseK15.corpusBox.chiLam ℓ x ≤ C * (ℓ ^ N)⁻¹ * (ℓ / 2 - ‖x‖) ^ N := by
  have hnorm : ‖(ℓ⁻¹ : ℝ) • x‖ = ℓ⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
  have h2 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
  have hlt : ℓ⁻¹ * ‖x‖ < 1 / 2 := by
    have h := mul_lt_mul_of_pos_left hx (inv_pos.mpr hℓ)
    rwa [h2] at h
  have hstep := hC ((ℓ⁻¹ : ℝ) • x) (by rw [hnorm]; exact hlt.le)
  rw [chiLam_eq_chi]
  have harg : (1 / 2 : ℝ) - ‖(ℓ⁻¹ : ℝ) • x‖ = ℓ⁻¹ * (ℓ / 2 - ‖x‖) := by
    rw [hnorm, mul_sub, h2]
  rw [harg, mul_pow, inv_pow] at hstep
  calc Submission.BoseGases.chi (ℓ⁻¹ • x)
      ≤ C * ((ℓ ^ N)⁻¹ * (ℓ / 2 - ‖x‖) ^ N) := hstep
    _ = C * (ℓ ^ N)⁻¹ * (ℓ / 2 - ‖x‖) ^ N := by ring

/-- **The two-point convolution of the localisation function is flat at tangency.** -/
theorem chiLam_conv_flat {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ ≤ ℓ →
      (∫ x : EuclideanSpace ℝ (Fin 3),
          Work.BoseK15.corpusBox.chiLam ℓ x * Work.BoseK15.corpusBox.chiLam ℓ (x - u))
        ≤ C * (ℓ - ‖u‖) ^ N := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.BoseFixB1.chi_boundary_taylor N
  -- compact support and integrability of the localisation function
  have hcs : HasCompactSupport (fun x : E3 => Work.BoseK15.corpusBox.chiLam ℓ x) :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).of_isClosed_subset
      (isClosed_tsupport _)
      (Work.BoseB4.BoxData.tsupport_chiLam_subset Work.BoseK15.corpusBox hℓ)
  have hIntA : Integrable (fun x : E3 => Work.BoseK15.corpusBox.chiLam ℓ x) :=
    (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox ℓ).integrable_of_hasCompactSupport hcs
  have hA0 : ∀ x : E3, 0 ≤ Work.BoseK15.corpusBox.chiLam ℓ x :=
    fun x => Work.BoseB4.BoxData.chiLam_nonneg Work.BoseK15.corpusBox ℓ x
  have hIL0 : 0 ≤ ∫ x : E3, Work.BoseK15.corpusBox.chiLam ℓ x := integral_nonneg hA0
  refine ⟨C₀ * (ℓ ^ N)⁻¹ * (∫ x : E3, Work.BoseK15.corpusBox.chiLam ℓ x), by positivity, ?_⟩
  intro u hu
  have hδ : 0 ≤ ℓ - ‖u‖ := by linarith
  have hMb0 : 0 ≤ C₀ * (ℓ ^ N)⁻¹ * (ℓ - ‖u‖) ^ N := by positivity
  have hIntMb : Integrable (fun x : E3 =>
      (C₀ * (ℓ ^ N)⁻¹ * (ℓ - ‖u‖) ^ N) * Work.BoseK15.corpusBox.chiLam ℓ x) :=
    hIntA.const_mul _
  have key : ∀ x : E3,
      Work.BoseK15.corpusBox.chiLam ℓ x * Work.BoseK15.corpusBox.chiLam ℓ (x - u)
        ≤ (C₀ * (ℓ ^ N)⁻¹ * (ℓ - ‖u‖) ^ N) * Work.BoseK15.corpusBox.chiLam ℓ x := by
    intro x
    by_cases hA : Work.BoseK15.corpusBox.chiLam ℓ x = 0
    · rw [hA, mul_zero, zero_mul]
    · have hxn : ‖x‖ < ℓ / 2 := norm_lt_half_of_chiLam_ne_zero hℓ hA
      by_cases hB : Work.BoseK15.corpusBox.chiLam ℓ (x - u) = 0
      · rw [hB, mul_zero]
        exact mul_nonneg hMb0 (hA0 x)
      · have hxun : ‖x - u‖ < ℓ / 2 := norm_lt_half_of_chiLam_ne_zero hℓ hB
        have hb : ℓ / 2 - ‖x - u‖ ≤ ℓ - ‖u‖ := by
          have h1 : ‖u‖ ≤ ‖x - u‖ + ‖x‖ := by
            have h := norm_add_le (u - x) x
            rw [sub_add_cancel, norm_sub_rev] at h
            exact h
          linarith
        have hb0 : 0 ≤ ℓ / 2 - ‖x - u‖ := by linarith
        have hflat := chiLam_le_flat hℓ N hC₀ hxun
        have hle : Work.BoseK15.corpusBox.chiLam ℓ (x - u)
            ≤ C₀ * (ℓ ^ N)⁻¹ * (ℓ - ‖u‖) ^ N := by
          calc Work.BoseK15.corpusBox.chiLam ℓ (x - u)
              ≤ C₀ * (ℓ ^ N)⁻¹ * (ℓ / 2 - ‖x - u‖) ^ N := hflat
            _ ≤ C₀ * (ℓ ^ N)⁻¹ * (ℓ - ‖u‖) ^ N := by
                refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb N) ?_
                positivity
        calc Work.BoseK15.corpusBox.chiLam ℓ x * Work.BoseK15.corpusBox.chiLam ℓ (x - u)
            ≤ Work.BoseK15.corpusBox.chiLam ℓ x * (C₀ * (ℓ ^ N)⁻¹ * (ℓ - ‖u‖) ^ N) :=
              mul_le_mul_of_nonneg_left hle (hA0 x)
          _ = (C₀ * (ℓ ^ N)⁻¹ * (ℓ - ‖u‖) ^ N) * Work.BoseK15.corpusBox.chiLam ℓ x := by ring
  calc ∫ x : E3,
        Work.BoseK15.corpusBox.chiLam ℓ x * Work.BoseK15.corpusBox.chiLam ℓ (x - u)
      ≤ ∫ x : E3,
          (C₀ * (ℓ ^ N)⁻¹ * (ℓ - ‖u‖) ^ N) * Work.BoseK15.corpusBox.chiLam ℓ x :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => mul_nonneg (hA0 x) (hA0 (x - u)))
          hIntMb (Filter.Eventually.of_forall key)
    _ = (C₀ * (ℓ ^ N)⁻¹ * (ℓ - ‖u‖) ^ N) * ∫ x : E3, Work.BoseK15.corpusBox.chiLam ℓ x :=
        integral_const_mul _ _
    _ = (C₀ * (ℓ ^ N)⁻¹ * (∫ x : E3, Work.BoseK15.corpusBox.chiLam ℓ x)) * (ℓ - ‖u‖) ^ N := by
        ring

end Work.BoseBoxFock
