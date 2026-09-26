/-
# The cone-separated bound for the tile kernel `K` (general `ζ`)

For `w ∈ E = KEpsilon`, `n = ±1` and any `ζ ∈ ℍ` whose `S`-image `z = S ζ` lies in the cone
(`1 ≤ Im z`) at distance `≥ 1/8` from `S w` modulo the parabolic translations `ℤ`, the CKMRV
kernel differs from the principal part of its translate pole `ζ = w` by at most `C (scale w)^N`:

  `‖K(n +ᵥ w, ζ) - (n/2π)/(ζ - w)‖ ≤ C (scale w)^N`.

This is the cone-separated (off-spike) input of the tile principal-part window; its inputs are
`tile_divisor_lower_cone`, `tileXi_poly` and `tile_ncusp_pi` (the `Ncusp` bound with exponent
`π < 2π`, `Submission/Work/Asymptotics/TileWindow/tile_ncusp_own.lean`), combined through the
cleared identity `two_KfunClear_S_eq_eight` / `..._twentyfour`.

The `S`-image of the cone is bounded (`‖z‖ ≥ Im z ≥ 1`, and the cone condition gives
`‖ζ‖ ≤ 1`), so `‖ζ - w‖ ≥ 1/(64 (scale w)²)` and the principal part is polynomially bounded.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.TileCone.Basic
import Submission.Work.Asymptotics.tile_divisor_lower_cone
import Submission.Work.Asymptotics.tileXi_poly
import Submission.Work.Asymptotics.TileWindow.tile_ncusp_own

namespace Work.Asymptotics.TileWindow

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold

set_option maxHeartbeats 8000000

noncomputable section

/-- The coordinate of the `S`-action on `ℍ`. -/
lemma coe_S_smul' (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -((z : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]

/-- `KfunClear = growthPrefactor · Kfun`, from the two `ClearLink` halves. -/
theorem KfunClear_eq_smul_of (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.KfunClear ℓ d τ z
      = Work.Kernels.growthPrefactor d τ z * Work.Kernels.Kfun ℓ d τ z := by
  rw [Work.Kernels.KfunClear, Work.Kernels.Kfun,
    Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ z h,
    Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ z h]
  ring

/-- **The value of the tile kernel in terms of the cleared identity, `d = 8`.** -/
theorem Kfun_S_value_eight (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z)
      = (Work.Asymptotics.Xi8 τ z / Work.Asymptotics.cEight + Work.Asymptotics.Ncusp ℓ 8 τ z)
        / (2 * (z : ℂ) ^ 2 * Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
  set K : ℂ := Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z) with hKdef
  set N : ℂ := Work.Asymptotics.Xi8 τ z / Work.Asymptotics.cEight
      + Work.Asymptotics.Ncusp ℓ 8 τ z with hNdef
  have hSj : Work.Kernels.jInvariantFun (ModularGroup.S • z) = Work.Kernels.jInvariantFun z :=
    Work.Kernels.KernelFacts.jInvariantFun_S_smul z
  have hgp : Work.Kernels.KfunClear ℓ 8 τ (ModularGroup.S • z)
      = Work.Kernels.growthPrefactor 8 τ (ModularGroup.S • z) * K := by
    have h := KfunClear_eq_smul_of ℓ 8 (Or.inl rfl) τ (ModularGroup.S • z) (by rw [hSj]; exact hne)
    exact h
  have hgpe : Work.Kernels.growthPrefactor 8 τ (ModularGroup.S • z)
      = Work.Kernels.DeltaFun τ * ((z : ℂ) ^ 12 * Work.Kernels.DeltaFun z)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) := by
    rw [Work.Kernels.growthPrefactor, if_pos rfl, pow_one,
      Work.Asymptotics.DeltaFun_S_smul_eq z, hSj]
  have h2 : Work.Kernels.KfunClear ℓ 8 τ (ModularGroup.S • z)
      = Work.Kernels.DeltaFun τ * ((z : ℂ) ^ 12 * Work.Kernels.DeltaFun z)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) * K := by
    rw [hgp, hgpe]
  have h1 := Work.Asymptotics.two_KfunClear_S_eq_eight ℓ τ z hne
  have hΔτ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hΔz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hz0 : (z : ℂ) ≠ 0 := fun h0 => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h0]; simp)
  have hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 :=
    sub_ne_zero.mpr hne
  have hD : 2 * (z : ℂ) ^ 2 * Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0)) hΔz) hJ
  rw [eq_div_iff hD]
  have hkey : (z : ℂ) ^ 10 * Work.Kernels.DeltaFun τ
        * (K * (2 * (z : ℂ) ^ 2 * Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)))
      = (z : ℂ) ^ 10 * Work.Kernels.DeltaFun τ * N := by
    linear_combination h1 - 2 * h2
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 10 hz0) hΔτ) hkey

/-- **The value of the tile kernel in terms of the cleared identity, `d = 24`.** -/
theorem Kfun_S_value_twentyfour (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z)
      = (Work.Asymptotics.Xi24 τ z / Work.Asymptotics.cTwentyFour
          + Work.Asymptotics.Ncusp ℓ 24 τ z)
        / (2 * (z : ℂ) ^ 10 * Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
  set K : ℂ := Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z) with hKdef
  set N : ℂ := Work.Asymptotics.Xi24 τ z / Work.Asymptotics.cTwentyFour
      + Work.Asymptotics.Ncusp ℓ 24 τ z with hNdef
  have hSj : Work.Kernels.jInvariantFun (ModularGroup.S • z) = Work.Kernels.jInvariantFun z :=
    Work.Kernels.KernelFacts.jInvariantFun_S_smul z
  have hgp : Work.Kernels.KfunClear ℓ 24 τ (ModularGroup.S • z)
      = Work.Kernels.growthPrefactor 24 τ (ModularGroup.S • z) * K := by
    have h := KfunClear_eq_smul_of ℓ 24 (Or.inr rfl) τ (ModularGroup.S • z)
      (by rw [hSj]; exact hne)
    exact h
  have hgpe : Work.Kernels.growthPrefactor 24 τ (ModularGroup.S • z)
      = Work.Kernels.DeltaFun τ * ((z : ℂ) ^ 12 * Work.Kernels.DeltaFun z) ^ 2
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) := by
    rw [Work.Kernels.growthPrefactor, if_neg (by norm_num : ¬ ((24 : ℕ) = 8)),
      Work.Asymptotics.DeltaFun_S_smul_eq z, hSj]
  have h2 : Work.Kernels.KfunClear ℓ 24 τ (ModularGroup.S • z)
      = Work.Kernels.DeltaFun τ * ((z : ℂ) ^ 12 * Work.Kernels.DeltaFun z) ^ 2
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) * K := by
    rw [hgp, hgpe]
  have h1 := Work.Asymptotics.two_KfunClear_S_eq_twentyfour ℓ τ z hne
  have hΔτ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hΔz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hz0 : (z : ℂ) ≠ 0 := fun h0 => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h0]; simp)
  have hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 :=
    sub_ne_zero.mpr hne
  have hD : 2 * (z : ℂ) ^ 10 * Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 10 hz0)) hΔz) hJ
  rw [eq_div_iff hD]
  have hkey : (z : ℂ) ^ 14 * Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun τ
        * (K * (2 * (z : ℂ) ^ 10 * Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)))
      = (z : ℂ) ^ 14 * Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun τ * N := by
    linear_combination h1 - 2 * h2
  exact mul_left_cancel₀
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 14 hz0) hΔz) hΔτ) hkey

/-- **The principal part is polynomially bounded on the cone.**  If `z = S ζ` is at distance
`≥ 1/8` from `S w` then `‖ζ - w‖ ≥ 1/(64 (scale w)²)`. -/
lemma inv_norm_sub_le (w ζ : ℍ)
    (h8 : (1 / 8 : ℝ) ≤
      ‖((ModularGroup.S • ζ : ℍ) : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖) :
    ‖(ζ : ℂ) - (w : ℂ)‖⁻¹ ≤ 64 * (Work.Kernels.scale w) ^ (2 : ℝ) := by
  have hcoe := coe_S_smul'
  have hmul : (ζ : ℂ) - (w : ℂ)
      = (((ModularGroup.S • ζ : ℍ) : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
        * (ζ : ℂ) * (w : ℂ) := by
    rw [hcoe, hcoe]
    have hz : (ζ : ℂ) ≠ 0 := ζ.ne_zero
    have hw0 : (w : ℂ) ≠ 0 := w.ne_zero
    field_simp
    ring
  have hnorm : ‖(ζ : ℂ) - (w : ℂ)‖
      = ‖((ModularGroup.S • ζ : ℍ) : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖
        * ‖(ζ : ℂ)‖ * ‖(w : ℂ)‖ := by
    rw [hmul, norm_mul, norm_mul]
  have hR : 0 < (Work.Kernels.scale w)⁻¹ := inv_pos.mpr (Work.Kernels.scale_pos w)
  have hR1 : (Work.Kernels.scale w)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Work.Kernels.scale_pos w)]; exact Work.Kernels.one_le_scale w
  have hwlo : (1 / 2 : ℝ) * (Work.Kernels.scale w)⁻¹ ≤ ‖(w : ℂ)‖ := by
    have hsw : (w.im)⁻¹ ≤ Work.Kernels.scale w := by
      simp only [Work.Kernels.scale]; linarith [norm_nonneg (w : ℂ)]
    have h1 : (Work.Kernels.scale w)⁻¹ ≤ w.im := by
      rw [← inv_inv w.im, inv_le_inv₀ (Work.Kernels.scale_pos w) (by positivity)]
      exact hsw
    have h4 : w.im ≤ ‖(w : ℂ)‖ := Complex.im_le_norm _
    nlinarith [h1, h4, hR, hR1]
  have hgap : (1 / 64 : ℝ) * ((Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹)
      ≤ ‖(ζ : ℂ) - (w : ℂ)‖ := by
    rw [hnorm]
    by_cases h : ((1 / 4 : ℝ) * (Work.Kernels.scale w)⁻¹) ≤ ‖(ζ : ℂ)‖
    · have ha : (1 / 8 : ℝ) * ((1 / 4 : ℝ) * (Work.Kernels.scale w)⁻¹)
          ≤ (1 / 8 : ℝ) * ‖(ζ : ℂ)‖ := mul_le_mul_of_nonneg_left h (by norm_num)
      have h1 : (1 / 8 : ℝ) * ((1 / 4 : ℝ) * (Work.Kernels.scale w)⁻¹)
            * ((1 / 2 : ℝ) * (Work.Kernels.scale w)⁻¹)
          ≤ (1 / 8 : ℝ) * ‖(ζ : ℂ)‖ * ‖(w : ℂ)‖ :=
        mul_le_mul ha hwlo (by positivity) (by positivity)
      have h2 : (1 / 8 : ℝ) * ((1 / 4 : ℝ) * (Work.Kernels.scale w)⁻¹)
            * ((1 / 2 : ℝ) * (Work.Kernels.scale w)⁻¹)
          = (1 / 64 : ℝ) * ((Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹) := by ring
      have h3 : (1 / 8 : ℝ) * ‖(ζ : ℂ)‖ * ‖(w : ℂ)‖
          ≤ ‖((ModularGroup.S • ζ : ℍ) : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖
            * ‖(ζ : ℂ)‖ * ‖(w : ℂ)‖ := by
        have h4 := mul_le_mul_of_nonneg_right h8
          (mul_nonneg (norm_nonneg (ζ : ℂ)) (norm_nonneg (w : ℂ)))
        linarith [h4]
      rw [h2] at h1
      linarith [h1, h3]
    · have hlt : ‖(ζ : ℂ)‖ < (1 / 4 : ℝ) * (Work.Kernels.scale w)⁻¹ := not_le.mp h
      have hsplit : ‖(w : ℂ)‖ - ‖(ζ : ℂ)‖ ≤ ‖(ζ : ℂ) - (w : ℂ)‖ := by
        have h1 := abs_norm_sub_norm_le (w : ℂ) (ζ : ℂ)
        have h2 : ‖(w : ℂ) - (ζ : ℂ)‖ = ‖(ζ : ℂ) - (w : ℂ)‖ := norm_sub_rev _ _
        have h3 : ‖(w : ℂ)‖ - ‖(ζ : ℂ)‖ ≤ |‖(w : ℂ)‖ - ‖(ζ : ℂ)‖| := le_abs_self _
        rw [h2] at h1
        linarith [h1, h3]
      have h1 : (1 / 4 : ℝ) * (Work.Kernels.scale w)⁻¹ ≤ ‖(ζ : ℂ) - (w : ℂ)‖ := by
        linarith [hsplit, hwlo, le_of_lt hlt]
      have h2 : (1 / 64 : ℝ) * ((Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹)
          ≤ (1 / 4 : ℝ) * (Work.Kernels.scale w)⁻¹ := by
        have h3 : (Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹
            ≤ (Work.Kernels.scale w)⁻¹ := by
          calc (Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹
              ≤ (Work.Kernels.scale w)⁻¹ * 1 := mul_le_mul_of_nonneg_left hR1 hR.le
            _ = (Work.Kernels.scale w)⁻¹ := mul_one _
        calc (1 / 64 : ℝ) * ((Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹)
            ≤ (1 / 64 : ℝ) * (Work.Kernels.scale w)⁻¹ :=
              mul_le_mul_of_nonneg_left h3 (by norm_num)
          _ ≤ (1 / 4 : ℝ) * (Work.Kernels.scale w)⁻¹ :=
              mul_le_mul_of_nonneg_right (by norm_num) hR.le
      linarith [h1, h2]
  have hE2 : ((Work.Kernels.scale w) ^ (2 : ℝ))⁻¹
      = (Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹ := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_two, mul_inv]
  have hsq : ((Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹)⁻¹
      = (Work.Kernels.scale w) ^ (2 : ℝ) := by
    rw [← hE2, inv_inv]
  have hRR : 0 < (Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹ := mul_pos hR hR
  have hposn : 0 < ‖(ζ : ℂ) - (w : ℂ)‖ := lt_of_lt_of_le (by positivity) hgap
  have hRRne : (Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹ ≠ 0 := ne_of_gt hRR
  have h3 : (1 / 64 : ℝ) * ((Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹)
        * ((Work.Kernels.scale w)⁻¹ * (Work.Kernels.scale w)⁻¹)⁻¹ = (1 / 64 : ℝ) := by
    rw [mul_assoc, mul_inv_cancel₀ hRRne, mul_one]
  have h2 := mul_le_mul_of_nonneg_right hgap (le_of_lt (inv_pos.mpr hRR))
  rw [h3] at h2
  rw [hsq] at h2
  rw [inv_le_iff_one_le_mul₀ hposn]
  nlinarith [h2, Real.rpow_pos_of_pos (Work.Kernels.scale_pos w) 2]

/-- **The cone-separated bound for the tile kernel** (see the module docstring). -/
theorem tile_K_cone_sep (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (ζ : UpperHalfPlane),
        1 ≤ ((ModularGroup.S • ζ : UpperHalfPlane)).im →
        (∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖((ModularGroup.S • ζ : UpperHalfPlane) : ℂ)
            - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖) →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
        ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨cD, hcD, hDiv⟩ := Work.Asymptotics.tile_divisor_lower_cone
  obtain ⟨CX, NX, hCX, hNX, hXi⟩ := Work.Asymptotics.tileXi_poly ℓ d hd
  obtain ⟨CN, NN, hCN, hNN, hNc⟩ := tile_ncusp_pi ℓ d hd
  rcases hd with hd8 | hd24

  · subst hd8
    refine ⟨(CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) / (2 * cD) + 32 / Real.pi,
      max (max NX NN) 2, by positivity, ?_, ?_⟩
    · exact le_trans (le_trans hNX (le_max_left _ _)) (le_max_left _ _)
    · intro w hw n hn ζ hcone hsep
      set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
      set z : ℍ := ModularGroup.S • ζ with hzdef
      have hSz : ModularGroup.S • z = ζ := by rw [hzdef]; exact Work.Asymptotics.S_smul_S_smul ζ
      have hzim : 1 ≤ z.im := by rw [hzdef]; exact hcone
      have hzn : (1 : ℝ) ≤ ‖(z : ℂ)‖ := le_trans hzim (Complex.im_le_norm _)
      have hsepz : ∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖(z : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ := by
        intro k; rw [hzdef]; exact hsep k
      have hdiv := hDiv w hw n hn z hzim hsepz
      set ρ : ℝ := Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) with hρdef
      have hρpos : 0 < 1 + ρ := by positivity
      have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
        intro heq
        have h0 : Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) = 0 := by
          rw [heq, sub_self, mul_zero]
        rw [h0, norm_zero] at hdiv
        have hp := mul_pos hcD hρpos
        linarith [hdiv, hp]
      have hval := Kfun_S_value_eight ℓ τ z hne
      set W : ℝ := ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ with hWdef
      have hΔz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
      have hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 :=
        sub_ne_zero.mpr hne
      have hz0 : (z : ℂ) ≠ 0 := fun h0 => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h0]; simp)
      have hD : (2 : ℂ) * (z : ℂ) ^ 2 * Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0)) hΔz) hJ
      have hDnorm : ‖(2 : ℂ) * (z : ℂ) ^ 2 * Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
          = 2 * ‖(z : ℂ)‖ ^ 2 * W := by
        simp only [hWdef, norm_mul, norm_pow, Complex.norm_ofNat]
        ring
      have hdivW : cD * (1 + ρ) ≤ W := by
        have h := hdiv
        rw [hWdef]
        exact h
      have hW0 : 0 ≤ W := by rw [hWdef]; exact norm_nonneg _
      have hznp : (1 : ℝ) ≤ ‖(z : ℂ)‖ ^ 2 := one_le_pow₀ hzn
      have hX : 2 * cD * (1 + ρ)
          ≤ ‖(2 : ℂ) * (z : ℂ) ^ 2 * Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
        rw [hDnorm]
        have h1 : 2 * cD * (1 + ρ) ≤ 2 * W := by linarith [hdivW]
        have h2 : 2 * W ≤ 2 * ‖(z : ℂ)‖ ^ 2 * W := by nlinarith [hW0, hznp]
        linarith [h1, h2]
      have hXi' : ‖Work.Asymptotics.Xi8 τ z‖ ≤ CX * (Work.Kernels.scale w) ^ NX * (1 + ρ) := by
        have h := hXi w hw n hn z hzim
        simp only [if_pos rfl] at h
        rwa [← hρdef] at h
      have hNc' : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
          ≤ CN * (Work.Kernels.scale w) ^ NN
              * (1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im))) :=
        hNc w hw n hn z hzim
      have hexp : 1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im)) ≤ 2 * (1 + ρ) := by
        have hρ0 : (0 : ℝ) ≤ Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) := Real.exp_nonneg _
        by_cases h : 0 ≤ (ModularGroup.S • w).im - z.im
        · have h1 : Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im)) ≤ Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) :=
            Real.exp_le_exp.mpr (by nlinarith [h, Real.pi_pos])
          linarith
        · have h1 : Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im)) ≤ 1 := by
            rw [Real.exp_le_one_iff]; nlinarith [h, Real.pi_pos]
          linarith
      have hNbound : ‖Work.Asymptotics.Xi8 τ z / Work.Asymptotics.cEight
            + Work.Asymptotics.Ncusp ℓ 8 τ z‖
          ≤ (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) := by
        have hc0 : 0 < ‖Work.Asymptotics.cEight‖ := norm_pos_iff.mpr Work.Asymptotics.cEight_ne_zero
        have hNXm : (Work.Kernels.scale w) ^ NX ≤ (Work.Kernels.scale w) ^ (max NX NN) :=
          Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_left _ _)
        have hNNm : (Work.Kernels.scale w) ^ NN ≤ (Work.Kernels.scale w) ^ (max NX NN) :=
          Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_right _ _)
        have h1 : ‖Work.Asymptotics.Xi8 τ z / Work.Asymptotics.cEight‖
            ≤ CX / ‖Work.Asymptotics.cEight‖ * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) := by
          rw [norm_div]
          have h3 : CX / ‖Work.Asymptotics.cEight‖ * (Work.Kernels.scale w) ^ NX
              ≤ CX / ‖Work.Asymptotics.cEight‖ * (Work.Kernels.scale w) ^ (max NX NN) :=
            mul_le_mul_of_nonneg_left hNXm (by positivity)
          calc ‖Work.Asymptotics.Xi8 τ z‖ / ‖Work.Asymptotics.cEight‖
              ≤ (CX * (Work.Kernels.scale w) ^ NX * (1 + ρ)) / ‖Work.Asymptotics.cEight‖ :=
                div_le_div_of_nonneg_right hXi' hc0.le
            _ = CX / ‖Work.Asymptotics.cEight‖ * (Work.Kernels.scale w) ^ NX * (1 + ρ) := by ring
            _ ≤ CX / ‖Work.Asymptotics.cEight‖ * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) :=
                mul_le_mul_of_nonneg_right h3 (by positivity)
        have h2 : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
            ≤ 2 * CN * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) := by
          have h6 : CN * (Work.Kernels.scale w) ^ NN ≤ CN * (Work.Kernels.scale w) ^ (max NX NN) :=
            mul_le_mul_of_nonneg_left hNNm hCN.le
          calc ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
              ≤ CN * (Work.Kernels.scale w) ^ NN * (1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im))) := hNc'
            _ ≤ CN * (Work.Kernels.scale w) ^ (max NX NN)
                  * (1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im))) :=
                mul_le_mul_of_nonneg_right h6 (by positivity)
            _ ≤ CN * (Work.Kernels.scale w) ^ (max NX NN) * (2 * (1 + ρ)) :=
                mul_le_mul_of_nonneg_left hexp
                  (mul_nonneg hCN.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
            _ = 2 * CN * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) := by ring
        have hsum0 : ‖Work.Asymptotics.Xi8 τ z / Work.Asymptotics.cEight
            + Work.Asymptotics.Ncusp ℓ 8 τ z‖
            ≤ ‖Work.Asymptotics.Xi8 τ z / Work.Asymptotics.cEight‖
              + ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖ := norm_add_le _ _
        have hsum := add_le_add h1 h2
        have h8 : CX / ‖Work.Asymptotics.cEight‖ * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ)
              + 2 * CN * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ)
            = (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN)
              * (1 + ρ) := by ring
        linarith [hsum0, hsum, h8.le, h8.ge]
      have hnormK : ‖Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z)‖
          * ‖(2 : ℂ) * (z : ℂ) ^ 2 * Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
          = ‖Work.Asymptotics.Xi8 τ z / Work.Asymptotics.cEight
              + Work.Asymptotics.Ncusp ℓ 8 τ z‖ := by
        rw [hval, norm_div]
        exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hD)
      have hstep1 : ‖Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z)‖ * (2 * cD * (1 + ρ))
          ≤ ‖Work.Asymptotics.Xi8 τ z / Work.Asymptotics.cEight
              + Work.Asymptotics.Ncusp ℓ 8 τ z‖ := by
        rw [← hnormK]
        exact mul_le_mul_of_nonneg_left hX (norm_nonneg _)
      have hstep3 : ‖Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z)‖ * (2 * cD)
          ≤ (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) := by
        have h9 := mul_le_mul_of_nonneg_right (le_trans hstep1 hNbound)
          (le_of_lt (inv_pos.mpr hρpos))
        have h10 : ‖Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z)‖ * (2 * cD * (1 + ρ))
              * (1 + ρ)⁻¹ = ‖Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z)‖ * (2 * cD) := by
          have hne : (1 + ρ) ≠ 0 := ne_of_gt hρpos
          field_simp
        have h11 : (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) * (1 + ρ)⁻¹
            = (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) := by
          have hne : (1 + ρ) ≠ 0 := ne_of_gt hρpos
          field_simp
        rw [h10, h11] at h9
        exact h9
      have hpos2 : 0 < 2 * cD := by linarith
      have hkern : ‖Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z)‖
          ≤ (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) / (2 * cD) * (Work.Kernels.scale w) ^ (max NX NN) := by
        have h0 : ‖Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z)‖
            ≤ (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) / (2 * cD) := by
          rw [le_div_iff₀ hpos2]; exact hstep3
        calc ‖Work.Kernels.Kfun ℓ 8 τ (ModularGroup.S • z)‖
            ≤ (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) / (2 * cD) := h0
          _ = (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) / (2 * cD) * (Work.Kernels.scale w) ^ (max NX NN) := by ring
      have hpp : ‖((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
          ≤ (32 / Real.pi) * (Work.Kernels.scale w) ^ (2 : ℝ) := by
        have h8' : (1 / 8 : ℝ) ≤
            ‖((ModularGroup.S • ζ : UpperHalfPlane) : ℂ)
              - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ := by
          have h := hsep (0 : ℤ)
          simp only [Int.cast_zero, sub_zero] at h
          exact h
        have hinv := inv_norm_sub_le w ζ h8'
        have hnm : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
        have hcc : ‖((n : ℂ) / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
          rw [norm_div, hnm, norm_mul, Complex.norm_ofNat, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        rw [norm_mul, norm_inv, hcc]
        calc (1 / (2 * Real.pi)) * ‖(ζ : ℂ) - (w : ℂ)‖⁻¹
            ≤ (1 / (2 * Real.pi)) * (64 * (Work.Kernels.scale w) ^ (2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = (32 / Real.pi) * (Work.Kernels.scale w) ^ (2 : ℝ) := by
              have h3 : (1 / (2 * Real.pi)) * (64 * (Work.Kernels.scale w) ^ (2 : ℝ))
                  = (32 / Real.pi) * (Work.Kernels.scale w) ^ (2 : ℝ) := by
                field_simp
                ring
              rw [h3]
      rw [hSz] at hkern
      have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
      have hC0 : (0 : ℝ) ≤ (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) / (2 * cD) := by positivity
      have hN0 : (0 : ℝ) ≤ 32 / Real.pi := by positivity
      have hM1 : (Work.Kernels.scale w) ^ (max NX NN)
          ≤ (Work.Kernels.scale w) ^ (max (max NX NN) 2) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
      have hM2 : (Work.Kernels.scale w) ^ (2 : ℝ)
          ≤ (Work.Kernels.scale w) ^ (max (max NX NN) 2) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
      have ha := mul_le_mul_of_nonneg_left hM1 hC0
      have hb := mul_le_mul_of_nonneg_left hM2 hN0
      have hc : (CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) / (2 * cD) * (Work.Kernels.scale w) ^ (max (max NX NN) 2)
            + 32 / Real.pi * (Work.Kernels.scale w) ^ (max (max NX NN) 2)
          = ((CX / ‖Work.Asymptotics.cEight‖ + 2 * CN) / (2 * cD) + 32 / Real.pi) * (Work.Kernels.scale w) ^ (max (max NX NN) 2) := by
        ring
      refine le_trans (norm_sub_le _ _) ?_
      linarith [hkern, hpp, ha, hb, hc.le, hc.ge]

  · subst hd24
    refine ⟨(CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) / (2 * cD) + 32 / Real.pi,
      max (max NX NN) 2, by positivity, ?_, ?_⟩
    · exact le_trans (le_trans hNX (le_max_left _ _)) (le_max_left _ _)
    · intro w hw n hn ζ hcone hsep
      set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
      set z : ℍ := ModularGroup.S • ζ with hzdef
      have hSz : ModularGroup.S • z = ζ := by rw [hzdef]; exact Work.Asymptotics.S_smul_S_smul ζ
      have hzim : 1 ≤ z.im := by rw [hzdef]; exact hcone
      have hzn : (1 : ℝ) ≤ ‖(z : ℂ)‖ := le_trans hzim (Complex.im_le_norm _)
      have hsepz : ∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖(z : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖ := by
        intro k; rw [hzdef]; exact hsep k
      have hdiv := hDiv w hw n hn z hzim hsepz
      set ρ : ℝ := Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) with hρdef
      have hρpos : 0 < 1 + ρ := by positivity
      have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
        intro heq
        have h0 : Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) = 0 := by
          rw [heq, sub_self, mul_zero]
        rw [h0, norm_zero] at hdiv
        have hp := mul_pos hcD hρpos
        linarith [hdiv, hp]
      have hval := Kfun_S_value_twentyfour ℓ τ z hne
      set W : ℝ := ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ with hWdef
      have hΔz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
      have hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 :=
        sub_ne_zero.mpr hne
      have hz0 : (z : ℂ) ≠ 0 := fun h0 => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h0]; simp)
      have hD : (2 : ℂ) * (z : ℂ) ^ 10 * Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 10 hz0)) hΔz) hJ
      have hDnorm : ‖(2 : ℂ) * (z : ℂ) ^ 10 * Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
          = 2 * ‖(z : ℂ)‖ ^ 10 * W := by
        simp only [hWdef, norm_mul, norm_pow, Complex.norm_ofNat]
        ring
      have hdivW : cD * (1 + ρ) ≤ W := by
        have h := hdiv
        rw [hWdef]
        exact h
      have hW0 : 0 ≤ W := by rw [hWdef]; exact norm_nonneg _
      have hznp : (1 : ℝ) ≤ ‖(z : ℂ)‖ ^ 10 := one_le_pow₀ hzn
      have hX : 2 * cD * (1 + ρ)
          ≤ ‖(2 : ℂ) * (z : ℂ) ^ 10 * Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
        rw [hDnorm]
        have h1 : 2 * cD * (1 + ρ) ≤ 2 * W := by linarith [hdivW]
        have h2 : 2 * W ≤ 2 * ‖(z : ℂ)‖ ^ 10 * W := by nlinarith [hW0, hznp]
        linarith [h1, h2]
      have hXi' : ‖Work.Asymptotics.Xi24 τ z‖ ≤ CX * (Work.Kernels.scale w) ^ NX * (1 + ρ) := by
        have h := hXi w hw n hn z hzim
        simp only [if_neg (by norm_num : ¬ ((24 : ℕ) = 8))] at h
        rwa [← hρdef] at h
      have hNc' : ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖
          ≤ CN * (Work.Kernels.scale w) ^ NN
              * (1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im))) :=
        hNc w hw n hn z hzim
      have hexp : 1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im)) ≤ 2 * (1 + ρ) := by
        have hρ0 : (0 : ℝ) ≤ Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) := Real.exp_nonneg _
        by_cases h : 0 ≤ (ModularGroup.S • w).im - z.im
        · have h1 : Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im)) ≤ Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) :=
            Real.exp_le_exp.mpr (by nlinarith [h, Real.pi_pos])
          linarith
        · have h1 : Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im)) ≤ 1 := by
            rw [Real.exp_le_one_iff]; nlinarith [h, Real.pi_pos]
          linarith
      have hNbound : ‖Work.Asymptotics.Xi24 τ z / Work.Asymptotics.cTwentyFour
            + Work.Asymptotics.Ncusp ℓ 24 τ z‖
          ≤ (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) := by
        have hc0 : 0 < ‖Work.Asymptotics.cTwentyFour‖ := norm_pos_iff.mpr Work.Asymptotics.cTwentyFour_ne_zero
        have hNXm : (Work.Kernels.scale w) ^ NX ≤ (Work.Kernels.scale w) ^ (max NX NN) :=
          Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_left _ _)
        have hNNm : (Work.Kernels.scale w) ^ NN ≤ (Work.Kernels.scale w) ^ (max NX NN) :=
          Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_right _ _)
        have h1 : ‖Work.Asymptotics.Xi24 τ z / Work.Asymptotics.cTwentyFour‖
            ≤ CX / ‖Work.Asymptotics.cTwentyFour‖ * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) := by
          rw [norm_div]
          have h3 : CX / ‖Work.Asymptotics.cTwentyFour‖ * (Work.Kernels.scale w) ^ NX
              ≤ CX / ‖Work.Asymptotics.cTwentyFour‖ * (Work.Kernels.scale w) ^ (max NX NN) :=
            mul_le_mul_of_nonneg_left hNXm (by positivity)
          calc ‖Work.Asymptotics.Xi24 τ z‖ / ‖Work.Asymptotics.cTwentyFour‖
              ≤ (CX * (Work.Kernels.scale w) ^ NX * (1 + ρ)) / ‖Work.Asymptotics.cTwentyFour‖ :=
                div_le_div_of_nonneg_right hXi' hc0.le
            _ = CX / ‖Work.Asymptotics.cTwentyFour‖ * (Work.Kernels.scale w) ^ NX * (1 + ρ) := by ring
            _ ≤ CX / ‖Work.Asymptotics.cTwentyFour‖ * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) :=
                mul_le_mul_of_nonneg_right h3 (by positivity)
        have h2 : ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖
            ≤ 2 * CN * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) := by
          have h6 : CN * (Work.Kernels.scale w) ^ NN ≤ CN * (Work.Kernels.scale w) ^ (max NX NN) :=
            mul_le_mul_of_nonneg_left hNNm hCN.le
          calc ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖
              ≤ CN * (Work.Kernels.scale w) ^ NN * (1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im))) := hNc'
            _ ≤ CN * (Work.Kernels.scale w) ^ (max NX NN)
                  * (1 + Real.exp (Real.pi * ((ModularGroup.S • w).im - z.im))) :=
                mul_le_mul_of_nonneg_right h6 (by positivity)
            _ ≤ CN * (Work.Kernels.scale w) ^ (max NX NN) * (2 * (1 + ρ)) :=
                mul_le_mul_of_nonneg_left hexp
                  (mul_nonneg hCN.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
            _ = 2 * CN * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) := by ring
        have hsum0 : ‖Work.Asymptotics.Xi24 τ z / Work.Asymptotics.cTwentyFour
            + Work.Asymptotics.Ncusp ℓ 24 τ z‖
            ≤ ‖Work.Asymptotics.Xi24 τ z / Work.Asymptotics.cTwentyFour‖
              + ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖ := norm_add_le _ _
        have hsum := add_le_add h1 h2
        have h8 : CX / ‖Work.Asymptotics.cTwentyFour‖ * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ)
              + 2 * CN * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ)
            = (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN)
              * (1 + ρ) := by ring
        linarith [hsum0, hsum, h8.le, h8.ge]
      have hnormK : ‖Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z)‖
          * ‖(2 : ℂ) * (z : ℂ) ^ 10 * Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
          = ‖Work.Asymptotics.Xi24 τ z / Work.Asymptotics.cTwentyFour
              + Work.Asymptotics.Ncusp ℓ 24 τ z‖ := by
        rw [hval, norm_div]
        exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hD)
      have hstep1 : ‖Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z)‖ * (2 * cD * (1 + ρ))
          ≤ ‖Work.Asymptotics.Xi24 τ z / Work.Asymptotics.cTwentyFour
              + Work.Asymptotics.Ncusp ℓ 24 τ z‖ := by
        rw [← hnormK]
        exact mul_le_mul_of_nonneg_left hX (norm_nonneg _)
      have hstep3 : ‖Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z)‖ * (2 * cD)
          ≤ (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) := by
        have h9 := mul_le_mul_of_nonneg_right (le_trans hstep1 hNbound)
          (le_of_lt (inv_pos.mpr hρpos))
        have h10 : ‖Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z)‖ * (2 * cD * (1 + ρ))
              * (1 + ρ)⁻¹ = ‖Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z)‖ * (2 * cD) := by
          have hne : (1 + ρ) ≠ 0 := ne_of_gt hρpos
          field_simp
        have h11 : (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) * (1 + ρ) * (1 + ρ)⁻¹
            = (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) := by
          have hne : (1 + ρ) ≠ 0 := ne_of_gt hρpos
          field_simp
        rw [h10, h11] at h9
        exact h9
      have hpos2 : 0 < 2 * cD := by linarith
      have hkern : ‖Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z)‖
          ≤ (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) / (2 * cD) * (Work.Kernels.scale w) ^ (max NX NN) := by
        have h0 : ‖Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z)‖
            ≤ (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) / (2 * cD) := by
          rw [le_div_iff₀ hpos2]; exact hstep3
        calc ‖Work.Kernels.Kfun ℓ 24 τ (ModularGroup.S • z)‖
            ≤ (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) * (Work.Kernels.scale w) ^ (max NX NN) / (2 * cD) := h0
          _ = (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) / (2 * cD) * (Work.Kernels.scale w) ^ (max NX NN) := by ring
      have hpp : ‖((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖
          ≤ (32 / Real.pi) * (Work.Kernels.scale w) ^ (2 : ℝ) := by
        have h8' : (1 / 8 : ℝ) ≤
            ‖((ModularGroup.S • ζ : UpperHalfPlane) : ℂ)
              - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ := by
          have h := hsep (0 : ℤ)
          simp only [Int.cast_zero, sub_zero] at h
          exact h
        have hinv := inv_norm_sub_le w ζ h8'
        have hnm : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
        have hcc : ‖((n : ℂ) / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
          rw [norm_div, hnm, norm_mul, Complex.norm_ofNat, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        rw [norm_mul, norm_inv, hcc]
        calc (1 / (2 * Real.pi)) * ‖(ζ : ℂ) - (w : ℂ)‖⁻¹
            ≤ (1 / (2 * Real.pi)) * (64 * (Work.Kernels.scale w) ^ (2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = (32 / Real.pi) * (Work.Kernels.scale w) ^ (2 : ℝ) := by
              have h3 : (1 / (2 * Real.pi)) * (64 * (Work.Kernels.scale w) ^ (2 : ℝ))
                  = (32 / Real.pi) * (Work.Kernels.scale w) ^ (2 : ℝ) := by
                field_simp
                ring
              rw [h3]
      rw [hSz] at hkern
      have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
      have hC0 : (0 : ℝ) ≤ (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) / (2 * cD) := by positivity
      have hN0 : (0 : ℝ) ≤ 32 / Real.pi := by positivity
      have hM1 : (Work.Kernels.scale w) ^ (max NX NN)
          ≤ (Work.Kernels.scale w) ^ (max (max NX NN) 2) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
      have hM2 : (Work.Kernels.scale w) ^ (2 : ℝ)
          ≤ (Work.Kernels.scale w) ^ (max (max NX NN) 2) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
      have ha := mul_le_mul_of_nonneg_left hM1 hC0
      have hb := mul_le_mul_of_nonneg_left hM2 hN0
      have hc : (CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) / (2 * cD) * (Work.Kernels.scale w) ^ (max (max NX NN) 2)
            + 32 / Real.pi * (Work.Kernels.scale w) ^ (max (max NX NN) 2)
          = ((CX / ‖Work.Asymptotics.cTwentyFour‖ + 2 * CN) / (2 * cD) + 32 / Real.pi) * (Work.Kernels.scale w) ^ (max (max NX NN) 2) := by
        ring
      refine le_trans (norm_sub_le _ _) ?_
      linarith [hkern, hpp, ha, hb, hc.le, hc.ge]

end

end Work.Asymptotics.TileWindow
