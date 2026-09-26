/-
# Flatness of the CKMRV kernel on the cusp-`0` neighbourhood `E` from the four global bounds

The target `Work.Asymptotics.EFlat ℓ d` is the flatness statement for the contour kernel
`t ↦ Kaxis (Kfun ℓ d) w t` on the whole cusp-`0` neighbourhood `E = Work.Asymptotics.KEpsilon`:

  for every `N ≥ 0` there are `c ≥ 0` and `N'` with
  `‖Kaxis (Kfun ℓ d) w t‖ ≤ c * (scale w)^{N'} * t^N`  for all `w ∈ E` and `0 < t ≤ 1`.

The purpose of this file is to deduce that flatness from four *global* analytic inputs:

* `hplus`, `hminus` — the CKMRV Lemma 4.12 bounds (`quotientbounds1new`) for `K_±`, in the form
  `‖z^{-(2-d/2)} K_±(τ, S z)‖ ≤ C (scale τ)^N (1+‖z‖)² e^{-π Im z} / ‖Δ(z)(j τ - j z)‖`
  for `Im (S τ) ≥ 3/2` and `Im z ≥ 1` (i.e. exactly the half-plane conditions under which the
  CKMRV estimates hold);
* `hdiv` — the lower bound `|Δ(i/t)(j w - j(i/t))| ≥ c` for `w ∈ E`, `0 < t ≤ 1` which are
  *not* within `ρ t²` of an `SL(2,ℤ)`-translate of `i t`;
* `hnear` — flatness of `Kaxis (Kfun ℓ d)` at the cusp `0`, i.e. on the region where `w` *is*
  within `c₀ t²` of such a translate.

The proof splits on the two regions.  Near the cusp `hnear` applies directly.  Away from the
cusp the divisor factor is bounded below by `hdiv`, and the two kernel bounds `hplus`/`hminus`
apply: the coincidence `j w = j(i/t)` is impossible there, because `j` separates `SL(2,ℤ)`-orbits
(`Work.Asymptotics.jInvariantFun_eq_smul_of_eq`) and `i/t = S • (i t)`.  The resulting polynomial
factor `t^{-2}` is absorbed into `t^N` by `t^{-2} e^{-π/t} = O(t^N)` at `t → 0⁺`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.MFix.Cusp0Flat
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

/-! ## Auxiliary facts about the imaginary axis -/

private lemma coe_imagAxis_norm (t : ℝ) (ht : 0 < t) :
    ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := by
  rw [show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le]

private lemma imagAxis_im_aux (t : ℝ) (ht : 0 < t) :
    (Work.Kernels.imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

/-- `‖(i/t)^{(2-d/2)}‖ ≤ 1` for `d ∈ {8,24}` and `0 < t ≤ 1`. -/
private lemma norm_zpow_two_sub_half_le_one (d : ℕ) (hd : d = 8 ∨ d = 24) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖(((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : UpperHalfPlane)) : ℂ)
        ^ ((2 : ℤ) - (d : ℤ) / 2)‖ ≤ 1 := by
  rw [norm_zpow, coe_imagAxis_norm t⁻¹ (inv_pos.mpr ht)]
  refine zpow_le_one_of_nonpos₀ ((one_le_inv₀ ht).mpr ht1) ?_
  rcases hd with h8 | h24
  · subst h8; norm_num
  · subst h24; norm_num

/-- `(1 + ‖i/t‖)² ≤ 4 t^{-2}` for `0 < t ≤ 1`. -/
private lemma one_add_norm_imagAxis_inv_sq_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (1 + ‖(((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : UpperHalfPlane)) : ℂ)‖) ^ (2 : ℕ)
      ≤ 4 * t ^ (-(2 : ℝ)) := by
  rw [coe_imagAxis_norm t⁻¹ (inv_pos.mpr ht)]
  have h2 : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have h3 : 1 + t⁻¹ ≤ 2 * t⁻¹ := by linarith
  have h4 : (1 + t⁻¹) ^ 2 ≤ (2 * t⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
  have h5 : (2 * t⁻¹) ^ 2 = 4 * t ^ (-(2 : ℝ)) := by
    have h6 : t ^ (-(2 : ℝ)) = (t ^ 2)⁻¹ := by rw [Real.rpow_neg ht.le]; norm_num
    rw [h6, mul_pow, inv_pow]
    norm_num
  linarith [h4, h5.ge, h5.le]

/-! ## The main deduction -/

theorem EFlat_of_bounds (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hplus : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KPlus d τ (ModularGroup.S • z)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
            Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
    (hminus : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
            Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
    (hdiv : ∀ ρ : ℝ, 0 < ρ → ∃ c : ℝ, 0 < c ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
        (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          ρ * t ^ 2 ≤ ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖) →
        c ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
              (Work.Kernels.jInvariantFun w -
                Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖)
    (hnear : ∀ N : ℝ, 0 ≤ N → ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c N' : ℝ, 0 ≤ c ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
        (∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖ < c₀ * t ^ 2) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ c * (Work.Kernels.scale w) ^ N' * t ^ N) :
    Work.Asymptotics.EFlat ℓ d := by
  intro N hN
  obtain ⟨Cplus, Nplus, hCplus, hNplus, hbp⟩ := hplus
  obtain ⟨Cminus, Nminus, hCminus, hNminus, hbm⟩ := hminus
  obtain ⟨c₀, hc₀, c₁, N₁, hc₁, hbn⟩ := hnear N hN
  obtain ⟨cdiv, hcdiv, hbd⟩ := hdiv c₀ hc₀
  obtain ⟨K₀, hK₀pos, hK₀b⟩ := Work.Asymptotics.MFix.rpow_neg_mul_exp_le 2 N
  have hC0 : 0 ≤ max Cplus Cminus := le_trans hCplus.le (le_max_left _ _)
  have hCfar0 : 0 ≤ max Cplus Cminus * 4 / cdiv :=
    div_nonneg (mul_nonneg hC0 (by norm_num)) hcdiv.le
  have hCK0 : 0 ≤ max Cplus Cminus * 4 / cdiv * K₀ := mul_nonneg hCfar0 hK₀pos.le
  refine ⟨max c₁ (max Cplus Cminus * 4 / cdiv * K₀), max N₁ (max Nplus Nminus),
    le_trans hc₁ (le_max_left _ _), ?_⟩
  intro w t hw ht ht1
  rw [Work.Kernels.Kaxis, dif_pos ht]
  by_cases hnearcase : ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖ < c₀ * t ^ 2
  · -- near the cusp: `hnear` applies directly
    have hb := hbn w t ht hw ht1 hnearcase
    rw [Work.Kernels.Kaxis, dif_pos ht] at hb
    have hs1 : (Work.Kernels.scale w) ^ N₁
        ≤ (Work.Kernels.scale w) ^ (max N₁ (max Nplus Nminus)) :=
      Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_left _ _)
    have hAB : c₁ * (Work.Kernels.scale w) ^ N₁
        ≤ max c₁ (max Cplus Cminus * 4 / cdiv * K₀) *
            (Work.Kernels.scale w) ^ (max N₁ (max Nplus Nminus)) :=
      mul_le_mul (le_max_left _ _) hs1 (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N₁)
        (le_trans hc₁ (le_max_left _ _))
    exact hb.trans (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg ht.le N))
  · -- away from the cusp: the divisor factor is bounded below and `hplus`/`hminus` apply
    have hfar : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        c₀ * t ^ 2 ≤ ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖ :=
      fun γ => not_lt.mp (not_exists.mp hnearcase γ)
    set z₀ : UpperHalfPlane := Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) with hz₀
    have hz₀im : z₀.im = t⁻¹ := by rw [hz₀]; exact imagAxis_im_aux t⁻¹ (inv_pos.mpr ht)
    have hz₀norm : ‖(z₀ : ℂ)‖ = t⁻¹ := by
      rw [hz₀]; exact coe_imagAxis_norm t⁻¹ (inv_pos.mpr ht)
    have hz₀ne : (z₀ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z₀
    have hz₁ : 1 ≤ z₀.im := by rw [hz₀im]; exact (one_le_inv₀ ht).mpr ht1
    have hSw : (3 / 2 : ℝ) ≤ (ModularGroup.S • w).im := by linarith [hw.2]
    have hSit : ModularGroup.S • Work.Kernels.imagAxis t ht = z₀ := by
      rw [hz₀]; exact Work.Asymptotics.imagAxis_smul_S t ht
    have hSz₀ : ModularGroup.S • z₀ = Work.Kernels.imagAxis t ht := by
      rw [← hSit, Work.Asymptotics.S_smul_S_smul]
    -- the coincidence `j w = j(i/t)` cannot happen here
    have hne : Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun z₀ := by
      intro hj
      obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hj
      have h0 : ‖(w : ℂ) -
          ((((γ * ModularGroup.S) • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖ = 0 := by
        rw [mul_smul, hSit, hγ, sub_self, norm_zero]
      have h2 := hfar (γ * ModularGroup.S)
      rw [h0] at h2
      have hpos : 0 < c₀ * t ^ 2 := mul_pos hc₀ (pow_pos ht 2)
      linarith
    have hden : cdiv ≤ ‖Work.Kernels.DeltaFun z₀ *
        (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀)‖ := by
      have h := hbd w t ht hw ht1 hfar
      rwa [← hz₀] at h
    have hpowinv : ‖((z₀ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)))⁻¹‖ ≤ 1 := by
      rw [← _root_.zpow_neg]
      have h1 : -(-((2 : ℤ) - (d : ℤ) / 2)) = (2 : ℤ) - (d : ℤ) / 2 := by ring
      rw [h1, hz₀]
      exact norm_zpow_two_sub_half_le_one d hd ht ht1
    have hzn : (1 + ‖(z₀ : ℂ)‖) ^ (2 : ℕ) ≤ 4 * t ^ (-(2 : ℝ)) := by
      rw [hz₀]; exact one_add_norm_imagAxis_inv_sq_le ht ht1
    -- the common bounds on `t^{-2} e^{-π/t}`
    have hXexp : t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t)) ≤ K₀ * t ^ N := hK₀b t ht ht1
    -- ## `K_+`
    have hKP : ‖Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖
        ≤ (Cplus * 4 / cdiv) * (Work.Kernels.scale w) ^ Nplus * t ^ (-(2 : ℝ)) *
            Real.exp (-(Real.pi / t)) := by
      have hbP := hbp w z₀ hSw hz₁ hne
      rw [hSz₀] at hbP
      have hsplit : Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)
          = ((z₀ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)))⁻¹ *
            ((z₀ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) *
              Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hz₀ne), one_mul]
      have h1 : ‖Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖
          ≤ ‖(z₀ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) *
              Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖ := by
        conv_lhs => rw [hsplit]
        exact le_trans (norm_mul_le _ _) (mul_le_of_le_one_left (norm_nonneg _) hpowinv)
      have hnum : Cplus * (Work.Kernels.scale w) ^ Nplus * (1 + ‖(z₀ : ℂ)‖) ^ (2 : ℕ) *
              Real.exp (-(Real.pi * z₀.im)) ≤
            Cplus * (Work.Kernels.scale w) ^ Nplus * (4 * t ^ (-(2 : ℝ))) *
              Real.exp (-(Real.pi / t)) := by
        have hpos : 0 ≤ Cplus * (Work.Kernels.scale w) ^ Nplus :=
          mul_nonneg hCplus.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nplus)
        rw [hz₀im, show Real.exp (-(Real.pi * t⁻¹)) = Real.exp (-(Real.pi / t)) by
          rw [div_eq_mul_inv]]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzn hpos)
          (Real.exp_nonneg _)
      have hlast : Cplus * (Work.Kernels.scale w) ^ Nplus * (1 + ‖(z₀ : ℂ)‖) ^ (2 : ℕ) *
              Real.exp (-(Real.pi * z₀.im)) /
              ‖Work.Kernels.DeltaFun z₀ *
                (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀)‖
            ≤ (Cplus * 4 / cdiv) * (Work.Kernels.scale w) ^ Nplus * t ^ (-(2 : ℝ)) *
              Real.exp (-(Real.pi / t)) := by
        have ha : 0 ≤ Cplus * (Work.Kernels.scale w) ^ Nplus * (4 * t ^ (-(2 : ℝ))) *
            Real.exp (-(Real.pi / t)) :=
          mul_nonneg (mul_nonneg (mul_nonneg hCplus.le
            (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nplus))
            (mul_nonneg (by norm_num) (Real.rpow_nonneg ht.le _))) (Real.exp_nonneg _)
        have h1' := div_le_div₀ ha hnum hcdiv hden
        have h2' : (Cplus * (Work.Kernels.scale w) ^ Nplus * (4 * t ^ (-(2 : ℝ))) *
              Real.exp (-(Real.pi / t))) / cdiv
            = (Cplus * 4 / cdiv) * (Work.Kernels.scale w) ^ Nplus * t ^ (-(2 : ℝ)) *
              Real.exp (-(Real.pi / t)) := by ring
        exact h1'.trans h2'.le
      exact h1.trans (hbP.trans hlast)
    -- ## `K_-`
    have hKM : ‖Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖
        ≤ (Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ Nminus * t ^ (-(2 : ℝ)) *
            Real.exp (-(Real.pi / t)) := by
      have hbM := hbm w z₀ hSw hz₁ hne
      rw [hSz₀] at hbM
      have hsplit : Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)
          = ((z₀ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)))⁻¹ *
            ((z₀ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) *
              Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hz₀ne), one_mul]
      have h1 : ‖Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖
          ≤ ‖(z₀ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) *
              Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖ := by
        conv_lhs => rw [hsplit]
        exact le_trans (norm_mul_le _ _) (mul_le_of_le_one_left (norm_nonneg _) hpowinv)
      have hnum : Cminus * (Work.Kernels.scale w) ^ Nminus * (1 + ‖(z₀ : ℂ)‖) ^ (2 : ℕ) *
              Real.exp (-(Real.pi * z₀.im)) ≤
            Cminus * (Work.Kernels.scale w) ^ Nminus * (4 * t ^ (-(2 : ℝ))) *
              Real.exp (-(Real.pi / t)) := by
        have hpos : 0 ≤ Cminus * (Work.Kernels.scale w) ^ Nminus :=
          mul_nonneg hCminus.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nminus)
        rw [hz₀im, show Real.exp (-(Real.pi * t⁻¹)) = Real.exp (-(Real.pi / t)) by
          rw [div_eq_mul_inv]]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzn hpos)
          (Real.exp_nonneg _)
      have hlast : Cminus * (Work.Kernels.scale w) ^ Nminus * (1 + ‖(z₀ : ℂ)‖) ^ (2 : ℕ) *
              Real.exp (-(Real.pi * z₀.im)) /
              ‖Work.Kernels.DeltaFun z₀ *
                (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀)‖
            ≤ (Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ Nminus * t ^ (-(2 : ℝ)) *
              Real.exp (-(Real.pi / t)) := by
        have ha : 0 ≤ Cminus * (Work.Kernels.scale w) ^ Nminus * (4 * t ^ (-(2 : ℝ))) *
            Real.exp (-(Real.pi / t)) :=
          mul_nonneg (mul_nonneg (mul_nonneg hCminus.le
            (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nminus))
            (mul_nonneg (by norm_num) (Real.rpow_nonneg ht.le _))) (Real.exp_nonneg _)
        have h1' := div_le_div₀ ha hnum hcdiv hden
        have h2' : (Cminus * (Work.Kernels.scale w) ^ Nminus * (4 * t ^ (-(2 : ℝ))) *
              Real.exp (-(Real.pi / t))) / cdiv
            = (Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ Nminus * t ^ (-(2 : ℝ)) *
              Real.exp (-(Real.pi / t)) := by ring
        exact h1'.trans h2'.le
      exact h1.trans (hbM.trans hlast)
    -- ## combine `K_+` and `K_-` into `Kfun`
    have hKP' : ‖Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖
        ≤ (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t)) := by
      refine hKP.trans ?_
      have hc : Cplus * 4 / cdiv ≤ max Cplus Cminus * 4 / cdiv :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by norm_num))
          hcdiv.le
      have hs : (Work.Kernels.scale w) ^ Nplus
          ≤ (Work.Kernels.scale w) ^ (max Nplus Nminus) :=
        Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_left _ _)
      have hprod : (Cplus * 4 / cdiv) * (Work.Kernels.scale w) ^ Nplus
          ≤ (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) :=
        mul_le_mul hc hs (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nplus) hCfar0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg ht.le _)) (Real.exp_nonneg _)
    have hKM' : ‖Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖
        ≤ (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t)) := by
      refine hKM.trans ?_
      have hc : Cminus * 4 / cdiv ≤ max Cplus Cminus * 4 / cdiv :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by norm_num))
          hcdiv.le
      have hs : (Work.Kernels.scale w) ^ Nminus
          ≤ (Work.Kernels.scale w) ^ (max Nplus Nminus) :=
        Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_right _ _)
      have hprod : (Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ Nminus
          ≤ (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) :=
        mul_le_mul hc hs (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nminus) hCfar0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg ht.le _)) (Real.exp_nonneg _)
    have hKfun : ‖Work.Kernels.Kfun ℓ d w (Work.Kernels.imagAxis t ht)‖
        ≤ (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t)) := by
      rw [Work.Kernels.Kfun, norm_div, show ‖((2 : ℂ))‖ = 2 from by norm_num]
      calc ‖Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht) +
              Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖ / 2
          ≤ (‖Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖ +
              ‖Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖) / 2 :=
              div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
        _ ≤ (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
              t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t)) := by
              linarith [hKP', hKM']
    -- ## absorb `t^{-2} e^{-π/t}` into `t^N` and enlarge the constants
    have hsmax : (Work.Kernels.scale w) ^ (max Nplus Nminus)
        ≤ (Work.Kernels.scale w) ^ (max N₁ (max Nplus Nminus)) :=
      Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_right _ _)
    have hstep1b : (max Cplus Cminus * 4 / cdiv) *
            (Work.Kernels.scale w) ^ (max Nplus Nminus) * t ^ (-(2 : ℝ)) *
            Real.exp (-(Real.pi / t))
        = (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            (t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t))) := by ring
    have hstep1a : (max Cplus Cminus * 4 / cdiv) *
            (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            (t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t)))
        ≤ (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            (K₀ * t ^ N) :=
      mul_le_mul_of_nonneg_left hXexp
        (mul_nonneg hCfar0 (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
    have hstep2 : (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            (K₀ * t ^ N)
        = (max Cplus Cminus * 4 / cdiv * K₀) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            t ^ N := by ring
    have hstep3 : (max Cplus Cminus * 4 / cdiv * K₀) *
            (Work.Kernels.scale w) ^ (max Nplus Nminus) * t ^ N
        ≤ max c₁ (max Cplus Cminus * 4 / cdiv * K₀) *
            (Work.Kernels.scale w) ^ (max N₁ (max Nplus Nminus)) * t ^ N := by
      have hAB : (max Cplus Cminus * 4 / cdiv * K₀) *
            (Work.Kernels.scale w) ^ (max Nplus Nminus)
          ≤ max c₁ (max Cplus Cminus * 4 / cdiv * K₀) *
            (Work.Kernels.scale w) ^ (max N₁ (max Nplus Nminus)) :=
        mul_le_mul (le_max_right _ _) hsmax (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
          (le_trans hCK0 (le_max_right _ _))
      exact mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg ht.le N)
    calc ‖Work.Kernels.Kfun ℓ d w (Work.Kernels.imagAxis t ht)‖
        ≤ (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t)) := hKfun
      _ = (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            (t ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / t))) := hstep1b
      _ ≤ (max Cplus Cminus * 4 / cdiv) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            (K₀ * t ^ N) := hstep1a
      _ = (max Cplus Cminus * 4 / cdiv * K₀) * (Work.Kernels.scale w) ^ (max Nplus Nminus) *
            t ^ N := hstep2
      _ ≤ max c₁ (max Cplus Cminus * 4 / cdiv * K₀) *
            (Work.Kernels.scale w) ^ (max N₁ (max Nplus Nminus)) * t ^ N := hstep3

end Work.Asymptotics
