/-
# The bracket of `K_-^{(8)}` on the imaginary axis: polynomial growth in `τ` and `t`

`Work.Residues.bracket8 ℓ z τ` is the bracket of `KMinus8_eq`, i.e. the numerator of
`K_-^{(8)}(τ,z) = bracket8 ℓ z τ / (2·1728·π·Δ(z)·(j τ - j z))` (see `KMinusCuspDefs`).

This file bounds `bracket8` at the contour points `z = i t` (with `t ≥ 1`) uniformly in `τ`
on the half-plane `{Im τ ≥ H}`: there are `C > 0`, `N, M ≥ 0` and `H ≥ 0` with

  `‖bracket8 ℓ (i t) τ‖ ≤ C · (scale τ)^N · (1+t)^M`     for `Im τ ≥ H`, `t ≥ 1`.

Two ingredients enter.  For the `τ`-side, `Γ = Gamm ℓ` and `Λ = Lamb ℓ` are the two
brackets of the `K_-` decomposition; `Work.Residues.Gamma_cusp` and
`Work.Residues.Lamb_cusp` (proved in `KMinusCuspDefs` from the cusp-vanishing of
`P₁, P₂, Q₁, Q₂` and the two-sided bound on `Δ`) give `‖Γ τ‖, ‖Λ τ‖ ≤ C (1 + ‖τ‖)` for
large `Im τ`, and `1 + ‖τ‖ ≤ 2 · scale τ`.  For the `z`-side we use the boundedness of
`E₄, E₆, W, U, V` on `{Im ≥ 1}` (`Work.Asymptotics.E4Fun_bound`, `E6Fun_bound`,
`Work.Residues.UFun_decay`, `WFun_decay`, `VFun_decay`) together with the moderate growth
of `ℓ.L` (`LogLambdaData.memP`).
-/
import Mathlib
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Residues

set_option maxHeartbeats 2000000

/-- The norm of a fourfold product. -/
private lemma nrm4 (a b c d : ℂ) : ‖a * b * (c * d)‖ = ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
  rw [norm_mul, norm_mul, norm_mul]; ring

/-- Pad a nonnegative quantity by a factor `≥ 1`. -/
private lemma le_mul_of_one_le_right' {x s : ℝ} (hx : 0 ≤ x) (hs : 1 ≤ s) : x ≤ x * s := by
  nlinarith [hx, hs]

theorem bracket8_axis_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ H C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ 0 ≤ H ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), H ≤ τ.im → 1 ≤ t →
        ‖Work.Residues.bracket8 ℓ (Work.Kernels.imagAxis t ht) τ‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨Hg, Cg, hCg, hG⟩ := Work.Residues.Gamma_cusp ℓ
  obtain ⟨Hl, Cl, hCl, hL⟩ := Work.Residues.Lamb_cusp ℓ
  obtain ⟨C4, hC4, hE4⟩ := Work.Asymptotics.E4Fun_bound
  obtain ⟨C6, hC6, hE6⟩ := Work.Asymptotics.E6Fun_bound
  obtain ⟨CW, hCW, hW⟩ := Work.Residues.WFun_decay
  obtain ⟨CU, hCU, hU⟩ := Work.Residues.UFun_decay
  obtain ⟨CV, hCV, hV⟩ := Work.Residues.VFun_decay
  obtain ⟨al, be, ga, hal, hbe, hga, hLmg⟩ := ℓ.memP
  refine ⟨max (max Hg Hl) 1,
    3456 * C4 * (C4 * C6) * (2 * al) + C4 ^ 2 * (CW + 1) * (2 * Cg)
      + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) + 1,
    1, max ga 1, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ 3456 * C4 * (C4 * C6) * (2 * al) := by
      apply mul_nonneg _ (by linarith)
      apply mul_nonneg _ (by positivity)
      apply mul_nonneg (by norm_num) hC4.le
    have h2 : (0:ℝ) ≤ C4 ^ 2 * (CW + 1) * (2 * Cg) := by positivity
    have h3 : (0:ℝ) ≤ C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) := by positivity
    linarith
  · norm_num
  · positivity
  · exact le_trans zero_le_one (le_max_right _ _)
  · intro τ t ht hH ht1
    set z : UpperHalfPlane := Work.Kernels.imagAxis t ht with hzdef
    have hzim : z.im = t := by
      rw [hzdef]; simp [Work.Kernels.imagAxis]
    have hzcoe : (z : ℂ) = (t : ℂ) * Complex.I := by rw [hzdef]; rfl
    have hzn : ‖(z : ℂ)‖ = t := by
      rw [hzcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht]
    have hH1 : 1 ≤ τ.im := le_trans (le_max_right _ _) hH
    have hHg : Hg ≤ τ.im := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hH
    have hHl : Hl ≤ τ.im := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hH
    have hHz : 1 ≤ z.im := by rw [hzim]; exact ht1
    have hM : (0:ℝ) ≤ max ga 1 := le_trans zero_le_one (le_max_right _ _)
    have hP1 : 1 ≤ (1 + t) ^ max ga 1 := Real.one_le_rpow (by linarith) hM
    have hP0 : 0 ≤ (1 + t) ^ max ga 1 := le_trans zero_le_one hP1
    have hLz : ‖ℓ.L z‖ ≤ 2 * al * (1 + t) ^ max ga 1 := by
      have h := hLmg z (Set.mem_univ z)
      rw [hzim, hzn] at h
      have hinv0 : (0:ℝ) ≤ t⁻¹ := by positivity
      have hinv1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
      have hb : t⁻¹ ^ be ≤ 1 := Real.rpow_le_one hinv0 hinv1 hbe
      have hgt : t ^ ga ≤ (1 + t) ^ ga := Real.rpow_le_rpow ht.le (by linarith) hga
      have hgm : (1 + t) ^ ga ≤ (1 + t) ^ max ga 1 :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left ga 1)
      have hsum : t⁻¹ ^ be + t ^ ga ≤ 2 * (1 + t) ^ max ga 1 := by linarith
      calc ‖ℓ.L z‖ ≤ al * (t⁻¹ ^ be + t ^ ga) := h
        _ ≤ al * (2 * (1 + t) ^ max ga 1) := mul_le_mul_of_nonneg_left hsum hal
        _ = 2 * al * (1 + t) ^ max ga 1 := by ring
    have hexp_le : Real.exp (-(Real.pi * z.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff, hzim]; nlinarith [Real.pi_pos, ht1]
    have hWz0 : ‖Work.Kernels.WFun z - 1‖ ≤ CW := by
      calc ‖Work.Kernels.WFun z - 1‖ ≤ CW * Real.exp (-(Real.pi * z.im)) := hW z hHz
        _ ≤ CW * 1 := mul_le_mul_of_nonneg_left hexp_le hCW.le
        _ = CW := by ring
    have hWz : ‖Work.Kernels.WFun z‖ ≤ CW + 1 := by
      have h := norm_add_le (Work.Kernels.WFun z - 1) (1:ℂ)
      rw [sub_add_cancel, norm_one] at h
      linarith
    have hUz0 : ‖Work.Kernels.UFun z - 1‖ ≤ CU := by
      calc ‖Work.Kernels.UFun z - 1‖ ≤ CU * Real.exp (-(Real.pi * z.im)) := hU z hHz
        _ ≤ CU * 1 := mul_le_mul_of_nonneg_left hexp_le hCU.le
        _ = CU := by ring
    have hUz : ‖Work.Kernels.UFun z‖ ≤ 1 + CU := by
      have h := norm_add_le (Work.Kernels.UFun z - 1) (1:ℂ)
      rw [sub_add_cancel, norm_one] at h
      linarith
    have hVz : ‖Work.Kernels.VFun z‖ ≤ CV := by
      calc ‖Work.Kernels.VFun z‖ ≤ CV * Real.exp (-(Real.pi * z.im)) := hV z hHz
        _ ≤ CV * 1 := mul_le_mul_of_nonneg_left hexp_le hCV.le
        _ = CV := by ring
    have hE4z : ‖Work.Kernels.E4Fun z‖ ≤ C4 := hE4 z hHz
    have hE6z : ‖Work.Kernels.E6Fun z‖ ≤ C6 := hE6 z hHz
    have hE4τ : ‖Work.Kernels.E4Fun τ‖ ≤ C4 := hE4 τ hH1
    have hE10 : ‖Work.Kernels.E10Fun z‖ ≤ C4 * C6 := by
      show ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z‖ ≤ C4 * C6
      rw [norm_mul]
      exact mul_le_mul hE4z hE6z (norm_nonneg _) hC4.le
    have hUV : ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖
        ≤ (1 + CU) ^ 2 + CV ^ 2 := by
      have h := norm_sub_le (Work.Kernels.UFun z ^ 2) (Work.Kernels.VFun z ^ 2)
      have h1 : ‖Work.Kernels.UFun z ^ 2‖ ≤ (1 + CU) ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hUz 2
      have h2 : ‖Work.Kernels.VFun z ^ 2‖ ≤ CV ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hVz 2
      linarith
    have hGτ : ‖Work.Residues.Gamm ℓ τ‖ ≤ 2 * Cg * Work.Kernels.scale τ := by
      have h1 : ‖Work.Residues.Gamm ℓ τ‖ ≤ Cg * (1 + ‖(τ:ℂ)‖) := by simpa using hG τ hHg
      have hs := Work.Kernels.coe_norm_le_scale τ
      have hs1 := Work.Kernels.one_le_scale τ
      calc ‖Work.Residues.Gamm ℓ τ‖ ≤ Cg * (1 + ‖(τ:ℂ)‖) := h1
        _ ≤ Cg * (2 * Work.Kernels.scale τ) :=
            mul_le_mul_of_nonneg_left (by linarith) hCg.le
        _ = 2 * Cg * Work.Kernels.scale τ := by ring
    have hLτ : ‖Work.Residues.Lamb ℓ τ‖ ≤ 2 * Cl * Work.Kernels.scale τ := by
      have h1 : ‖Work.Residues.Lamb ℓ τ‖ ≤ Cl * (1 + ‖(τ:ℂ)‖) := by simpa using hL τ hHl
      have hs := Work.Kernels.coe_norm_le_scale τ
      have hs1 := Work.Kernels.one_le_scale τ
      calc ‖Work.Residues.Lamb ℓ τ‖ ≤ Cl * (1 + ‖(τ:ℂ)‖) := h1
        _ ≤ Cl * (2 * Work.Kernels.scale τ) :=
            mul_le_mul_of_nonneg_left (by linarith) hCl.le
        _ = 2 * Cl * Work.Kernels.scale τ := by ring
    have hsc : (0:ℝ) ≤ Work.Kernels.scale τ := by linarith [Work.Kernels.one_le_scale τ]
    have hbr : Work.Residues.bracket8 ℓ z τ
        = (-3456 : ℂ) * Work.Kernels.E4Fun τ * (Work.Kernels.E10Fun z * ℓ.L z)
          + (Work.Kernels.E8Fun z * Work.Kernels.WFun z) * Work.Residues.Gamm ℓ τ
          + (Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
              * Work.Residues.Lamb ℓ τ := by
      simp only [Work.Residues.bracket8, Work.Kernels.c1728]
      ring
    have hA : ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * (Work.Kernels.E10Fun z * ℓ.L z)‖
        ≤ 3456 * C4 * (C4 * C6) * (2 * al) * Work.Kernels.scale τ * (1 + t) ^ max ga 1 := by
      have h1 : ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * (Work.Kernels.E10Fun z * ℓ.L z)‖
          = 3456 * ‖Work.Kernels.E4Fun τ‖ * ‖Work.Kernels.E10Fun z‖ * ‖ℓ.L z‖ := by
        rw [nrm4]; norm_num
      rw [h1]
      have hstep : 3456 * ‖Work.Kernels.E4Fun τ‖ * ‖Work.Kernels.E10Fun z‖ * ‖ℓ.L z‖
          ≤ 3456 * C4 * (C4 * C6) * (2 * al * (1 + t) ^ max ga 1) := by
        have h2 : 3456 * ‖Work.Kernels.E4Fun τ‖ * ‖Work.Kernels.E10Fun z‖
            ≤ 3456 * C4 * (C4 * C6) := by
          have ha : 3456 * ‖Work.Kernels.E4Fun τ‖ ≤ 3456 * C4 :=
            mul_le_mul_of_nonneg_left hE4τ (by norm_num)
          have hb : (0:ℝ) ≤ 3456 * C4 := by positivity
          calc 3456 * ‖Work.Kernels.E4Fun τ‖ * ‖Work.Kernels.E10Fun z‖
              ≤ (3456 * C4) * (C4 * C6) := mul_le_mul ha hE10 (norm_nonneg _) hb
            _ = 3456 * C4 * (C4 * C6) := by ring
        exact mul_le_mul h2 hLz (norm_nonneg _) (by positivity)
      calc 3456 * ‖Work.Kernels.E4Fun τ‖ * ‖Work.Kernels.E10Fun z‖ * ‖ℓ.L z‖
          ≤ 3456 * C4 * (C4 * C6) * (2 * al * (1 + t) ^ max ga 1) := hstep
        _ ≤ 3456 * C4 * (C4 * C6) * (2 * al * (1 + t) ^ max ga 1) * Work.Kernels.scale τ :=
            le_mul_of_one_le_right'
              (mul_nonneg (by positivity) (mul_nonneg (by linarith) hP0))
              (by linarith [Work.Kernels.one_le_scale τ])
        _ = 3456 * C4 * (C4 * C6) * (2 * al) * Work.Kernels.scale τ * (1 + t) ^ max ga 1 := by
            ring
    have hB : ‖(Work.Kernels.E8Fun z * Work.Kernels.WFun z) * Work.Residues.Gamm ℓ τ‖
        ≤ C4 ^ 2 * (CW + 1) * (2 * Cg) * Work.Kernels.scale τ * (1 + t) ^ max ga 1 := by
      have hE8 : ‖Work.Kernels.E8Fun z‖ ≤ C4 ^ 2 := by
        show ‖Work.Kernels.E4Fun z ^ 2‖ ≤ C4 ^ 2
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4z 2
      have hEW : ‖Work.Kernels.E8Fun z * Work.Kernels.WFun z‖ ≤ C4 ^ 2 * (CW + 1) := by
        rw [norm_mul]
        exact mul_le_mul hE8 hWz (norm_nonneg _) (by positivity)
      have hstep : ‖(Work.Kernels.E8Fun z * Work.Kernels.WFun z) * Work.Residues.Gamm ℓ τ‖
          ≤ C4 ^ 2 * (CW + 1) * (2 * Cg) * Work.Kernels.scale τ := by
        calc ‖(Work.Kernels.E8Fun z * Work.Kernels.WFun z) * Work.Residues.Gamm ℓ τ‖
            = ‖Work.Kernels.E8Fun z * Work.Kernels.WFun z‖ * ‖Work.Residues.Gamm ℓ τ‖ := by
              rw [norm_mul]
          _ ≤ (C4 ^ 2 * (CW + 1)) * (2 * Cg * Work.Kernels.scale τ) :=
              mul_le_mul hEW hGτ (norm_nonneg _) (by positivity)
          _ = C4 ^ 2 * (CW + 1) * (2 * Cg) * Work.Kernels.scale τ := by ring
      calc ‖(Work.Kernels.E8Fun z * Work.Kernels.WFun z) * Work.Residues.Gamm ℓ τ‖
          ≤ C4 ^ 2 * (CW + 1) * (2 * Cg) * Work.Kernels.scale τ := hstep
        _ ≤ C4 ^ 2 * (CW + 1) * (2 * Cg) * Work.Kernels.scale τ * (1 + t) ^ max ga 1 :=
            le_mul_of_one_le_right' (by positivity) hP1
    have hC : ‖(Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
        * Work.Residues.Lamb ℓ τ‖
        ≤ C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) * Work.Kernels.scale τ
          * (1 + t) ^ max ga 1 := by
      have hEUV : ‖Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)‖
          ≤ C6 * ((1 + CU) ^ 2 + CV ^ 2) := by
        rw [norm_mul]
        exact mul_le_mul hE6z hUV (norm_nonneg _) (by positivity)
      have hstep :
          ‖(Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
            * Work.Residues.Lamb ℓ τ‖
          ≤ C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) * Work.Kernels.scale τ := by
        calc ‖(Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
              * Work.Residues.Lamb ℓ τ‖
            = ‖Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)‖
              * ‖Work.Residues.Lamb ℓ τ‖ := by rw [norm_mul]
          _ ≤ (C6 * ((1 + CU) ^ 2 + CV ^ 2)) * (2 * Cl * Work.Kernels.scale τ) :=
              mul_le_mul hEUV hLτ (norm_nonneg _) (by positivity)
          _ = C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) * Work.Kernels.scale τ := by ring
      calc ‖(Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
            * Work.Residues.Lamb ℓ τ‖
          ≤ C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) * Work.Kernels.scale τ := hstep
        _ ≤ C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) * Work.Kernels.scale τ
              * (1 + t) ^ max ga 1 :=
            le_mul_of_one_le_right' (by positivity) hP1
    rw [hbr]
    have hs1 := norm_add_le ((-3456 : ℂ) * Work.Kernels.E4Fun τ * (Work.Kernels.E10Fun z * ℓ.L z)
        + (Work.Kernels.E8Fun z * Work.Kernels.WFun z) * Work.Residues.Gamm ℓ τ)
      ((Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
        * Work.Residues.Lamb ℓ τ)
    have hs2 := norm_add_le ((-3456 : ℂ) * Work.Kernels.E4Fun τ * (Work.Kernels.E10Fun z * ℓ.L z))
      ((Work.Kernels.E8Fun z * Work.Kernels.WFun z) * Work.Residues.Gamm ℓ τ)
    have h33 : ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * (Work.Kernels.E10Fun z * ℓ.L z)
          + (Work.Kernels.E8Fun z * Work.Kernels.WFun z) * Work.Residues.Gamm ℓ τ
          + (Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
              * Work.Residues.Lamb ℓ τ‖
        ≤ (3456 * C4 * (C4 * C6) * (2 * al) * Work.Kernels.scale τ
            * (1 + t) ^ max ga 1
          + C4 ^ 2 * (CW + 1) * (2 * Cg) * Work.Kernels.scale τ * (1 + t) ^ max ga 1
          + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) * Work.Kernels.scale τ
            * (1 + t) ^ max ga 1) := by
      linarith [hs1, hs2, hA, hB, hC]
    have hbar : (3456 * C4 * (C4 * C6) * (2 * al) * Work.Kernels.scale τ * (1 + t) ^ max ga 1
          + C4 ^ 2 * (CW + 1) * (2 * Cg) * Work.Kernels.scale τ * (1 + t) ^ max ga 1
          + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) * Work.Kernels.scale τ
            * (1 + t) ^ max ga 1)
        = (3456 * C4 * (C4 * C6) * (2 * al) + C4 ^ 2 * (CW + 1) * (2 * Cg)
            + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl))
          * (Work.Kernels.scale τ * (1 + t) ^ max ga 1) := by ring
    have hsp : (0:ℝ) ≤ Work.Kernels.scale τ * (1 + t) ^ max ga 1 := mul_nonneg hsc hP0
    have h44 : (3456 * C4 * (C4 * C6) * (2 * al) + C4 ^ 2 * (CW + 1) * (2 * Cg)
            + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl))
          * (Work.Kernels.scale τ * (1 + t) ^ max ga 1)
        ≤ (3456 * C4 * (C4 * C6) * (2 * al) + C4 ^ 2 * (CW + 1) * (2 * Cg)
            + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) + 1)
          * (Work.Kernels.scale τ * (1 + t) ^ max ga 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hsp
    calc ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * (Work.Kernels.E10Fun z * ℓ.L z)
          + (Work.Kernels.E8Fun z * Work.Kernels.WFun z) * Work.Residues.Gamm ℓ τ
          + (Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
              * Work.Residues.Lamb ℓ τ‖
        ≤ (3456 * C4 * (C4 * C6) * (2 * al) * Work.Kernels.scale τ * (1 + t) ^ max ga 1
          + C4 ^ 2 * (CW + 1) * (2 * Cg) * Work.Kernels.scale τ * (1 + t) ^ max ga 1
          + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) * Work.Kernels.scale τ
            * (1 + t) ^ max ga 1) := h33
      _ = (3456 * C4 * (C4 * C6) * (2 * al) + C4 ^ 2 * (CW + 1) * (2 * Cg)
            + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl))
          * (Work.Kernels.scale τ * (1 + t) ^ max ga 1) := hbar
      _ ≤ (3456 * C4 * (C4 * C6) * (2 * al) + C4 ^ 2 * (CW + 1) * (2 * Cg)
            + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) + 1)
          * (Work.Kernels.scale τ * (1 + t) ^ max ga 1) := h44
      _ = (3456 * C4 * (C4 * C6) * (2 * al) + C4 ^ 2 * (CW + 1) * (2 * Cg)
            + C6 * ((1 + CU) ^ 2 + CV ^ 2) * (2 * Cl) + 1)
          * (Work.Kernels.scale τ) ^ (1:ℝ) * (1 + t) ^ max ga 1 := by
          rw [Real.rpow_one]; ring

end Work.Residues
