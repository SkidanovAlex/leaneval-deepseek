import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.growthPrefactor_lower_atZero
import Submission.Work.Asymptotics.norm_Eisenstein_imagAxis_atZero
import Submission.Work.Asymptotics.norm_theta_imagAxis_atZero
import Submission.Work.Asymptotics.norm_L_imagAxis_atZero

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup

noncomputable section

set_option maxHeartbeats 8000000

/-! ## Elementary facts about the imaginary axis and the closed ball -/

private lemma norm_imagAxis_coe (t : ℝ) (ht : 0 < t) :
    ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := by
  show ‖(t : ℂ) * Complex.I‖ = t
  rw [norm_mul, Complex.norm_I, mul_one]
  have hsq : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  nlinarith [hsq, norm_nonneg (t : ℂ), ht]

private lemma imagAxis_im' (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).im = t := by
  show ((t : ℂ) * Complex.I).im = t
  simp

private lemma coe_norm_le_closedBall (τ₀ : UpperHalfPlane) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ‖(τ : ℂ)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (x := τ₀) (r := R)).exists_bound_of_continuousOn
    (UpperHalfPlane.continuous_coe.norm).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun τ hτ => ?_⟩
  have h := hM τ hτ
  have h' : ‖(τ : ℂ)‖ ≤ M := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (τ : ℂ))] using h
  exact le_trans h' (le_max_left _ _)

private lemma scale_le_closedBall (τ₀ : UpperHalfPlane) {R : ℝ} (hR : 0 ≤ R) :
    ∃ S₀ : ℝ, 1 ≤ S₀ ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → Work.Kernels.scale τ ≤ S₀ := by
  obtain ⟨τm, _, hτm_min⟩ :=
    (isCompact_closedBall (x := τ₀) (r := R)).exists_isMinOn
      ⟨τ₀, Metric.mem_closedBall_self hR⟩ UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨M, _, hM⟩ := coe_norm_le_closedBall τ₀ hR
  refine ⟨max 1 (1 + (τm.im)⁻¹ + M), le_max_left _ _, fun τ hτ => ?_⟩
  have him : τm.im ≤ τ.im := hτm_min hτ
  have h1 : (τ.im)⁻¹ ≤ (τm.im)⁻¹ := (inv_le_inv₀ τ.im_pos τm.im_pos).mpr him
  have h2 : ‖(τ : ℂ)‖ ≤ M := hM τ hτ
  have h3 : Work.Kernels.scale τ = 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := rfl
  rw [h3]
  linarith [le_max_right (1 : ℝ) (1 + (τm.im)⁻¹ + M)]

private lemma bound_of_moderate {τ₀ : UpperHalfPlane} {R : ℝ} {F : UpperHalfPlane → ℂ}
    (hF : Work.Kernels.ModerateGrowthOn Set.univ F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ‖F τ‖ ≤ C := by
  by_cases hR : 0 ≤ R
  · obtain ⟨S₀, hS₀1, hS₀⟩ := scale_le_closedBall τ₀ hR
    obtain ⟨α, N, hα, hN, hb⟩ := (Work.Kernels.moderateGrowthOn_iff_scale Set.univ F).mp hF
    refine ⟨α * S₀ ^ N, mul_nonneg hα (Real.rpow_nonneg (by linarith) N), fun τ hτ => ?_⟩
    refine le_trans (hb τ (Set.mem_univ τ)) (mul_le_mul_of_nonneg_left ?_ hα)
    exact Real.rpow_le_rpow (by linarith [Work.Kernels.one_le_scale τ]) (hS₀ τ hτ) hN
  · push Not at hR
    refine ⟨0, le_refl 0, fun τ hτ => ?_⟩
    exfalso
    linarith [dist_nonneg (x := τ) (y := τ₀), hτ, hR]

/-! ## Two elementary arithmetic lemmas -/

private lemma inv_pow_le_inv_pow' {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    ((t : ℝ) ^ m)⁻¹ ≤ ((t : ℝ) ^ n)⁻¹ := by
  have h : t ^ n ≤ t ^ m := pow_le_pow_of_le_one ht.le ht1 hmn
  have := one_div_le_one_div_of_le (a := t ^ n) (b := t ^ m) (pow_pos ht n) h
  simpa only [one_div] using this

private lemma exp_neg_mul_exp_pos (a : ℝ) : Real.exp (-a) * Real.exp a = 1 := by
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-! ## The combination `U² - V²` at the cusp `t → 0` -/

private lemma norm_UFun_sq_sub_VFun_sq_imagAxis :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
      ‖Work.Kernels.UFun (Work.Kernels.imagAxis t ht) ^ 2 -
        Work.Kernels.VFun (Work.Kernels.imagAxis t ht) ^ 2‖ ≤ C * ((t : ℝ) ^ 4)⁻¹ := by
  obtain ⟨CU, hCU, hUd⟩ := Work.Residues.UFun_decay
  obtain ⟨CW, hCW, hWd⟩ := Work.Residues.WFun_decay
  refine ⟨(1 + CU) ^ 2 + (1 + CW) ^ 2, 1, by positivity, one_pos, ?_⟩
  intro t ht ht1
  set z : UpperHalfPlane := Work.Kernels.imagAxis t ht with hz
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have hS : ModularGroup.S • z = Work.Kernels.imagAxis t⁻¹ hti := by
    rw [hz]; exact imagAxis_smul_S t ht
  have him : (Work.Kernels.imagAxis t⁻¹ hti).im = t⁻¹ := imagAxis_im' t⁻¹ hti
  have him1 : 1 ≤ (Work.Kernels.imagAxis t⁻¹ hti).im := by
    rw [him]; exact (one_le_inv₀ ht).mpr ht1
  have hU1 : ‖Work.Kernels.UFun (Work.Kernels.imagAxis t⁻¹ hti)‖ ≤ 1 + CU := by
    have h := hUd _ him1
    have hexp1 : Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 < Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im :=
        mul_pos Real.pi_pos (lt_of_lt_of_le zero_lt_one him1)
      linarith
    have h2 := norm_sub_norm_le 1 (Work.Kernels.UFun (Work.Kernels.imagAxis t⁻¹ hti))
    rw [norm_one] at h2
    have h3 : CU * Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) ≤ CU := by
      calc CU * Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) ≤ CU * 1 :=
            mul_le_mul_of_nonneg_left hexp1 hCU.le
        _ = CU := mul_one CU
    have h4 : ‖Work.Kernels.UFun (Work.Kernels.imagAxis t⁻¹ hti)‖ - 1
        ≤ ‖Work.Kernels.UFun (Work.Kernels.imagAxis t⁻¹ hti) - 1‖ := by
      have h5 := norm_sub_norm_le (Work.Kernels.UFun (Work.Kernels.imagAxis t⁻¹ hti)) (1 : ℂ)
      rw [norm_one] at h5
      exact h5
    linarith [h, h3, h4]
  have hW1 : ‖Work.Kernels.WFun (Work.Kernels.imagAxis t⁻¹ hti)‖ ≤ 1 + CW := by
    have h := hWd _ him1
    have hexp1 : Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 < Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im :=
        mul_pos Real.pi_pos (lt_of_lt_of_le zero_lt_one him1)
      linarith
    have h2 := norm_sub_norm_le 1 (Work.Kernels.WFun (Work.Kernels.imagAxis t⁻¹ hti))
    rw [norm_one] at h2
    have h3 : CW * Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) ≤ CW := by
      calc CW * Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) ≤ CW * 1 :=
            mul_le_mul_of_nonneg_left hexp1 hCW.le
        _ = CW := mul_one CW
    have h4 : ‖Work.Kernels.WFun (Work.Kernels.imagAxis t⁻¹ hti)‖ - 1
        ≤ ‖Work.Kernels.WFun (Work.Kernels.imagAxis t⁻¹ hti) - 1‖ := by
      have h5 := norm_sub_norm_le (Work.Kernels.WFun (Work.Kernels.imagAxis t⁻¹ hti)) (1 : ℂ)
      rw [norm_one] at h5
      exact h5
    linarith [h, h3, h4]
  have hkey : (z : ℂ) ^ 4 * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
      = Work.Kernels.UFun (ModularGroup.S • z) ^ 2 - Work.Kernels.WFun (ModularGroup.S • z) ^ 2 := by
    rw [Work.Kernels.KernelFacts.UFun_S_smul z, Work.Kernels.KernelFacts.WFun_S_smul z]
    ring
  have hz4 : ‖(z : ℂ) ^ 4‖ = t ^ 4 := by
    rw [norm_pow, hz, norm_imagAxis_coe t ht]
  have hmul : t ^ 4 * ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖
      = ‖Work.Kernels.UFun (ModularGroup.S • z) ^ 2 - Work.Kernels.WFun (ModularGroup.S • z) ^ 2‖ := by
    rw [← hkey, norm_mul, hz4]
  have hB : ‖Work.Kernels.UFun (ModularGroup.S • z) ^ 2 - Work.Kernels.WFun (ModularGroup.S • z) ^ 2‖
      ≤ (1 + CU) ^ 2 + (1 + CW) ^ 2 := by
    rw [hS]
    have h0 := norm_sub_le (Work.Kernels.UFun (Work.Kernels.imagAxis t⁻¹ hti) ^ 2)
      (Work.Kernels.WFun (Work.Kernels.imagAxis t⁻¹ hti) ^ 2)
    have h1 : ‖Work.Kernels.UFun (Work.Kernels.imagAxis t⁻¹ hti) ^ 2‖ ≤ (1 + CU) ^ 2 := by
      rw [norm_pow (Work.Kernels.UFun (Work.Kernels.imagAxis t⁻¹ hti)) 2]
      exact pow_le_pow_left₀ (norm_nonneg _) hU1 2
    have h2 : ‖Work.Kernels.WFun (Work.Kernels.imagAxis t⁻¹ hti) ^ 2‖ ≤ (1 + CW) ^ 2 := by
      rw [norm_pow (Work.Kernels.WFun (Work.Kernels.imagAxis t⁻¹ hti)) 2]
      exact pow_le_pow_left₀ (norm_nonneg _) hW1 2
    linarith
  have ht4 : 0 < t ^ 4 := pow_pos ht 4
  have hstep : t ^ 4 * ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖
      ≤ (1 + CU) ^ 2 + (1 + CW) ^ 2 := by rw [hmul]; exact hB
  calc ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖
      = ((t : ℝ) ^ 4)⁻¹ * (t ^ 4 * ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht4), one_mul]
    _ ≤ ((t : ℝ) ^ 4)⁻¹ * ((1 + CU) ^ 2 + (1 + CW) ^ 2) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr ht4.le)
    _ = ((1 + CU) ^ 2 + (1 + CW) ^ 2) * ((t : ℝ) ^ 4)⁻¹ := by ring

/-! ## The cleared coefficient matrices, entrywise -/

private def cP : ℂ := ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

private def cM : ℂ := ((2 : ℂ) * (1728 : ℂ) * (Real.pi : ℂ))⁻¹

private def M8 (J : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![J, 0, 1; -2 * J, -2, 0; 1, 0, 0]

private def colP8 (J : ℂ) : Fin 3 → ℝ := ![2 * ‖J‖ + 1, 2, 1]

private def Mm (jτ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(2 * (1728 : ℂ)), 0, 0; 0, 1, -1; 0, (1728 : ℂ) - jτ, jτ]

private def colM8 (jτ : ℂ) : Fin 3 → ℝ := ![(2 : ℝ) * 1728, 1729 + ‖jτ‖, 1 + ‖jτ‖]

private lemma M8_col0 (J : ℂ) : ∀ i : Fin 3, ‖M8 J i 0‖ ≤ 2 * ‖J‖ + 1 := by
  intro i
  fin_cases i <;> norm_num [M8, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val] <;> linarith [norm_nonneg J]

private lemma M8_col1 (J : ℂ) : ∀ i : Fin 3, ‖M8 J i 1‖ ≤ 2 := by
  intro i
  fin_cases i <;> norm_num [M8, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val]

private lemma M8_col2 (J : ℂ) : ∀ i : Fin 3, ‖M8 J i 2‖ ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [M8, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val]

private lemma Mm_col0 (jτ : ℂ) : ∀ i : Fin 3, ‖Mm jτ i 0‖ ≤ 2 * 1728 := by
  intro i
  fin_cases i <;> norm_num [Mm, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val]

private lemma Mm_col1 (jτ : ℂ) : ∀ i : Fin 3, ‖Mm jτ i 1‖ ≤ 1729 + ‖jτ‖ := by
  intro i
  fin_cases i
  · norm_num [Mm, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]
    linarith [norm_nonneg jτ]
  · norm_num [Mm, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]
    linarith [norm_nonneg jτ]
  · norm_num [Mm, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]
    calc ‖(1728 : ℂ) - jτ‖ ≤ ‖(1728 : ℂ)‖ + ‖jτ‖ := norm_sub_le _ _
      _ = 1728 + ‖jτ‖ := by simp
      _ ≤ 1729 + ‖jτ‖ := by linarith

private lemma Mm_col2 (jτ : ℂ) : ∀ i : Fin 3, ‖Mm jτ i 2‖ ≤ 1 + ‖jτ‖ := by
  intro i
  fin_cases i <;> norm_num [Mm, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val] <;> linarith [norm_nonneg jτ]

private lemma norm_M8_le_colP8 (J : ℂ) : ∀ i j : Fin 3, ‖M8 J i j‖ ≤ colP8 J j := by
  intro i j
  fin_cases j
  · exact M8_col0 J i
  · exact M8_col1 J i
  · exact M8_col2 J i

private lemma norm_Mm_le_colM8 (jτ : ℂ) : ∀ i j : Fin 3, ‖Mm jτ i j‖ ≤ colM8 jτ j := by
  intro i j
  fin_cases j
  · exact Mm_col0 jτ i
  · exact Mm_col1 jτ i
  · exact Mm_col2 jτ i

private lemma UpsilonPlusClear8_entry (τ z : UpperHalfPlane) (i j : Fin 3) :
    Work.Kernels.UpsilonPlusClear 8 τ z i j =
      cP * (Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ) *
        M8 (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) i j *
        Work.Kernels.fk (![12, 10, 8] j) z := by
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, M8, cP,
    if_true, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  ring

private lemma UpsilonMinusClear8_entry (τ z : UpperHalfPlane) (i j : Fin 3) :
    Work.Kernels.UpsilonMinusClear 8 τ z i j =
      cM * (Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ) *
        Mm (Work.Kernels.jInvariantFun τ) i j *
        Work.Kernels.fk (![10, 8, 6] j) z := by
  simp only [Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Mm, cM,
    Work.Kernels.c1728, if_true, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.of_apply]
  ring_nf

private lemma norm_UpsilonPlusClear8_entry_le (τ z : UpperHalfPlane) (i j : Fin 3) :
    ‖Work.Kernels.UpsilonPlusClear 8 τ z i j‖ ≤ ‖cP‖ *
      ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ‖ *
      colP8 (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) j *
      ‖Work.Kernels.fk (![12, 10, 8] j) z‖ := by
  rw [UpsilonPlusClear8_entry, norm_mul, norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (norm_M8_le_colP8 _ i j) (by positivity)) (norm_nonneg _)

private lemma norm_UpsilonMinusClear8_entry_le (τ z : UpperHalfPlane) (i j : Fin 3) :
    ‖Work.Kernels.UpsilonMinusClear 8 τ z i j‖ ≤ ‖cM‖ *
      ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ‖ *
      colM8 (Work.Kernels.jInvariantFun τ) j *
      ‖Work.Kernels.fk (![10, 8, 6] j) z‖ := by
  rw [UpsilonMinusClear8_entry, norm_mul, norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (norm_Mm_le_colM8 _ i j) (by positivity)) (norm_nonneg _)

/-! ## The cleared kernels, bounded by the two factors -/

private lemma norm_KPlusClear8_le (τ z : UpperHalfPlane) :
    ‖Work.Kernels.KPlusClear 8 τ z‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      ‖Work.Kernels.phiVec τ i‖ *
        (‖cP‖ * ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ‖ *
          colP8 (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) j *
          ‖Work.Kernels.fk (![12, 10, 8] j) z‖) * ‖Work.Kernels.phitVec z j‖ := by
  rw [Work.Kernels.KPlusClear]
  refine le_trans (norm_sum_le Finset.univ _) ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine le_trans (norm_sum_le Finset.univ _) ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (norm_UpsilonPlusClear8_entry_le τ z i j) (norm_nonneg _)) (norm_nonneg _)

private lemma norm_KMinusClear8_le (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    ‖Work.Kernels.KMinusClear ℓ 8 τ z‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      ‖Work.Kernels.psiVec ℓ τ i‖ *
        (‖cM‖ * ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ‖ *
          colM8 (Work.Kernels.jInvariantFun τ) j *
          ‖Work.Kernels.fk (![10, 8, 6] j) z‖) * ‖Work.Kernels.psitVec ℓ z j‖ := by
  rw [Work.Kernels.KMinusClear]
  refine le_trans (norm_sum_le Finset.univ _) ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine le_trans (norm_sum_le Finset.univ _) ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (norm_UpsilonMinusClear8_entry_le τ z i j) (norm_nonneg _)) (norm_nonneg _)

private lemma sum_factor_three (a b : Fin 3 → ℝ) (c : ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, c * (a i * b j)) = c * (∑ i, a i) * (∑ j, b j) := by
  simp only [Fin.sum_univ_three]
  ring

private lemma KPlusClear8_le_cP (τ z : UpperHalfPlane) :
    ‖Work.Kernels.KPlusClear 8 τ z‖ ≤ ‖cP‖ *
      (∑ i : Fin 3, ‖Work.Kernels.phiVec τ i‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ‖) *
      (∑ j : Fin 3, colP8 (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) j *
        ‖Work.Kernels.fk (![12, 10, 8] j) z‖ * ‖Work.Kernels.phitVec z j‖) := by
  refine le_trans (norm_KPlusClear8_le τ z) ?_
  rw [show (∑ i : Fin 3, ∑ j : Fin 3, ‖Work.Kernels.phiVec τ i‖ *
        (‖cP‖ * ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ‖ *
          colP8 (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) j *
          ‖Work.Kernels.fk (![12, 10, 8] j) z‖) * ‖Work.Kernels.phitVec z j‖)
      = ∑ i : Fin 3, ∑ j : Fin 3, ‖cP‖ *
        ((‖Work.Kernels.phiVec τ i‖ *
          ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ‖) *
         (colP8 (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) j *
          ‖Work.Kernels.fk (![12, 10, 8] j) z‖ * ‖Work.Kernels.phitVec z j‖)) from
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))]
  exact le_of_eq (sum_factor_three _ _ _)

private lemma KMinusClear8_le_cM (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    ‖Work.Kernels.KMinusClear ℓ 8 τ z‖ ≤ ‖cM‖ *
      (∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ‖) *
      (∑ j : Fin 3, colM8 (Work.Kernels.jInvariantFun τ) j *
        ‖Work.Kernels.fk (![10, 8, 6] j) z‖ * ‖Work.Kernels.psitVec ℓ z j‖) := by
  refine le_trans (norm_KMinusClear8_le ℓ τ z) ?_
  rw [show (∑ i : Fin 3, ∑ j : Fin 3, ‖Work.Kernels.psiVec ℓ τ i‖ *
        (‖cM‖ * ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ‖ *
          colM8 (Work.Kernels.jInvariantFun τ) j *
          ‖Work.Kernels.fk (![10, 8, 6] j) z‖) * ‖Work.Kernels.psitVec ℓ z j‖)
      = ∑ i : Fin 3, ∑ j : Fin 3, ‖cM‖ *
        ((‖Work.Kernels.psiVec ℓ τ i‖ *
          ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ‖) *
         (colM8 (Work.Kernels.jInvariantFun τ) j *
          ‖Work.Kernels.fk (![10, 8, 6] j) z‖ * ‖Work.Kernels.psitVec ℓ z j‖)) from
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))]
  exact le_of_eq (sum_factor_three _ _ _)

/-! ## Bounds on the closed ball: the `τ`-side factors -/

private lemma norm_pi_coe : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
  have h := Complex.normSq_eq_norm_sq ((Real.pi : ℝ) : ℂ)
  rw [Complex.normSq_ofReal] at h
  have h2 : Real.pi ^ 2 = ‖((Real.pi : ℝ) : ℂ)‖ ^ 2 := by rw [← h]; ring
  nlinarith [h2, norm_nonneg ((Real.pi : ℝ) : ℂ), Real.pi_pos]

private lemma norm_three_I_div_pi_le : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ ≤ 3 := by
  have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, h3, norm_pi_coe, div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_three]

private lemma norm_six_I_div_pi_le : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ ≤ 6 := by
  have h6 : ‖(6 : ℂ)‖ = 6 := by norm_num
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, h6, norm_pi_coe, div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_three]

private lemma ball_data (ℓ : Work.Kernels.LogLambdaData) {τ₀ : UpperHalfPlane} {R : ℝ}
    (hR : 0 < R) :
    ∃ (Cphi Cpsi C4 C6 C14 Cj δ : ℝ), 0 ≤ Cphi ∧ 0 ≤ Cpsi ∧ 0 ≤ C4 ∧ 0 ≤ C6 ∧ 0 ≤ C14 ∧
      0 ≤ Cj ∧ 0 < δ ∧
      ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R →
        (∀ i : Fin 3, ‖Work.Kernels.phiVec τ i‖ ≤ Cphi) ∧
        (∀ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i‖ ≤ Cpsi) ∧
        ‖Work.Kernels.E4Fun τ‖ ≤ C4 ∧ ‖Work.Kernels.E6Fun τ‖ ≤ C6 ∧
        ‖Work.Kernels.E14Fun τ‖ ≤ C14 ∧ ‖Work.Kernels.jInvariantFun τ‖ ≤ Cj ∧
        δ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  have hRm : 0 ≤ R := hR.le
  obtain ⟨M, hM0, hM⟩ := coe_norm_le_closedBall τ₀ hRm
  obtain ⟨CE2, hCE20, hE2⟩ := bound_of_moderate (F := Work.Kernels.E2Fun)
    Work.Kernels.ClassicalFacts.E2Fun_mem_InP.2
  obtain ⟨CE4, hCE40, hE4⟩ := bound_of_moderate (F := Work.Kernels.E4Fun)
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP.2
  obtain ⟨CE6, hCE60, hE6⟩ := bound_of_moderate (F := Work.Kernels.E6Fun)
    Work.Kernels.ClassicalFacts.E6Fun_mem_InP.2
  obtain ⟨CE14, hCE140, hE14⟩ := bound_of_moderate
    (F := fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
    (Work.Kernels.InP.mul (Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.E4Fun_mem_InP 2)
      Work.Kernels.ClassicalFacts.E6Fun_mem_InP).2
  obtain ⟨CL, hCL0, hL⟩ := bound_of_moderate (F := ℓ.L) ℓ.memP
  obtain ⟨CLS, hCLS0, hLS⟩ := bound_of_moderate (F := ℓ.L_S) ℓ.memP_S
  have hUinP : Work.Kernels.InP (fun τ : UpperHalfPlane => Work.Kernels.theta00Fun τ ^ 4) :=
    Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta00Fun_mem_InP 4
  have hWinP : Work.Kernels.InP (fun τ : UpperHalfPlane => Work.Kernels.theta01Fun τ ^ 4) :=
    Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta01Fun_mem_InP 4
  have hVinP : Work.Kernels.InP (fun τ : UpperHalfPlane => Work.Kernels.theta10Fun τ ^ 4) :=
    Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta10Fun_mem_InP 4
  have hXi2inP : Work.Kernels.InP
      (fun τ : UpperHalfPlane => Work.Kernels.theta00Fun τ ^ 4 + Work.Kernels.theta01Fun τ ^ 4) :=
    Work.Kernels.InP.add hUinP hWinP
  have hXi4inP : Work.Kernels.InP
      (fun τ : UpperHalfPlane =>
        Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2) :=
    Work.Kernels.InP.sub
      (Work.Kernels.InP.add (Work.Kernels.InP.pow hUinP 2) (Work.Kernels.InP.pow hWinP 2))
      ((Work.Kernels.InP.pow hVinP 2).const_mul 2)
  obtain ⟨CXi2, hCXi20, hXi2⟩ := bound_of_moderate (F := fun τ : UpperHalfPlane =>
    Work.Kernels.theta00Fun τ ^ 4 + Work.Kernels.theta01Fun τ ^ 4) hXi2inP.2
  obtain ⟨CXi2S, hCXi2S0, hXi2S⟩ := bound_of_moderate
    (F := SlashAction.map (2 : ℤ) ModularGroup.S (fun τ : UpperHalfPlane =>
      Work.Kernels.theta00Fun τ ^ 4 + Work.Kernels.theta01Fun τ ^ 4))
    (hXi2inP.slash 2 ModularGroup.S).2
  obtain ⟨CXi4, hCXi40, hXi4⟩ := bound_of_moderate (F := fun τ : UpperHalfPlane =>
    Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2) hXi4inP.2
  obtain ⟨CXi4S, hCXi4S0, hXi4S⟩ := bound_of_moderate
    (F := SlashAction.map (4 : ℤ) ModularGroup.S (fun τ : UpperHalfPlane =>
      Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2))
    (hXi4inP.slash 4 ModularGroup.S).2
  obtain ⟨τm, _, hτm_min⟩ :=
    (isCompact_closedBall (x := τ₀) (r := R)).exists_isMinOn
      ⟨τ₀, Metric.mem_closedBall_self hRm⟩
      (Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous.norm).continuousOn
  set δ : ℝ := ‖Work.Kernels.DeltaFun τm‖ with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τm)
  have hδb : ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → δ ≤ ‖Work.Kernels.DeltaFun τ‖ :=
    fun τ hτ => hτm_min hτ
  set Cphi : ℝ := M + (M * CE2 + 3) + (M * CE2 ^ 2 + 6 * CE2) with hCphidef
  set Cpsi : ℝ := 1 + (CXi2 * CL + CXi2S * CLS) + (CXi4 * CL + CXi4S * CLS) with hCpsidef
  set C4 : ℝ := CE4 + 1 with hC4def
  set C6 : ℝ := CE6 + 1 with hC6def
  set C14 : ℝ := CE14 + 1 with hC14def
  set Cj : ℝ := C4 ^ 3 / δ with hCjdef
  have hCphi0 : 0 ≤ Cphi := by rw [hCphidef]; positivity
  have hCpsi0 : 0 ≤ Cpsi := by rw [hCpsidef]; positivity
  have hC40 : 0 ≤ C4 := by rw [hC4def]; positivity
  have hC60 : 0 ≤ C6 := by rw [hC6def]; positivity
  have hC140 : 0 ≤ C14 := by rw [hC14def]; positivity
  have hCj0 : 0 ≤ Cj := by rw [hCjdef]; positivity
  refine ⟨Cphi, Cpsi, C4, C6, C14, Cj, δ, hCphi0, hCpsi0, hC40, hC60, hC140, hCj0, hδpos, ?_⟩
  intro τ hτ
  have hMτ : ‖(τ : ℂ)‖ ≤ M := hM τ hτ
  have hE2τ : ‖Work.Kernels.E2Fun τ‖ ≤ CE2 := hE2 τ hτ
  have hE4τ : ‖Work.Kernels.E4Fun τ‖ ≤ CE4 := hE4 τ hτ
  have hE6τ : ‖Work.Kernels.E6Fun τ‖ ≤ CE6 := hE6 τ hτ
  have hE14τ : ‖Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ‖ ≤ CE14 := hE14 τ hτ
  have hLτ : ‖ℓ.L τ‖ ≤ CL := hL τ hτ
  have hLSτ : ‖ℓ.L_S τ‖ ≤ CLS := hLS τ hτ
  have hXi2τ : ‖Work.Kernels.theta00Fun τ ^ 4 + Work.Kernels.theta01Fun τ ^ 4‖ ≤ CXi2 := hXi2 τ hτ
  have hXi2Sτ : ‖SlashAction.map (2 : ℤ) ModularGroup.S (fun τ : UpperHalfPlane =>
      Work.Kernels.theta00Fun τ ^ 4 + Work.Kernels.theta01Fun τ ^ 4) τ‖ ≤ CXi2S := hXi2S τ hτ
  have hXi4τ : ‖Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 -
      2 * Work.Kernels.VFun τ ^ 2‖ ≤ CXi4 := hXi4 τ hτ
  have hXi4Sτ : ‖SlashAction.map (4 : ℤ) ModularGroup.S (fun τ : UpperHalfPlane =>
      Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2) τ‖ ≤ CXi4S :=
    hXi4S τ hτ
  have hδτ : δ ≤ ‖Work.Kernels.DeltaFun τ‖ := hδb τ hτ
  have hC4ge : CE4 ≤ C4 := by rw [hC4def]; linarith
  have hC6ge : CE6 ≤ C6 := by rw [hC6def]; linarith
  have hC14ge : CE14 ≤ C14 := by rw [hC14def]; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change ‖Work.Kernels.phiVec τ (0 : Fin 3)‖ ≤ Cphi
      have h0 : ‖Work.Kernels.phiVec τ 0‖ = ‖(τ : ℂ)‖ := by
        simp [Work.Kernels.phiVec, Work.Kernels.phiNeg2]
      rw [h0, hCphidef]
      nlinarith [hMτ, hCE20]
    · change ‖Work.Kernels.phiVec τ (1 : Fin 3)‖ ≤ Cphi
      have h1 : ‖Work.Kernels.phiVec τ 1‖ ≤ ‖(τ : ℂ) * Work.Kernels.E2Fun τ‖ + 3 := by
        have h := norm_sub_le ((τ : ℂ) * Work.Kernels.E2Fun τ)
          ((3 : ℂ) * Complex.I / (Real.pi : ℂ))
        have h3 := norm_three_I_div_pi_le
        have hphi : Work.Kernels.phiVec τ 1 = (τ : ℂ) * Work.Kernels.E2Fun τ -
            (3 : ℂ) * Complex.I / (Real.pi : ℂ) := by
          simp [Work.Kernels.phiVec, Work.Kernels.phi0]
        rw [hphi]
        linarith
      have hb : ‖(τ : ℂ) * Work.Kernels.E2Fun τ‖ ≤ M * CE2 := by
        rw [norm_mul]
        exact mul_le_mul hMτ hE2τ (norm_nonneg _) hM0
      rw [hCphidef]
      nlinarith [h1, hb, hM0, hCE20]
    · change ‖Work.Kernels.phiVec τ (2 : Fin 3)‖ ≤ Cphi
      have h2 : ‖Work.Kernels.phiVec τ 2‖ ≤
          ‖(τ : ℂ) * Work.Kernels.E2Fun τ ^ 2‖ +
          ‖((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ‖ := by
        have h := norm_sub_le ((τ : ℂ) * Work.Kernels.E2Fun τ ^ 2)
          (((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ)
        have hphi : Work.Kernels.phiVec τ 2 = (τ : ℂ) * Work.Kernels.E2Fun τ ^ 2 -
            (6 : ℂ) * Complex.I / (Real.pi : ℂ) * Work.Kernels.E2Fun τ := by
          simp [Work.Kernels.phiVec, Work.Kernels.phi2]
        rw [hphi]
        exact h
      have hb : ‖(τ : ℂ) * Work.Kernels.E2Fun τ ^ 2‖ ≤ M * CE2 ^ 2 := by
        rw [norm_mul, norm_pow]
        exact mul_le_mul hMτ (pow_le_pow_left₀ (norm_nonneg _) hE2τ 2) (by positivity) hM0
      have hc : ‖((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ‖ ≤ 6 * CE2 := by
        rw [norm_mul]
        exact mul_le_mul norm_six_I_div_pi_le hE2τ (norm_nonneg _) (by norm_num)
      rw [hCphidef]
      nlinarith [h2, hb, hc, hM0, hCE20]
  · intro i
    fin_cases i
    · change ‖Work.Kernels.psiVec ℓ τ (0 : Fin 3)‖ ≤ Cpsi
      have h0 : ‖Work.Kernels.psiVec ℓ τ 0‖ = 1 := by
        simp [Work.Kernels.psiVec]
      rw [h0, hCpsidef]
      have : 0 ≤ CXi2 * CL + CXi2S * CLS + (CXi4 * CL + CXi4S * CLS) := by positivity
      linarith
    · change ‖Work.Kernels.psiVec ℓ τ (1 : Fin 3)‖ ≤ Cpsi
      have h1 : ‖Work.Kernels.psiVec ℓ τ 1‖ ≤ CXi2 * CL + CXi2S * CLS := by
        have h := norm_add_le (Work.Kernels.xi2Fun τ * ℓ.L τ)
          ((SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * ℓ.L_S τ)
        have hpsi : Work.Kernels.psiVec ℓ τ 1 =
            Work.Kernels.xi2Fun τ * ℓ.L τ +
              (SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * ℓ.L_S τ := rfl
        rw [hpsi]
        refine le_trans h ?_
        rw [norm_mul, norm_mul]
        exact add_le_add
          (mul_le_mul hXi2τ hLτ (norm_nonneg _) hCXi20)
          (mul_le_mul hXi2Sτ hLSτ (norm_nonneg _) hCXi2S0)
      rw [hCpsidef]
      nlinarith [h1, hCXi20, hCXi2S0, hCL0, hCLS0, mul_nonneg hCXi40 hCL0,
        mul_nonneg hCXi4S0 hCLS0]
    · change ‖Work.Kernels.psiVec ℓ τ (2 : Fin 3)‖ ≤ Cpsi
      have h1 : ‖Work.Kernels.psiVec ℓ τ 2‖ ≤ CXi4 * CL + CXi4S * CLS := by
        have h := norm_add_le (Work.Kernels.xi4Fun τ * ℓ.L τ)
          ((SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * ℓ.L_S τ)
        have hpsi : Work.Kernels.psiVec ℓ τ 2 =
            Work.Kernels.xi4Fun τ * ℓ.L τ +
              (SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * ℓ.L_S τ := rfl
        rw [hpsi]
        refine le_trans h ?_
        rw [norm_mul, norm_mul]
        exact add_le_add
          (mul_le_mul hXi4τ hLτ (norm_nonneg _) hCXi40)
          (mul_le_mul hXi4Sτ hLSτ (norm_nonneg _) hCXi4S0)
      rw [hCpsidef]
      nlinarith [h1, hCXi40, hCXi4S0, hCL0, hCLS0, mul_nonneg hCXi20 hCL0,
        mul_nonneg hCXi2S0 hCLS0]
  · exact le_trans hE4τ hC4ge
  · exact le_trans hE6τ hC6ge
  · have : ‖Work.Kernels.E14Fun τ‖ = ‖Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ‖ := rfl
    rw [this]
    exact le_trans hE14τ hC14ge
  · have hj : ‖Work.Kernels.jInvariantFun τ‖ =
        ‖Work.Kernels.E4Fun τ ^ 3‖ / ‖Work.Kernels.DeltaFun τ‖ := by
      show ‖Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ‖ = _
      rw [norm_div]
    rw [hj, hCjdef]
    have hδτpos : 0 < ‖Work.Kernels.DeltaFun τ‖ := lt_of_lt_of_le hδpos hδτ
    have hnum : ‖Work.Kernels.E4Fun τ ^ 3‖ ≤ C4 ^ 3 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (le_trans hE4τ hC4ge) 3
    rw [div_le_div_iff₀ hδτpos hδpos]
    have hC4pow : (0 : ℝ) ≤ C4 ^ 3 := by positivity
    nlinarith [hnum, hδτ, hδpos, hC4pow, norm_nonneg (Work.Kernels.DeltaFun τ)]
  · exact hδτ

/-! ## Values of `f_k`, of the basis vectors and of the column bounds -/

private lemma colP8_zero (J : ℂ) : colP8 J 0 = 2 * ‖J‖ + 1 := by
  simp [colP8, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma colP8_one (J : ℂ) : colP8 J 1 = 2 := by
  simp [colP8, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma colP8_two (J : ℂ) : colP8 J 2 = 1 := by
  simp [colP8, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma colM8_zero (jτ : ℂ) : colM8 jτ 0 = 2 * 1728 := by
  simp [colM8, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma colM8_one (jτ : ℂ) : colM8 jτ 1 = 1729 + ‖jτ‖ := by
  simp [colM8, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma colM8_two (jτ : ℂ) : colM8 jτ 2 = 1 + ‖jτ‖ := by
  simp [colM8, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]

private lemma colP8_nonneg (J : ℂ) (j : Fin 3) : 0 ≤ colP8 J j := by
  fin_cases j
  · change 0 ≤ colP8 J (0 : Fin 3); rw [colP8_zero]; linarith [norm_nonneg J]
  · change 0 ≤ colP8 J (1 : Fin 3); rw [colP8_one]; norm_num
  · change 0 ≤ colP8 J (2 : Fin 3); rw [colP8_two]; norm_num

private lemma colM8_nonneg (jτ : ℂ) (j : Fin 3) : 0 ≤ colM8 jτ j := by
  fin_cases j
  · change 0 ≤ colM8 jτ (0 : Fin 3); rw [colM8_zero]; norm_num
  · change 0 ≤ colM8 jτ (1 : Fin 3); rw [colM8_one]; linarith [norm_nonneg jτ]
  · change 0 ≤ colM8 jτ (2 : Fin 3); rw [colM8_two]; linarith [norm_nonneg jτ]

private lemma fk_twelve (z : UpperHalfPlane) :
    Work.Kernels.fk (12 : ℤ) z = Work.Kernels.DeltaFun z := by simp [Work.Kernels.fk]
private lemma fk_ten (z : UpperHalfPlane) :
    Work.Kernels.fk (10 : ℤ) z = Work.Kernels.E10Fun z := by simp [Work.Kernels.fk]
private lemma fk_eight (z : UpperHalfPlane) :
    Work.Kernels.fk (8 : ℤ) z = Work.Kernels.E8Fun z := by simp [Work.Kernels.fk]
private lemma fk_six (z : UpperHalfPlane) :
    Work.Kernels.fk (6 : ℤ) z = Work.Kernels.E6Fun z := by simp [Work.Kernels.fk]
private lemma fk_four (z : UpperHalfPlane) :
    Work.Kernels.fk (4 : ℤ) z = Work.Kernels.E4Fun z := by simp [Work.Kernels.fk]
private lemma fk_two (z : UpperHalfPlane) :
    Work.Kernels.fk (2 : ℤ) z = Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z := by
  simp [Work.Kernels.fk]
private lemma fk_zero (z : UpperHalfPlane) : Work.Kernels.fk (0 : ℤ) z = 1 := by
  simp [Work.Kernels.fk]

private lemma DeltaFun_mul_fk_two (τ : UpperHalfPlane) :
    Work.Kernels.DeltaFun τ * Work.Kernels.fk (2 : ℤ) τ = Work.Kernels.E14Fun τ := by
  rw [fk_two, mul_div_assoc']
  exact mul_div_cancel_left₀ _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)

private lemma vec642_zero : ![6, 4, 2] (0 : Fin 3) = (6 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec642_one : ![6, 4, 2] (1 : Fin 3) = (4 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec642_two : ![6, 4, 2] (2 : Fin 3) = (2 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec128_zero : ![12, 10, 8] (0 : Fin 3) = (12 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec128_one : ![12, 10, 8] (1 : Fin 3) = (10 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec128_two : ![12, 10, 8] (2 : Fin 3) = (8 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec420_zero : ![4, 2, 0] (0 : Fin 3) = (4 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec420_one : ![4, 2, 0] (1 : Fin 3) = (2 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec420_two : ![4, 2, 0] (2 : Fin 3) = (0 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec1086_zero : ![10, 8, 6] (0 : Fin 3) = (10 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec1086_one : ![10, 8, 6] (1 : Fin 3) = (8 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
private lemma vec1086_two : ![10, 8, 6] (2 : Fin 3) = (6 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]

private lemma phitVec_zero (z : UpperHalfPlane) : Work.Kernels.phitVec z 0 = (z : ℂ) ^ 2 := rfl
private lemma phitVec_one (z : UpperHalfPlane) :
    Work.Kernels.phitVec z 1 = (z : ℂ) ^ 2 * Work.Kernels.E2S z := rfl
private lemma phitVec_two (z : UpperHalfPlane) :
    Work.Kernels.phitVec z 2 = (z : ℂ) ^ 2 * (Work.Kernels.E2S z) ^ 2 := rfl
private lemma psitVec_zero (ℓ : Work.Kernels.LogLambdaData) (z : UpperHalfPlane) :
    Work.Kernels.psitVec ℓ z 0 = ℓ.L z := rfl
private lemma psitVec_one (ℓ : Work.Kernels.LogLambdaData) (z : UpperHalfPlane) :
    Work.Kernels.psitVec ℓ z 1 = Work.Kernels.WFun z := rfl
private lemma psitVec_two (ℓ : Work.Kernels.LogLambdaData) (z : UpperHalfPlane) :
    Work.Kernels.psitVec ℓ z 2 = Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 := rfl

private lemma inv_pow_mul_inv_pow {t : ℝ} (m n : ℕ) :
    ((t : ℝ) ^ m)⁻¹ * ((t : ℝ) ^ n)⁻¹ = ((t : ℝ) ^ (m + n))⁻¹ := by
  rw [← mul_inv, ← pow_add]

private lemma mul_inv_pow_mono {A : ℝ} (hA : 0 ≤ A) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {m n : ℕ} (hmn : m ≤ n) : A * ((t : ℝ) ^ m)⁻¹ ≤ A * ((t : ℝ) ^ n)⁻¹ :=
  mul_le_mul_of_nonneg_left (inv_pow_le_inv_pow' ht ht1 hmn) hA

private lemma le_mul_of_divisor {A D t cL : ℝ} (hA : 0 ≤ A) (hcL : 0 < cL)
    (hDP : cL * ((t : ℝ) ^ 12)⁻¹ ≤ D) : A * ((t : ℝ) ^ 12)⁻¹ ≤ (A / cL) * D := by
  have h1 : A * ((t : ℝ) ^ 12)⁻¹ = (A / cL) * (cL * ((t : ℝ) ^ 12)⁻¹) := by
    have hne : cL ≠ 0 := ne_of_gt hcL
    field_simp
  rw [h1]
  exact mul_le_mul_of_nonneg_left hDP (by positivity)

/-- **The CKMRV kernel is bounded near the cusp `t → 0` on a contour-clean ball.**  For `τ` in
the hyperbolic closed ball of radius `R` around `τ₀` on which the contour `z = it` carries no pole
of `z ↦ K^{(8)}(τ,z)`, and `0 < t ≤ T` small, `‖K^{(8)}(τ,it)‖` is bounded by a constant.

Hints (all ingredients are available): `K = K^{clear}/growthPrefactor`
(`Work.Kernels.ClearLink.KPlusClear_eq_smul`, `Work.Kernels.ClearLink.KMinusClear_eq_smul`);
`Work.Asymptotics.UpsilonPlusClear_norm_le` / `Work.Asymptotics.UpsilonMinusClear_norm_le` (in
`Submission.Work.Asymptotics.KernelBoundAux`) bound the entries of the cleared matrices in terms of
`Work.Asymptotics.colP` / `Work.Asymptotics.colM`; `colP J 0 = 2‖J‖+1` so the first column needs
`Δ(z)j(z) = E₄(z)³` (`Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun`); the `z`-side cusp
bounds are `Work.Asymptotics.norm_Eisenstein_imagAxis_atZero`,
`Work.Asymptotics.norm_theta_imagAxis_atZero`, `Work.Asymptotics.norm_L_imagAxis_atZero`,
`Work.Asymptotics.DeltaFun_imagAxis_atZero`; the divisor bound `‖growthPrefactor(τ,it)‖ ≥ c t^{-12}`
follows from `Work.Asymptotics.DeltaFun_imagAxis_atZero` and
`Work.Asymptotics.jInvariantFun_sub_imagAxis_atZero` (or `Work.Asymptotics.exists_delta_Aj` for the
uniform-in-`τ` compactness input); the `τ`-side factors are bounded on the compact ball via
`Work.Asymptotics.bound_on_ball_real`.  Beware: `positivity` on the *set*-bound constants and
`mul_le_mul`/`mul_le_mul_of_nonneg` argument orders are the practical traps (their 3rd/4th arguments
are `0 ≤ c`, `0 ≤ b` resp. `0 ≤ a`, `0 ≤ d`) -/
theorem norm_Kaxis_Kfun8_le_near_zero (ℓ : Work.Kernels.LogLambdaData) {τ₀ : UpperHalfPlane}
    {R : ℝ} (hR : 0 < R)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), dist τ τ₀ ≤ R → t ≤ T →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t‖ ≤ C := by
  obtain ⟨Cphi, Cpsi, C4b, C6b, C14b, Cj, δ, hCphi0, hCpsi0, hC4b0, hC6b0, hC14b0, hCj0,
    hδpos, hball⟩ := ball_data ℓ hR
  obtain ⟨cΔ, CΔ, TΔ, hcΔpos, hCΔpos, hTΔpos, hΔb⟩ := DeltaFun_imagAxis_atZero
  obtain ⟨C4, hC4pos, hE4z'⟩ := norm_Eisenstein_imagAxis_atZero.1
  obtain ⟨C6, hC6pos, hE6z'⟩ := norm_Eisenstein_imagAxis_atZero.2.1
  obtain ⟨C2S, hC2Spos, hE2Sz'⟩ := norm_Eisenstein_imagAxis_atZero.2.2
  obtain ⟨CU, hCUpos, hUz'⟩ := norm_theta_imagAxis_atZero.1
  obtain ⟨CV, hCVpos, hVz'⟩ := norm_theta_imagAxis_atZero.2.1
  obtain ⟨CW, hCWpos, hWz'⟩ := norm_theta_imagAxis_atZero.2.2
  obtain ⟨CUV, TUV, hCUVpos, hTUVpos, hUVz'⟩ := norm_UFun_sq_sub_VFun_sq_imagAxis
  obtain ⟨CLp, hCLppos, hLz'⟩ := norm_L_imagAxis_atZero ℓ
  obtain ⟨cj0, Tj0, hcj0pos, hTj0pos, hJ0⟩ := jInvariantFun_imagAxis_atZero
  set Aj : ℝ := max Cj 1 with hAjdef
  have hAj1 : 1 ≤ Aj := le_max_right _ _
  have hAjCj : Cj ≤ Aj := le_max_left _ _
  obtain ⟨Texp, hTexp, hexp⟩ := exists_le_exp_two_pi_div (2 * Aj / cj0)
  set cL : ℝ := cΔ * cj0 / 2 with hcLdef
  have hcLpos : 0 < cL := by rw [hcLdef]; exact div_pos (mul_pos hcΔpos hcj0pos) (by norm_num)
  set T : ℝ := min (min TΔ Tj0) (min (min Texp TUV) 1) with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]
    exact lt_min (lt_min hTΔpos hTj0pos) (lt_min (lt_min hTexp hTUVpos) one_pos)
  have hTTΔ : T ≤ TΔ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hTTj0 : T ≤ Tj0 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hTTexp : T ≤ Texp :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hTTUV : T ≤ TUV :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hT1 : T ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  set P : ℝ := 3 * Cphi * (C4b + C6b + C14b / δ) with hPdef
  set Q : ℝ := 3 * Cpsi * (C4b + C14b / δ + 1) with hQdef
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg (by norm_num) hCphi0)
      (by linarith [hC4b0, hC6b0, div_nonneg hC14b0 hδpos.le])
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg (by norm_num) hCpsi0)
      (by linarith [hC4b0, div_nonneg hC14b0 hδpos.le])
  set ZK : ℝ := 3 + (2 * C4 * C6 * C2S + C4 ^ 2 * C2S ^ 2) / cL with hZKdef
  set ZM : ℝ := (3456 * (C4 * C6 * CLp) + (1729 + Aj) * (C4 ^ 2 * CW) +
    (1 + Aj) * (C6 * CUV)) / cL with hZMdef
  have hZK0 : 0 ≤ ZK := by
    rw [hZKdef]
    exact add_nonneg (by norm_num)
      (div_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC4pos.le) hC6pos.le) hC2Spos.le)
        (mul_nonneg (pow_nonneg hC4pos.le 2) (pow_nonneg hC2Spos.le 2))) hcLpos.le)
  have hZM0 : 0 ≤ ZM := by
    rw [hZMdef]
    exact div_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hC4pos.le hC6pos.le) hCLppos.le))
      (mul_nonneg (by linarith [hAj1]) (mul_nonneg (pow_nonneg hC4pos.le 2) hCWpos.le)))
      (mul_nonneg (by linarith [hAj1]) (mul_nonneg hC6pos.le hCUVpos.le))) hcLpos.le
  have hCpos : 0 < ‖cP‖ * P * ZK / 2 + ‖cM‖ * Q * ZM / 2 + 1 := by
    have h1 : (0:ℝ) ≤ ‖cP‖ * P * ZK := mul_nonneg (mul_nonneg (norm_nonneg _) hP0) hZK0
    have h2 : (0:ℝ) ≤ ‖cM‖ * Q * ZM := mul_nonneg (mul_nonneg (norm_nonneg _) hQ0) hZM0
    linarith
  refine ⟨_, T, hCpos, hTpos, ?_⟩
  intro τ t ht hτ htT
  obtain ⟨hφb, hψb, hE4b, hE6b, hE14b, hjb, hδb⟩ := hball τ hτ
  set z : UpperHalfPlane := Work.Kernels.imagAxis t ht with hz
  set J : ℂ := Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z with hJdef
  have ht1 : t ≤ 1 := le_trans htT hT1
  have hzt : ‖(z : ℂ)‖ = t := by rw [hz]; exact norm_imagAxis_coe t ht
  have hz2 : ‖(z : ℂ) ^ 2‖ = t ^ 2 := by rw [norm_pow, hzt]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht, ht1]
  -- (A) cusp bounds at `z = it`
  have hE4z : ‖Work.Kernels.E4Fun z‖ ≤ C4 * ((t : ℝ) ^ 4)⁻¹ := by
    simpa only [hz] using hE4z' t ht ht1
  have hE6z : ‖Work.Kernels.E6Fun z‖ ≤ C6 * ((t : ℝ) ^ 6)⁻¹ := by
    simpa only [hz] using hE6z' t ht ht1
  have hE2Sz : ‖Work.Kernels.E2S z‖ ≤ C2S * ((t : ℝ) ^ 2)⁻¹ := by
    simpa only [hz] using hE2Sz' t ht ht1
  have hLz : ‖ℓ.L z‖ ≤ CLp := by simpa only [hz] using hLz' t ht ht1
  have hWz : ‖Work.Kernels.WFun z‖ ≤ CW * ((t : ℝ) ^ 2)⁻¹ := by
    simpa only [hz] using hWz' t ht ht1
  have hUVz : ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖ ≤ CUV * ((t : ℝ) ^ 4)⁻¹ := by
    simpa only [hz] using hUVz' t ht (le_trans htT hTTUV)
  have hΔlow : cΔ * ((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)) ≤
      ‖Work.Kernels.DeltaFun z‖ := by
    have h := (hΔb t ht (le_trans htT hTTΔ)).1
    rwa [← hz] at h
  have hJz : cj0 * Real.exp (2 * Real.pi / t) ≤ ‖Work.Kernels.jInvariantFun z‖ := by
    simpa only [hz] using hJ0 t ht (le_trans htT hTTj0)
  have hjτb : ‖Work.Kernels.jInvariantFun τ‖ ≤ Aj := le_trans hjb hAjCj
  have hexpA : Aj ≤ cj0 / 2 * Real.exp (2 * Real.pi / t) := by
    have h := hexp t ht (le_trans htT hTTexp)
    have h2 : 2 * Aj / cj0 * (cj0 / 2) ≤ Real.exp (2 * Real.pi / t) * (cj0 / 2) :=
      mul_le_mul_of_nonneg_right h (div_nonneg hcj0pos.le (by norm_num))
    have h3 : 2 * Aj / cj0 * (cj0 / 2) = Aj := by field_simp
    rw [h3] at h2
    linarith [h2]
  have hJdiff : cj0 / 2 * Real.exp (2 * Real.pi / t) ≤ ‖J‖ := by
    have h1 : ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun τ‖ = ‖J‖ := by
      rw [hJdef, ← norm_neg, neg_sub]
    have h := norm_sub_norm_le (Work.Kernels.jInvariantFun z) (Work.Kernels.jInvariantFun τ)
    rw [h1] at h
    linarith [hJz, hjτb, hexpA, h]
  have hJ1 : 1 ≤ ‖J‖ := le_trans hAj1 (le_trans hexpA hJdiff)
  have hDP : cL * ((t : ℝ) ^ 12)⁻¹ ≤ ‖Work.Kernels.DeltaFun z‖ * ‖J‖ := by
    have h := mul_le_mul hΔlow hJdiff (mul_nonneg (div_nonneg hcj0pos.le (by norm_num)) (Real.exp_nonneg _)) (norm_nonneg _)
    have heq : cΔ * ((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)) *
        (cj0 / 2 * Real.exp (2 * Real.pi / t)) = cL * ((t : ℝ) ^ 12)⁻¹ := by
      rw [hcLdef]
      calc cΔ * ((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)) *
            (cj0 / 2 * Real.exp (2 * Real.pi / t))
          = cΔ * (cj0 / 2) * (Real.exp (-(2 * Real.pi / t)) * Real.exp (2 * Real.pi / t)) *
              ((t : ℝ) ^ 12)⁻¹ := by ring
        _ = cΔ * (cj0 / 2) * ((t : ℝ) ^ 12)⁻¹ := by
              rw [exp_neg_mul_exp_pos, mul_one]
        _ = cΔ * cj0 / 2 * ((t : ℝ) ^ 12)⁻¹ := by ring
    rw [← heq]
    exact h
  -- (B) the `τ`-side sums
  have hPK : (∑ i : Fin 3, ‖Work.Kernels.phiVec τ i‖ *
      ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ‖) ≤
      ‖Work.Kernels.DeltaFun τ‖ * P := by
    set P' : ℝ := Cphi * (C4b + C6b + C14b / δ) with hP'def
    have hPrw : P = 3 * P' := by rw [hPdef, hP'def]; ring
    rw [Fin.sum_univ_three, hPrw]
    have h0 : ‖Work.Kernels.phiVec τ (0 : Fin 3)‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] (0 : Fin 3)) τ‖ ≤
        ‖Work.Kernels.DeltaFun τ‖ * P' := by
      rw [vec642_zero, fk_six, norm_mul, hP'def]
      have hb : ‖Work.Kernels.phiVec τ (0 : Fin 3)‖ *
          (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E6Fun τ‖) ≤
          Cphi * (‖Work.Kernels.DeltaFun τ‖ * C6b) :=
        mul_le_mul (hφb 0) (mul_le_mul_of_nonneg_left hE6b (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCphi0
      refine le_trans hb ?_
      calc Cphi * (‖Work.Kernels.DeltaFun τ‖ * C6b)
          = ‖Work.Kernels.DeltaFun τ‖ * (Cphi * C6b) := by ring
        _ ≤ ‖Work.Kernels.DeltaFun τ‖ * (Cphi * (C4b + C6b + C14b / δ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (by linarith [hC4b0, div_nonneg hC14b0 hδpos.le]) hCphi0)
              (norm_nonneg _)
    have h1 : ‖Work.Kernels.phiVec τ (1 : Fin 3)‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] (1 : Fin 3)) τ‖ ≤
        ‖Work.Kernels.DeltaFun τ‖ * P' := by
      rw [vec642_one, fk_four, norm_mul, hP'def]
      have hb : ‖Work.Kernels.phiVec τ (1 : Fin 3)‖ *
          (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E4Fun τ‖) ≤
          Cphi * (‖Work.Kernels.DeltaFun τ‖ * C4b) :=
        mul_le_mul (hφb 1) (mul_le_mul_of_nonneg_left hE4b (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCphi0
      refine le_trans hb ?_
      calc Cphi * (‖Work.Kernels.DeltaFun τ‖ * C4b)
          = ‖Work.Kernels.DeltaFun τ‖ * (Cphi * C4b) := by ring
        _ ≤ ‖Work.Kernels.DeltaFun τ‖ * (Cphi * (C4b + C6b + C14b / δ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (by linarith [hC6b0, div_nonneg hC14b0 hδpos.le]) hCphi0)
              (norm_nonneg _)
    have h2 : ‖Work.Kernels.phiVec τ (2 : Fin 3)‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] (2 : Fin 3)) τ‖ ≤
        ‖Work.Kernels.DeltaFun τ‖ * P' := by
      rw [vec642_two, fk_two, hP'def]
      rw [show Work.Kernels.DeltaFun τ *
            (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) = Work.Kernels.E14Fun τ from by
          rw [mul_div_assoc']
          exact mul_div_cancel_left₀ _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)]
      have hb : ‖Work.Kernels.phiVec τ (2 : Fin 3)‖ * ‖Work.Kernels.E14Fun τ‖ ≤
          Cphi * C14b :=
        mul_le_mul (hφb 2) hE14b (norm_nonneg _) hCphi0
      refine le_trans hb ?_
      have h1 : C14b ≤ (C14b / δ) * ‖Work.Kernels.DeltaFun τ‖ := by
        calc C14b = (C14b / δ) * δ := by field_simp
          _ ≤ (C14b / δ) * ‖Work.Kernels.DeltaFun τ‖ :=
              mul_le_mul_of_nonneg_left hδb (div_nonneg hC14b0 hδpos.le)
      calc Cphi * C14b ≤ Cphi * ((C14b / δ) * ‖Work.Kernels.DeltaFun τ‖) :=
            mul_le_mul_of_nonneg_left h1 hCphi0
        _ = ‖Work.Kernels.DeltaFun τ‖ * (Cphi * (C14b / δ)) := by ring
        _ ≤ ‖Work.Kernels.DeltaFun τ‖ * (Cphi * (C4b + C6b + C14b / δ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (by linarith [hC4b0, hC6b0]) hCphi0)
              (norm_nonneg _)
    calc _ + _ + _ ≤ ‖Work.Kernels.DeltaFun τ‖ * P' + ‖Work.Kernels.DeltaFun τ‖ * P' +
          ‖Work.Kernels.DeltaFun τ‖ * P' := by linarith [h0, h1, h2]
      _ = ‖Work.Kernels.DeltaFun τ‖ * (3 * P') := by ring
  have hQM : (∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i‖ *
      ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ‖) ≤
      ‖Work.Kernels.DeltaFun τ‖ * Q := by
    set Q' : ℝ := Cpsi * (C4b + C14b / δ + 1) with hQ'def
    have hQrw : Q = 3 * Q' := by rw [hQdef, hQ'def]; ring
    rw [Fin.sum_univ_three, hQrw]
    have h0 : ‖Work.Kernels.psiVec ℓ τ (0 : Fin 3)‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] (0 : Fin 3)) τ‖ ≤
        ‖Work.Kernels.DeltaFun τ‖ * Q' := by
      rw [vec420_zero, fk_four, norm_mul, hQ'def]
      have hb : ‖Work.Kernels.psiVec ℓ τ (0 : Fin 3)‖ *
          (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E4Fun τ‖) ≤
          Cpsi * (‖Work.Kernels.DeltaFun τ‖ * C4b) :=
        mul_le_mul (hψb 0) (mul_le_mul_of_nonneg_left hE4b (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCpsi0
      refine le_trans hb ?_
      calc Cpsi * (‖Work.Kernels.DeltaFun τ‖ * C4b)
          = ‖Work.Kernels.DeltaFun τ‖ * (Cpsi * C4b) := by ring
        _ ≤ ‖Work.Kernels.DeltaFun τ‖ * (Cpsi * (C4b + C14b / δ + 1)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (by linarith [div_nonneg hC14b0 hδpos.le]) hCpsi0)
              (norm_nonneg _)
    have h1 : ‖Work.Kernels.psiVec ℓ τ (1 : Fin 3)‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] (1 : Fin 3)) τ‖ ≤
        ‖Work.Kernels.DeltaFun τ‖ * Q' := by
      rw [vec420_one, fk_two, hQ'def]
      rw [show Work.Kernels.DeltaFun τ *
            (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) = Work.Kernels.E14Fun τ from by
          rw [mul_div_assoc']
          exact mul_div_cancel_left₀ _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)]
      have hb : ‖Work.Kernels.psiVec ℓ τ (1 : Fin 3)‖ * ‖Work.Kernels.E14Fun τ‖ ≤
          Cpsi * C14b :=
        mul_le_mul (hψb 1) hE14b (norm_nonneg _) hCpsi0
      refine le_trans hb ?_
      have h2 : C14b ≤ (C14b / δ) * ‖Work.Kernels.DeltaFun τ‖ := by
        calc C14b = (C14b / δ) * δ := by field_simp
          _ ≤ (C14b / δ) * ‖Work.Kernels.DeltaFun τ‖ :=
              mul_le_mul_of_nonneg_left hδb (div_nonneg hC14b0 hδpos.le)
      calc Cpsi * C14b ≤ Cpsi * ((C14b / δ) * ‖Work.Kernels.DeltaFun τ‖) :=
            mul_le_mul_of_nonneg_left h2 hCpsi0
        _ = ‖Work.Kernels.DeltaFun τ‖ * (Cpsi * (C14b / δ)) := by ring
        _ ≤ ‖Work.Kernels.DeltaFun τ‖ * (Cpsi * (C4b + C14b / δ + 1)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by linarith [hC4b0]) hCpsi0)
              (norm_nonneg _)
    have h2 : ‖Work.Kernels.psiVec ℓ τ (2 : Fin 3)‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] (2 : Fin 3)) τ‖ ≤
        ‖Work.Kernels.DeltaFun τ‖ * Q' := by
      rw [vec420_two, fk_zero, mul_one, hQ'def]
      have hb : ‖Work.Kernels.psiVec ℓ τ (2 : Fin 3)‖ * ‖Work.Kernels.DeltaFun τ‖ ≤
          Cpsi * ‖Work.Kernels.DeltaFun τ‖ :=
        mul_le_mul_of_nonneg_right (hψb 2) (norm_nonneg _)
      refine le_trans hb ?_
      calc Cpsi * ‖Work.Kernels.DeltaFun τ‖ = ‖Work.Kernels.DeltaFun τ‖ * Cpsi := by ring
        _ ≤ ‖Work.Kernels.DeltaFun τ‖ * (Cpsi * (C4b + C14b / δ + 1)) :=
            mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_right hCpsi0
                (by linarith [hC4b0, div_nonneg hC14b0 hδpos.le]))
              (norm_nonneg _)
    calc _ + _ + _ ≤ ‖Work.Kernels.DeltaFun τ‖ * Q' + ‖Work.Kernels.DeltaFun τ‖ * Q' +
          ‖Work.Kernels.DeltaFun τ‖ * Q' := by linarith [h0, h1, h2]
      _ = ‖Work.Kernels.DeltaFun τ‖ * (3 * Q') := by ring
  -- (C) the `z`-side sums
  have hE10z : ‖Work.Kernels.E10Fun z‖ ≤ C4 * C6 * ((t : ℝ) ^ 10)⁻¹ := by
    show ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z‖ ≤ C4 * C6 * ((t : ℝ) ^ 10)⁻¹
    rw [norm_mul]
    refine le_trans (mul_le_mul hE4z hE6z (norm_nonneg _) (mul_nonneg hC4pos.le (inv_nonneg.mpr (pow_nonneg ht.le 4)))) ?_
    have heq : C4 * ((t : ℝ) ^ 4)⁻¹ * (C6 * ((t : ℝ) ^ 6)⁻¹) =
        C4 * C6 * ((t : ℝ) ^ 10)⁻¹ := by
      rw [show ((t : ℝ) ^ 10)⁻¹ = ((t : ℝ) ^ 4)⁻¹ * ((t : ℝ) ^ 6)⁻¹ from
        (inv_pow_mul_inv_pow 4 6).symm]
      ring
    exact le_of_eq heq
  have hE8z : ‖Work.Kernels.E8Fun z‖ ≤ C4 ^ 2 * ((t : ℝ) ^ 8)⁻¹ := by
    show ‖Work.Kernels.E4Fun z ^ 2‖ ≤ C4 ^ 2 * ((t : ℝ) ^ 8)⁻¹
    rw [norm_pow]
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hE4z 2) ?_
    have h3 : ((t : ℝ) ^ 8)⁻¹ = (((t : ℝ) ^ 4)⁻¹) ^ 2 := by
      rw [inv_pow, ← pow_mul]
    have heq : (C4 * ((t : ℝ) ^ 4)⁻¹) ^ 2 = C4 ^ 2 * ((t : ℝ) ^ 8)⁻¹ := by
      rw [mul_pow, h3]
    exact le_of_eq heq
  have hphi1 : ‖Work.Kernels.phitVec z (1 : Fin 3)‖ ≤ C2S * ((t : ℝ) ^ 2)⁻¹ := by
    rw [phitVec_one, norm_mul, hz2]
    calc t ^ 2 * ‖Work.Kernels.E2S z‖ ≤ 1 * (C2S * ((t : ℝ) ^ 2)⁻¹) :=
          mul_le_mul ht2 hE2Sz (norm_nonneg _) (by norm_num)
      _ = C2S * ((t : ℝ) ^ 2)⁻¹ := by ring
  have hphi2 : ‖Work.Kernels.phitVec z (2 : Fin 3)‖ ≤ C2S ^ 2 * ((t : ℝ) ^ 4)⁻¹ := by
    rw [phitVec_two, norm_mul, hz2, norm_pow]
    calc t ^ 2 * ‖Work.Kernels.E2S z‖ ^ 2 ≤ 1 * (C2S * ((t : ℝ) ^ 2)⁻¹) ^ 2 :=
          mul_le_mul ht2 (pow_le_pow_left₀ (norm_nonneg _) hE2Sz 2) (sq_nonneg _) (by norm_num)
      _ = C2S ^ 2 * ((t : ℝ) ^ 4)⁻¹ := by
          rw [one_mul, mul_pow, show ((t : ℝ) ^ 4)⁻¹ = (((t : ℝ) ^ 2)⁻¹) ^ 2 by
            rw [inv_pow, ← pow_mul]]
  have hZP0 : colP8 J (0 : Fin 3) * ‖Work.Kernels.fk (![12, 10, 8] (0 : Fin 3)) z‖ *
      ‖Work.Kernels.phitVec z (0 : Fin 3)‖ ≤ 3 * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by
    rw [colP8_zero, vec128_zero, fk_twelve, phitVec_zero, hz2]
    have h2 : 2 * ‖J‖ + 1 ≤ 3 * ‖J‖ := by linarith [hJ1]
    calc (2 * ‖J‖ + 1) * ‖Work.Kernels.DeltaFun z‖ * t ^ 2
        = ((2 * ‖J‖ + 1) * t ^ 2) * ‖Work.Kernels.DeltaFun z‖ := by ring
      _ ≤ (3 * ‖J‖ * 1) * ‖Work.Kernels.DeltaFun z‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul h2 ht2 (sq_nonneg t) (mul_nonneg (by norm_num) (norm_nonneg _)))
            (norm_nonneg _)
      _ = 3 * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by ring
  have hZP1 : colP8 J (1 : Fin 3) * ‖Work.Kernels.fk (![12, 10, 8] (1 : Fin 3)) z‖ *
      ‖Work.Kernels.phitVec z (1 : Fin 3)‖ ≤
      (2 * C4 * C6 * C2S / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by
    rw [colP8_one, vec128_one, fk_ten]
    have hstep1 : 2 * ‖Work.Kernels.E10Fun z‖ ≤ 2 * (C4 * C6 * ((t : ℝ) ^ 10)⁻¹) :=
      mul_le_mul_of_nonneg_left hE10z (by norm_num)
    have hstep : 2 * ‖Work.Kernels.E10Fun z‖ * ‖Work.Kernels.phitVec z (1 : Fin 3)‖ ≤
        (2 * (C4 * C6 * ((t : ℝ) ^ 10)⁻¹)) * (C2S * ((t : ℝ) ^ 2)⁻¹) :=
      mul_le_mul hstep1 hphi1 (norm_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hC4pos.le hC6pos.le) (inv_nonneg.mpr (pow_nonneg ht.le 10))))
    refine le_trans hstep ?_
    rw [show 2 * (C4 * C6 * ((t : ℝ) ^ 10)⁻¹) * (C2S * ((t : ℝ) ^ 2)⁻¹)
        = 2 * C4 * C6 * C2S * (((t : ℝ) ^ 10)⁻¹ * ((t : ℝ) ^ 2)⁻¹) from by ring]
    rw [inv_pow_mul_inv_pow]
    exact le_mul_of_divisor (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC4pos.le) hC6pos.le) hC2Spos.le) hcLpos hDP
  have hZP2 : colP8 J (2 : Fin 3) * ‖Work.Kernels.fk (![12, 10, 8] (2 : Fin 3)) z‖ *
      ‖Work.Kernels.phitVec z (2 : Fin 3)‖ ≤
      (C4 ^ 2 * C2S ^ 2 / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by
    rw [colP8_two, vec128_two, fk_eight]
    have hstep : 1 * ‖Work.Kernels.E8Fun z‖ * ‖Work.Kernels.phitVec z (2 : Fin 3)‖ ≤
        1 * (C4 ^ 2 * ((t : ℝ) ^ 8)⁻¹) * (C2S ^ 2 * ((t : ℝ) ^ 4)⁻¹) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hE8z (by norm_num)) hphi2 (norm_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hC4pos.le 2) (inv_nonneg.mpr (pow_nonneg ht.le 8))))
    refine le_trans hstep ?_
    rw [show 1 * (C4 ^ 2 * ((t : ℝ) ^ 8)⁻¹) * (C2S ^ 2 * ((t : ℝ) ^ 4)⁻¹)
        = C4 ^ 2 * C2S ^ 2 * (((t : ℝ) ^ 8)⁻¹ * ((t : ℝ) ^ 4)⁻¹) from by ring]
    rw [inv_pow_mul_inv_pow]
    exact le_mul_of_divisor (mul_nonneg (pow_nonneg hC4pos.le 2) (pow_nonneg hC2Spos.le 2)) hcLpos hDP
  have hZP : (∑ j : Fin 3, colP8 J j * ‖Work.Kernels.fk (![12, 10, 8] j) z‖ *
      ‖Work.Kernels.phitVec z j‖) ≤ ZK * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by
    rw [Fin.sum_univ_three, hZKdef]
    have hsplit : (3 + (2 * C4 * C6 * C2S + C4 ^ 2 * C2S ^ 2) / cL) *
        (‖Work.Kernels.DeltaFun z‖ * ‖J‖) =
        3 * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) +
          (2 * C4 * C6 * C2S / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) +
          (C4 ^ 2 * C2S ^ 2 / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by ring
    rw [hsplit]
    linarith [hZP0, hZP1, hZP2]
  have hcol1 : colM8 (Work.Kernels.jInvariantFun τ) (1 : Fin 3) ≤ 1729 + Aj := by
    rw [colM8_one]; linarith [hjτb]
  have hcol2 : colM8 (Work.Kernels.jInvariantFun τ) (2 : Fin 3) ≤ 1 + Aj := by
    rw [colM8_two]; linarith [hjτb]
  have hZM0' : colM8 (Work.Kernels.jInvariantFun τ) (0 : Fin 3) * ‖Work.Kernels.fk (![10, 8, 6] (0 : Fin 3)) z‖ *
      ‖Work.Kernels.psitVec ℓ z (0 : Fin 3)‖ ≤
      (3456 * (C4 * C6 * CLp) / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by
    rw [colM8_zero, vec1086_zero, fk_ten, psitVec_zero]
    have hstep : (2 * 1728) * ‖Work.Kernels.E10Fun z‖ * ‖ℓ.L z‖ ≤
        (2 * 1728) * (C4 * C6 * ((t : ℝ) ^ 10)⁻¹) * CLp :=
      mul_le_mul (mul_le_mul_of_nonneg_left hE10z (by norm_num)) hLz (norm_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hC4pos.le hC6pos.le) (inv_nonneg.mpr (pow_nonneg ht.le 10))))
    refine le_trans hstep ?_
    rw [show (2 * 1728) * (C4 * C6 * ((t : ℝ) ^ 10)⁻¹) * CLp
        = 3456 * (C4 * C6 * CLp) * ((t : ℝ) ^ 10)⁻¹ from by ring]
    calc 3456 * (C4 * C6 * CLp) * ((t : ℝ) ^ 10)⁻¹
        ≤ 3456 * (C4 * C6 * CLp) * ((t : ℝ) ^ 12)⁻¹ :=
          mul_inv_pow_mono (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hC4pos.le hC6pos.le) hCLppos.le)) ht ht1 (by norm_num)
      _ ≤ (3456 * (C4 * C6 * CLp) / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) :=
          le_mul_of_divisor (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hC4pos.le hC6pos.le) hCLppos.le)) hcLpos hDP
  have hZM1' : colM8 (Work.Kernels.jInvariantFun τ) (1 : Fin 3) * ‖Work.Kernels.fk (![10, 8, 6] (1 : Fin 3)) z‖ *
      ‖Work.Kernels.psitVec ℓ z (1 : Fin 3)‖ ≤
      ((1729 + Aj) * (C4 ^ 2 * CW) / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by
    rw [vec1086_one, fk_eight, psitVec_one]
    have hstep1 : colM8 (Work.Kernels.jInvariantFun τ) (1 : Fin 3) *
        ‖Work.Kernels.E8Fun z‖ ≤ (1729 + Aj) * (C4 ^ 2 * ((t : ℝ) ^ 8)⁻¹) :=
      mul_le_mul hcol1 hE8z (norm_nonneg _) (by linarith [hAj1])
    have hstep : colM8 (Work.Kernels.jInvariantFun τ) (1 : Fin 3) * ‖Work.Kernels.E8Fun z‖ *
        ‖Work.Kernels.WFun z‖ ≤
        ((1729 + Aj) * (C4 ^ 2 * ((t : ℝ) ^ 8)⁻¹)) * (CW * ((t : ℝ) ^ 2)⁻¹) :=
      mul_le_mul hstep1 hWz (norm_nonneg _) (mul_nonneg (by linarith [hAj1]) (mul_nonneg (pow_nonneg hC4pos.le 2) (inv_nonneg.mpr (pow_nonneg ht.le 8))))
    refine le_trans hstep ?_
    rw [show ((1729 + Aj) * (C4 ^ 2 * ((t : ℝ) ^ 8)⁻¹)) * (CW * ((t : ℝ) ^ 2)⁻¹)
        = (1729 + Aj) * (C4 ^ 2 * CW) * (((t : ℝ) ^ 8)⁻¹ * ((t : ℝ) ^ 2)⁻¹) from by ring]
    rw [inv_pow_mul_inv_pow]
    calc (1729 + Aj) * (C4 ^ 2 * CW) * ((t : ℝ) ^ 10)⁻¹
        ≤ (1729 + Aj) * (C4 ^ 2 * CW) * ((t : ℝ) ^ 12)⁻¹ :=
          mul_inv_pow_mono (mul_nonneg (by linarith [hAj1]) (mul_nonneg (pow_nonneg hC4pos.le 2) hCWpos.le)) ht ht1 (by norm_num)
      _ ≤ ((1729 + Aj) * (C4 ^ 2 * CW) / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) :=
          le_mul_of_divisor (mul_nonneg (by linarith [hAj1]) (mul_nonneg (pow_nonneg hC4pos.le 2) hCWpos.le)) hcLpos hDP
  have hZM2' : colM8 (Work.Kernels.jInvariantFun τ) (2 : Fin 3) * ‖Work.Kernels.fk (![10, 8, 6] (2 : Fin 3)) z‖ *
      ‖Work.Kernels.psitVec ℓ z (2 : Fin 3)‖ ≤
      ((1 + Aj) * (C6 * CUV) / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by
    rw [vec1086_two, fk_six, psitVec_two]
    have hstep1 : colM8 (Work.Kernels.jInvariantFun τ) (2 : Fin 3) *
        ‖Work.Kernels.E6Fun z‖ ≤ (1 + Aj) * (C6 * ((t : ℝ) ^ 6)⁻¹) :=
      mul_le_mul hcol2 hE6z (norm_nonneg _) (by linarith [hAj1])
    have hstep : colM8 (Work.Kernels.jInvariantFun τ) (2 : Fin 3) * ‖Work.Kernels.E6Fun z‖ *
        ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖ ≤
        ((1 + Aj) * (C6 * ((t : ℝ) ^ 6)⁻¹)) * (CUV * ((t : ℝ) ^ 4)⁻¹) :=
      mul_le_mul hstep1 hUVz (norm_nonneg _) (mul_nonneg (by linarith [hAj1]) (mul_nonneg hC6pos.le (inv_nonneg.mpr (pow_nonneg ht.le 6))))
    refine le_trans hstep ?_
    rw [show ((1 + Aj) * (C6 * ((t : ℝ) ^ 6)⁻¹)) * (CUV * ((t : ℝ) ^ 4)⁻¹)
        = (1 + Aj) * (C6 * CUV) * (((t : ℝ) ^ 6)⁻¹ * ((t : ℝ) ^ 4)⁻¹) from by ring]
    rw [inv_pow_mul_inv_pow]
    calc (1 + Aj) * (C6 * CUV) * ((t : ℝ) ^ 10)⁻¹
        ≤ (1 + Aj) * (C6 * CUV) * ((t : ℝ) ^ 12)⁻¹ :=
          mul_inv_pow_mono (mul_nonneg (by linarith [hAj1]) (mul_nonneg hC6pos.le hCUVpos.le)) ht ht1 (by norm_num)
      _ ≤ ((1 + Aj) * (C6 * CUV) / cL) * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) :=
          le_mul_of_divisor (mul_nonneg (by linarith [hAj1]) (mul_nonneg hC6pos.le hCUVpos.le)) hcLpos hDP
  have hZM : (∑ j : Fin 3, colM8 (Work.Kernels.jInvariantFun τ) j *
      ‖Work.Kernels.fk (![10, 8, 6] j) z‖ * ‖Work.Kernels.psitVec ℓ z j‖) ≤
      ZM * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by
    rw [Fin.sum_univ_three, hZMdef]
    have hsplit : (3456 * (C4 * C6 * CLp) + (1729 + Aj) * (C4 ^ 2 * CW) +
          (1 + Aj) * (C6 * CUV)) / cL * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) =
        3456 * (C4 * C6 * CLp) / cL * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) +
          (1729 + Aj) * (C4 ^ 2 * CW) / cL * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) +
          (1 + Aj) * (C6 * CUV) / cL * (‖Work.Kernels.DeltaFun z‖ * ‖J‖) := by ring
    rw [hsplit]
    linarith [hZM0', hZM1', hZM2']
  have hZPnn : (0 : ℝ) ≤ ∑ j : Fin 3, colP8 J j * ‖Work.Kernels.fk (![12, 10, 8] j) z‖ *
      ‖Work.Kernels.phitVec z j‖ :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (colP8_nonneg J j) (norm_nonneg _))
      (norm_nonneg _))
  have hZMnn : (0 : ℝ) ≤ ∑ j : Fin 3, colM8 (Work.Kernels.jInvariantFun τ) j *
      ‖Work.Kernels.fk (![10, 8, 6] j) z‖ * ‖Work.Kernels.psitVec ℓ z j‖ :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (colM8_nonneg _ j) (norm_nonneg _))
      (norm_nonneg _))
  -- (D) the kernel bound
  have hJne : J ≠ 0 := by
    rw [hJdef]
    have h := hclean t ht τ hτ
    rw [← hz] at h
    exact sub_ne_zero.mpr h
  have hGP : ‖Work.Kernels.growthPrefactor 8 τ z‖ =
      ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖ * ‖J‖ := by
    rw [hJdef, Work.Kernels.growthPrefactor, if_pos rfl, pow_one, norm_mul, norm_mul]
  have hGPpos : 0 < ‖Work.Kernels.growthPrefactor 8 τ z‖ := by
    rw [hGP]
    exact mul_pos (mul_pos (norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ))
      (norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z))) (norm_pos_iff.mpr hJne)
  have hcleansmul : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    have h := hclean t ht τ hτ
    rwa [← hz] at h
  have hKP : ‖Work.Kernels.KPlus 8 τ z‖ ≤ ‖cP‖ * P * ZK := by
    have hsm := Work.Kernels.ClearLink.KPlusClear_eq_smul 8 (Or.inl rfl) τ z hcleansmul
    have hb2 : ‖Work.Kernels.KPlusClear 8 τ z‖ ≤
        ‖cP‖ * P * ZK * ‖Work.Kernels.growthPrefactor 8 τ z‖ := by
      refine le_trans (KPlusClear8_le_cP τ z) ?_
      calc ‖cP‖ * (∑ i : Fin 3, ‖Work.Kernels.phiVec τ i‖ *
              ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ‖) *
            (∑ j : Fin 3, colP8 J j * ‖Work.Kernels.fk (![12, 10, 8] j) z‖ *
              ‖Work.Kernels.phitVec z j‖)
          ≤ ‖cP‖ * (‖Work.Kernels.DeltaFun τ‖ * P) *
              (ZK * (‖Work.Kernels.DeltaFun z‖ * ‖J‖)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hPK (norm_nonneg _)) hZP hZPnn
              (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hP0))
        _ = ‖cP‖ * P * ZK * ‖Work.Kernels.growthPrefactor 8 τ z‖ := by rw [hGP]; ring
    have hmain : ‖Work.Kernels.growthPrefactor 8 τ z‖ * ‖Work.Kernels.KPlus 8 τ z‖ ≤
        ‖Work.Kernels.growthPrefactor 8 τ z‖ * (‖cP‖ * P * ZK) := by
      calc ‖Work.Kernels.growthPrefactor 8 τ z‖ * ‖Work.Kernels.KPlus 8 τ z‖
          = ‖Work.Kernels.growthPrefactor 8 τ z * Work.Kernels.KPlus 8 τ z‖ := (norm_mul _ _).symm
        _ = ‖Work.Kernels.KPlusClear 8 τ z‖ := by rw [hsm]
        _ ≤ ‖cP‖ * P * ZK * ‖Work.Kernels.growthPrefactor 8 τ z‖ := hb2
        _ = ‖Work.Kernels.growthPrefactor 8 τ z‖ * (‖cP‖ * P * ZK) := by ring
    exact le_of_mul_le_mul_left hmain hGPpos
  have hKM : ‖Work.Kernels.KMinus ℓ 8 τ z‖ ≤ ‖cM‖ * Q * ZM := by
    have hsm := Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ 8 (Or.inl rfl) τ z hcleansmul
    have hb2 : ‖Work.Kernels.KMinusClear ℓ 8 τ z‖ ≤
        ‖cM‖ * Q * ZM * ‖Work.Kernels.growthPrefactor 8 τ z‖ := by
      refine le_trans (KMinusClear8_le_cM ℓ τ z) ?_
      calc ‖cM‖ * (∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i‖ *
              ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ‖) *
            (∑ j : Fin 3, colM8 (Work.Kernels.jInvariantFun τ) j *
              ‖Work.Kernels.fk (![10, 8, 6] j) z‖ * ‖Work.Kernels.psitVec ℓ z j‖)
          ≤ ‖cM‖ * (‖Work.Kernels.DeltaFun τ‖ * Q) *
              (ZM * (‖Work.Kernels.DeltaFun z‖ * ‖J‖)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hQM (norm_nonneg _)) hZM hZMnn
              (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hQ0))
        _ = ‖cM‖ * Q * ZM * ‖Work.Kernels.growthPrefactor 8 τ z‖ := by rw [hGP]; ring
    have hmain : ‖Work.Kernels.growthPrefactor 8 τ z‖ * ‖Work.Kernels.KMinus ℓ 8 τ z‖ ≤
        ‖Work.Kernels.growthPrefactor 8 τ z‖ * (‖cM‖ * Q * ZM) := by
      calc ‖Work.Kernels.growthPrefactor 8 τ z‖ * ‖Work.Kernels.KMinus ℓ 8 τ z‖
          = ‖Work.Kernels.growthPrefactor 8 τ z * Work.Kernels.KMinus ℓ 8 τ z‖ := (norm_mul _ _).symm
        _ = ‖Work.Kernels.KMinusClear ℓ 8 τ z‖ := by rw [hsm]
        _ ≤ ‖cM‖ * Q * ZM * ‖Work.Kernels.growthPrefactor 8 τ z‖ := hb2
        _ = ‖Work.Kernels.growthPrefactor 8 τ z‖ * (‖cM‖ * Q * ZM) := by ring
    exact le_of_mul_le_mul_left hmain hGPpos
  have hKfun : ‖Work.Kernels.Kfun ℓ 8 τ z‖ ≤ (‖cP‖ * P * ZK + ‖cM‖ * Q * ZM) / 2 := by
    have h1 : ‖Work.Kernels.Kfun ℓ 8 τ z‖ ≤
        (‖Work.Kernels.KPlus 8 τ z‖ + ‖Work.Kernels.KMinus ℓ 8 τ z‖) / 2 := by
      show ‖(Work.Kernels.KPlus 8 τ z + Work.Kernels.KMinus ℓ 8 τ z) / 2‖ ≤ _
      rw [norm_div]
      norm_num
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    exact le_trans h1 (div_le_div_of_nonneg_right (add_le_add hKP hKM) (by norm_num))
  rw [Work.Kernels.Kaxis, dif_pos ht, ← hz]
  exact le_trans hKfun (by linarith)


end

end Work.Asymptotics
