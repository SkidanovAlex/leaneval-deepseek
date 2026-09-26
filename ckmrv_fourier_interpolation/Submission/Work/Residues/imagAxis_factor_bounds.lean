import Mathlib
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Kernels.Theorem31
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp

namespace Work.Residues

open UpperHalfPlane

noncomputable section

/-! ## The imaginary axis `τ = it` -/

/-- The imaginary part of `it` is `t`. -/
private lemma imagAxis_im (t : ℝ) (ht : 0 < t) :
    (Work.Kernels.imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

/-- The complex number underlying `it : ℍ` is `t * I`. -/
private lemma imagAxis_coe (t : ℝ) (ht : 0 < t) :
    ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl

/-- `‖it‖ = t` for `t > 0`. -/
private lemma norm_imagAxis_coe (t : ℝ) (ht : 0 < t) :
    ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)‖ = t := by
  rw [imagAxis_coe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht]

/-- The moderate-growth scale at `it` is `1 + t⁻¹ + t`. -/
private lemma scale_imagAxis (t : ℝ) (ht : 0 < t) :
    Work.Kernels.scale (Work.Kernels.imagAxis t ht) = 1 + t⁻¹ + t := by
  rw [Work.Kernels.scale, imagAxis_im t ht, norm_imagAxis_coe t ht]

/-- If `‖x - 1‖ ≤ C` then `‖x‖ ≤ 1 + C`. -/
private lemma norm_le_one_add_of_sub_one {x : ℂ} {C : ℝ} (h : ‖x - 1‖ ≤ C) :
    ‖x‖ ≤ 1 + C := by
  have htri := norm_add_le (x - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at htri
  linarith

/-- `B / (2⁻¹ e^{-2πt}) = B * 2 * e^{2πt}`. -/
private lemma div_half_exp_neg_eq (B t : ℝ) :
    B / ((1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t))) = B * 2 * Real.exp (2 * Real.pi * t) := by
  rw [Real.exp_neg]
  field_simp

/-- `‖X / Y‖ ≤ B * 2 * e^{2πt}` when `0 ≤ B`, `‖X‖ ≤ B` and
`2⁻¹ e^{-2πt} ≤ ‖Y‖`. -/
private lemma norm_div_le_two_mul_exp {X Y : ℂ} {B t : ℝ} (hB : 0 ≤ B)
    (hX : ‖X‖ ≤ B) (hY : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) ≤ ‖Y‖) :
    ‖X / Y‖ ≤ B * 2 * Real.exp (2 * Real.pi * t) := by
  have hd : (0 : ℝ) < (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) := by positivity
  have hmain : ‖X / Y‖ ≤ B / ((1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t))) := by
    calc ‖X / Y‖ = ‖X‖ / ‖Y‖ := norm_div _ _
      _ ≤ B / ((1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t))) := div_le_div₀ hB hX hd hY
  exact le_trans hmain (le_of_eq (div_half_exp_neg_eq B t))

/-- `‖X³ / Y‖ ≤ B * 2 * e^{2πt}` when `0 ≤ B`, `‖X‖ ≤ B ^ (1/3)`-style bounds; here
`‖X‖ ≤ 1 + C` and `2⁻¹ e^{-2πt} ≤ ‖Y‖` gives `‖X³ / Y‖ ≤ 2 (1 + C)³ e^{2πt}`. -/
private lemma norm_cube_div_le_exp {X Y : ℂ} {C t : ℝ} (hC : 0 ≤ C)
    (hX : ‖X‖ ≤ 1 + C) (hY : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) ≤ ‖Y‖) :
    ‖X ^ 3 / Y‖ ≤ 2 * (1 + C) ^ 3 * Real.exp (2 * Real.pi * t) := by
  have hnum : ‖X ^ 3‖ ≤ (1 + C) ^ 3 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hX 3
  have h := norm_div_le_two_mul_exp (B := (1 + C) ^ 3) (by positivity) hnum hY
  calc ‖X ^ 3 / Y‖ ≤ (1 + C) ^ 3 * 2 * Real.exp (2 * Real.pi * t) := h
    _ = 2 * (1 + C) ^ 3 * Real.exp (2 * Real.pi * t) := by ring

theorem imagAxis_factor_bounds (ℓ : Work.Kernels.LogLambdaData) :
    ∃ CW Cj CE CUV CLL M : ℝ, 0 ≤ CW ∧ 0 < Cj ∧ 0 < CE ∧ 0 ≤ CUV ∧ 0 ≤ CLL ∧ 0 ≤ M ∧
      ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
        ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖ ≤ CW ∧
        ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ ≤
            Cj * Real.exp (2 * Real.pi * t) ∧
        ‖Work.Kernels.E10Fun (Work.Kernels.imagAxis t ht)
            / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ≤
          CE * Real.exp (2 * Real.pi * t) ∧
        ‖Work.Kernels.E14Fun (Work.Kernels.imagAxis t ht)
            / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ≤
          CE * Real.exp (2 * Real.pi * t) ∧
        ‖Work.Kernels.UFun (Work.Kernels.imagAxis t ht) ^ 2
            - Work.Kernels.VFun (Work.Kernels.imagAxis t ht) ^ 2‖ ≤ CUV ∧
        ‖ℓ.L (Work.Kernels.imagAxis t ht)‖ ≤ CLL * (1 + t) ^ M := by
  obtain ⟨CU, hCU, hUb⟩ := UFun_decay
  obtain ⟨CW, hCW, hWb⟩ := WFun_decay
  obtain ⟨CV, hCV, hVb⟩ := VFun_decay
  obtain ⟨C4, hC4, h4b⟩ := E4Fun_decay
  obtain ⟨C6, hC6, h6b⟩ := E6Fun_decay
  obtain ⟨α, N, hα, hN, hLb⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ ℓ.L).mp ℓ.memP
  refine ⟨1 + CW, 2 * (1 + C4) ^ 3, 2 * ((1 + C4) ^ 2 * (1 + C6)),
    (1 + CU) ^ 2 + CV ^ 2, α * 2 ^ N, N, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [hCW.le]
  · exact mul_pos (by norm_num) (pow_pos (by linarith) 3)
  · exact mul_pos (by norm_num) (mul_pos (pow_pos (by linarith) 2) (by linarith))
  · positivity
  · exact mul_nonneg hα (by positivity)
  · exact hN
  · intro t ht ht1
    set p : ℍ := Work.Kernels.imagAxis t ht with hp
    have him : p.im = t := by rw [hp]; exact imagAxis_im t ht
    have h1im : 1 ≤ p.im := by rw [him]; exact ht1
    have hscale : Work.Kernels.scale p = 1 + t⁻¹ + t := by
      rw [hp]; exact scale_imagAxis t ht
    have htnn : 0 ≤ t := ht.le
    have hexp1 : Real.exp (-(Real.pi * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, htnn]
    have hexp2 : Real.exp (-(2 * Real.pi * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, htnn]
    -- upper bounds coming from the decay theorems
    have hUfin : ‖Work.Kernels.UFun p‖ ≤ 1 + CU := by
      have h := hUb p h1im
      rw [him] at h
      refine norm_le_one_add_of_sub_one ?_
      calc ‖Work.Kernels.UFun p - 1‖ ≤ CU * Real.exp (-(Real.pi * t)) := h
        _ ≤ CU * 1 := mul_le_mul_of_nonneg_left hexp1 hCU.le
        _ = CU := mul_one _
    have hWfin : ‖Work.Kernels.WFun p‖ ≤ 1 + CW := by
      have h := hWb p h1im
      rw [him] at h
      refine norm_le_one_add_of_sub_one ?_
      calc ‖Work.Kernels.WFun p - 1‖ ≤ CW * Real.exp (-(Real.pi * t)) := h
        _ ≤ CW * 1 := mul_le_mul_of_nonneg_left hexp1 hCW.le
        _ = CW := mul_one _
    have hVfin : ‖Work.Kernels.VFun p‖ ≤ CV := by
      have h := hVb p h1im
      rw [him] at h
      calc ‖Work.Kernels.VFun p‖ ≤ CV * Real.exp (-(Real.pi * t)) := h
        _ ≤ CV * 1 := mul_le_mul_of_nonneg_left hexp1 hCV.le
        _ = CV := mul_one _
    have hE4fin : ‖Work.Kernels.E4Fun p‖ ≤ 1 + C4 := by
      have h := h4b p h1im
      rw [him] at h
      refine norm_le_one_add_of_sub_one ?_
      calc ‖Work.Kernels.E4Fun p - 1‖ ≤ C4 * Real.exp (-(2 * Real.pi * t)) := h
        _ ≤ C4 * 1 := mul_le_mul_of_nonneg_left hexp2 hC4.le
        _ = C4 := mul_one _
    have hE6fin : ‖Work.Kernels.E6Fun p‖ ≤ 1 + C6 := by
      have h := h6b p h1im
      rw [him] at h
      refine norm_le_one_add_of_sub_one ?_
      calc ‖Work.Kernels.E6Fun p - 1‖ ≤ C6 * Real.exp (-(2 * Real.pi * t)) := h
        _ ≤ C6 * 1 := mul_le_mul_of_nonneg_left hexp2 hC6.le
        _ = C6 := mul_one _
    -- lower bound for `Δ` on the imaginary axis
    have hΔlow : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) ≤
        ‖Work.Kernels.DeltaFun p‖ := by
      have := Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1
      rwa [← hp] at this
    -- the `j`-invariant
    have hjfin : ‖Work.Kernels.jInvariantFun p‖ ≤
        2 * (1 + C4) ^ 3 * Real.exp (2 * Real.pi * t) := by
      have hE4cube : ‖Work.Kernels.E4Fun p ^ 3‖ ≤ (1 + C4) ^ 3 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4fin 3
      have hb : (0 : ℝ) ≤ (1 + C4) ^ 3 := by positivity
      have h := norm_div_le_two_mul_exp (X := Work.Kernels.E4Fun p ^ 3)
        (Y := Work.Kernels.DeltaFun p) (B := (1 + C4) ^ 3) hb hE4cube hΔlow
      have hEq : Work.Kernels.jInvariantFun p
          = Work.Kernels.E4Fun p ^ 3 / Work.Kernels.DeltaFun p := rfl
      rw [hEq]
      calc ‖Work.Kernels.E4Fun p ^ 3 / Work.Kernels.DeltaFun p‖
          ≤ (1 + C4) ^ 3 * 2 * Real.exp (2 * Real.pi * t) := h
        _ = 2 * (1 + C4) ^ 3 * Real.exp (2 * Real.pi * t) := by ring
    -- `E₁₀ / Δ` and `E₁₄ / Δ`
    have hE10bound : ‖Work.Kernels.E10Fun p‖ ≤ (1 + C4) * (1 + C6) := by
      have hEq : Work.Kernels.E10Fun p = Work.Kernels.E4Fun p * Work.Kernels.E6Fun p := rfl
      rw [hEq, norm_mul]
      exact mul_le_mul hE4fin hE6fin (norm_nonneg _) (by linarith)
    have hE10fin : ‖Work.Kernels.E10Fun p / Work.Kernels.DeltaFun p‖ ≤
        2 * ((1 + C4) ^ 2 * (1 + C6)) * Real.exp (2 * Real.pi * t) := by
      have hb : (0 : ℝ) ≤ (1 + C4) * (1 + C6) :=
        mul_nonneg (by linarith) (by linarith)
      have h := norm_div_le_two_mul_exp (X := Work.Kernels.E10Fun p)
        (Y := Work.Kernels.DeltaFun p) (B := (1 + C4) * (1 + C6)) hb hE10bound hΔlow
      refine le_trans h ?_
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      nlinarith [hC4, hC6]
    have hE14bound : ‖Work.Kernels.E14Fun p‖ ≤ (1 + C4) ^ 2 * (1 + C6) := by
      have hEq : Work.Kernels.E14Fun p = Work.Kernels.E4Fun p ^ 2 * Work.Kernels.E6Fun p := rfl
      rw [hEq, norm_mul, norm_pow]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE4fin 2) hE6fin
        (norm_nonneg _) (by positivity)
    have hE14fin : ‖Work.Kernels.E14Fun p / Work.Kernels.DeltaFun p‖ ≤
        2 * ((1 + C4) ^ 2 * (1 + C6)) * Real.exp (2 * Real.pi * t) := by
      have hb : (0 : ℝ) ≤ (1 + C4) ^ 2 * (1 + C6) := by positivity
      have h := norm_div_le_two_mul_exp (X := Work.Kernels.E14Fun p)
        (Y := Work.Kernels.DeltaFun p) (B := (1 + C4) ^ 2 * (1 + C6)) hb hE14bound hΔlow
      calc ‖Work.Kernels.E14Fun p / Work.Kernels.DeltaFun p‖
          ≤ ((1 + C4) ^ 2 * (1 + C6)) * 2 * Real.exp (2 * Real.pi * t) := h
        _ = 2 * ((1 + C4) ^ 2 * (1 + C6)) * Real.exp (2 * Real.pi * t) := by ring
    -- `U² − V²`
    have hUVfin : ‖Work.Kernels.UFun p ^ 2 - Work.Kernels.VFun p ^ 2‖ ≤
        (1 + CU) ^ 2 + CV ^ 2 := by
      calc ‖Work.Kernels.UFun p ^ 2 - Work.Kernels.VFun p ^ 2‖
          ≤ ‖Work.Kernels.UFun p ^ 2‖ + ‖Work.Kernels.VFun p ^ 2‖ := norm_sub_le _ _
        _ = ‖Work.Kernels.UFun p‖ ^ 2 + ‖Work.Kernels.VFun p‖ ^ 2 := by
              rw [norm_pow (Work.Kernels.UFun p) 2, norm_pow (Work.Kernels.VFun p) 2]
        _ ≤ (1 + CU) ^ 2 + CV ^ 2 :=
              add_le_add (pow_le_pow_left₀ (norm_nonneg _) hUfin 2)
                (pow_le_pow_left₀ (norm_nonneg _) hVfin 2)
    -- `𝓛` on the imaginary axis
    have hLfin : ‖ℓ.L p‖ ≤ (α * 2 ^ N) * (1 + t) ^ N := by
      have h1 := hLb p (Set.mem_univ p)
      rw [hscale] at h1
      have hs0 : 0 ≤ 1 + t⁻¹ + t := by
        have : 0 ≤ t⁻¹ := inv_nonneg.mpr htnn
        linarith
      have hle : 1 + t⁻¹ + t ≤ 2 * (1 + t) := by
        have hinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
        linarith
      have hrpow : (1 + t⁻¹ + t) ^ N ≤ (2 * (1 + t)) ^ N := Real.rpow_le_rpow hs0 hle hN
      have hmul : (2 * (1 + t)) ^ N = 2 ^ N * (1 + t) ^ N :=
        Real.mul_rpow (by norm_num) (by linarith)
      rw [hmul] at hrpow
      refine le_trans h1 ?_
      calc α * (1 + t⁻¹ + t) ^ N ≤ α * (2 ^ N * (1 + t) ^ N) :=
            mul_le_mul_of_nonneg_left hrpow hα
        _ = (α * 2 ^ N) * (1 + t) ^ N := by ring
    exact ⟨hWfin, hjfin, hE10fin, hE14fin, hUVfin, hLfin⟩

end

end Work.Residues
