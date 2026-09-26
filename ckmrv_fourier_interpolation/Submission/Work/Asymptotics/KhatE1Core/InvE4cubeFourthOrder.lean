import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KPlus24Refs
import Submission.Work.Asymptotics.KhatE1Core.DKPlusBounds
import Submission.Work.Asymptotics.K24FZ

/-!
# `(E₄ z)⁻³` to second order at the cusp

`(E₄ z)⁻¹ ^ 3 - (1 - 720q + 339120q²) = O(‖q(z)‖³)` on `Im z ≥ 3`, `q = qParamFun z`.
This is the deviation `dI4` of `KPlus24Refs.lean`; plan and constants in `InvE4Plan.lean`.

Proof: `dI4 = (E₄⁻¹)³(1 - E₄³T)` (`T = I4Ref z`), and
`1 - E₄³T = (1 - P³T) + (P³ - E₄³)T` with `P = E4Ref z`; the first bracket is
`q³(-132019200 - 48991910400q - … - 3417548267520000q⁵)` (bounded by `4683905430105600‖q‖³`)
and the second is `(P - E₄)(P² + PE₄ + E₄²)T` with `‖P - E₄‖ = ‖dE₄‖ ≤ C₄‖q‖³`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

theorem InvE4cubeFourthOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 3 ≤ UpperHalfPlane.im z →
      ‖(Work.Kernels.E4Fun z)⁻¹ ^ 3 - (1 - 720 * Work.Kernels.qParamFun z
        + 339120 * (Work.Kernels.qParamFun z) ^ 2)‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C4, hC4, h4⟩ := dE4_bound
  have hC40 : (0 : ℝ) ≤ C4 := hC4.le
  refine ⟨8 * (4683905430105600 + C4 * (((2401 + C4) ^ 2 + (2401 + C4) * 2401 + 2401 ^ 2))
      * 339841) + 1, by positivity, fun z hz => ?_⟩
  set q : ℂ := Work.Kernels.qParamFun z with hqdef
  have hqn : ‖q‖ = Real.exp (-(2 * Real.pi * z.im)) := Work.Asymptotics.norm_qParamFun z
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  have hq1 : ‖q‖ ≤ 1 := by
    rw [hqn, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq3n : (0 : ℝ) ≤ ‖q‖ ^ 3 := pow_nonneg hq0 3
  have hq3le : ‖q‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  have hE4inv : ‖(Work.Kernels.E4Fun z)⁻¹‖ ≤ 2 :=
    Work.Asymptotics.K24F.E4_inv_le_two_three z hz
  have hE4ne : Work.Kernels.E4Fun z ≠ 0 := Work.Asymptotics.K24F.E4_ne_zero_three z hz
  have hPn : ‖E4Ref z‖ ≤ 2401 := norm_E4Ref_le hz1
  have hd4 : ‖dE4 z‖ ≤ C4 * ‖q‖ ^ 3 := h4 z hz1
  have hEn : ‖Work.Kernels.E4Fun z‖ ≤ 2401 + C4 := by
    have hEq : Work.Kernels.E4Fun z = E4Ref z + dE4 z := by simp only [dE4]; ring
    calc ‖Work.Kernels.E4Fun z‖ = ‖E4Ref z + dE4 z‖ := by rw [hEq]
      _ ≤ ‖E4Ref z‖ + ‖dE4 z‖ := norm_add_le _ _
      _ ≤ 2401 + C4 := by nlinarith [hPn, hd4, hq0, hq1, hq3le, hC40]
  have hTn : ‖I4Ref z‖ ≤ 339841 := by
    have h2 : ‖(339120 : ℂ) * q ^ 2‖ = 339120 * ‖q‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
    have h2le : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
    calc ‖I4Ref z‖ = ‖(1 : ℂ) - 720 * q + 339120 * q ^ 2‖ := by
          simp only [I4Ref, hqdef]
      _ ≤ ‖(1 : ℂ) - 720 * q‖ + ‖(339120 : ℂ) * q ^ 2‖ := norm_add_le _ _
      _ ≤ (1 + 720 * ‖q‖) + 339120 * ‖q‖ ^ 2 := by
          rw [h2]
          have h1 : ‖(1 : ℂ) - 720 * q‖ ≤ 1 + 720 * ‖q‖ := by
            refine le_trans (norm_sub_le _ _) (le_of_eq ?_)
            rw [norm_one, norm_mul]
            norm_num
          linarith
      _ ≤ 339841 := by nlinarith [hq0, hq1, h2le]
  -- (1) factor out `(E₄⁻¹)³`
  have hfac : (Work.Kernels.E4Fun z)⁻¹ ^ 3 - I4Ref z
      = (Work.Kernels.E4Fun z)⁻¹ ^ 3 * (1 - Work.Kernels.E4Fun z ^ 3 * I4Ref z) := by
    have h3 : (Work.Kernels.E4Fun z)⁻¹ ^ 3 * Work.Kernels.E4Fun z ^ 3 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hE4ne, one_pow]
    rw [mul_sub, mul_one, ← mul_assoc, h3, one_mul]
  -- (2) the two brackets
  have hsplit : (1 : ℂ) - Work.Kernels.E4Fun z ^ 3 * I4Ref z
      = (1 - E4Ref z ^ 3 * I4Ref z)
        + (E4Ref z ^ 3 - Work.Kernels.E4Fun z ^ 3) * I4Ref z := by ring
  have hA : ‖(1 : ℂ) - E4Ref z ^ 3 * I4Ref z‖ ≤ 4683905430105600 * ‖q‖ ^ 3 := by
    have hid : (1 : ℂ) - E4Ref z ^ 3 * I4Ref z
        = q ^ 3 * ((-132019200 : ℂ) - 48991910400 * q - 5467336704000 * q ^ 2
            - 128913887232000 * q ^ 3 - 1131926814720000 * q ^ 4
            - 3417548267520000 * q ^ 5) := by
      simp only [E4Ref, I4Ref, hqdef]
      ring
    rw [hid, norm_mul, norm_pow]
    have hR : ‖(-132019200 : ℂ) - 48991910400 * q - 5467336704000 * q ^ 2
        - 128913887232000 * q ^ 3 - 1131926814720000 * q ^ 4
        - 3417548267520000 * q ^ 5‖ ≤ 4683905430105600 := by
      have h2 : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
      have h3 : ‖q‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
      have h4' : ‖q‖ ^ 4 ≤ 1 := pow_le_one₀ hq0 hq1
      have h5 : ‖q‖ ^ 5 ≤ 1 := pow_le_one₀ hq0 hq1
      have e0 : ‖(-132019200 : ℂ) - 48991910400 * q‖ ≤ 132019200 + 48991910400 * ‖q‖ := by
        refine le_trans (norm_sub_le _ _) (le_of_eq ?_)
        rw [show ‖(-132019200 : ℂ)‖ = 132019200 from by norm_num, norm_mul,
          show ‖(48991910400 : ℂ)‖ = 48991910400 from by norm_num]
      have e1 : ‖(-132019200 : ℂ) - 48991910400 * q - 5467336704000 * q ^ 2‖
          ≤ 132019200 + 48991910400 * ‖q‖ + 5467336704000 * ‖q‖ ^ 2 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_pow, show ‖(5467336704000 : ℂ)‖ = 5467336704000 from by norm_num]
        linarith [e0]
      have e2 : ‖(-132019200 : ℂ) - 48991910400 * q - 5467336704000 * q ^ 2
          - 128913887232000 * q ^ 3‖
          ≤ 132019200 + 48991910400 * ‖q‖ + 5467336704000 * ‖q‖ ^ 2
            + 128913887232000 * ‖q‖ ^ 3 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_pow, show ‖(128913887232000 : ℂ)‖ = 128913887232000 from by norm_num]
        linarith [e1]
      have e3 : ‖(-132019200 : ℂ) - 48991910400 * q - 5467336704000 * q ^ 2
          - 128913887232000 * q ^ 3 - 1131926814720000 * q ^ 4‖
          ≤ 132019200 + 48991910400 * ‖q‖ + 5467336704000 * ‖q‖ ^ 2
            + 128913887232000 * ‖q‖ ^ 3 + 1131926814720000 * ‖q‖ ^ 4 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_pow, show ‖(1131926814720000 : ℂ)‖ = 1131926814720000 from by norm_num]
        linarith [e2]
      have e4 : ‖(-132019200 : ℂ) - 48991910400 * q - 5467336704000 * q ^ 2
          - 128913887232000 * q ^ 3 - 1131926814720000 * q ^ 4
          - 3417548267520000 * q ^ 5‖
          ≤ 132019200 + 48991910400 * ‖q‖ + 5467336704000 * ‖q‖ ^ 2
            + 128913887232000 * ‖q‖ ^ 3 + 1131926814720000 * ‖q‖ ^ 4
            + 3417548267520000 * ‖q‖ ^ 5 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_pow, show ‖(3417548267520000 : ℂ)‖ = 3417548267520000 from by norm_num]
        linarith [e3]
      linarith [e4, hq0, hq1, h2, h3, h4', h5]
    calc ‖q‖ ^ 3 * ‖(-132019200 : ℂ) - 48991910400 * q - 5467336704000 * q ^ 2
          - 128913887232000 * q ^ 3 - 1131926814720000 * q ^ 4
          - 3417548267520000 * q ^ 5‖
        ≤ ‖q‖ ^ 3 * 4683905430105600 := mul_le_mul_of_nonneg_left hR (pow_nonneg hq0 3)
      _ = 4683905430105600 * ‖q‖ ^ 3 := by ring
  have hB : ‖(E4Ref z ^ 3 - Work.Kernels.E4Fun z ^ 3) * I4Ref z‖
      ≤ C4 * (((2401 + C4) ^ 2 + (2401 + C4) * 2401 + 2401 ^ 2)) * 339841 * ‖q‖ ^ 3 := by
    have hcube : E4Ref z ^ 3 - Work.Kernels.E4Fun z ^ 3
        = (E4Ref z - Work.Kernels.E4Fun z)
          * (E4Ref z ^ 2 + E4Ref z * Work.Kernels.E4Fun z + Work.Kernels.E4Fun z ^ 2) := by ring
    have hPm : E4Ref z - Work.Kernels.E4Fun z = -dE4 z := by simp only [dE4]; ring
    have hfacn : ‖E4Ref z ^ 2 + E4Ref z * Work.Kernels.E4Fun z + Work.Kernels.E4Fun z ^ 2‖
        ≤ (2401 + C4) ^ 2 + (2401 + C4) * 2401 + 2401 ^ 2 := by
      have h1 : ‖E4Ref z ^ 2‖ ≤ 2401 ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hPn 2
      have h2 : ‖E4Ref z * Work.Kernels.E4Fun z‖ ≤ 2401 * (2401 + C4) := by
        rw [norm_mul]
        exact mul_le_mul hPn hEn (norm_nonneg _) (by linarith)
      have h3 : ‖Work.Kernels.E4Fun z ^ 2‖ ≤ (2401 + C4) ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hEn 2
      refine le_trans (norm_add_le _ _) (le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_)
      nlinarith [h1, h2, h3]
    calc ‖(E4Ref z ^ 3 - Work.Kernels.E4Fun z ^ 3) * I4Ref z‖
        = ‖(E4Ref z - Work.Kernels.E4Fun z)
            * (E4Ref z ^ 2 + E4Ref z * Work.Kernels.E4Fun z + Work.Kernels.E4Fun z ^ 2)
            * I4Ref z‖ := by rw [hcube]
      _ ≤ (C4 * ‖q‖ ^ 3) * ((2401 + C4) ^ 2 + (2401 + C4) * 2401 + 2401 ^ 2) * 339841 := by
          rw [norm_mul, norm_mul]
          refine mul_le_mul (mul_le_mul ?_ hfacn (norm_nonneg _) (by positivity)) hTn
            (norm_nonneg _) (by positivity)
          rw [hPm, norm_neg]
          exact hd4
      _ = C4 * (((2401 + C4) ^ 2 + (2401 + C4) * 2401 + 2401 ^ 2)) * 339841 * ‖q‖ ^ 3 := by ring
  have hmain : ‖(1 : ℂ) - Work.Kernels.E4Fun z ^ 3 * I4Ref z‖
      ≤ 4683905430105600 * ‖q‖ ^ 3
        + C4 * (((2401 + C4) ^ 2 + (2401 + C4) * 2401 + 2401 ^ 2)) * 339841 * ‖q‖ ^ 3 := by
    rw [hsplit]
    exact le_trans (norm_add_le _ _) (add_le_add hA hB)
  have hE4inv3 : ‖(Work.Kernels.E4Fun z)⁻¹ ^ 3‖ ≤ 8 := by
    rw [norm_pow]
    calc ‖(Work.Kernels.E4Fun z)⁻¹‖ ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hE4inv 3
      _ = 8 := by norm_num
  rw [show (1 : ℂ) - 720 * Work.Kernels.qParamFun z
        + 339120 * Work.Kernels.qParamFun z ^ 2 = I4Ref z from by simp only [I4Ref, hqdef]]
  rw [hfac, norm_mul]
  calc ‖(Work.Kernels.E4Fun z)⁻¹ ^ 3‖ * ‖(1 : ℂ) - Work.Kernels.E4Fun z ^ 3 * I4Ref z‖
      ≤ 8 * (4683905430105600 * ‖q‖ ^ 3
          + C4 * (((2401 + C4) ^ 2 + (2401 + C4) * 2401 + 2401 ^ 2)) * 339841 * ‖q‖ ^ 3) :=
        mul_le_mul hE4inv3 hmain (norm_nonneg _) (by norm_num)
    _ = 8 * (4683905430105600 + C4 * (((2401 + C4) ^ 2 + (2401 + C4) * 2401 + 2401 ^ 2))
          * 339841) * ‖q‖ ^ 3 := by ring
    _ ≤ (8 * (4683905430105600 + C4 * (((2401 + C4) ^ 2 + (2401 + C4) * 2401 + 2401 ^ 2))
          * 339841) + 1) * ‖q‖ ^ 3 := by
        nlinarith [hq3n, hC40]

end

end Work.Asymptotics.KhatE1Core
