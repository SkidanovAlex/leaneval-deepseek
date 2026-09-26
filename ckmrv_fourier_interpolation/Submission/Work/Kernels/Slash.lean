/-
# The slash operator preserves the class `𝒫`

This file proves Lemma "HCmoderategrowthPslashed" of CKMRV (Ann. of Math. 196 (2022)),
Section 4.1: the slash operator `F ↦ F ∣[k] γ` maps functions of moderate growth on a set
`S ⊆ ℍ` to functions of moderate growth on the preimage `γ⁻¹ S`.  In particular the class
`𝒫 = Work.Kernels.InP` is preserved, so that `𝒫` is a representation space for `SL(2,ℤ)`.

The proof uses the bounds
* `Work.Kernels.SlashBounds.jFun_bound_upper` : `‖j(γ,τ)‖ ≤ C (1 + ‖τ‖)`,
* `Work.Kernels.SlashBounds.jFun_bound_inv` : `‖j(γ,τ)‖⁻¹ ≤ 1 + (im τ)⁻¹`,
* `Work.Kernels.SlashBounds.nFun_bound` : `‖a τ + b‖ ≤ C (1 + ‖τ‖)`,
* `Work.Kernels.SlashBounds.jFun_rpow_bound` : `‖j(γ,τ)‖ ^ m ≤ C (S τ) ^ N` for every `m`,
together with `(γ • τ).im = (im τ)/‖j‖²` and `‖(γ • τ)‖ = ‖nFun‖/‖jFun‖`.
-/
import Mathlib
import Submission.Work.Kernels.SlashDefs
import Submission.Work.Kernels.SlashBounds.jFun_bound_upper
import Submission.Work.Kernels.SlashBounds.jFun_bound_inv
import Submission.Work.Kernels.SlashBounds.jFun_rpow_bound
import Submission.Work.Kernels.SlashBounds.nFun_bound

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

lemma rpow_three_eq (x : ℝ) : x ^ (3 : ℝ) = x ^ 3 := by
  norm_num [Real.rpow_natCast]

lemma rpow_two_eq (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  norm_num [Real.rpow_natCast]

/-- The bound `scale (γ • τ) ≤ C * (scale τ) ^ 3`, the geometric content of Lemma 4.1 of
CKMRV: a Möbius transformation changes the scale `1 + (im τ)⁻¹ + |τ|` by a factor that is
at most cubic in the scale, uniformly in `τ`. -/
lemma scale_smul_le (γ : SL(2,ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, scale (γ • τ) ≤ C * (scale τ) ^ (3 : ℝ) := by
  obtain ⟨Cu, hCu0, hCu⟩ := SlashBounds.jFun_bound_upper γ
  obtain ⟨Cn, hCn0, hCn⟩ := SlashBounds.nFun_bound γ
  set Cq : ℝ := 2 * max Cu 1 with hCq
  have hCq0 : 0 ≤ Cq := by rw [hCq]; positivity
  have htwoCu_le_Cq : 2 * Cu ≤ Cq := by rw [hCq]; linarith [le_max_left Cu 1]
  set M : ℝ := 1 + Cq ^ 2 + 2 * Cn with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨M, hM0, fun τ => ?_⟩
  set A : ℝ := ‖jFun γ (τ : ℂ)‖ with hA
  set B : ℝ := ‖(τ : ℂ)‖ with hB
  set s : ℝ := scale τ with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact one_le_scale τ
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hA0 : 0 < A := by rw [hA]; exact norm_pos_iff.mpr (jFun_ne_zero γ τ)
  have hBs : B ≤ s := by rw [hB, hs, scale]; linarith [inv_nonneg.mpr τ.im_pos.le]
  have hA_le : A ≤ Cq * s := by
    have h1 : 1 + B ≤ 2 * s := by linarith
    calc A ≤ Cu * (1 + B) := by rw [hA]; exact hCu τ
      _ ≤ Cu * (2 * s) := mul_le_mul_of_nonneg_left h1 hCu0
      _ = (2 * Cu) * s := by ring
      _ ≤ Cq * s := mul_le_mul_of_nonneg_right htwoCu_le_Cq hs0.le
  have hAinv : A⁻¹ ≤ s := by
    rw [hA]
    refine le_trans (SlashBounds.jFun_bound_inv γ τ) ?_
    rw [hs, scale]; linarith [norm_nonneg (τ : ℂ)]
  have him : (γ • τ).im = τ.im / A ^ 2 := by rw [im_smul_eq γ τ, ← hA]
  have hnorm_eq : ‖(((γ • τ : ℍ)) : ℂ)‖ = ‖nFun γ (τ : ℂ)‖ / A := by
    rw [coe_smul_eq γ τ, norm_div, ← hA]
  have hnorm_le : ‖(((γ • τ : ℍ)) : ℂ)‖ ≤ 2 * Cn * s ^ (2 : ℝ) := by
    have h1 : ‖nFun γ (τ : ℂ)‖ ≤ Cn * (1 + B) := by rw [hB]; exact hCn τ
    have h4 : Cn * (1 + B) * A⁻¹ ≤ Cn * (2 * s) * s := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : 1 + B ≤ 2 * s) hCn0) hAinv
        (inv_nonneg.mpr hA0.le) (by positivity)
    calc ‖(((γ • τ : ℍ)) : ℂ)‖ = ‖nFun γ (τ : ℂ)‖ / A := hnorm_eq
      _ ≤ Cn * (1 + B) / A := div_le_div_of_nonneg_right h1 hA0.le
      _ = Cn * (1 + B) * A⁻¹ := by ring
      _ ≤ Cn * (2 * s) * s := h4
      _ = 2 * Cn * s ^ (2 : ℝ) := by rw [rpow_two_eq]; ring
  have hscale : scale (γ • τ) ≤ M * s ^ (3 : ℝ) := by
    have hY : (τ.im)⁻¹ ≤ s := by rw [hs, scale]; linarith [norm_nonneg (τ : ℂ)]
    have him' : ((γ • τ).im)⁻¹ = A ^ 2 / τ.im := by
      rw [him]; field_simp
    have hA2 : A ^ 2 / τ.im ≤ Cq ^ 2 * s ^ (3 : ℝ) := by
      rw [div_eq_mul_inv]
      have h3 : A ^ 2 ≤ (Cq * s) ^ 2 := pow_le_pow_left₀ hA0.le hA_le 2
      calc A ^ 2 * (τ.im)⁻¹ ≤ (Cq * s) ^ 2 * (τ.im)⁻¹ :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ ≤ (Cq * s) ^ 2 * s := mul_le_mul_of_nonneg_left hY (by positivity)
        _ = Cq ^ 2 * s ^ (3 : ℝ) := by rw [rpow_three_eq]; ring
    have h6 : s ^ (2 : ℝ) ≤ s ^ (3 : ℝ) := by
      rw [rpow_two_eq, rpow_three_eq]
      exact pow_le_pow_right₀ hs1 (by norm_num)
    have h7 : (1:ℝ) ≤ s ^ (3 : ℝ) := by
      rw [rpow_three_eq]; exact one_le_pow₀ hs1
    have h8 : (0:ℝ) ≤ s ^ (3 : ℝ) := Real.rpow_nonneg hs0.le 3
    calc scale (γ • τ) = 1 + ((γ • τ).im)⁻¹ + ‖(((γ • τ : ℍ)) : ℂ)‖ := rfl
      _ ≤ 1 + Cq ^ 2 * s ^ (3 : ℝ) + 2 * Cn * s ^ (2 : ℝ) := by
            rw [him']; exact add_le_add (add_le_add le_rfl hA2) hnorm_le
      _ ≤ 1 + Cq ^ 2 * s ^ (3 : ℝ) + 2 * Cn * s ^ (3 : ℝ) := by
            have h9 : 2 * Cn * s ^ (2:ℝ) ≤ 2 * Cn * s ^ (3:ℝ) :=
              mul_le_mul_of_nonneg_left h6 (by positivity)
            linarith
      _ = 1 + (Cq ^ 2 + 2 * Cn) * s ^ (3 : ℝ) := by ring
      _ ≤ s ^ (3 : ℝ) + (Cq ^ 2 + 2 * Cn) * s ^ (3 : ℝ) := by linarith
      _ = (1 + Cq ^ 2 + 2 * Cn) * s ^ (3 : ℝ) := by ring
      _ = M * s ^ (3 : ℝ) := by rw [hM]
  exact hscale

/-- **Lemma "HCmoderategrowthPslashed"** (CKMRV, Section 4.1): the slash operator sends
functions of moderate growth on `S` to functions of moderate growth on `{τ | γ • τ ∈ S}`. -/
theorem moderateGrowthOn_slash {S : Set ℍ} {F : ℍ → ℂ} (hF : ModerateGrowthOn S F)
    (k : ℤ) (γ : SL(2,ℤ)) :
    ModerateGrowthOn {τ : ℍ | γ • τ ∈ S} (F ∣[k] γ) := by
  rw [moderateGrowthOn_iff_scale] at hF ⊢
  obtain ⟨α, N, hα, hN, hF⟩ := hF
  obtain ⟨Cj, Nj, hCj0, hNj0, hCj⟩ := SlashBounds.jFun_rpow_bound γ (-(k:ℝ))
  obtain ⟨M, hM0, hM⟩ := scale_smul_le γ
  refine ⟨α * M ^ N * Cj, 3 * N + Nj, ?_, ?_, fun τ hτ => ?_⟩
  · exact mul_nonneg (mul_nonneg hα (Real.rpow_nonneg hM0 N)) hCj0
  · linarith
  have h1 : ‖(F ∣[k] γ) τ‖ = ‖F (γ • τ)‖ * ‖jFun γ (τ : ℂ)‖ ^ (-k) := norm_slash F k γ τ
  have hspos : (0:ℝ) < scale τ := scale_pos τ
  have h2 : ‖F (γ • τ)‖ ≤ α * (scale (γ • τ)) ^ N := hF (γ • τ) hτ
  have h3 : (scale (γ • τ)) ^ N ≤ (M * (scale τ) ^ (3:ℝ)) ^ N :=
    Real.rpow_le_rpow (le_trans zero_le_one (one_le_scale _)) (hM τ) hN
  have h4 : (M * (scale τ) ^ (3:ℝ)) ^ N = M ^ N * (scale τ) ^ (3 * N) := by
    rw [Real.mul_rpow hM0 (Real.rpow_nonneg hspos.le 3),
      ← Real.rpow_mul hspos.le 3 N]
  have h5 : ‖jFun γ (τ : ℂ)‖ ^ (-k) ≤ Cj * (scale τ) ^ Nj := by
    have hcast : (-(k:ℝ)) = ((-k : ℤ) : ℝ) := by push_cast; ring
    rw [← Real.rpow_intCast, ← hcast]
    exact hCj τ
  rw [h1]
  calc ‖F (γ • τ)‖ * ‖jFun γ (τ : ℂ)‖ ^ (-k)
      ≤ (α * M ^ N * (scale τ) ^ (3 * N)) * (Cj * (scale τ) ^ Nj) := by
        refine mul_le_mul ?_ h5 (zpow_nonneg (norm_nonneg _) _) ?_
        · calc ‖F (γ • τ)‖ ≤ α * (scale (γ • τ)) ^ N := h2
            _ ≤ α * (M * (scale τ) ^ (3:ℝ)) ^ N := mul_le_mul_of_nonneg_left h3 hα
            _ = α * (M ^ N * (scale τ) ^ (3 * N)) := by rw [h4]
            _ = α * M ^ N * (scale τ) ^ (3 * N) := by ring
        · exact mul_nonneg (mul_nonneg hα (Real.rpow_nonneg hM0 N))
            (Real.rpow_nonneg (scale_pos τ).le (3 * N))
    _ = α * M ^ N * Cj * (scale τ) ^ (3 * N + Nj) := by
        rw [Real.rpow_add hspos]; ring

/-- Dot-notation alias for `Work.Kernels.moderateGrowthOn_slash`. -/
theorem ModerateGrowthOn.slash {S : Set ℍ} {F : ℍ → ℂ} (hF : ModerateGrowthOn S F)
    (k : ℤ) (γ : SL(2,ℤ)) :
    ModerateGrowthOn {τ : ℍ | γ • τ ∈ S} (F ∣[k] γ) :=
  moderateGrowthOn_slash hF k γ

/-- The class `𝒫` is preserved by the slash action of `SL(2,ℤ)`. -/
theorem InP.slash {F : ℍ → ℂ} (hF : InP F) (k : ℤ) (γ : SL(2,ℤ)) : InP (F ∣[k] γ) := by
  refine ⟨?_, ?_⟩
  · exact hF.1.slash k (glOf γ)
  · have := moderateGrowthOn_slash hF.2 k γ
    simpa using this

end Work.Kernels
