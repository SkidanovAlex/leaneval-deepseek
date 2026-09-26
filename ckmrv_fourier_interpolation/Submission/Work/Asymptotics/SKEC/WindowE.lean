/-
# The polynomial window on the cusp-`0` tile `E`, assembled from the three regimes

`Work.Asymptotics.SKEC.EpolyWindowE_of_pieces`: the plain window
`‖K^{(d)}(w, i t)‖ ≤ C (scale w)^N (1 + t)^M` for `w ∈ E = KEpsilon` and `0 < t ≤ scale w` is
assembled from the four `w`-dependent regimes

* `0 < t ≤ 1` — the flatness at the cusp `0`, `Work.Asymptotics.EFlat` (proved as the first
  component of `Work.Asymptotics.Epoint_Kfun`);
* `1 ≤ t ≤ Im (S • w) - 1` — below the pole height (`Work.Asymptotics.SKEC.EWfar`);
* `Im (S • w) - 1 ≤ t ≤ Im (S • w) + 1` — the pole strip (`Work.Asymptotics.SKEC.EWstrip`);
* `Im (S • w) + 1 ≤ t` — above the pole (`Work.Asymptotics.EpolyWindowE_top`, proved).

The last regime needs `t ≤ scale w`; the four ranges cover `(0, scale w]` because
`Im (S • w) + 1 ≤ scale w` (`Work.Asymptotics.E_T_le_scale`).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.SKEC.Defs
import Submission.Work.Asymptotics.Epoint_Kfun
import Submission.Work.Asymptotics.EpolyWindowE_top
import Submission.Work.Kernels.All

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

open Work.Kernels

/-- **Combining two polynomial bounds** of the shape `C (scale w)^N (1+t)^M` into one. -/
lemma scaleWin_mono {C₁ N₁ M₁ C₂ N₂ M₂ S T : ℝ} (hS : 1 ≤ S) (hT : 1 ≤ T)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    C₁ * S ^ N₁ * T ^ M₁ ≤ (C₁ + C₂) * S ^ (max N₁ N₂) * T ^ (max M₁ M₂) := by
  have h1 : S ^ N₁ ≤ S ^ (max N₁ N₂) := Real.rpow_le_rpow_of_exponent_le hS (le_max_left _ _)
  have h2 : T ^ M₁ ≤ T ^ (max M₁ M₂) := Real.rpow_le_rpow_of_exponent_le hT (le_max_left _ _)
  have hS0 : (0 : ℝ) ≤ S ^ (max N₁ N₂) := Real.rpow_nonneg (by linarith) _
  have hT0 : (0 : ℝ) ≤ T ^ (max M₁ M₂) := Real.rpow_nonneg (by linarith) _
  calc C₁ * S ^ N₁ * T ^ M₁ ≤ C₁ * S ^ (max N₁ N₂) * T ^ (max M₁ M₂) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₁) h2
          (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ ≤ (C₁ + C₂) * S ^ (max N₁ N₂) * T ^ (max M₁ M₂) := by
        have : C₁ * S ^ (max N₁ N₂) ≤ (C₁ + C₂) * S ^ (max N₁ N₂) :=
          mul_le_mul_of_nonneg_right (by linarith) hS0
        exact mul_le_mul_of_nonneg_right this hT0

lemma scaleWin_mono₂ {C₁ C₂ N₁ N₂ M₁ M₂ S T : ℝ} (hS : 1 ≤ S) (hT : 1 ≤ T)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    C₂ * S ^ N₂ * T ^ M₂ ≤ (C₁ + C₂) * S ^ (max N₁ N₂) * T ^ (max M₁ M₂) := by
  have h1 : S ^ N₂ ≤ S ^ (max N₁ N₂) := Real.rpow_le_rpow_of_exponent_le hS (le_max_right _ _)
  have h2 : T ^ M₂ ≤ T ^ (max M₁ M₂) := Real.rpow_le_rpow_of_exponent_le hT (le_max_right _ _)
  have hS0 : (0 : ℝ) ≤ S ^ (max N₁ N₂) := Real.rpow_nonneg (by linarith) _
  have hT0 : (0 : ℝ) ≤ T ^ (max M₁ M₂) := Real.rpow_nonneg (by linarith) _
  calc C₂ * S ^ N₂ * T ^ M₂ ≤ C₂ * S ^ (max N₁ N₂) * T ^ (max M₁ M₂) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₂) h2
          (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ ≤ (C₁ + C₂) * S ^ (max N₁ N₂) * T ^ (max M₁ M₂) := by
        have : C₂ * S ^ (max N₁ N₂) ≤ (C₁ + C₂) * S ^ (max N₁ N₂) :=
          mul_le_mul_of_nonneg_right (by linarith) hS0
        exact mul_le_mul_of_nonneg_right this hT0

/-- **The window from the four regimes.**  If the kernel is polynomially bounded
* below the pole height `Im (S • w) - 1` in `t ≥ 1` (`hfar`),
 * on the pole strip `|t - Im (S • w)| ≤ 1` (`hstrip`),
then it is polynomially bounded for the whole window `0 < t ≤ scale w`. -/
theorem EpolyWindowE_of_pieces (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hfar : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon → 1 ≤ t →
        t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M)
    (hstrip : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon →
        (ModularGroup.S • w).im - 1 ≤ t → t ≤ (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon → 0 < t →
        t ≤ Work.Kernels.scale w →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
  obtain ⟨c1, N1, M1, hc1, hN1, hM1, hb1⟩ := hfar
  obtain ⟨c2, N2, M2, hc2, hN2, hM2, hb2⟩ := hstrip
  obtain ⟨c3, N3, M3, hc3, hN3, hM3, hb3⟩ := EpolyWindowE_top ℓ d hd
  obtain ⟨c0, N0, hc0, hb0⟩ := (Epoint_Kfun ℓ d hd).1 0 (le_refl 0)
  set N : ℝ := max (max (max (max N0 0) N1) N2) N3 with hN
  set M : ℝ := max (max (max 0 M1) M2) M3 with hM
  set Ct : ℝ := (((c0 + c1) + c2) + c3) with hCt
  have hN0le : max N0 0 ≤ N := by
    rw [hN]
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hN1le : N1 ≤ N := by
    rw [hN]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hN2le : N2 ≤ N := by
    rw [hN]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hN3le : N3 ≤ N := by rw [hN]; exact le_max_right _ _
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hM1le : M1 ≤ M := by
    rw [hM]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hM2le : M2 ≤ M := by
    rw [hM]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hM3le : M3 ≤ M := by rw [hM]; exact le_max_right _ _
  have hN0 : 0 ≤ N := le_trans (le_max_right N0 0) hN0le
  have hCt0 : 0 < Ct := by rw [hCt]; linarith
  have hc0le : c0 ≤ Ct := by rw [hCt]; linarith
  have hc1le : c1 ≤ Ct := by rw [hCt]; linarith
  have hc2le : c2 ≤ Ct := by rw [hCt]; linarith
  have hc3le : c3 ≤ Ct := by rw [hCt]; linarith
  refine ⟨Ct, N, M, hCt0, hN0, hM0, ?_⟩
  intro w t hw ht htw
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hS0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans (by norm_num) hs1
  have ht0 : (0 : ℝ) ≤ 1 + t := by linarith
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have key : ∀ (c N' M' : ℝ), 0 ≤ c → c ≤ Ct → N' ≤ N → M' ≤ M →
      c * (Work.Kernels.scale w) ^ N' * (1 + t) ^ M'
        ≤ Ct * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
    intro c N' M' hc hcc hNN hMM
    have h1 : (Work.Kernels.scale w) ^ N' ≤ (Work.Kernels.scale w) ^ N :=
      Real.rpow_le_rpow_of_exponent_le hs1 hNN
    have h2 : (1 + t) ^ M' ≤ (1 + t) ^ M := Real.rpow_le_rpow_of_exponent_le ht1 hMM
    have hSN : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N := Real.rpow_nonneg hS0 N
    have hTM : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg ht0 M
    have hT1 : (0 : ℝ) ≤ (1 + t) ^ M' := Real.rpow_nonneg ht0 M'
    have step1 : c * (Work.Kernels.scale w) ^ N' * (1 + t) ^ M'
        ≤ c * (Work.Kernels.scale w) ^ N * (1 + t) ^ M :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 hT1 (by positivity)
    have step2 : c * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
        ≤ Ct * (Work.Kernels.scale w) ^ N * (1 + t) ^ M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hSN) hTM
    exact le_trans step1 step2
  by_cases h1 : t ≤ 1
  · have hbs := hb0 w t hw ht h1
    have h1' : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ c0 * (Work.Kernels.scale w) ^ (max N0 0) * (1 + t) ^ (0 : ℝ) := by
      refine le_trans hbs ?_
      simp only [Real.rpow_zero, mul_one]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)) hc0
    exact le_trans h1' (key c0 (max N0 0) 0 hc0 hc0le hN0le hM0)
  · have ht1' : (1 : ℝ) ≤ t := le_of_lt (not_le.mp h1)
    by_cases h2 : t ≤ (ModularGroup.S • w).im - 1
    · exact le_trans (hb1 w t hw ht1' h2) (key c1 N1 M1 hc1.le hc1le hN1le hM1le)
    · have h2' : (ModularGroup.S • w).im - 1 ≤ t := le_of_lt (not_le.mp h2)
      by_cases h3 : t ≤ (ModularGroup.S • w).im + 1
      · exact le_trans (hb2 w t hw h2' h3) (key c2 N2 M2 hc2.le hc2le hN2le hM2le)
      · have h3' : (ModularGroup.S • w).im + 1 ≤ t := le_of_lt (not_le.mp h3)
        exact le_trans (hb3 w t hw h3' htw) (key c3 N3 M3 hc3.le hc3le hN3le hM3le)

end Work.Asymptotics
