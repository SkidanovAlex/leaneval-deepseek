import Mathlib
import Submission.Work.KMTAreas.A4.zFourierInj
import Submission.Work.KMTAreas.A4.lip2Kernel

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Two elementary lemmas about `ℓ¹` convolution and the `ℤ`-Fourier transform -/

/-- The convolution of two absolutely summable sequences on `ℤ` is absolutely summable:
`∑_x ‖∑_m w m * F (x - m)‖ < ∞`.  (Tonelli for the non-negative double family
`(m, x) ↦ ‖w m‖ ‖F (x - m)‖`, which is summable because the shear `(m, x) ↦ (m, x - m)` is an
injective self-map of `ℤ × ℤ` and `Summable.mul_of_nonneg` applies to `‖w‖` and `‖F‖`.) -/
theorem summable_conv_norm {w F : ℤ → ℂ} (hw : Summable fun m : ℤ => ‖w m‖)
    (hF : Summable fun x : ℤ => ‖F x‖) :
    Summable fun x : ℤ => ‖∑' m : ℤ, w m * F (x - m)‖ := by
  have hprod : Summable fun p : ℤ × ℤ => ‖w p.1‖ * ‖F (p.2 - p.1)‖ := by
    have h1 : Summable fun p : ℤ × ℤ => ‖w p.1‖ * ‖F p.2‖ :=
      Summable.mul_of_nonneg hw hF (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hφ : Function.Injective fun p : ℤ × ℤ => (p.1, p.2 - p.1) := by
      intro p q hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (by omega)
    exact (h1.comp_injective hφ).congr fun p => rfl
  have hproj : Summable fun x : ℤ => ∑' m : ℤ, ‖w m‖ * ‖F (x - m)‖ := by
    have hφ : Function.Injective fun p : ℤ × ℤ => (p.2, p.1) := by
      intro p q hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.2 hpq.1
    have h2 : Summable fun p : ℤ × ℤ => ‖w p.2‖ * ‖F (p.1 - p.2)‖ :=
      (hprod.comp_injective hφ).congr fun p => rfl
    exact h2.prod
  have hproj' : Summable fun x : ℤ => ∑' m : ℤ, ‖w m * F (x - m)‖ :=
    hproj.congr fun x => tsum_congr fun m => (norm_mul _ _).symm
  have hB : ∀ y : ℤ, ‖F y‖ ≤ ∑' y : ℤ, ‖F y‖ :=
    fun y => Summable.le_tsum hF y (fun j _ => norm_nonneg _)
  have hinner : ∀ x : ℤ, Summable fun m : ℤ => ‖w m * F (x - m)‖ := fun x =>
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => by
        rw [norm_mul]
        calc ‖w m‖ * ‖F (x - m)‖ ≤ ‖w m‖ * (∑' y : ℤ, ‖F y‖) :=
              mul_le_mul_of_nonneg_left (hB (x - m)) (norm_nonneg _)
          _ = (∑' y : ℤ, ‖F y‖) * ‖w m‖ := by ring)
      (hw.mul_left _)
  exact Summable.of_nonneg_of_le (fun x => norm_nonneg _)
    (fun x => norm_tsum_le_tsum_norm (hinner x)) hproj'

/-- Linearity of the `ℤ`-Fourier transform on absolutely summable sequences. -/
theorem ZFourier_sub_of_summable {f g : ℤ → ℂ} (hf : Summable fun x : ℤ => ‖f x‖)
    (hg : Summable fun x : ℤ => ‖g x‖) (ξ : FreqCircle) :
    ZFourier (f - g) ξ = ZFourier f ξ - ZFourier g ξ := by
  have h1 : Summable fun x : ℤ => f x * (fourier (-x) ξ : ℂ) :=
    Summable.of_norm_bounded hf fun x => by rw [norm_mul, fourier_norm_one (-x) ξ, mul_one]
  have h2 : Summable fun x : ℤ => g x * (fourier (-x) ξ : ℂ) :=
    Summable.of_norm_bounded hg fun x => by rw [norm_mul, fourier_norm_one (-x) ξ, mul_one]
  rw [ZFourier, ZFourier, ZFourier]
  calc ∑' x : ℤ, (f - g) x * (fourier (-x) ξ : ℂ)
      = ∑' x : ℤ, (f x * (fourier (-x) ξ : ℂ) - g x * (fourier (-x) ξ : ℂ)) := by
        refine tsum_congr fun x => ?_
        simp only [Pi.sub_apply]
        ring
    _ = (∑' x : ℤ, f x * (fourier (-x) ξ : ℂ)) - ∑' x : ℤ, g x * (fourier (-x) ξ : ℂ) :=
        Summable.tsum_sub h1 h2

/-! ## The reproducing property of the window -/

/-- **The reproducing property of the window.**  If `𝓕_ℤ F` is supported in the arc of radius
`1/(2M)` around the frequency `γ` and `M ≥ 2`, then the window `win M γ` reproduces `F`:
`F x = ∑_m win M γ m * F (x - m)` for every `x : ℤ`.

Proof.  Let `G = win M γ * F`.  By the convolution theorem for absolutely summable sequences
(`lipZFourierSmoothOp`) and the Poisson-summation computation of the window transform
(`winZFourier`), `𝓕_ℤ G(ξ) = 𝓕_ℤ F(ξ) · winFT M s t`.  On the arc (`winFT_eq_one`) the window
transform equals `1`, so `𝓕_ℤ G = 𝓕_ℤ F` everywhere; hence `G = F` by injectivity of `𝓕_ℤ` on
`ℓ¹(ℤ)` (`zFourierInj`). -/
theorem lip2Reproduce {F : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖)
    {M : ℝ} (hM : 2 ≤ M) {γ : Work.Analysis.InverseTheory.FreqCircle}
    (hsupp : Work.Analysis.InverseTheory.FourierSupportIn F
      (Work.KMTAreas.A4.arcSet γ (1 / (2 * M)))) (x : ℤ) :
    F x = ∑' m : ℤ, Work.KMTAreas.A4.win M γ m * F (x - m) := by
  have hMpos : 0 < M := by linarith
  have hw : Summable fun m : ℤ => ‖win M γ m‖ := win_summable M (by linarith) γ
  set G : ℤ → ℂ := fun x => ∑' m : ℤ, win M γ m * F (x - m) with hG
  have hGsum : Summable fun x : ℤ => ‖G x‖ := summable_conv_norm hw hF
  -- The Fourier transform of the convolution is the product of the transforms.
  have hconv : ∀ ξ : FreqCircle, ZFourier G ξ = ZFourier F ξ * ZFourier (win M γ) ξ := by
    intro ξ
    have h := lipZFourierSmoothOp (w := win M γ) (G := F) hw hF 1 ξ
    have hsm : smoothOp (win M γ) F 1 = G := by
      rw [hG]
      funext y
      simp only [smoothOp, one_mul]
    rw [hsm] at h
    have hzf : (∑' m : ℤ, win M γ m * (fourier (-(1 * m)) ξ : ℂ)) = ZFourier (win M γ) ξ := by
      rw [ZFourier]
      exact tsum_congr fun m => by rw [one_mul]
    rwa [hzf] at h
  -- The window transform is `1` on the arc where `𝓕_ℤ F` lives, and `𝓕_ℤ F` vanishes off it.
  have hkey : ∀ ξ : FreqCircle, ZFourier G ξ = ZFourier F ξ := by
    intro ξ
    rw [hconv ξ]
    by_cases hξ : ξ ∈ arcSet γ (1 / (2 * M))
    · obtain ⟨θ, hθ, hξeq⟩ := hξ
      obtain ⟨s, hs⟩ : ∃ s : ℝ, ((s : ℝ) : FreqCircle) = γ :=
        ⟨(AddCircle.equivIco (1 : ℝ) (0 : ℝ) γ : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)),
          AddCircle.coe_equivIco⟩
      have ht : ((s + θ : ℝ) : FreqCircle) = ξ := by
        rw [hξeq, ← hs]
        exact AddCircle.coe_add 1 s θ
      have hb : |M * ((s + θ) - s)| ≤ 1 / 2 := by
        have h2 : (s + θ) - s = θ := by ring
        rw [h2, abs_mul, abs_of_pos hMpos]
        calc M * |θ| ≤ M * (1 / (2 * M)) := mul_le_mul_of_nonneg_left hθ (le_of_lt hMpos)
          _ = 1 / 2 := by field_simp
      have hwin : ZFourier (win M γ) ξ = 1 := by
        rw [← hs, ← ht, winZFourier M s (s + θ) hMpos, winFT_eq_one hM hb]
      rw [hwin, mul_one]
    · rw [hsupp ξ hξ, zero_mul]
  -- Uniqueness of the Fourier transform on `ℓ¹(ℤ)`.
  have hsub : Summable fun x : ℤ => ‖(G - F) x‖ :=
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => norm_sub_le (G x) (F x))
      (hGsum.add hF)
  have hdiff : ∀ ξ : FreqCircle, ZFourier (G - F) ξ = 0 := by
    intro ξ
    rw [ZFourier_sub_of_summable hGsum hF ξ, hkey ξ, sub_self]
  have hgoal : ∀ y : ℤ, G y = F y := fun y => by
    have h := zFourierInj (G - F) hsub (fun ξ => hdiff ξ) y
    simpa only [Pi.sub_apply, sub_eq_zero] using h
  have hx : (∑' m : ℤ, win M γ m * F (x - m)) = F x := by
    have h := hgoal x
    rw [hG] at h
    exact h
  exact hx.symm

end Work.KMTAreas.A4
