import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.integral_le_two_r
import Submission.Work.GM.Affine.supf_le_integral_norm_fhat

/-!
# `∫ f² ≤ C (∫ f)²` for the GM §9 test function, in the range `T < 2 C₀`

This is the small-`T` ingredient of the affine-sums area (`Submission.Work.GM.Affine`).

The hypotheses are those of GM §9: `f : ℝ → ℝ` is continuous, non-negative, supported in
`[1/C₀, C₀]` (`SuppHyp C₀ f`), and its Fourier transform satisfies the pointwise decay bound

  `‖Fhat f ξ‖ ≤ c j ε · T^ε · (T/|ξ|)^j · Λ`  for all `j`, `ε > 0`, `ξ ≠ 0`

for a positive parameter `Λ` which is itself bounded by `16 · c(2,1) · T³ · ∫ f`.

## Proof

1. `Λ > 0` and `Λ ≤ 16 c(2,1) T³ ∫ f` force `0 < c(2,1)` and `∫ f ≥ 0`.
2. The decay hypothesis with `(j, ε) = (2, 1)` gives `‖Fhat f ξ‖ ≤ B/ξ²` with
   `B = c(2,1) T³ Λ ≥ 0`, while `‖Fhat f ξ‖ ≤ ∫ f` always holds.  These two bounds make
   `Fhat f` integrable (it is dominated by a multiple of `(1+ξ²)⁻¹`).
3. Fourier inversion (`supf_le_integral_norm_fhat`) and the two-sided tail estimate
   (`integral_le_two_r`) give, for every `r > 0`,

   `supf f ≤ ∫ ξ, ‖Fhat f ξ‖ ≤ 2 r ∫ f + 2 B / r`.

   Choosing `r = 2 B / Λ · Λ/...`, i.e. `r = 2 (c(2,1) T³)`, turns this into
   `supf f ≤ 4 (c(2,1) T³) ∫ f + Λ`.
4. `∫ f² ≤ supf f · ∫ f` (pointwise `f u ^ 2 ≤ supf f * f u`, using `f ≥ 0`), hence
   `∫ f² ≤ (4 c(2,1) T³ + 16 c(2,1) T³) (∫ f)²`, where `Λ ∫ f ≤ 16 c(2,1) T³ (∫ f)²`.
5. Since `T < 2 C₀`, `T³ ≤ (2 C₀)³`, so `20 c(2,1) T³ ≤ 160 c(2,1) C₀³`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-! ### Elementary facts about the test function -/

/-- `SuppHyp C₀ f` implies that `f` has compact support. -/
lemma hasCompactSupport_of_SuppHyp' {C₀ : ℝ} {f : ℝ → ℝ} (h : SuppHyp C₀ f) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 / C₀) C₀) isCompact_Icc
    (fun x hx => h x (Function.mem_support.mp hx))

/-- The trivial bound `‖Fhat f ξ‖ ≤ ∫ f` for a non-negative `f`. -/
lemma norm_Fhat_le_integral_aux {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u) (ξ : ℝ) :
    ‖Fhat f ξ‖ ≤ ∫ u, f u := by
  rw [Fhat, Real.fourier_eq (fun u : ℝ => ((f u : ℝ) : ℂ)) ξ]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm (e := 𝐞) (μ := volume)
    (L := innerₗ ℝ) (f := fun u : ℝ => ((f u : ℝ) : ℂ)) (w := ξ)).trans ?_
  refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_)))
  show ‖((f u : ℝ) : ℂ)‖ = f u
  rw [Complex.norm_real, Real.norm_of_nonneg (hfnn u)]

/-- `Fhat f` is continuous for continuous compactly supported `f`. -/
lemma continuous_Fhat_aux {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (Fhat f) := by
  rw [show Fhat f = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
      (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) from rfl]
  exact VectorFourier.fourierIntegral_continuous (μ := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := fun u : ℝ => (f u : ℂ)) Real.continuous_fourierChar (by fun_prop)
    ((hf.integrable_of_hasCompactSupport hcs).ofReal)

/-! ### The decay hypothesis with parameter `Λ` -/

/-- Decay at `(j, ε) = (2, 1)`, in the form `‖Fhat f ξ‖ ≤ B / ξ²` with `B = c 2 1 * T³ * Λ`. -/
lemma norm_Fhat_le_div_sq_aux {c : ℕ → ℝ → ℝ} {T Λ : ℝ} {f : ℝ → ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖Fhat f ξ‖ ≤ (c 2 1 * T ^ 3 * Λ) / ξ ^ 2 := by
  have h := hdec 2 1 one_pos ξ hξ
  rw [Real.rpow_one, div_pow, sq_abs] at h
  calc ‖Fhat f ξ‖ ≤ c 2 1 * T * (T ^ 2 / ξ ^ 2) * Λ := h
    _ = c 2 1 * T ^ 3 * Λ / ξ ^ 2 := by rw [div_eq_mul_inv]; ring

/-- The point `0` is negligible for the Lebesgue measure on `ℝ`. -/
lemma ae_ne_zero_real_aux : ∀ᵐ ξ : ℝ ∂(volume : Measure ℝ), ξ ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have h : {x : ℝ | ¬ (x ≠ 0)} = {0} := by ext x; simp
  rw [h]; exact measure_singleton 0

/-- Under the `Λ`-decay hypothesis (with `B = c 2 1 * T³ * Λ ≥ 0`), `Fhat f` is integrable. -/
lemma integrable_Fhat_of_lam {c : ℕ → ℝ → ℝ} {T Λ : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u)
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (hB0 : 0 ≤ c 2 1 * T ^ 3 * Λ) :
    Integrable (Fhat f) := by
  have hA : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have hcont : Continuous (Fhat f) := continuous_Fhat_aux hf hcs
  have hg : Integrable (fun ξ : ℝ =>
      (2 * (∫ u, f u) + 2 * (c 2 1 * T ^ 3 * Λ)) / (1 + ξ ^ 2)) := by
    have h := integrable_inv_one_add_sq.const_mul (2 * (∫ u, f u) + 2 * (c 2 1 * T ^ 3 * Λ))
    simpa [div_eq_mul_inv] using h
  refine Integrable.mono' hg hcont.aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero_real_aux] with ξ hξ
  have h1 : ‖Fhat f ξ‖ ≤ ∫ u, f u := norm_Fhat_le_integral_aux hnn ξ
  have h2 : ‖Fhat f ξ‖ ≤ (c 2 1 * T ^ 3 * Λ) / ξ ^ 2 := norm_Fhat_le_div_sq_aux hdec hξ
  have hden : 0 < 1 + ξ ^ 2 := by positivity
  rcases le_or_gt |ξ| 1 with h | h
  · have hsq : ξ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ξ]
    have hbound : (∫ u, f u) ≤ (2 * (∫ u, f u) + 2 * (c 2 1 * T ^ 3 * Λ)) / (1 + ξ ^ 2) := by
      rw [le_div_iff₀ hden]
      nlinarith [hA, hB0, hsq]
    linarith
  · have hsq : 1 ≤ ξ ^ 2 := by rw [← sq_abs]; nlinarith [abs_pos.mpr hξ]
    have hξ2pos : 0 < ξ ^ 2 := by linarith
    have hbound : (c 2 1 * T ^ 3 * Λ) / ξ ^ 2
        ≤ (2 * (∫ u, f u) + 2 * (c 2 1 * T ^ 3 * Λ)) / (1 + ξ ^ 2) := by
      rw [div_le_div_iff₀ hξ2pos hden]
      nlinarith [hA, hB0, hsq]
    linarith

/-- `supf f ≤ 2 r ∫ f + 2 B / r` with `B = c 2 1 * T³ Λ`, for every `r > 0`. -/
lemma supf_le_of_decay_lam {c : ℕ → ℝ → ℝ} {T Λ : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u)
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (hB0 : 0 ≤ c 2 1 * T ^ 3 * Λ) {r : ℝ} (hr : 0 < r) :
    supf f ≤ 2 * r * (∫ u, f u) + 2 * (c 2 1 * T ^ 3 * Λ) / r := by
  have hint : Integrable (Fhat f) := integrable_Fhat_of_lam hf hcs hnn hdec hB0
  have h1 : supf f ≤ ∫ ξ, ‖Fhat f ξ‖ := supf_le_integral_norm_fhat hf hcs hnn hint
  have h2 : ∫ ξ, ‖Fhat f ξ‖ ≤ 2 * r * (∫ u, f u) + 2 * (c 2 1 * T ^ 3 * Λ) / r :=
    integral_le_two_r hr hint.norm (fun ξ => norm_Fhat_le_integral_aux hnn ξ)
      (fun ξ hξ => norm_Fhat_le_div_sq_aux hdec hξ)
  linarith

/-! ### `∫ f² ≤ supf f · ∫ f` -/

lemma integral_sq_le_supf_mul {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (hnn : ∀ u, 0 ≤ f u) :
    ∫ u, (f u) ^ 2 ≤ supf f * ∫ u, f u := by
  have hg : Integrable (fun u : ℝ => supf f * f u) :=
    (hf.integrable_of_hasCompactSupport hcs).const_mul (supf f)
  have hle : ∀ u : ℝ, (f u) ^ 2 ≤ supf f * f u := by
    intro u
    have h1 : f u ≤ supf f := le_supf hf hcs u
    have h2 : 0 ≤ f u := hnn u
    calc (f u) ^ 2 = f u * f u := by ring
      _ ≤ supf f * f u := mul_le_mul_of_nonneg_right h1 h2
  calc ∫ u, (f u) ^ 2 ≤ ∫ u, supf f * f u :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => sq_nonneg (f u))) hg
          (Filter.Eventually.of_forall hle)
    _ = supf f * ∫ u, f u := integral_const_mul _ _

/-! ### The main estimate -/

theorem f_sq_le_const_sq_smallT {C₀ T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, T₀ ≤ T → T < 2 * C₀ → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) →
        SuppHyp C₀ f → ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∫ u, (f u) ^ 2 ≤ C * (∫ u, f u) ^ 2 := by
  refine ⟨max 1 (160 * c 2 1 * C₀ ^ 3), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro T hT₀T hTC₀ f hf hnn hsupp Λ hΛ hdec hΛle
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (le_trans hT₀ hT₀T)
  have hT3pos : 0 < T ^ 3 := pow_pos hTpos 3
  have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp' hsupp
  have hA : 0 ≤ ∫ u, f u := integral_nonneg hnn
  -- `Λ > 0` and `Λ ≤ 16 c(2,1) T³ ∫f` force `0 < c(2,1)`.
  have hc21 : 0 < c 2 1 := by
    have h16 : 0 < 16 * c 2 1 * T ^ 3 * ∫ u, f u := lt_of_lt_of_le hΛ hΛle
    have hT3A : 0 ≤ T ^ 3 * ∫ u, f u := mul_nonneg (le_of_lt hT3pos) hA
    have heq : 16 * c 2 1 * T ^ 3 * ∫ u, f u = (16 * c 2 1) * (T ^ 3 * ∫ u, f u) := by ring
    rw [heq] at h16
    have h16c : 0 < 16 * c 2 1 := pos_of_mul_pos_left h16 hT3A
    linarith
  have hB0 : 0 ≤ c 2 1 * T ^ 3 * Λ :=
    mul_nonneg (mul_nonneg (le_of_lt hc21) (le_of_lt hT3pos)) (le_of_lt hΛ)
  have hrpos : 0 < 2 * (c 2 1 * T ^ 3) := mul_pos two_pos (mul_pos hc21 hT3pos)
  have hsup := supf_le_of_decay_lam hf hcs hnn hdec hB0 hrpos
  have hsimp : 2 * (c 2 1 * T ^ 3 * Λ) / (2 * (c 2 1 * T ^ 3)) = Λ := by
    field_simp
  have h4 : 2 * (2 * (c 2 1 * T ^ 3)) * (∫ u, f u) = 4 * (c 2 1 * T ^ 3) * (∫ u, f u) := by
    ring
  rw [h4, hsimp] at hsup
  -- `supf f ≤ 4 c(2,1) T³ ∫f + Λ`
  have hsq : ∫ u, (f u) ^ 2 ≤ supf f * ∫ u, f u := integral_sq_le_supf_mul hf hcs hnn
  have hstep : ∫ u, (f u) ^ 2 ≤ (4 * (c 2 1 * T ^ 3) * (∫ u, f u) + Λ) * ∫ u, f u :=
    le_trans hsq (mul_le_mul_of_nonneg_right hsup hA)
  have hLamA : Λ * ∫ u, f u ≤ 16 * c 2 1 * T ^ 3 * (∫ u, f u) ^ 2 := by
    calc Λ * ∫ u, f u ≤ (16 * c 2 1 * T ^ 3 * ∫ u, f u) * ∫ u, f u :=
          mul_le_mul_of_nonneg_right hΛle hA
      _ = 16 * c 2 1 * T ^ 3 * (∫ u, f u) ^ 2 := by ring
  have hfinal : ∫ u, (f u) ^ 2 ≤ 20 * c 2 1 * T ^ 3 * (∫ u, f u) ^ 2 := by
    have hexp : (4 * (c 2 1 * T ^ 3) * (∫ u, f u) + Λ) * ∫ u, f u
        = 4 * (c 2 1 * T ^ 3) * (∫ u, f u) ^ 2 + Λ * ∫ u, f u := by ring
    rw [hexp] at hstep
    calc ∫ u, (f u) ^ 2
        ≤ 4 * (c 2 1 * T ^ 3) * (∫ u, f u) ^ 2 + Λ * ∫ u, f u := hstep
      _ ≤ 4 * (c 2 1 * T ^ 3) * (∫ u, f u) ^ 2
            + 16 * c 2 1 * T ^ 3 * (∫ u, f u) ^ 2 := by linarith [hLamA]
      _ = 20 * c 2 1 * T ^ 3 * (∫ u, f u) ^ 2 := by ring
  have hT3le : T ^ 3 ≤ (2 * C₀) ^ 3 := pow_le_pow_left₀ (le_of_lt hTpos) (le_of_lt hTC₀) 3
  have hcoef : 20 * c 2 1 * T ^ 3 ≤ 160 * c 2 1 * C₀ ^ 3 := by
    calc 20 * c 2 1 * T ^ 3 ≤ 20 * c 2 1 * (2 * C₀) ^ 3 :=
          mul_le_mul_of_nonneg_left hT3le (mul_nonneg (by norm_num) (le_of_lt hc21))
      _ = 160 * c 2 1 * C₀ ^ 3 := by ring
  have hV : ∫ u, (f u) ^ 2 ≤ 160 * c 2 1 * C₀ ^ 3 * (∫ u, f u) ^ 2 :=
    le_trans hfinal (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  exact le_trans hV (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))

end

end Work.GM.Affine
