import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# Fourier inversion for the test function `f` of GM §9

`Fhat f ξ = ∫ u, e^{-2πi u ξ} f u` is the (complex) Fourier transform of the real-valued test
function `f`, normalised as in `Submission/Work/GM/Affine/setup.lean`.  The decay hypothesis
`DecayHyp c T f` of §9 (a bound `‖Fhat f ξ‖ ≤ c j ε · T^ε · (T/|ξ|)^j · supf f` for every `j` and
every `ξ ≠ 0`) makes `Fhat f` integrable, so Mathlib's Fourier inversion formula
(`Continuous.fourierInv_fourier_eq`) applies, giving

  `∫ ξ, e(ξ x) · Fhat f ξ = f x`,   `e(t) = exp (2 π i t)`.

The quantitative input is that the decay with `j = 2` yields `‖Fhat f ξ‖ ≪ (1 + ξ²)⁻¹`.
-/

open Complex MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- Pointwise form of the Fourier transform on `ℝ → ℂ` used below. -/
lemma fhat_apply (f : ℝ → ℝ) (ξ : ℝ) :
    Fhat f ξ = ∫ u : ℝ, 𝐞 (-(inner ℝ u ξ)) • (f u : ℂ) := rfl

/-- **Fourier inversion** for the GM §9 test function: the decay hypothesis on `Fhat f` makes it
integrable, so that the inverse Fourier integral of `Fhat f` reproduces `f`. -/
theorem fhat_inversion {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hdec : DecayHyp c T f) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (∫ ξ, efun (ξ * x) * Fhat f ξ) = (f x : ℂ) := by
  have hg : Integrable (fun u : ℝ => (f u : ℂ)) :=
    (Complex.continuous_ofReal.comp hf).integrable_of_hasCompactSupport (hcs.comp_left (by simp))
  have hcont : Continuous (Fhat f) :=
    VectorFourier.fourierIntegral_continuous (e := Real.fourierChar) (μ := volume)
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hg
  set M : ℝ := ∫ u : ℝ, ‖(f u : ℂ)‖ with hM
  set A : ℝ := c 2 ε * T ^ ε * T ^ 2 * supf f with hA
  set C : ℝ := 2 * max M |A| with hC
  have hMnn : 0 ≤ M := by
    rw [hM]; exact integral_nonneg (fun u => norm_nonneg _)
  have hbound : ∀ ξ : ℝ, ‖Fhat f ξ‖ ≤ C * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have hpos : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
    rcases lt_or_ge (1 : ℝ) |ξ| with h | h
    · -- large `ξ`: use the decay with `j = 2`
      have hξne : ξ ≠ 0 := by
        intro h0; rw [h0, abs_zero] at h; linarith
      have hd := hdec 2 ε hε ξ hξne
      have h3 : ((|ξ| : ℝ) ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
        have hge : (1 : ℝ) ≤ (|ξ|) ^ 2 := by
          nlinarith [abs_nonneg ξ]
        have hgt : (0 : ℝ) < (|ξ|) ^ 2 := lt_of_lt_of_le one_pos hge
        have hthis : (2 : ℝ) * (1 + ξ ^ 2)⁻¹ = ((1 + ξ ^ 2) / 2)⁻¹ := by rw [inv_div]; ring
        rw [hthis, inv_le_inv₀ hgt (by positivity)]
        linarith [sq_abs ξ, hge]
      have h6 : 2 * |A| ≤ C := by
        rw [hC]; have := le_max_right M |A|; linarith
      have h1 : c 2 ε * T ^ ε * (T / |ξ|) ^ 2 * supf f = A / |ξ| ^ 2 := by
        rw [div_pow, hA]; ring
      calc ‖Fhat f ξ‖ ≤ A / |ξ| ^ 2 := by rw [← h1]; exact hd
        _ ≤ |A| / |ξ| ^ 2 := div_le_div_of_nonneg_right (le_abs_self A) (by positivity)
        _ = |A| * ((|ξ| : ℝ) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ |A| * (2 * (1 + ξ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h3 (abs_nonneg A)
        _ = 2 * |A| * (1 + ξ ^ 2)⁻¹ := by ring
        _ ≤ C * (1 + ξ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h6 (by positivity)
    · -- small `ξ`: use the trivial bound `‖Fhat f ξ‖ ≤ ∫ ‖f‖`
      have hξ2 : ξ ^ 2 ≤ 1 := by have := sq_abs ξ; nlinarith [abs_nonneg ξ, h]
      have hle : (1 : ℝ) ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
        rw [show (2 : ℝ) * (1 + ξ ^ 2)⁻¹ = 2 / (1 + ξ ^ 2) by rw [div_eq_mul_inv]]
        rw [le_div_iff₀ hpos]
        linarith
      have hMξ : ‖Fhat f ξ‖ ≤ M := by
        change ‖𝓕 (fun u : ℝ => (f u : ℂ)) ξ‖ ≤ M
        rw [Real.fourier_eq, hM]
        refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
        apply integral_congr_ae
        filter_upwards with u
        rw [Circle.norm_smul]
      calc ‖Fhat f ξ‖ ≤ M := hMξ
        _ ≤ max M |A| := le_max_left _ _
        _ = max M |A| * 1 := by ring
        _ ≤ max M |A| * (2 * (1 + ξ ^ 2)⁻¹) := by
            apply mul_le_mul_of_nonneg_left hle
            exact le_trans hMnn (le_max_left M |A|)
        _ = C * (1 + ξ ^ 2)⁻¹ := by rw [hC]; ring
  have h_int : Integrable (Fhat f) := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hcont.aestronglyMeasurable ?_
    filter_upwards with ξ
    exact hbound ξ
  have hinv := Continuous.fourierInv_fourier_eq (f := fun u : ℝ => (f u : ℂ))
    (Complex.continuous_ofReal.comp hf) hg h_int
  have hx : 𝓕⁻ (𝓕 (fun u : ℝ => (f u : ℂ))) x = (f x : ℂ) := congrFun hinv x
  have hpt : ∀ v : ℝ, efun (v * x) * Fhat f v = (𝐞 (inner ℝ v x)) • Fhat f v := by
    intro v
    rw [show inner ℝ v x = v * x from by simp [mul_comm]]
    rw [Circle.smul_def]
    have hh : ((𝐞 (v * x) : Circle) : ℂ) = efun (v * x) := by
      rw [Real.fourierChar_apply]; unfold efun; congr 1; push_cast; ring
    rw [hh, smul_eq_mul]
  rw [← hx, Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => hpt v)

end

end Work.GM.Affine
