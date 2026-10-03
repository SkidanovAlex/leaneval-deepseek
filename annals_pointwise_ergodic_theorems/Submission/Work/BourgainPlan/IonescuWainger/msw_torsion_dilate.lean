import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.rescaled_mikhlin_multiplier_lp

/-!
# Dilating the frequency variable in an `Lᵖ` multiplier bound

If a multiplier bound

`‖𝓕⁻ (m · 𝓕 g)‖_{Lᵖ} ≤ A ‖g‖_{Lᵖ}`

holds for every function `g` band limited to `[-1/2, 1/2]`, then the same bound holds for the
rescaled symbol `ξ ↦ m (ξ / Q)`, `Q ≥ 1` an integer.  This is purely the dilation isometry of the
Fourier transform: with `w x = g (x / Q)` one has `𝓕 w η = Q · 𝓕 g (Q η)`, hence
`m (ξ / Q) · 𝓕 g ξ = Q⁻¹ · (m · 𝓕 w) (ξ / Q)` and therefore

`𝓕⁻ (m (· / Q) · 𝓕 g) x = 𝓕⁻ (m · 𝓕 w) (Q x)`,

so the two `Lᵖ` norms differ by exactly the two changes of variables `x ↦ Q x` and `x ↦ x / Q`.
-/

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped FourierTransform ENNReal

noncomputable section

/-- Change of variables `x ↦ c x` for the lower Lebesgue integral, valid for an *arbitrary*
function `F : ℝ → ℝ≥0∞` (no measurability assumption), since `x ↦ c x` is a measurable
embedding. -/
lemma lintegral_comp_mul_left_all (c : ℝ) (hc : c ≠ 0) (F : ℝ → ℝ≥0∞) :
    ∫⁻ x, F (c * x) = ENNReal.ofReal |c⁻¹| * ∫⁻ x, F x := by
  have hg : MeasurableEmbedding (fun x : ℝ => c * x) := by
    have h := (Homeomorph.mulLeft₀ c hc).toMeasurableEquiv.measurableEmbedding
    simpa using h
  rw [← hg.lintegral_map F, Real.map_volume_mul_left hc, lintegral_smul_measure]
  rfl

theorem msw_torsion_dilate {p : ℝ} (hp : 0 < p) {Q : ℕ} (hQ : 1 ≤ Q) (m : ℝ → ℂ)
    (hmi : MeasureTheory.Integrable m)
    (hmsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) → m ξ = 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hOp : ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → FourierTransform.fourier g ξ = 0) →
      MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ENNReal.ofReal
        ‖FourierTransformInv.fourierInv (fun ξ : ℝ => m ξ * FourierTransform.fourier g ξ) x‖ ^ p)
        ≤ ENNReal.ofReal (A ^ p) *
          MeasureTheory.lintegral MeasureTheory.volume
            (fun x : ℝ => ENNReal.ofReal ‖g x‖ ^ p))
    (g : ℝ → ℂ) (hg : MeasureTheory.Integrable g)
    (hgband : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → FourierTransform.fourier g ξ = 0) :
    MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ENNReal.ofReal
        ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => m (ξ / (Q : ℝ)) * FourierTransform.fourier g ξ) x‖ ^ p)
      ≤ ENNReal.ofReal (A ^ p) *
        MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ENNReal.ofReal ‖g x‖ ^ p) := by
  set Qr : ℝ := (Q : ℝ) with hQrdef
  have hQr1 : 1 ≤ Qr := by rw [hQrdef]; exact_mod_cast hQ
  have hQrpos : 0 < Qr := lt_of_lt_of_le one_pos hQr1
  have hQr_ne : Qr ≠ 0 := hQrpos.ne'
  -- The rescaled function `w = g (· / Q)`.
  set w : ℝ → ℂ := fun x => g (Qr⁻¹ * x) with hwdef
  have hw_int : MeasureTheory.Integrable w := hg.comp_mul_left' (R := Qr⁻¹) (inv_ne_zero hQr_ne)
  have hFw : ∀ η, FourierTransform.fourier w η = (Qr : ℂ) * FourierTransform.fourier g (Qr * η) := by
    intro η
    rw [hwdef]
    exact fourier_dilate_inv g Qr η hQrpos
  have hw_band : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → FourierTransform.fourier w ξ = 0 := by
    intro ξ hξ
    rw [hFw ξ]
    have hnot : Qr * ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
      intro hmem
      apply hξ
      rw [Set.mem_Icc] at hmem ⊢
      have habs : |Qr * ξ| ≤ (1 / 2 : ℝ) := abs_le.mpr hmem
      rw [abs_mul, abs_of_pos hQrpos] at habs
      have hle : |ξ| ≤ Qr * |ξ| := by nlinarith [abs_nonneg ξ, hQr1]
      have : |ξ| ≤ (1 / 2 : ℝ) := by linarith
      exact abs_le.mp this
    rw [hgband (Qr * ξ) hnot, mul_zero]
  -- The multiplier symbol for `w`.
  set C : ℝ → ℂ := fun η => m η * FourierTransform.fourier w η with hCdef
  have hOpu := hOp w hw_int hw_band
  rw [← hCdef] at hOpu
  -- The pointwise dilation identity.
  have hkey : ∀ x : ℝ, FourierTransformInv.fourierInv
        (fun ξ : ℝ => m (ξ / Qr) * FourierTransform.fourier g ξ) x
      = FourierTransformInv.fourierInv C (Qr * x) := by
    intro x
    have hfun : (fun ξ : ℝ => m (ξ / Qr) * FourierTransform.fourier g ξ)
        = (Qr : ℂ)⁻¹ • (fun ξ : ℝ => C (ξ / Qr)) := by
      funext ξ
      simp only [Pi.smul_apply, smul_eq_mul, hCdef, hFw]
      have harg : Qr * (ξ / Qr) = ξ := by field_simp
      rw [harg]
      rw [show (Qr : ℂ)⁻¹ * (m (ξ / Qr) * ((Qr : ℂ) * FourierTransform.fourier g ξ))
            = (m (ξ / Qr) * FourierTransform.fourier g ξ) * ((Qr : ℂ)⁻¹ * (Qr : ℂ)) by ring,
        inv_mul_cancel₀ (by exact_mod_cast hQr_ne : (Qr : ℂ) ≠ 0), mul_one]
    rw [hfun, fourierInv_const_smul', fourierInv_dilate C Qr x hQrpos]
    rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hQr_ne : (Qr : ℂ) ≠ 0),
      one_mul]
  -- The left-hand side is `Q⁻¹` times the `w`-integral.
  have hLHS : MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ENNReal.ofReal
        ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => m (ξ / Qr) * FourierTransform.fourier g ξ) x‖ ^ p)
      = ENNReal.ofReal (Qr⁻¹) * MeasureTheory.lintegral MeasureTheory.volume
          (fun y : ℝ => ENNReal.ofReal ‖FourierTransformInv.fourierInv C y‖ ^ p) := by
    have hfun : (fun x : ℝ => ENNReal.ofReal
        ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => m (ξ / Qr) * FourierTransform.fourier g ξ) x‖ ^ p)
        = fun x : ℝ =>
            (fun y : ℝ => ENNReal.ofReal ‖FourierTransformInv.fourierInv C y‖ ^ p) (Qr * x) := by
      funext x
      rw [hkey x]
    calc ∫⁻ x, ENNReal.ofReal
          ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => m (ξ / Qr) * FourierTransform.fourier g ξ) x‖ ^ p
        = ∫⁻ x, (fun y : ℝ => ENNReal.ofReal ‖FourierTransformInv.fourierInv C y‖ ^ p) (Qr * x) := by
            rw [hfun]
      _ = ENNReal.ofReal |Qr⁻¹| * ∫⁻ y, ENNReal.ofReal ‖FourierTransformInv.fourierInv C y‖ ^ p :=
            lintegral_comp_mul_left_all Qr hQr_ne
              (fun y : ℝ => ENNReal.ofReal ‖FourierTransformInv.fourierInv C y‖ ^ p)
      _ = ENNReal.ofReal (Qr⁻¹) * ∫⁻ y, ENNReal.ofReal ‖FourierTransformInv.fourierInv C y‖ ^ p := by
            rw [abs_of_pos (inv_pos.mpr hQrpos)]
  -- The `w`-integral is `Q` times the `g`-integral.
  have hRHS : MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ENNReal.ofReal ‖w x‖ ^ p)
      = ENNReal.ofReal Qr * MeasureTheory.lintegral MeasureTheory.volume
          (fun y : ℝ => ENNReal.ofReal ‖g y‖ ^ p) := by
    have hfun : (fun x : ℝ => ENNReal.ofReal ‖w x‖ ^ p)
        = fun x : ℝ => (fun y : ℝ => ENNReal.ofReal ‖g y‖ ^ p) (Qr⁻¹ * x) := by
      funext x
      rw [hwdef]
    calc ∫⁻ x, ENNReal.ofReal ‖w x‖ ^ p
        = ∫⁻ x, (fun y : ℝ => ENNReal.ofReal ‖g y‖ ^ p) (Qr⁻¹ * x) := by rw [hfun]
      _ = ENNReal.ofReal |(Qr⁻¹)⁻¹| * ∫⁻ y, ENNReal.ofReal ‖g y‖ ^ p :=
            lintegral_comp_mul_left_all Qr⁻¹ (inv_ne_zero hQr_ne)
              (fun y : ℝ => ENNReal.ofReal ‖g y‖ ^ p)
      _ = ENNReal.ofReal Qr * ∫⁻ y, ENNReal.ofReal ‖g y‖ ^ p := by
            rw [inv_inv, abs_of_pos hQrpos]
  have hQrinv : ENNReal.ofReal (Qr⁻¹) * ENNReal.ofReal Qr = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hQrpos.le), inv_mul_cancel₀ hQr_ne,
      ENNReal.ofReal_one]
  calc MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ENNReal.ofReal
        ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => m (ξ / Qr) * FourierTransform.fourier g ξ) x‖ ^ p)
      = ENNReal.ofReal (Qr⁻¹) * MeasureTheory.lintegral MeasureTheory.volume
          (fun y : ℝ => ENNReal.ofReal ‖FourierTransformInv.fourierInv C y‖ ^ p) := hLHS
    _ ≤ ENNReal.ofReal (Qr⁻¹) * (ENNReal.ofReal (A ^ p) *
          MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ENNReal.ofReal ‖w x‖ ^ p)) :=
        mul_le_mul_right hOpu _
    _ = ENNReal.ofReal (A ^ p) *
          MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ENNReal.ofReal ‖g x‖ ^ p) := by
        rw [hRHS]
        calc ENNReal.ofReal (Qr⁻¹) * (ENNReal.ofReal (A ^ p) *
                (ENNReal.ofReal Qr * MeasureTheory.lintegral MeasureTheory.volume
                  (fun y : ℝ => ENNReal.ofReal ‖g y‖ ^ p)))
            = ENNReal.ofReal (A ^ p) * (ENNReal.ofReal (Qr⁻¹) * ENNReal.ofReal Qr) *
                MeasureTheory.lintegral MeasureTheory.volume
                  (fun y : ℝ => ENNReal.ofReal ‖g y‖ ^ p) := by
              ring
          _ = ENNReal.ofReal (A ^ p) *
                MeasureTheory.lintegral MeasureTheory.volume
                  (fun y : ℝ => ENNReal.ofReal ‖g y‖ ^ p) := by
              rw [hQrinv, mul_one]

end

end Work.BourgainPlan.IonescuWainger
