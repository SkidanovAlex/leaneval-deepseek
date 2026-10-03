import Mathlib
import Submission.Work.KMTAreas.SupNorm.WavePacket
import Submission.Work.KMTAreas.SupNorm.Norms
import Submission.Work.KMTAreas.SupNorm.fourierInv_add_of_integrable
import Submission.Work.KMTAreas.SupNorm.exists_delta_rpow_mul_le
import Submission.Work.KMTAreas.SupNorm.exists_nu_C1_C2_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.SupNorm

open scoped FourierTransform ENNReal NNReal
open MeasureTheory

/-- **The wave packet splitting of the multiplier `T_θ = 𝓕⁻ ∘ (θ · 𝓕)`.**

For the wave packet `f_δ = 𝓕⁻(η((· - x₀)/δ))` (whose Fourier transform is the bump
`ξ ↦ η((ξ - x₀)/δ)`) and a continuous symbol `θ`,

`T_θ f_δ = θ x₀ • f_δ + 𝓕⁻((θ - θ x₀) · η((· - x₀)/δ))`.

This is the only place where Fourier analysis enters `supNorm_smooth`; the first summand carries
the value of the symbol at `x₀`, the second is the error term estimated by `hpoint`/`herr`. -/
theorem contMulOp_wavePacket_decomp {θ : ℝ → ℂ} (hθ : Continuous θ) {x₀ δ : ℝ} (hδ : 0 < δ) :
    Work.Analysis.IWMultiplier.contMulOp θ (⇑(wavePacket x₀ δ hδ))
      = (fun x => θ x₀ * wavePacket x₀ δ hδ x)
        + FourierTransformInv.fourierInv (fun ξ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) := by
  have hcont : Continuous (scaledBump x₀ δ) := (scaledBump_contDiff x₀ δ).continuous
  have hcs : HasCompactSupport (scaledBump x₀ δ) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ δ)
      (scaledBump_support hδ)
  have hIntB : Integrable (scaledBump x₀ δ) :=
    Continuous.integrable_of_hasCompactSupport hcont hcs
  have hIntG : Integrable (fun ξ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) :=
    Continuous.integrable_of_hasCompactSupport ((hθ.sub continuous_const).mul hcont)
      hcs.mul_left
  have hIntA : Integrable (fun ξ => θ x₀ * scaledBump x₀ δ ξ) := hIntB.const_mul (θ x₀)
  have hstep : Work.Analysis.IWMultiplier.contMulOp θ (⇑(wavePacket x₀ δ hδ))
      = FourierTransformInv.fourierInv (fun ξ => θ ξ * scaledBump x₀ δ ξ) := by
    rw [Work.Analysis.IWMultiplier.contMulOp]
    congr 1
    funext ξ
    rw [wavePacket_fourier_apply hδ]
  have hsplit : (fun ξ => θ ξ * scaledBump x₀ δ ξ)
      = (fun ξ => θ x₀ * scaledBump x₀ δ ξ)
        + (fun ξ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) := by
    funext ξ; simp only [Pi.add_apply]; ring
  have hadd : FourierTransformInv.fourierInv (fun ξ => θ ξ * scaledBump x₀ δ ξ)
      = FourierTransformInv.fourierInv (fun ξ => θ x₀ * scaledBump x₀ δ ξ)
        + FourierTransformInv.fourierInv (fun ξ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) := by
    rw [hsplit]; exact fourierInv_add_of_integrable hIntA hIntG
  have hfirst : FourierTransformInv.fourierInv (fun ξ => θ x₀ * scaledBump x₀ δ ξ)
      = fun x => θ x₀ * wavePacket x₀ δ hδ x := by
    have h1 : (fun ξ => θ x₀ * scaledBump x₀ δ ξ) = ⇑(θ x₀ • scaledBumpSch x₀ δ hδ) := by
      funext ξ
      rw [smul_apply, scaledBumpSch_apply]
      rfl
    rw [h1, ← SchwartzMap.fourierInv_coe (θ x₀ • scaledBumpSch x₀ δ hδ),
      FourierTransform.fourierInv_smul]
    ext x
    rw [smul_apply]
    rfl
  rw [hstep, hadd, hfirst]

/-- **The `Lᵖ` convexity step of `supNorm_smooth`.**

Given the two `Lᵖ` bounds `‖T_θ f_δ‖_p ≤ M ‖f_δ‖_p` and `‖E‖_p ≤ ofReal R`, and the exact value
`‖f_δ‖_p = ofReal (δ^{1-1/p} c₀)` of the wave packet norm together with the splitting
`T_θ f_δ = θ x₀ • f_δ + E`, we get the pointwise bound

`‖θ x₀‖ ≤ M + C · δ^{1-1/(2p)}`,  `C = 2^{3/(2p)} Kb^{1/(2p)} η₀^{1-1/(2p)} (2p/(2p-1))^{1/p} D^{1-1/(2p)} / c₀`.

Everything here is the triangle inequality in `ℒᵖ` followed by the division by the (positive,
explicit) norm of the wave packet; the hypothesis `hE'` carries the decay `R = C' ν^{1-1/(2p)}
δ^{1-1/p}` with `ν = D δ` of the error term. -/
theorem eLpNorm_bound_of_decomp {p : ENNReal} (hp1 : 1 ≤ p) (hp2 : p < ⊤)
    {θ : ℝ → ℂ} {x₀ M c₀ D Kb η0 δ : ℝ} (hM : 0 ≤ M) (hc₀ : 0 < c₀) (hδ : 0 < δ)
    (hD : 0 ≤ D) (hKb : 0 ≤ Kb) (hη0 : 0 ≤ η0)
    {W E : ℝ → ℂ}
    (hWmeas : AEStronglyMeasurable W volume)
    (hq : eLpNorm W p volume = ENNReal.ofReal (δ ^ (1 - 1 / p.toReal) * c₀))
    (hEmeas : AEStronglyMeasurable E volume)
    (hident : Work.Analysis.IWMultiplier.contMulOp θ W = (fun x => θ x₀ * W x) + E)
    (hT' : eLpNorm (Work.Analysis.IWMultiplier.contMulOp θ W) p volume
      ≤ ENNReal.ofReal M * eLpNorm W p volume)
    (hE' : eLpNorm E p volume
      ≤ ENNReal.ofReal (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
          * η0 ^ (1 - 1 / (2 * p.toReal)) * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
          * (D * δ) ^ (1 - 1 / (2 * p.toReal)) * δ ^ (1 - 1 / p.toReal))) :
    ‖θ x₀‖ ≤ M + (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
        * η0 ^ (1 - 1 / (2 * p.toReal)) * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
        * D ^ (1 - 1 / (2 * p.toReal)) / c₀) * δ ^ (1 - 1 / (2 * p.toReal)) := by
  have hp1' : (1:ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hp2.ne hp1
  have hQle : 0 ≤ δ ^ (1 - 1 / p.toReal) * c₀ :=
    le_of_lt (mul_pos (Real.rpow_pos_of_pos hδ _) hc₀)
  have hQpos : 0 < δ ^ (1 - 1 / p.toReal) * c₀ := mul_pos (Real.rpow_pos_of_pos hδ _) hc₀
  have hRnn : 0 ≤ 2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
      * η0 ^ (1 - 1 / (2 * p.toReal)) * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
      * (D * δ) ^ (1 - 1 / (2 * p.toReal)) * δ ^ (1 - 1 / p.toReal) := by
    have h2p : 0 < 2 * p.toReal - 1 := by linarith
    positivity
  have hsmul : (θ x₀) • W = fun x => θ x₀ * W x := by
    ext x; simp [smul_eq_mul]
  have hcmeas : AEStronglyMeasurable (Work.Analysis.IWMultiplier.contMulOp θ W) volume := by
    rw [hident]; exact (hWmeas.const_mul (θ x₀)).add hEmeas
  have hcongr : Work.Analysis.IWMultiplier.contMulOp θ W - E = (θ x₀) • W := by
    rw [hident, hsmul]; ext x; simp
  have h1 : eLpNorm ((θ x₀) • W) p volume
      ≤ eLpNorm (Work.Analysis.IWMultiplier.contMulOp θ W) p volume + eLpNorm E p volume := by
    have hsub := eLpNorm_sub_le (f := Work.Analysis.IWMultiplier.contMulOp θ W) (g := E)
      (μ := volume) hp1
    rwa [hcongr] at hsub
  have hineq : ‖θ x₀‖ₑ * eLpNorm W p volume
      ≤ ENNReal.ofReal M * eLpNorm W p volume
        + ENNReal.ofReal (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
            * η0 ^ (1 - 1 / (2 * p.toReal)) * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
            * (D * δ) ^ (1 - 1 / (2 * p.toReal)) * δ ^ (1 - 1 / p.toReal)) := by
    rw [← eLpNorm_const_smul (θ x₀) W p volume]
    exact h1.trans (add_le_add hT' hE')
  have hqne : eLpNorm W p volume ≠ ⊤ := by rw [hq]; exact ENNReal.ofReal_ne_top
  have hLne : ‖θ x₀‖ₑ * eLpNorm W p volume ≠ ⊤ := ENNReal.mul_ne_top enorm_ne_top hqne
  have hMne : ENNReal.ofReal M * eLpNorm W p volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqne
  have hineqR : ‖θ x₀‖ * (δ ^ (1 - 1 / p.toReal) * c₀)
      ≤ M * (δ ^ (1 - 1 / p.toReal) * c₀)
        + 2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
          * η0 ^ (1 - 1 / (2 * p.toReal)) * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
          * (D * δ) ^ (1 - 1 / (2 * p.toReal)) * δ ^ (1 - 1 / p.toReal) := by
    have h := (ENNReal.toReal_le_toReal hLne
      (by rw [ENNReal.add_ne_top]; exact ⟨hMne, ENNReal.ofReal_ne_top⟩)).2 hineq
    calc ‖θ x₀‖ * (δ ^ (1 - 1 / p.toReal) * c₀)
        = (‖θ x₀‖ₑ * eLpNorm W p volume).toReal := by
          rw [ENNReal.toReal_mul, toReal_enorm, hq, ENNReal.toReal_ofReal hQle]
      _ ≤ (ENNReal.ofReal M * eLpNorm W p volume
            + ENNReal.ofReal (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
                * η0 ^ (1 - 1 / (2 * p.toReal))
                * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
                * (D * δ) ^ (1 - 1 / (2 * p.toReal)) * δ ^ (1 - 1 / p.toReal))).toReal := h
      _ = M * (δ ^ (1 - 1 / p.toReal) * c₀)
            + 2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
              * η0 ^ (1 - 1 / (2 * p.toReal))
              * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
              * (D * δ) ^ (1 - 1 / (2 * p.toReal)) * δ ^ (1 - 1 / p.toReal) := by
          rw [ENNReal.toReal_add hMne ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal hM, hq, ENNReal.toReal_ofReal hQle, ENNReal.toReal_ofReal hRnn]
  have hRrewrite : 2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
      * η0 ^ (1 - 1 / (2 * p.toReal)) * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
      * (D * δ) ^ (1 - 1 / (2 * p.toReal)) * δ ^ (1 - 1 / p.toReal)
      = (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
          * η0 ^ (1 - 1 / (2 * p.toReal)) * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
          * D ^ (1 - 1 / (2 * p.toReal)) / c₀) * δ ^ (1 - 1 / (2 * p.toReal))
          * (δ ^ (1 - 1 / p.toReal) * c₀) := by
    rw [Real.mul_rpow hD hδ.le]
    field_simp
  have h2 : ‖θ x₀‖ * (δ ^ (1 - 1 / p.toReal) * c₀)
      ≤ (M + (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
          * η0 ^ (1 - 1 / (2 * p.toReal)) * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
          * D ^ (1 - 1 / (2 * p.toReal)) / c₀) * δ ^ (1 - 1 / (2 * p.toReal)))
        * (δ ^ (1 - 1 / p.toReal) * c₀) := by
    rw [hRrewrite] at hineqR
    calc ‖θ x₀‖ * (δ ^ (1 - 1 / p.toReal) * c₀)
        ≤ M * (δ ^ (1 - 1 / p.toReal) * c₀)
            + (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
              * η0 ^ (1 - 1 / (2 * p.toReal))
              * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
              * D ^ (1 - 1 / (2 * p.toReal)) / c₀) * δ ^ (1 - 1 / (2 * p.toReal))
              * (δ ^ (1 - 1 / p.toReal) * c₀) := hineqR
      _ = (M + (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
              * η0 ^ (1 - 1 / (2 * p.toReal))
              * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
              * D ^ (1 - 1 / (2 * p.toReal)) / c₀) * δ ^ (1 - 1 / (2 * p.toReal)))
            * (δ ^ (1 - 1 / p.toReal) * c₀) := by ring
  exact le_of_mul_le_mul_right h2 hQpos

/-- **The pointwise sup-norm bound for a smooth `Lᵖ` Fourier multiplier, tested on wave packets.**

If a `C²` symbol `θ` satisfies, for every `δ ∈ (0,1]`, the single-scale bound
`‖T_θ f_δ‖_p ≤ M ‖f_δ‖_p` on the wave packet `f_δ = 𝓕⁻(η((· - x₀)/δ))`, and if the two auxiliary
estimates `hpoint` (pointwise decay of `𝓕⁻((θ - θ x₀) η_{x₀,δ})`) and `herr` (its `Lᵖ` norm, fed
by the explicit norm `hwp` of the wave packet and the normalising constant `hker`) are available,
then `‖θ x₀‖ ≤ M`.

The proof tests the multiplier at `x₀` with the wave packet, uses the splitting
`T_θ f_δ = θ x₀ • f_δ + E` of `contMulOp_wavePacket_decomp`, bounds `‖E‖_p` by `herr`, divides by
the exact norm `‖f_δ‖_p = δ^{1-1/p} c₀` of `hwp`/`hker`, and lets `δ → 0`. -/
theorem supNorm_smooth {p : ENNReal} (hp1 : 1 ≤ p) (hp2 : p < ⊤)
    {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) {x₀ : ℝ} {M : ℝ} (hM : 0 ≤ M)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hker : MeasureTheory.eLpNorm (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) p MeasureTheory.volume = ENNReal.ofReal c₀)
    (hwp : ∀ {δ : ℝ} (hδ : 0 < δ),
        MeasureTheory.eLpNorm (⇑(Work.KMTAreas.SupNorm.wavePacket x₀ δ hδ)) p MeasureTheory.volume
          = ENNReal.ofReal (δ ^ (1 - 1 / p.toReal))
              * MeasureTheory.eLpNorm (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) p MeasureTheory.volume)
    (herr : ∀ {E : ℝ → ℂ} {A B ν δ Kb : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hKb : 0 ≤ Kb)
        (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
        (hE : ∀ x : ℝ, x ≠ 0 → ‖E x‖ ≤ min A (B / x ^ 2))
        (hAb : A ≤ ν * δ * Work.KMTAreas.SupNorm.etaI0) (hBb : B ≤ Kb * (ν / δ + 1))
        (hEm : MeasureTheory.AEStronglyMeasurable E MeasureTheory.volume),
        MeasureTheory.eLpNorm E p MeasureTheory.volume
          ≤ ENNReal.ofReal (2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
              * Work.KMTAreas.SupNorm.etaI0 ^ (1 - 1 / (2 * p.toReal))
              * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
              * ν ^ (1 - 1 / (2 * p.toReal)) * δ ^ (1 - 1 / p.toReal)))
    (hpoint : ∀ {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ν C₁ C₂ : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
        (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
        (hν : ∀ y ∈ Metric.closedBall x₀ δ, ‖θ y - θ x₀‖ ≤ ν)
        (hC₁ : ∀ y ∈ Metric.closedBall x₀ δ, ‖deriv θ y‖ ≤ C₁)
        (hC₂ : ∀ y ∈ Metric.closedBall x₀ δ, ‖iteratedDeriv 2 θ y‖ ≤ C₂),
        ∀ x : ℝ, x ≠ 0 →
          ‖FourierTransformInv.fourierInv (fun ξ => (θ ξ - θ x₀) * Work.KMTAreas.SupNorm.scaledBump x₀ δ ξ) x‖
            ≤ min (ν * δ * Work.KMTAreas.SupNorm.etaI0)
                (4 * (Work.KMTAreas.SupNorm.etaI0 + Work.KMTAreas.SupNorm.etaI1 + Work.KMTAreas.SupNorm.etaI2
                      + C₁ * Work.KMTAreas.SupNorm.etaI0 + C₂ * Work.KMTAreas.SupNorm.etaI0 + 2 * C₁ * Work.KMTAreas.SupNorm.etaI1)
                    * (ν / δ + 1) / x ^ 2))
    (hT : ∀ δ (hδ : 0 < δ) (hδ1 : δ ≤ 1),
        MeasureTheory.eLpNorm
            (Work.Analysis.IWMultiplier.contMulOp θ (⇑(Work.KMTAreas.SupNorm.wavePacket x₀ δ hδ)))
            p MeasureTheory.volume
          ≤ ENNReal.ofReal M
              * MeasureTheory.eLpNorm (⇑(Work.KMTAreas.SupNorm.wavePacket x₀ δ hδ)) p MeasureTheory.volume) :
    ‖θ x₀‖ ≤ M := by
  -- the local `C¹`/`C²` bounds on `θ` supplied by `exists_nu_C1_C2_bound`
  obtain ⟨D, hD, D₂, hD₂, hbc⟩ := exists_nu_C1_C2_bound hθ x₀
  have hp1' : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hp2.ne hp1
  have h2p : 0 < 2 * p.toReal - 1 := by linarith
  have ha : 0 < 1 - 1 / (2 * p.toReal) := by
    have h : 1 / (2 * p.toReal) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hη0 : 0 ≤ etaI0 := etaI0_nonneg
  have hη1 : 0 ≤ etaI1 := etaI1_nonneg
  have hη2 : 0 ≤ etaI2 := etaI2_nonneg
  -- the constant of the estimate
  set Kb : ℝ := 4 * (etaI0 + etaI1 + etaI2 + D * etaI0 + D₂ * etaI0 + 2 * D * etaI1) with hKbdef
  have hKb : 0 ≤ Kb := by
    rw [hKbdef]
    have h : 0 ≤ etaI0 + etaI1 + etaI2 + D * etaI0 + D₂ * etaI0 + 2 * D * etaI1 := by
      nlinarith [hη0, hη1, hη2, hD, hD₂, mul_nonneg hD hη0, mul_nonneg hD₂ hη0,
        mul_nonneg hD hη1]
    linarith
  set Cc : ℝ := 2 ^ (3 / (2 * p.toReal)) * Kb ^ (1 / (2 * p.toReal))
      * etaI0 ^ (1 - 1 / (2 * p.toReal)) * (2 * p.toReal / (2 * p.toReal - 1)) ^ (1 / p.toReal)
    with hCcdef
  have hCc_nonneg : 0 ≤ Cc := by
    rw [hCcdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hKb _)) (Real.rpow_nonneg hη0 _))
      (Real.rpow_nonneg (div_nonneg (by linarith) (le_of_lt h2p)) _)
  have hCcoe : 0 ≤ Cc * D ^ (1 - 1 / (2 * p.toReal)) / c₀ :=
    div_nonneg (mul_nonneg hCc_nonneg (Real.rpow_nonneg hD _)) hc₀.le
  -- the key estimate, for every small `δ`
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → D * δ ≤ 1 →
      ‖θ x₀‖ ≤ M + (Cc * D ^ (1 - 1 / (2 * p.toReal)) / c₀)
        * δ ^ (1 - 1 / (2 * p.toReal)) := by
    intro δ hδ hδ1 hDδ
    obtain ⟨hνb, hC₁b, hC₂b⟩ := hbc δ hδ hδ1
    -- integrability and measurability of the error term
    have hcontB : Continuous (scaledBump x₀ δ) := (scaledBump_contDiff x₀ δ).continuous
    have hcsB : HasCompactSupport (scaledBump x₀ δ) :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ δ)
        (scaledBump_support hδ)
    have hGint : Integrable (fun ξ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) :=
      Continuous.integrable_of_hasCompactSupport
        ((hθ.continuous.sub continuous_const).mul hcontB) hcsB.mul_left
    have hGmem : MemLp (fun ξ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) 1 volume :=
      (memLp_one_iff_integrable).2 hGint
    have hEmeas : AEStronglyMeasurable
        (FourierTransformInv.fourierInv (fun ξ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ)) volume := by
      rw [← Real.Lp.fourierTransformInv_toLp (f := fun ξ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ) hGmem]
      exact (Real.Lp.fourierTransformInv _).continuous.aestronglyMeasurable
    -- the wave packet is (strongly) measurable
    have hWmeas : AEStronglyMeasurable (⇑(wavePacket x₀ δ hδ)) volume :=
      (wavePacket x₀ δ hδ).continuous.aestronglyMeasurable
    -- the exact norm of the wave packet
    have hq : eLpNorm (⇑(wavePacket x₀ δ hδ)) p volume
        = ENNReal.ofReal (δ ^ (1 - 1 / p.toReal) * c₀) := by
      rw [hwp hδ, hker, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    -- the two numerical hypotheses of `herr`
    have hν0 : 0 ≤ D * δ := mul_nonneg hD hδ.le
    have hA : 0 ≤ D * δ * δ * etaI0 := by
      have := mul_nonneg (mul_nonneg hν0 hδ.le) hη0; linarith [this]
    have hB : 0 ≤ Kb * ((D * δ) / δ + 1) := by
      have h1 : 0 ≤ (D * δ) / δ + 1 := by
        have := div_nonneg hν0 hδ.le; linarith
      exact mul_nonneg hKb h1
    have hEbound := hpoint (δ := δ) hδ hδ1 (ν := D * δ) (C₁ := D) (C₂ := D₂)
      hν0 hDδ hD hD₂ hνb hC₁b hC₂b
    have hherr := herr (E := FourierTransformInv.fourierInv
          (fun ξ => (θ ξ - θ x₀) * scaledBump x₀ δ ξ))
      (A := D * δ * δ * etaI0) (B := Kb * ((D * δ) / δ + 1)) (ν := D * δ) (δ := δ) (Kb := Kb)
      hA hB hKb hν0 hDδ hδ hδ1 hEbound le_rfl le_rfl hEmeas
    -- the multiplier bound on the wave packet
    have hT' := hT δ hδ hδ1
    -- assemble
    have hmain := eLpNorm_bound_of_decomp (p := p) hp1 hp2 (θ := θ) (x₀ := x₀) (M := M)
      (c₀ := c₀) (D := D) (Kb := Kb) (η0 := etaI0) (δ := δ)
      hM hc₀ hδ hD hKb hη0 hWmeas hq hEmeas
      (contMulOp_wavePacket_decomp hθ.continuous hδ) hT' hherr
    exact hmain
  -- `δ → 0`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hδ1, hDδ, hδle⟩ :=
    exists_delta_rpow_mul_le (C := Cc * D ^ (1 - 1 / (2 * p.toReal)) / c₀)
      (a := 1 - 1 / (2 * p.toReal)) (D := D) (ε := ε) hCcoe ha hD hε
  exact (key δ hδ hδ1 hDδ).trans (by linarith)

end Work.KMTAreas.SupNorm
