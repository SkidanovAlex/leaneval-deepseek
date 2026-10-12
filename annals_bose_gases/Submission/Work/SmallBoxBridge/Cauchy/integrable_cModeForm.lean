import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Cauchy.pModeForm_le_pDiagForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the `fsKinCoeff`-weighted DIAGONAL mode content

The kinetic bridge's Cauchy step (`pModeForm_le_pDiagForm`) is stated with the
integrability of the weighted diagonal content

  `p ↦ [‖p‖−c]₊² · (s³)⁻¹ Σ_i ∫_{abox} ‖pSlotAmp s p Ψ i x‖²`

as a hypothesis; this module supplies it (`integrable_cModeForm`).

## Strategy

`pSlotAmp s p Ψ i x` is the `i`-th slot amplitude of the `Q_B`-projected momentum mode
`qMode s p`, i.e. the complex slot integral `∫_{acube} qMode s p z · Ψ(x_{i↦z}) dz`. Its real
and imaginary parts are the two *windowed `χ`-cosine/sine overlaps*
`∫_{acube} qModeRe s p z · Ψ(x_{i↦z}) dz` and `∫_{acube} qModeIm s p z · Ψ(x_{i↦z}) dz`
(`pSlotAmp_normSq_decomp_aux`). Each of these vanishes faster than any power of `‖p‖`
uniformly on `abox`: `exists_qModeRe_mode_bound` / `exists_qModeIm_mode_bound` give the
`K/(1+‖p‖)³` decay. Hence the squared slot amplitudes decay like `(1+‖p‖)⁻⁶` uniformly, so the
`x`-integral over the compact box is `≤ vol(abox)·(1+‖p‖)⁻⁶ = (s³)^{n+1}·(1+‖p‖)⁻⁶`
(`pModeDiagonal_decay_aux`). Multiplying by `(s³)⁻¹` and summing over the `n+1` slots gives

  `pModeDiagonal s p Φ ≤ K₀/(1+‖p‖)⁶`,

and since `[r−c]₊² ≤ r²` the weighted integrand is dominated by
`K₀·‖p‖²/(1+‖p‖)⁶`, which is integrable in dimension `3`
(`Commons.Measure.Integral.integrable_norm_sq_div_one_add_pow`).
-/

namespace Work.SmallBoxBridge.Cauchy

open MeasureTheory Metric
open scoped Topology Real BigOperators
open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-- **Decomposition of the slot amplitude**: the squared norm of the slot-`i` amplitude of the
`Q_B`-projected mode `qMode s p` is the sum of the squares of the two real `qModeRe`/`qModeIm`
overlaps. -/
private lemma pSlotAmp_normSq_decomp_aux {N : ℕ} {s : ℝ} (hs : 0 < s) (p : ℝ³)
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (i : Fin N) (x : X N) :
    ‖pSlotAmp s p Ψ i x‖ ^ 2 =
      (∫ z in acube s, qModeRe s p z * Ψ (Function.update x i z)) ^ 2
      + (∫ z in acube s, qModeIm s p z * Ψ (Function.update x i z)) ^ 2 := by
  have hint : Integrable (fun z : ℝ³ => qMode s p z * (Ψ (Function.update x i z) : ℂ))
      (volume.restrict (acube s)) := by
    refine ContinuousOn.integrableOn_compact (acube_compact hs) ?_
    exact (((continuous_qMode (ℓ := s) p).mul (Complex.continuous_ofReal.comp
      (hΨ.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i
        continuous_id))))).continuousOn
  have hre : (pSlotAmp s p Ψ i x).re
      = ∫ z in acube s, qModeRe s p z * Ψ (Function.update x i z) := by
    rw [pSlotAmp]
    have hcongr : (fun z : ℝ³ => qModeRe s p z * Ψ (Function.update x i z))
        = fun z : ℝ³ => (qMode s p z * (Ψ (Function.update x i z) : ℂ)).re := by
      funext z
      simp only [qModeRe, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
    rw [hcongr]
    exact (Complex.reCLM.integral_comp_comm (φ_int := hint)).symm
  have him : (pSlotAmp s p Ψ i x).im
      = ∫ z in acube s, qModeIm s p z * Ψ (Function.update x i z) := by
    rw [pSlotAmp]
    have hcongr : (fun z : ℝ³ => qModeIm s p z * Ψ (Function.update x i z))
        = fun z : ℝ³ => (qMode s p z * (Ψ (Function.update x i z) : ℂ)).im := by
      funext z
      simp only [qModeIm, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_add]
    rw [hcongr]
    exact (Complex.imCLM.integral_comp_comm (φ_int := hint)).symm
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  ring

/-- **The uniform `(1+‖p‖)⁻⁶` decay of the diagonal mode content.** -/
private lemma pModeDiagonal_decay_aux {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ³, pModeDiagonal s p Φ ≤ K / (1 + ‖p‖) ^ 6 := by
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hΦc : Continuous Φ := hΦ.continuous
  obtain ⟨K1, hK10, hK1⟩ := exists_qModeRe_mode_bound hs n Φ hΦ3
  obtain ⟨K2, hK20, hK2⟩ := exists_qModeIm_mode_bound hs n Φ hΦ3
  refine ⟨((n : ℝ) + 1) * (s ^ 3) ^ n * (K1 ^ 2 + K2 ^ 2), by positivity, fun p => ?_⟩
  have hvol : volume.real (abox (n + 1) s) = (s ^ 3) ^ (n + 1) := by
    rw [MeasureTheory.measureReal_def, abox_volume (n + 1) s hs.le]
    exact ENNReal.toReal_ofReal (pow_nonneg (pow_nonneg hs.le 3) (n + 1))
  have hPt : ∀ (i : Fin (n + 1)) (x : X (n + 1)), x ∈ abox (n + 1) s →
      ‖pSlotAmp s p Φ i x‖ ^ 2 ≤ (K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6 := by
    intro i x hx
    rw [pSlotAmp_normSq_decomp_aux hs p hΦc i x]
    have hR := hK1 x hx i p
    have hI := hK2 x hx i p
    have h1 : (∫ z in acube s, qModeRe s p z * Φ (Function.update x i z)) ^ 2
        ≤ K1 ^ 2 / (1 + ‖p‖) ^ 6 := by
      rw [← sq_abs]
      refine le_trans (pow_le_pow_left₀ (abs_nonneg _) hR 2) ?_
      rw [div_pow, ← pow_mul]
    have h2 : (∫ z in acube s, qModeIm s p z * Φ (Function.update x i z)) ^ 2
        ≤ K2 ^ 2 / (1 + ‖p‖) ^ 6 := by
      rw [← sq_abs]
      refine le_trans (pow_le_pow_left₀ (abs_nonneg _) hI 2) ?_
      rw [div_pow, ← pow_mul]
    have h3 : K1 ^ 2 / (1 + ‖p‖) ^ 6 + K2 ^ 2 / (1 + ‖p‖) ^ 6
        = (K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6 := by ring
    linarith [h1, h2, h3]
  have hInt : ∀ i : Fin (n + 1),
      ∫ x in abox (n + 1) s, ‖pSlotAmp s p Φ i x‖ ^ 2
        ≤ (s ^ 3) ^ (n + 1) * ((K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6) := by
    intro i
    have hcont : Continuous (fun x : X (n + 1) => ‖pSlotAmp s p Φ i x‖ ^ 2) :=
      (((Work.SmallBoxBridge.Cauchy.continuous_pSlotAmp_pair (N := n + 1) hs hΦc i).comp
        (continuous_const.prodMk continuous_id)).norm).pow 2
    have hg1 : IntegrableOn (fun x : X (n + 1) => ‖pSlotAmp s p Φ i x‖ ^ 2)
        (abox (n + 1) s) volume :=
      ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs) hcont.continuousOn
    have hg2 : IntegrableOn (fun _ : X (n + 1) => (K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6)
        (abox (n + 1) s) volume :=
      integrableOn_const (abox_lt_top (n + 1) s hs.le).ne
    calc ∫ x in abox (n + 1) s, ‖pSlotAmp s p Φ i x‖ ^ 2
        ≤ ∫ _x in abox (n + 1) s, (K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6 :=
          setIntegral_mono_on hg1 hg2 (abox_measurable (n + 1) s) (fun x hx => hPt i x hx)
      _ = (s ^ 3) ^ (n + 1) * ((K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6) := by
          rw [setIntegral_const, hvol, smul_eq_mul]
  rw [pModeDiagonal]
  have hsum : ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, ‖pSlotAmp s p Φ i x‖ ^ 2
      ≤ ((n : ℝ) + 1) * ((s ^ 3) ^ (n + 1) * ((K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6)) := by
    calc ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, ‖pSlotAmp s p Φ i x‖ ^ 2
        ≤ ∑ _i : Fin (n + 1), (s ^ 3) ^ (n + 1) * ((K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6) :=
          Finset.sum_le_sum (fun i _ => hInt i)
      _ = ((n : ℝ) + 1) * ((s ^ 3) ^ (n + 1) * ((K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hs3pos : 0 ≤ (s ^ 3)⁻¹ := by positivity
  calc (s ^ 3)⁻¹ * ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, ‖pSlotAmp s p Φ i x‖ ^ 2
      ≤ (s ^ 3)⁻¹ * (((n : ℝ) + 1) *
          ((s ^ 3) ^ (n + 1) * ((K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6))) :=
        mul_le_mul_of_nonneg_left hsum hs3pos
    _ = ((n : ℝ) + 1) * (s ^ 3) ^ n * (K1 ^ 2 + K2 ^ 2) / (1 + ‖p‖) ^ 6 := by
        have hs3ne : s ^ 3 ≠ 0 := by positivity
        have hdne : (1 + ‖p‖) ^ 6 ≠ 0 := by positivity
        field_simp
        ring

/-- **Integrability of the `fsKinCoeff`-weighted diagonal mode content.** -/
theorem integrable_cModeForm {n : ℕ} {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    {Φ : (Fin (n + 1) → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      (∑ i : Fin (n + 1), (s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) s,
        ‖Submission.BoseGases.pSlotAmp s p Φ i x‖ ^ 2)) := by
  obtain ⟨K, hK0, hKdec⟩ := pModeDiagonal_decay_aux hs hΦ
  have hEq : (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
        (∑ i : Fin (n + 1), (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, ‖pSlotAmp s p Φ i x‖ ^ 2))
      = fun p : ℝ³ => fsKinCoeff c ‖p‖ * pModeDiagonal s p Φ := by
    funext p
    congr 1
    simp only [pModeDiagonal]
    rw [Finset.mul_sum]
  rw [hEq]
  have hnn : ∀ p : ℝ³, 0 ≤ pModeDiagonal s p Φ := by
    intro p
    rw [pModeDiagonal]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _)))
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ => fsKinCoeff c ‖p‖ * pModeDiagonal s p Φ)
      volume := by
    refine Continuous.aestronglyMeasurable ?_
    refine ((?_ : Continuous (fun p : ℝ³ => fsKinCoeff c ‖p‖))).mul ?_
    · rw [show (fun p : ℝ³ => fsKinCoeff c ‖p‖)
          = (fun r : ℝ => (max (r - c) 0) ^ 2) ∘ (fun p : ℝ³ => ‖p‖) from rfl]
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp continuous_norm
    · rw [show (fun p : ℝ³ => pModeDiagonal s p Φ)
          = (fun p : ℝ³ => (s ^ 3)⁻¹ * ∑ i : Fin (n + 1),
              ∫ x in abox (n + 1) s, ‖pSlotAmp s p Φ i x‖ ^ 2) from by
        funext p; simp only [pModeDiagonal]]
      exact (continuous_finsetSum _ (fun i _ =>
        Work.SmallBoxBridge.Cauchy.continuous_integral_pSlotAmp_sq hs hΦ.continuous i)).const_mul _
  have hg : Integrable (fun p : ℝ³ => K * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6)) :=
    (Commons.Measure.Integral.integrable_norm_sq_div_one_add_pow 6 le_rfl).const_mul K
  refine Integrable.mono' hg hmeas ?_
  filter_upwards with p
  have h1 : fsKinCoeff c ‖p‖ ≤ ‖p‖ ^ 2 := by
    rw [fsKinCoeff]
    have h2 : max (‖p‖ - c) 0 ≤ ‖p‖ := max_le (by linarith) (norm_nonneg p)
    exact pow_le_pow_left₀ (le_max_right _ _) h2 2
  have h2 : pModeDiagonal s p Φ ≤ K / (1 + ‖p‖) ^ 6 := hKdec p
  have hfp : 0 ≤ fsKinCoeff c ‖p‖ * pModeDiagonal s p Φ :=
    mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (hnn p)
  rw [Real.norm_of_nonneg hfp]
  calc fsKinCoeff c ‖p‖ * pModeDiagonal s p Φ
      ≤ ‖p‖ ^ 2 * (K / (1 + ‖p‖) ^ 6) := mul_le_mul h1 h2 (hnn p) (by positivity)
    _ = K * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) := by ring

end Work.SmallBoxBridge.Cauchy
