import Submission.Work.BourgainPlan.Thm52.Defs
import Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel
import Submission.Work.Analysis.Fourier.lattice_sup_lp_sampling
import Submission.Work.BourgainPlan.IonescuWainger.aemeasurable_varRho_family
import Submission.Work.BourgainPlan.IonescuWainger.exists_pairing_attaining_sqrt_sum_sq
import Submission.Work.BourgainPlan.IonescuWainger.exists_kernel_lattice_weight_le
import Submission.Work.BourgainPlan.IonescuWainger.varRho_bandlimited_pointwise
import Submission.Work.BourgainPlan.IonescuWainger.varRho_fourierInv_pointwise

/-!
# The sampling principle for the `2`-variation (KMSZ Definition 5.1(3), `d = 1`)

Kosz–Mirek–Słomian–Zhang, arXiv:2606.12663, Definition 5.1(3) postulate, for a Rademacher–Menshov
seminorm `S`, the *sampling principle*

`‖(T_ℤ[J_1 | m_n K_Q])_n‖_{ℓ^p(ℤ) → S} ≤ C₃ ‖(T_ℝ[m_n])_n‖_{L^p(ℝ) → S}`

for multipliers `m_n` supported in `Q⁻¹𝕋`.  For this corpus the relevant `S` is the `2`-variation
`varRhoFrom 2 κ` of `Work.BourgainPlan.Thm52.LargeScaleBound` — the second named input of KMSZ
Theorem 5.2, whose discharge for the §6.3 model family is still open.

This file supplies the analytic core of that principle: the **lattice sampling inequality for the
`2`-variation**, i.e. the `varRhoFrom` analogue of
`Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow` (the same statement with
`⨆_j ‖·‖` in place of the variation).  For a band-limited family `h : ℕ → ℝ → ℂ`,

`∫⁻_ℤ (varRhoFrom 2 κ (n ↦ h_n(m)))^p ≤ C ∫⁻_ℝ (varRhoFrom 2 κ (n ↦ h_n(x)))^p`,

with `C` independent of the family `h` and of the threshold `κ`.

The proof has the shape of the `sup` version: the reproducing formula
`f(x) = ∫ f(y) K(x-y) dy` (`band_limited_reproducing_kernel`) is applied to the *differences*
`h_{t(j+1)} − h_{t j}` (`Work.BourgainPlan.IonescuWainger.varRho_bandlimited_pointwise`), the
weighted power-mean (`Commons.Analysis.Fourier.lintegral_mul_rpow_le_rpow_mul_lintegral`) replaces
the `sup`-over-`j` step at each lattice point, and the lattice bound `Σ_m ‖K(m−x)‖ ≤ C` of the
reproducing kernel (`Work.BourgainPlan.IonescuWainger.exists_kernel_lattice_weight_le`) closes the
estimate.
-/

open MeasureTheory
open scoped ENNReal BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

theorem exists_lattice_varRhoFrom_le_integral_varRhoFrom {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ → ℝ → ℂ),
      (∀ n, MeasureTheory.Integrable (h n)) →
      (∀ n, Continuous (h n)) →
      (∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) →
        FourierTransform.fourier (h n) ξ = 0) →
      ∀ κ : ℕ,
      ∫⁻ m : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => h n (m : ℝ))) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
          ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => h n x)) ^ p
            ∂MeasureTheory.volume := by
  obtain ⟨K, hKint, ⟨C0, hC0pos, hKdec⟩, hrep⟩ :=
    Commons.Analysis.Fourier.band_limited_reproducing_kernel
  obtain ⟨B, hBpos, hWle, hlatt⟩ := exists_kernel_lattice_weight_le K C0 hC0pos hKdec
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  refine ⟨B ^ p, Real.rpow_pos_of_pos hBpos p, ?_⟩
  intro h hint hcont hbl κ
  set G : ℝ → ℝ≥0∞ := fun x => Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => h n x) with hG
  have hGmeas : AEMeasurable G MeasureTheory.volume := by
    rw [hG]
    refine AEMeasurable.iSup (fun hi : ℕ => ?_)
    exact aemeasurable_varRho_family 2 κ hi hcont
  have hpoint : ∀ x : ℝ, G x ≤ ∫⁻ y : ℝ, G y * ‖K (x - y)‖ₑ := by
    intro x
    rw [hG]
    exact varRho_bandlimited_pointwise K C0 hC0pos hKint hKdec hrep h hint hcont hbl κ x
  -- the reproducing kernel is a fixed weight: its total mass and its lattice sum
  have hWtr : ∀ x : ℝ, (∫⁻ t : ℝ, ‖K (x - t)‖ₑ) = ∫⁻ t : ℝ, ‖K t‖ₑ := by
    intro x
    have hA : (∫⁻ t : ℝ, ‖K (x - t)‖ₑ) = ∫⁻ t : ℝ, ‖K (-t + x)‖ₑ := by
      apply lintegral_congr; intro t; rw [show -t + x = x - t by ring]
    have hB : (∫⁻ t : ℝ, ‖K (-t + x)‖ₑ) = ∫⁻ t : ℝ, ‖K (t + x)‖ₑ :=
      lintegral_neg_eq_self (fun u : ℝ => ‖K (u + x)‖ₑ)
    have hC : (∫⁻ t : ℝ, ‖K (t + x)‖ₑ) = ∫⁻ t : ℝ, ‖K (x + t)‖ₑ := by
      apply lintegral_congr; intro t; rw [add_comm]
    rw [hA, hB, hC]
    exact lintegral_add_left_eq_self (fun u : ℝ => ‖K u‖ₑ) x
  have hwmeas : ∀ x : ℝ, AEMeasurable (fun t : ℝ => ‖K (x - t)‖ₑ) MeasureTheory.volume := by
    intro x
    have h1 : AEMeasurable K
        (MeasureTheory.Measure.map (fun t : ℝ => x - t) MeasureTheory.volume) := by
      rw [MeasureTheory.Measure.map_sub_left_eq_self]
      exact hKint.aemeasurable
    exact (h1.comp_measurable (measurable_const.sub measurable_id)).enorm
  have hWne : (∫⁻ t : ℝ, ‖K t‖ₑ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hWle
  have hstep : ∀ m : ℤ, (∫⁻ t : ℝ, G t * ‖K ((m : ℝ) - t)‖ₑ) ^ p
      ≤ (∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1) * ∫⁻ t : ℝ, G t ^ p * ‖K ((m : ℝ) - t)‖ₑ := by
    intro m
    have h := Commons.Analysis.Fourier.lintegral_mul_rpow_le_rpow_mul_lintegral hp
      hGmeas (hwmeas (m : ℝ))
    rwa [hWtr (m : ℝ)] at h
  -- the assembly
  have hkey : ∫⁻ m : ℤ, G (m : ℝ) ^ p ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (B ^ p) * ∫⁻ t : ℝ, G t ^ p := by
    calc ∫⁻ m : ℤ, G (m : ℝ) ^ p ∂MeasureTheory.Measure.count
        = ∑' m : ℤ, G (m : ℝ) ^ p := MeasureTheory.lintegral_count _
      _ ≤ ∑' m : ℤ, (∫⁻ t : ℝ, G t * ‖K ((m : ℝ) - t)‖ₑ) ^ p :=
          ENNReal.tsum_le_tsum (fun m => ENNReal.rpow_le_rpow (hpoint (m : ℝ)) hp0.le)
      _ ≤ ∑' m : ℤ, (∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1)
            * ∫⁻ t : ℝ, G t ^ p * ‖K ((m : ℝ) - t)‖ₑ :=
          ENNReal.tsum_le_tsum hstep
      _ = (∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1)
            * ∑' m : ℤ, ∫⁻ t : ℝ, G t ^ p * ‖K ((m : ℝ) - t)‖ₑ :=
          ENNReal.tsum_mul_left
      _ = (∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1)
            * ∫⁻ t : ℝ, ∑' m : ℤ, G t ^ p * ‖K ((m : ℝ) - t)‖ₑ := by
          rw [← lintegral_tsum]
          intro m
          exact (hGmeas.pow_const p).mul (hwmeas (m : ℝ))
      _ = (∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1)
            * ∫⁻ t : ℝ, G t ^ p * (∑' m : ℤ, ‖K ((m : ℝ) - t)‖ₑ) := by
          congr 1
          apply lintegral_congr; intro t
          rw [ENNReal.tsum_mul_left]
      _ ≤ (∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1)
            * ∫⁻ t : ℝ, G t ^ p * ENNReal.ofReal B := by
          apply mul_le_mul_of_nonneg_left _ bot_le
          apply lintegral_mono; intro t
          exact mul_le_mul_of_nonneg_left (hlatt t) bot_le
      _ = (∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1)
            * (ENNReal.ofReal B * ∫⁻ t : ℝ, G t ^ p) := by
          rw [MeasureTheory.lintegral_mul_const'' _ (hGmeas.pow_const p),
            mul_comm (∫⁻ a : ℝ, G a ^ p) (ENNReal.ofReal B)]
      _ ≤ ENNReal.ofReal (B ^ p) * ∫⁻ t : ℝ, G t ^ p := by
          have hle : (∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1) ≤ ENNReal.ofReal (B ^ (p - 1)) := by
            rw [← ENNReal.ofReal_rpow_of_nonneg hBpos.le (by linarith)]
            exact ENNReal.rpow_le_rpow hWle (by linarith)
          have hconst : ENNReal.ofReal (B ^ (p - 1)) * ENNReal.ofReal B
              = ENNReal.ofReal (B ^ p) := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hBpos.le _)]
            congr 1
            have h1 : B ^ p = B ^ (p - 1) * B := by
              have h2 : B ^ p = B ^ (p - 1 + 1) := by rw [sub_add_cancel]
              rw [h2, Real.rpow_add hBpos, Real.rpow_one]
            exact h1.symm
          calc (∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1)
                * (ENNReal.ofReal B * ∫⁻ t : ℝ, G t ^ p)
              = ((∫⁻ t : ℝ, ‖K t‖ₑ) ^ (p - 1) * ENNReal.ofReal B)
                * ∫⁻ t : ℝ, G t ^ p := by ring
            _ ≤ (ENNReal.ofReal (B ^ (p - 1)) * ENNReal.ofReal B)
                * ∫⁻ t : ℝ, G t ^ p :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle bot_le) bot_le
            _ = ENNReal.ofReal (B ^ p) * ∫⁻ t : ℝ, G t ^ p := by rw [hconst]
  simpa only [hG] using hkey


/-- **The inverse Fourier transform of an integrable amplitude is continuous** (dominated
convergence), in the `L¹`-Fourier form of `Real.Lp.fourierTransformInv`. -/
theorem continuous_fourierInv_of_integrable {W : ℝ → ℂ} (hW : MeasureTheory.Integrable W) :
    Continuous (fun x : ℝ => FourierTransformInv.fourierInv W x) := by
  have h1 : (⇑(Real.Lp.fourierTransformInv
      (MemLp.toLp W (memLp_one_iff_integrable.mpr hW))) : ℝ → ℂ)
      = FourierTransformInv.fourierInv W := Real.Lp.fourierTransformInv_toLp _
  rw [← h1]
  exact (Real.Lp.fourierTransformInv _).continuous

/-- **The sampling inequality for the `2`-variation, in the amplitude (`𝓕⁻`) form of KMSZ
Definition 5.1(3).**  For `p > 1` there is a constant `C > 0`, independent of the integrable
amplitude family `W : ℕ → ℝ → ℂ`, of the reproducing kernel `w` and of its decay constant `B`, with

`∫⁻_ℤ (V²_{n ≥ κ}(𝓕⁻(W n)(m)))^p d# ≤ ofReal (C · B^p) ∫⁻_ℝ (V²_{n ≥ κ}(𝓕⁻(W n)(x)))^p dx`

whenever `𝓕w ≡ 1` on `⋃_n supp (W n)`.  This is the form consumed by the sampling principle of
KMSZ (§6.3): the discrete operators `T_ℤ[J_1|m_n K_Q]` are the lattice values of `𝓕⁻(m_n · trig)`
and the continuous ones are `𝓕⁻(m_n · 𝓕g)`. -/
theorem exists_lattice_varRhoFrom_fourierInv_le {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ → ℝ → ℂ), (∀ n, MeasureTheory.Integrable (W n)) →
      ∀ (w : ℝ → ℂ) (B : ℝ), MeasureTheory.Integrable w → 0 < B →
      (∀ z : ℝ, ‖w z‖ ≤ B / (1 + z ^ 2)) →
      (∀ (n : ℕ) (β : ℝ), W n β ≠ 0 → FourierTransform.fourier w β = 1) →
      ∀ κ : ℕ,
      ∫⁻ m : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n => FourierTransformInv.fourierInv (W n) (m : ℝ))) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * B ^ p) *
          ∫⁻ y : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => FourierTransformInv.fourierInv (W n) y)) ^ p ∂MeasureTheory.volume := by
  obtain ⟨B1, hB1pos, hB1mass, hB1latt⟩ :=
    exists_kernel_lattice_weight_le (fun u : ℝ => (((1 + u ^ 2)⁻¹ : ℝ) : ℂ)) 1 one_pos
      (fun u => by rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div])
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  have hB1nn : (0 : ℝ) ≤ B1 ^ (p - 1) * B1 := by positivity
  refine ⟨B1 ^ (p - 1) * B1, by positivity, ?_⟩
  intro W hW w B hw hBpos hwdec hprod κ
  set G : ℝ → ℝ≥0∞ :=
    fun x => Work.BourgainPlan.Maximal.varRhoFrom 2 κ
      (fun n => FourierTransformInv.fourierInv (W n) x) with hG
  have hGcont : ∀ n : ℕ, Continuous (fun x : ℝ => FourierTransformInv.fourierInv (W n) x) :=
    fun n => continuous_fourierInv_of_integrable (hW n)
  have hGmeas : AEMeasurable G MeasureTheory.volume := by
    rw [hG]
    refine AEMeasurable.iSup (fun hi : ℕ => ?_)
    exact aemeasurable_varRho_family 2 κ hi hGcont
  have hpoint : ∀ x : ℝ, G x ≤ ENNReal.ofReal B
      * ∫⁻ y : ℝ, G y * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹) := by
    intro x
    rw [hG]
    exact varRho_fourierInv_pointwise W hW w B hBpos hw hwdec hprod κ x
  have hwm_meas : ∀ x : ℝ,
      AEMeasurable (fun y : ℝ => ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹)) MeasureTheory.volume := by
    intro x
    have h1 : Measurable (fun y : ℝ => (x - y) ^ 2) :=
      (measurable_const.sub measurable_id).pow_const 2
    exact (ENNReal.measurable_ofReal.comp (Measurable.inv (h1.const_add 1))).aemeasurable
  have hnormK : ∀ u : ℝ, ‖(((1 + u ^ 2)⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal ((1 + u ^ 2)⁻¹) := by
    intro u
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hwmass : ∀ x : ℝ, (∫⁻ y : ℝ, ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹))
      ≤ ENNReal.ofReal B1 := by
    intro x
    have h0 : (∫⁻ y : ℝ, ENNReal.ofReal ((1 + ((-x) + y) ^ 2)⁻¹))
        = ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2)⁻¹) :=
      lintegral_add_left_eq_self (fun u : ℝ => ENNReal.ofReal ((1 + u ^ 2)⁻¹)) (-x)
    have h1 : (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2)⁻¹))
        = ∫⁻ u : ℝ, ‖(((1 + u ^ 2)⁻¹ : ℝ) : ℂ)‖ₑ :=
      lintegral_congr (fun u => (hnormK u).symm)
    have h2 : (∫⁻ y : ℝ, ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹))
        = ∫⁻ y : ℝ, ENNReal.ofReal ((1 + ((-x) + y) ^ 2)⁻¹) := by
      apply lintegral_congr; intro y
      rw [show (1 + (x - y) ^ 2)⁻¹ = (1 + ((-x) + y) ^ 2)⁻¹ by ring_nf]
    calc (∫⁻ y : ℝ, ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹))
        = ∫⁻ y : ℝ, ENNReal.ofReal ((1 + ((-x) + y) ^ 2)⁻¹) := h2
      _ = ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2)⁻¹) := h0
      _ = ∫⁻ u : ℝ, ‖(((1 + u ^ 2)⁻¹ : ℝ) : ℂ)‖ₑ := h1
      _ ≤ ENNReal.ofReal B1 := hB1mass
  have hlatt : ∀ x : ℝ, (∑' m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - x) ^ 2)⁻¹))
      ≤ ENNReal.ofReal B1 := by
    intro x
    refine le_trans (le_of_eq (tsum_congr (fun m => (hnormK ((m : ℝ) - x)).symm))) (hB1latt x)
  have hhold : ∀ m : ℤ,
      (∫⁻ y : ℝ, G y * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) ^ p
        ≤ ENNReal.ofReal B1 ^ (p - 1)
          * ∫⁻ y : ℝ, G y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) := by
    intro m
    have h := Commons.Analysis.Fourier.lintegral_mul_rpow_le_rpow_mul_lintegral hp hGmeas
      (hwm_meas (m : ℝ))
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hwmass (m : ℝ)) hp1) bot_le
  have hlin : ∀ m : ℤ, AEMeasurable
      (fun y : ℝ => G y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) MeasureTheory.volume :=
    fun m => (hGmeas.pow_const p).mul (hwm_meas (m : ℝ))
  calc ∫⁻ m : ℤ, G (m : ℝ) ^ p ∂MeasureTheory.Measure.count
      = ∑' m : ℤ, G (m : ℝ) ^ p := MeasureTheory.lintegral_count _
    _ ≤ ∑' m : ℤ, (ENNReal.ofReal B
          * ∫⁻ y : ℝ, G y * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) ^ p :=
        ENNReal.tsum_le_tsum (fun m => ENNReal.rpow_le_rpow (hpoint (m : ℝ)) hp0.le)
    _ = ∑' m : ℤ, ENNReal.ofReal (B ^ p)
          * (∫⁻ y : ℝ, G y * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) ^ p := by
        apply tsum_congr; intro m
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
          ← ENNReal.ofReal_rpow_of_nonneg hBpos.le hp0.le]
    _ ≤ ∑' m : ℤ, ENNReal.ofReal (B ^ p)
          * (ENNReal.ofReal B1 ^ (p - 1)
            * ∫⁻ y : ℝ, G y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) :=
        ENNReal.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_left (hhold m) bot_le)
    _ = ENNReal.ofReal (B ^ p) * ENNReal.ofReal B1 ^ (p - 1)
          * ∑' m : ℤ, ∫⁻ y : ℝ, G y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        ring
    _ = ENNReal.ofReal (B ^ p) * ENNReal.ofReal B1 ^ (p - 1)
          * ∫⁻ y : ℝ, ∑' m : ℤ, G y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) := by
        rw [← lintegral_tsum hlin]
    _ = ENNReal.ofReal (B ^ p) * ENNReal.ofReal B1 ^ (p - 1)
          * ∫⁻ y : ℝ, G y ^ p * (∑' m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) := by
        congr 1
        apply lintegral_congr; intro y
        rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (B ^ p) * ENNReal.ofReal B1 ^ (p - 1)
          * ∫⁻ y : ℝ, G y ^ p * ENNReal.ofReal B1 := by
        apply mul_le_mul_of_nonneg_left _ bot_le
        apply lintegral_mono; intro y
        exact mul_le_mul_of_nonneg_left (hlatt y) bot_le
    _ = ENNReal.ofReal (B ^ p) * ENNReal.ofReal B1 ^ (p - 1)
          * (ENNReal.ofReal B1 * ∫⁻ y : ℝ, G y ^ p) := by
        rw [MeasureTheory.lintegral_mul_const'' _ (hGmeas.pow_const p),
          mul_comm (∫⁻ y : ℝ, G y ^ p) (ENNReal.ofReal B1)]
    _ = ENNReal.ofReal (B1 ^ (p - 1) * B1 * B ^ p) * ∫⁻ y : ℝ, G y ^ p := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB1pos.le hp1]
        have hprod : ENNReal.ofReal (B1 ^ (p - 1)) * ENNReal.ofReal B1 * ENNReal.ofReal (B ^ p)
            = ENNReal.ofReal (B1 ^ (p - 1) * B1 * B ^ p) := by
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ B1 ^ (p - 1)),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ B1 ^ (p - 1) * B1)]
        calc ENNReal.ofReal (B ^ p) * ENNReal.ofReal (B1 ^ (p - 1))
              * (ENNReal.ofReal B1 * ∫⁻ y : ℝ, G y ^ p)
            = (ENNReal.ofReal (B1 ^ (p - 1)) * ENNReal.ofReal B1 * ENNReal.ofReal (B ^ p))
              * ∫⁻ y : ℝ, G y ^ p := by ring
          _ = ENNReal.ofReal (B1 ^ (p - 1) * B1 * B ^ p) * ∫⁻ y : ℝ, G y ^ p := by rw [hprod]
    _ = ENNReal.ofReal (B1 ^ (p - 1) * B1 * B ^ p)
          * ∫⁻ y : ℝ, (fun x => Work.BourgainPlan.Maximal.varRhoFrom 2 κ
              (fun n => FourierTransformInv.fourierInv (W n) x)) y ^ p := by rw [hG]
end

end Work.BourgainPlan.IonescuWainger
