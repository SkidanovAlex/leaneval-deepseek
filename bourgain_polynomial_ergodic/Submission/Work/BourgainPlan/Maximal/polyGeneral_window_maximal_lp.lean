import Mathlib
import Submission.Work.BourgainPlan.Maximal.genWindow_defs
import Submission.Work.BourgainPlan.Maximal.genWindow_analytic
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp
import Submission.Work.BourgainPlan.Maximal.genWindow_eq_genBlock
import Submission.Work.BourgainPlan.Maximal.fourier_genBlock
import Submission.Work.BourgainPlan.Maximal.continuous_genBlock
import Submission.Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow

set_option maxHeartbeats 4000000

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- `q^p * (q⁻¹ * q^(1-p)) = 1` for `q > 0`. -/
private lemma rpow_mul_inv_mul_eq_one {q p : ℝ} (hq : 0 < q) :
    q^p * (q⁻¹ * q^(1-p)) = 1 := by
  rw [← mul_assoc, show q^p * q⁻¹ = q^(p-1) by
      rw [Real.rpow_sub hq p 1, Real.rpow_one, div_eq_mul_inv], ← Real.rpow_add hq]
  rw [show p - 1 + (1 - p) = 0 by ring, Real.rpow_zero]

/-- The `q`-power factors cancel. -/
private lemma ofReal_rpow_cancel {q p : ℝ} (hq : 0 < q) :
    ENNReal.ofReal (q^p) * (ENNReal.ofReal (q⁻¹) * ENNReal.ofReal (q^(1-p))) = 1 := by
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ q⁻¹),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hq.le p), rpow_mul_inv_mul_eq_one hq,
    ENNReal.ofReal_one]

/-- `ofReal q * (ofReal q⁻¹)^p = ofReal (q^(1-p))`. -/
private lemma ofReal_mul_inv_rpow {q p : ℝ} (hq : 0 < q) (hp : 0 ≤ p) :
    ENNReal.ofReal q * (ENNReal.ofReal (q⁻¹))^p = ENNReal.ofReal (q^(1-p)) := by
  calc ENNReal.ofReal q * (ENNReal.ofReal (q⁻¹))^p
      = ENNReal.ofReal q * ENNReal.ofReal ((q⁻¹)^p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ q⁻¹) hp]
    _ = ENNReal.ofReal (q * ((q⁻¹)^p)) := by
        rw [ENNReal.ofReal_mul hq.le]
    _ = ENNReal.ofReal (q^(1-p)) := by
        congr 1
        rw [Real.inv_rpow hq.le, Real.rpow_sub hq 1 p, Real.rpow_one, div_eq_mul_inv]

/-- The `q`-factors cancelling, in the bracketing produced by the main chain. -/
private lemma cancel_q_factors {q p : ℝ} (hq : 0 < q) (A B : ℝ≥0∞) :
    ENNReal.ofReal (q^p) * (ENNReal.ofReal (q⁻¹) * (A * (ENNReal.ofReal (q^(1-p)) * B)))
      = A * B := by
  rw [show ENNReal.ofReal (q^p) *
        (ENNReal.ofReal (q⁻¹) * (A * (ENNReal.ofReal (q^(1-p)) * B)))
      = A * (ENNReal.ofReal (q^p) * (ENNReal.ofReal (q⁻¹) * ENNReal.ofReal (q^(1-p)))) * B
      from by ring]
  rw [ofReal_rpow_cancel hq]
  ring

/-- The pointwise dilation bound: the `k`-th block is dominated by the `q`-multiple dilation
maximal function of the slice amplitude. -/
lemma genBlock_sup_le (P : Polynomial ℤ) {q : ℕ} (hq : 0 < q) {D : ℝ} (hD : 0 < D)
    (h1D : 1 ≤ D) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) (x : ℝ) :
    (⨆ k : ℕ, ‖genBlock P k q D φ g s z x‖ₑ)
      ≤ ENNReal.ofReal q * genDilMax P q D φ g s z ((q:ℝ)*x) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  set f : ℝ → ℂ := FourierTransformInv.fourierInv (genBetaAmp q D φ g s z) with hf
  have hfcont : Continuous f := by
    rw [hf]
    exact Commons.Analysis.ExponentialSums.continuous_fourierInv
      (integrable_genBetaAmp q hD hφ.continuous hφs g s z)
  have hpt : ∀ k : ℕ, ‖genBlock P k q D φ g s z x‖ₑ
      ≤ ENNReal.ofReal q * genDilMax P q D φ g s z ((q:ℝ)*x) := by
    intro k
    set gfun : ℝ → ℝ := fun t => ‖f ((q:ℝ)*x - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * t))‖ with hgfun
    have hgcont : Continuous gfun := by
      rw [hgfun]
      exact (hfcont.comp (by fun_prop : Continuous fun t : ℝ =>
        (q:ℝ)*x - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * t))).norm
    have hgint : IntegrableOn gfun (Set.Ioc (0:ℝ) 1) :=
      (hgcont.continuousOn.integrableOn_compact (μ := volume) isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
    have hstep : ‖genBlock P k q D φ g s z x‖ ≤ (q:ℝ) * ∫ t in (0:ℝ)..1, gfun t := by
      rw [genBlock_dilation P k q hq hD h1D hφ hφs g s z x, norm_mul, norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := (0:ℝ)) (b := 1)
        (f := fun t : ℝ => FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)
          ((q:ℝ)*x - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * t))) (by norm_num)
      simpa only [hgfun] using this
    have hconv : ENNReal.ofReal (∫ t in (0:ℝ)..1, gfun t)
        = ∫⁻ t in Set.Ioc (0:ℝ) 1, ‖f ((q:ℝ)*x - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * t))‖ₑ := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      rw [ofReal_integral_eq_lintegral_ofReal hgint
        (Filter.Eventually.of_forall (fun t => norm_nonneg _))]
      apply lintegral_congr
      intro t
      rw [hgfun]
      beta_reduce
      rw [← ofReal_norm]
    calc ‖genBlock P k q D φ g s z x‖ₑ
        ≤ ENNReal.ofReal ((q:ℝ) * ∫ t in (0:ℝ)..1, gfun t) := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hstep
      _ = ENNReal.ofReal (q:ℝ) * ∫⁻ t in Set.Ioc (0:ℝ) 1,
            ‖f ((q:ℝ)*x - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * t))‖ₑ := by
          rw [ENNReal.ofReal_mul (by positivity), hconv]
      _ ≤ ENNReal.ofReal (q:ℝ) * genDilMax P q D φ g s z ((q:ℝ)*x) := by
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          simp only [genDilMax]
          exact le_iSup_of_le (2^k) le_rfl
  exact iSup_le hpt

/-- **The per-slice `ℓ^p` maximal bound** of Bourgain §7.2 for the general polynomial `P`. -/
theorem genBlock_slice_lp (P : Polynomial ℤ)
    (hP : ∀ x : ℝ, 0 ≤ x → 0 ≤ (P.map (Int.castRingHom ℝ)).eval x)
    {p : ℝ} (hp : 1 < p) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    {C₀ : ℝ} (hC₀pos : 0 < C₀)
    (hC₀ : ∀ u : ℝ, ‖FourierTransformInv.fourierInv φ u‖ ≤ C₀ * (1 + u^2)⁻¹)
    {C₂ C_p : ℝ} (hC₂pos : 0 < C₂) (hC_ppos : 0 < C_p)
    (hC₂ : ∀ (h : ℕ → ℝ → ℂ), (∀ j : ℕ, Integrable (h j)) → (∀ j : ℕ, Continuous (h j)) →
      (∀ (j : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) →
        FourierTransform.fourier (h j) ξ = 0) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ‖h j (m : ℝ)‖ₑ) ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C₂ * ∫⁻ x : ℝ, (⨆ j : ℕ, ‖h j x‖ₑ) ^ p ∂volume)
    (hC_p : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → (∀ x : ℝ, ψ x ≠ ⊤) →
      ∫⁻ x : ℝ, ψ x ^ p < ⊤ →
      ∫⁻ x : ℝ, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ (x - (toRealPoly P).eval ((N:ℝ)*s))) ^ p ∂volume
        ≤ ENNReal.ofReal C_p * ∫⁻ x : ℝ, ψ x ^ p ∂volume)
    (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    ∫⁻ y : ℤ, (⨆ k : ℕ, ‖genBlock P k q D φ g s z (y:ℝ)‖ₑ) ^ p
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
        (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ ∂volume) *
        (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), ‖g j‖ₑ ^ p) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have h1D : (1:ℝ) ≤ D := le_trans (by exact_mod_cast hq) hDq
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  set f : ℝ → ℂ := FourierTransformInv.fourierInv (genBetaAmp q D φ g s z) with hf
  have hfcont : Continuous f := by
    rw [hf]
    exact Commons.Analysis.ExponentialSums.continuous_fourierInv
      (integrable_genBetaAmp q hD hφ.continuous hφs g s z)
  set ψ : ℝ → ℝ≥0∞ := fun u => ‖f u‖ₑ with hψ
  have hψmeas : Measurable ψ := (hfcont.enorm).measurable
  have hψne : ∀ u : ℝ, ψ u ≠ ⊤ := fun u => by rw [hψ]; exact ENNReal.coe_ne_top
  have hψint : ∫⁻ u : ℝ, ψ u ^ p < ⊤ := by
    rw [hψ, hf]
    exact lintegral_enorm_fourierInv_genBetaAmp_rpow_lt_top q hD h1D hφ hφs g s z hp
  obtain ⟨Cψ, hCψpos, hCψ⟩ := fourierInv_genBetaAmp_le q hD h1D hφ hφs g s z
  have hψle : ∀ u : ℝ, ψ u ≤ ENNReal.ofReal Cψ := by
    intro u
    have hy1 : D / (D^2 + u^2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    calc ψ u ≤ ENNReal.ofReal (Cψ * (D / (D^2 + u^2))) := by
          simp only [hψ, hf]
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hCψ u)
      _ ≤ ENNReal.ofReal Cψ := by
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [hy1, hCψpos.le]
  have hFmeas : Measurable (genDilMax P q D φ g s z) := by
    unfold genDilMax
    refine Measurable.iSup (fun N : ℕ => ?_)
    have hfun : (fun u : ℝ => ∫⁻ t in Set.Ioc (0:ℝ) 1,
        ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)
          (u - (toRealPoly P).eval ((N:ℝ)*t))‖ₑ)
        = fun u : ℝ => ∫⁻ t in Set.Ioc (0:ℝ) 1,
          ψ (u - (toRealPoly P).eval ((N:ℝ)*t)) := by
      funext u
      rw [hψ, hf]
    rw [hfun]
    exact Measurable.lintegral_prod_right (ν := volume.restrict (Set.Ioc (0:ℝ) 1))
      (f := fun u t => ψ (u - (toRealPoly P).eval ((N:ℝ)*t)))
      (hψmeas.comp (by fun_prop))
  have hFne : ∀ u : ℝ, genDilMax P q D φ g s z u ≠ ⊤ := by
    intro u
    have hb : genDilMax P q D φ g s z u ≤ ENNReal.ofReal Cψ := by
      unfold genDilMax
      refine iSup_le (fun N : ℕ => ?_)
      have hfun : ∀ t : ℝ, ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)
          (u - (toRealPoly P).eval ((N:ℝ)*t))‖ₑ = ψ (u - (toRealPoly P).eval ((N:ℝ)*t)) := by
        intro t
        rw [hψ, hf]
      calc ∫⁻ t in Set.Ioc (0:ℝ) 1, ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)
              (u - (toRealPoly P).eval ((N:ℝ)*t))‖ₑ
          = ∫⁻ t in Set.Ioc (0:ℝ) 1, ψ (u - (toRealPoly P).eval ((N:ℝ)*t)) :=
            lintegral_congr hfun
        _ ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal Cψ := lintegral_mono (fun t => hψle _)
        _ = ENNReal.ofReal Cψ * (volume (Set.Ioc (0:ℝ) 1)) := setLIntegral_const _ _
        _ = ENNReal.ofReal Cψ := by
            rw [Real.volume_Ioc]
            simp
    exact ne_top_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  have hband : ∀ (k : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) →
      FourierTransform.fourier (genBlock P k q D φ g s z) ξ = 0 := by
    intro k ξ hξ
    rw [fourier_genBlock P k q hq hD h1D hφ hφs g s z ξ, genAmpF]
    refine mul_eq_zero.mpr (Or.inl ?_)
    refine genBetaAmp_eq_zero_of_notMem q hD hφs g s z ?_
    intro hmem
    rw [Set.mem_Icc] at hmem
    refine hξ ?_
    rw [Set.mem_Icc]
    have h1 : |ξ| ≤ (q:ℝ) * (1/(2*D)) := by
      have h2 : |ξ / (q:ℝ)| ≤ 1/(2*D) := abs_le.mpr hmem
      rw [abs_div, abs_of_pos hqR, div_le_iff₀ hqR] at h2
      linarith [h2]
    have h3 : (q:ℝ) * (1/(2*D)) ≤ 1/2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 2*D)]
      linarith
    have h4 : |ξ| ≤ 1/2 := le_trans h1 h3
    constructor
    · have := neg_abs_le ξ; linarith [h4]
    · have := le_abs_self ξ; linarith [h4]
  have hlat := hC₂ (fun k => genBlock P k q D φ g s z)
    (fun k => integrable_genBlock P k q hq hD h1D hφ hφs g s z)
    (fun k => continuous_genBlock P k q hq hD h1D hφ hφs g s z) hband
  have hcontmax : ∫⁻ x : ℝ, (⨆ k : ℕ, ‖genBlock P k q D φ g s z x‖ₑ)^p
      ≤ ENNReal.ofReal ((q:ℝ)^p) * (ENNReal.ofReal ((q:ℝ)⁻¹) *
          (ENNReal.ofReal C_p * ∫⁻ u : ℝ, ψ u ^ p)) := by
    calc ∫⁻ x : ℝ, (⨆ k : ℕ, ‖genBlock P k q D φ g s z x‖ₑ)^p
        ≤ ∫⁻ x : ℝ, (ENNReal.ofReal (q:ℝ) *
            genDilMax P q D φ g s z ((q:ℝ)*x))^p :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow
            (genBlock_sup_le P hq hD h1D hφ hφs g s z x) hp0.le)
      _ = ∫⁻ x : ℝ, ENNReal.ofReal ((q:ℝ)^p) *
            (genDilMax P q D φ g s z ((q:ℝ)*x))^p := by
          apply lintegral_congr
          intro x
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le]
      _ = ENNReal.ofReal ((q:ℝ)^p) *
            ∫⁻ x : ℝ, (genDilMax P q D φ g s z ((q:ℝ)*x))^p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((q:ℝ)^p) * (ENNReal.ofReal ((q:ℝ)⁻¹) *
            ∫⁻ u : ℝ, (genDilMax P q D φ g s z u)^p) := by
          congr 1
          rw [Commons.Analysis.ExponentialSums.lintegral_comp_mul_left_real hqR
            (F := fun u : ℝ => (genDilMax P q D φ g s z u)^p) (hFmeas.pow_const p)]
      _ ≤ ENNReal.ofReal ((q:ℝ)^p) * (ENNReal.ofReal ((q:ℝ)⁻¹) *
            (ENNReal.ofReal C_p * ∫⁻ u : ℝ, ψ u ^ p)) := by
          gcongr
          simpa only [genDilMax, hψ] using hC_p ψ hψmeas hψne hψint
  have hφint : Integrable φ :=
    Continuous.integrable_of_hasCompactSupport hφ.continuous
      (Commons.Analysis.ExponentialSums.hasCompactSupport_of_Icc hφs)
  have hφinvcont : Continuous (FourierTransformInv.fourierInv φ) :=
    Commons.Analysis.ExponentialSums.continuous_fourierInv hφint
  have hresid := Commons.Analysis.ExponentialSums.residue_slice_bound (p := p) hp hq
      (a := (q:ℝ)/D) (C := C₀) (by positivity)
      (by rw [div_le_one hD]; exact hDq) hC₀pos hφinvcont.measurable hC₀ g s z
  set A : ℝ≥0∞ := (ENNReal.ofReal ((2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
      (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ)) *
      (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), ‖g j‖ₑ ^ p) with hA
  have hident : ∀ x : ℝ, ψ ((q:ℝ)*x) = ENNReal.ofReal ((q:ℝ)⁻¹) *
      ‖∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)),
          g j * (((q:ℝ)/D) * FourierTransformInv.fourierInv φ
            (((q:ℝ)/D) * (x + ((j+z:ℤ):ℝ)/(q:ℝ))))‖ₑ := by
    intro x
    simp only [hψ, hf]
    rw [fourierInv_genBetaAmp_qx q hq hD hφ.continuous hφs g s z x, enorm_mul]
    congr 1
    rw [← ofReal_norm]
    congr 1
    rw [norm_inv, norm_natCast]
  have hres : ∫⁻ u : ℝ, ψ u ^ p ≤ ENNReal.ofReal ((q:ℝ)^(1-p)) * A := by
    have hscale : ∫⁻ u : ℝ, ψ u ^ p
        = ENNReal.ofReal (q:ℝ) * ∫⁻ x : ℝ, ψ ((q:ℝ)*x)^p := by
      have h := Commons.Analysis.ExponentialSums.lintegral_comp_mul_left_real hqR
        (F := fun u : ℝ => ψ u ^ p) (hψmeas.pow_const p)
      rw [h, ← mul_assoc, ENNReal.ofReal_inv_of_pos hqR, ENNReal.mul_inv_cancel
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr hqR)
        ENNReal.ofReal_ne_top, one_mul]
    rw [hscale]
    have hpt : ∀ x : ℝ, ψ ((q:ℝ)*x)^p
        = (ENNReal.ofReal ((q:ℝ)⁻¹))^p * ‖∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)),
            g j * (((q:ℝ)/D) * FourierTransformInv.fourierInv φ
              (((q:ℝ)/D) * (x + ((j+z:ℤ):ℝ)/(q:ℝ))))‖ₑ^p := by
      intro x
      rw [hident x, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    calc ENNReal.ofReal (q:ℝ) * ∫⁻ x : ℝ, ψ ((q:ℝ)*x)^p
        = ENNReal.ofReal (q:ℝ) * ∫⁻ x : ℝ,
            (ENNReal.ofReal ((q:ℝ)⁻¹))^p * ‖∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)),
              g j * (((q:ℝ)/D) * FourierTransformInv.fourierInv φ
                (((q:ℝ)/D) * (x + ((j+z:ℤ):ℝ)/(q:ℝ))))‖ₑ^p := by
          congr 1
          apply lintegral_congr
          intro x
          rw [hpt x]
      _ = ENNReal.ofReal (q:ℝ) * ((ENNReal.ofReal ((q:ℝ)⁻¹))^p *
            ∫⁻ x : ℝ, ‖∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)),
              g j * (((q:ℝ)/D) * FourierTransformInv.fourierInv φ
                (((q:ℝ)/D) * (x + ((j+z:ℤ):ℝ)/(q:ℝ))))‖ₑ^p) := by
          rw [← lintegral_const_mul' (ENNReal.ofReal ((q:ℝ)⁻¹) ^ p) _
            (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
      _ ≤ ENNReal.ofReal (q:ℝ) * ((ENNReal.ofReal ((q:ℝ)⁻¹))^p * A) := by
          gcongr
          refine le_trans (le_of_eq ?_) (by simpa only [hA] using hresid)
          apply lintegral_congr
          intro x
          rw [show (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), g j * (((q:ℝ)/D) *
                FourierTransformInv.fourierInv φ (((q:ℝ)/D) * (x + ((j+z:ℤ):ℝ)/(q:ℝ)))))
              = ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), g j * (((((q:ℝ)/D : ℝ)) : ℂ) *
                FourierTransformInv.fourierInv φ (((q:ℝ)/D) *
                  (x + ((j+z:ℤ):ℝ)/(q:ℝ)))) from by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            push_cast
            ring]
      _ = ENNReal.ofReal ((q:ℝ)^(1-p)) * A := by
          rw [show ENNReal.ofReal (q:ℝ) * ((ENNReal.ofReal ((q:ℝ)⁻¹))^p * A)
              = (ENNReal.ofReal (q:ℝ) * (ENNReal.ofReal ((q:ℝ)⁻¹))^p) * A from by ring,
            ofReal_mul_inv_rpow hqR hp0.le]
  calc ∫⁻ y : ℤ, (⨆ k : ℕ, ‖genBlock P k q D φ g s z (y:ℝ)‖ₑ) ^ p
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C₂ * ∫⁻ x : ℝ, (⨆ k : ℕ, ‖genBlock P k q D φ g s z x‖ₑ)^p := hlat
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal ((q:ℝ)^p) *
          (ENNReal.ofReal ((q:ℝ)⁻¹) * (ENNReal.ofReal C_p * ∫⁻ u : ℝ, ψ u ^ p))) :=
        mul_le_mul_of_nonneg_left hcontmax bot_le
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal ((q:ℝ)^p) *
          (ENNReal.ofReal ((q:ℝ)⁻¹) * (ENNReal.ofReal C_p *
            (ENNReal.ofReal ((q:ℝ)^(1-p)) * A)))) := by
        gcongr
    _ = ENNReal.ofReal C₂ * (ENNReal.ofReal C_p * A) := by
        rw [cancel_q_factors hqR (ENNReal.ofReal C_p) A]
    _ = ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ) *
          (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), ‖g j‖ₑ ^ p) := by
        rw [hA, show C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)
              = C₂ * (C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) by ring,
          ENNReal.ofReal_mul hC₂pos.le, ENNReal.ofReal_mul hC_ppos.le]
        ring

/-- **Bourgain §7.2, Lemma 7.20 (7.21) for an arbitrary integer polynomial `P`.**

Let `P : ℤ[X]` be nonnegative on `[0,∞)` with `2 ≤ P.natDegree` (then `0 < P.leadingCoeff`), let
`φ` be a smooth bump supported in `[-1/2, 1/2]`, `p > 1`, `q > 0`, `D ≥ q`, and `g : ℤ → ℂ`
finitely supported.  Then the major-arc model in Bourgain's (7.21) form, i.e. the family at
`N = 2^k`

`Σ_{0 ≤ a < q} ∫_β (Σ_j g_j e(2πi j (a/q + β))) · (∫_0^1 e(−β P(N t)) dt) · φ(D β) ·
 e(2πi m (a/q + β)) dβ`

satisfies `∫⁻_m (sup_k ‖·‖) ^ p d# ≤ C · (∫⁻_y ‖𝓕⁻φ y‖) · ∫⁻_m ‖g m‖ ^ p d#`, with `C` independent
of `q`, `D` and `g`.

Conventions (verified against `l2_defs` and against the PROVED pure-power case
`Work.BourgainPlan.Maximal.purePower_window_maximal_lp` in this directory, which is the instance
`P = X^d`, `d ≥ 2`): the **profile** `∫_0^1 e(−β P(N t)) dt = conj (polyProfile P N β)` is
evaluated at the **relative** variable `β` (the offset from the arc centre), and `φ` is fixed
*before* `C` (a `φ`-uniform `C` is false by the scaling `φ ↦ λφ`).

Ingredients already available:
* `Work.BourgainPlan.Maximal.poly_dilation_lp` (`poly_dilation_lp.lean`) — Bourgain (7.16)/(7.17) as
  an `L^p` inequality for the *general* `P`: `∫⁻_x (sup_N ∫_{(0,1]} ψ(x − P(Ns))ds)^p ≤ C∫⁻ψ^p`,
  with no degree restriction and with the non-monotone critical-value pieces handled.  ⚠ this is the
  only available form: the pointwise (in `x`, with `hlMax` on the right) form is FALSE for
  `P(0) > 0`, so the proof must use the `L^p` statement in the `y`-variable exactly as Bourgain does
  in (7.24)–(7.26), rather than the `hlMax`-domination route that works for the pure powers;
* `Work.BourgainPlan.Maximal.polyProfile_fourier_dilation` — `𝓕⁻(G · conj (polyProfile P N))(x) =
  ∫_{(0,1]} 𝓕⁻G (x − P(N s)) ds`;
* `Work.BourgainPlan.Maximal.purePower_window_maximal_lp` (PROVED) — the case `P = X^d`; its file
  chain (`ppAnalytic`, `ppSlicedMaximal`, `ppWindowBlock_eq_ppBlock`, `ppAssembly`) is a template.
  The difference for general `P` is that the profile is not the dilation of a *fixed* function, so
  the sliced route has to be replaced by Bourgain's (7.22)–(7.28) with the a-priori-constant
  bootstrap (7.24)–(7.28);
* the residue identity and the sub-lattice sampling of
  `Submission/Work/Analysis/ExponentialSums/model721_bundle.lean` and
  `Submission/Work/Analysis/Fourier/`.

Bourgain uses this estimate in §7.4 as (7.64) (the model increments); together with the restricted
maximal inequality (7.33) and the §6 `L²` estimates it is one of the three analytic inputs of the
`1 < p < 2` half of his theorem. -/
theorem polyGeneral_window_maximal_lp (P : Polynomial ℤ)
    (hP : ∀ x : ℝ, 0 ≤ x → 0 ≤ (P.map (Int.castRingHom ℝ)).eval x) (hd : 2 ≤ P.natDegree)
    {p : ℝ} (hp : 1 < p) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
        (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun m : ℤ => ENNReal.rpow (iSup fun k : ℕ =>
            ‖∑ a ∈ Finset.range q,
              ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
                (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
                    ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
                * (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I *
                    (((β : ℝ) * (P.map (Int.castRingHom ℝ)).eval (((2 : ℝ) ^ k) * t) : ℝ) : ℂ))))
                * φ (D * β)
                * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
                    ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ)))‖ₑ) p)
        ≤ ENNReal.ofReal C * (MeasureTheory.lintegral MeasureTheory.volume
            (fun y : ℝ => ‖FourierTransform.fourierInv φ y‖ₑ))
          * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun m : ℤ => ENNReal.rpow (‖g m‖ₑ) p) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.ExponentialSums.exists_decay_fourierInv
      (Commons.Analysis.ExponentialSums.hasCompactSupport_of_Icc hφs) hφ
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow (p := p) hp
  obtain ⟨C_p, hC_ppos, hC_p⟩ := poly_dilation_lp P hP (p := p) hp
  refine ⟨C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1), by positivity, ?_⟩
  intro q hq D hD hDq g s hs
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  haveI : NeZero q := ⟨hq.ne'⟩
  change MeasureTheory.lintegral MeasureTheory.Measure.count
      (fun m : ℤ => ENNReal.rpow (iSup fun k : ℕ => ‖genWindow P k q D φ g s m‖ₑ) p)
      ≤ _
  have hLHS : MeasureTheory.lintegral MeasureTheory.Measure.count
      (fun m : ℤ => ENNReal.rpow (iSup fun k : ℕ => ‖genWindow P k q D φ g s m‖ₑ) p)
      = ∑ z : Fin q, ∑' y : ℤ,
          (⨆ k : ℕ, ‖genBlock P k q D φ g s ((z:ℕ):ℤ) (y:ℝ)‖ₑ)^p := by
    rw [MeasureTheory.lintegral_count,
      Commons.Analysis.ExponentialSums.Commons.Analysis.ExponentialSums.tsum_int_eq_sum_fin q
        (fun m : ℤ => ENNReal.rpow (iSup fun k : ℕ => ‖genWindow P k q D φ g s m‖ₑ) p)]
    simp only [ENNReal.rpow_eq_pow]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    refine tsum_congr (fun y => ?_)
    congr 1
    apply iSup_congr
    intro k
    rw [genWindow_eq_genBlock P k q hq D hD hφ.continuous hφs g s ((z:ℕ):ℤ) y]
  rw [hLHS]
  calc ∑ z : Fin q, ∑' y : ℤ,
        (⨆ k : ℕ, ‖genBlock P k q D φ g s ((z:ℕ):ℤ) (y:ℝ)‖ₑ)^p
      = ∑ z : Fin q, ∫⁻ y : ℤ,
          (⨆ k : ℕ, ‖genBlock P k q D φ g s ((z:ℕ):ℤ) (y:ℝ)‖ₑ)^p
            ∂MeasureTheory.Measure.count := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [MeasureTheory.lintegral_count]
    _ ≤ ∑ z : Fin q, ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ ∂volume) *
          (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (((z:ℕ):ℤ)+j)), ‖g j‖ₑ ^ p) :=
        Finset.sum_le_sum (fun z _ =>
          genBlock_slice_lp P hP hp hφ hφs hC₀pos hC₀ hC₂pos hC_ppos hC₂ hC_p q hq D hD hDq
            g s ((z:ℕ):ℤ))
    _ = ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ ∂volume) *
          (∑ z : Fin q, ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (((z:ℕ):ℤ)+j)), ‖g j‖ₑ ^ p) := by
        rw [← Finset.mul_sum]
    _ = ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ ∂volume) *
          (∑ j ∈ s, ‖g j‖ₑ ^ p) := by
        congr 1
        rw [← Commons.Analysis.ExponentialSums.Commons.Analysis.ExponentialSums.sum_Icc_eq_sum_fin q
          (fun z : ℤ => ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), ‖g j‖ₑ ^ p)]
        exact Commons.Analysis.ExponentialSums.sum_filter_residue_le hq g s
    _ = ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ ∂volume) *
          ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂MeasureTheory.Measure.count := by
        congr 1
        rw [MeasureTheory.lintegral_count,
          tsum_eq_sum (s := s) (fun m hm => by rw [hs m hm]; simp [hp0])]

end
end Work.BourgainPlan.Maximal
