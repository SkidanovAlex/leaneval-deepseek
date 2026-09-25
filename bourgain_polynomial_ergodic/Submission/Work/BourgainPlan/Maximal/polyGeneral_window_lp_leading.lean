import Mathlib
import Submission.Work.BourgainPlan.Maximal.polyGeneral_window_maximal_lp
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp_leading

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set Finset
open scoped ENNReal

set_option maxHeartbeats 4000000

/-- `q^p * (q⁻¹ * q^(1-p)) = 1` for `q > 0`. -/
private lemma rpow_mul_inv_mul_eq_one_w {q p : ℝ} (hq : 0 < q) :
    q^p * (q⁻¹ * q^(1-p)) = 1 := by
  rw [← mul_assoc, show q^p * q⁻¹ = q^(p-1) by
      rw [Real.rpow_sub hq p 1, Real.rpow_one, div_eq_mul_inv], ← Real.rpow_add hq]
  rw [show p - 1 + (1 - p) = 0 by ring, Real.rpow_zero]

/-- The `q`-power factors cancel. -/
private lemma ofReal_rpow_cancel_w {q p : ℝ} (hq : 0 < q) :
    ENNReal.ofReal (q^p) * (ENNReal.ofReal (q⁻¹) * ENNReal.ofReal (q^(1-p))) = 1 := by
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ q⁻¹),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hq.le p), rpow_mul_inv_mul_eq_one_w hq,
    ENNReal.ofReal_one]

/-- `ofReal q * (ofReal q⁻¹)^p = ofReal (q^(1-p))`. -/
private lemma ofReal_mul_inv_rpow_w {q p : ℝ} (hq : 0 < q) (hp : 0 ≤ p) :
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
private lemma cancel_q_factors_w {q p : ℝ} (hq : 0 < q) (A B : ℝ≥0∞) :
    ENNReal.ofReal (q^p) * (ENNReal.ofReal (q⁻¹) * (A * (ENNReal.ofReal (q^(1-p)) * B)))
      = A * B := by
  rw [show ENNReal.ofReal (q^p) *
        (ENNReal.ofReal (q⁻¹) * (A * (ENNReal.ofReal (q^(1-p)) * B)))
      = A * (ENNReal.ofReal (q^p) * (ENNReal.ofReal (q⁻¹) * ENNReal.ofReal (q^(1-p)))) * B
      from by ring]
  rw [ofReal_rpow_cancel_w hq]
  ring


/-- **The per-slice `ℓ^p` maximal bound** of Bourgain §7.2 for the general polynomial `P`,
with the sign hypothesis on `P` dropped.  The body below never uses the sign hypothesis: it
consumes the dilation-maximal bound as the parameter `hC_p`. -/
theorem genBlock_slice_lp_leading (P : Polynomial ℤ)
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
            ofReal_mul_inv_rpow_w hqR hp0.le]
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
        rw [cancel_q_factors_w hqR (ENNReal.ofReal C_p) A]
    _ = ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ) *
          (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), ‖g j‖ₑ ^ p) := by
        rw [hA, show C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)
              = C₂ * (C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) by ring,
          ENNReal.ofReal_mul hC₂pos.le, ENNReal.ofReal_mul hC_ppos.le]
        ring



/-- **Bourgain §7.2 (Lemma 7.20, (7.21)) for an arbitrary polynomial with positive leading
coefficient.**

This is exactly `Work.BourgainPlan.Maximal.polyGeneral_window_maximal_lp`
(`polyGeneral_window_maximal_lp.lean`, PROVED) with the hypothesis `∀ x ≥ 0, 0 ≤ P.eval x` replaced
by `0 < P.leadingCoeff`.  The conclusion is the model bound

`∫⁻_m (sup_k ‖Σ_{0≤a<q} ∫_β (Σ_j g_j e(2πi j (a/q+β))) · (∫_0^1 e(−β P(2^k t)) dt) · φ(Dβ) ·
 e(2πi m (a/q + β)) dβ‖) ^ p d# ≤ C (∫⁻_y ‖𝓕⁻φ y‖) (∫⁻_m ‖g m‖ ^ p d#)`

with `C` independent of `q`, `D` and `g`, and with the profile at the **relative** offset `β`
(Bourgain's convention; see the docstring of `polyGeneral_window_maximal_lp`).

Why this weakening matters and is what the target needs: `Submission.BourgainPlan.NonnegOnNat P`
does **not** imply `0 ≤ P` on `[0,∞)` (e.g. `P = X² − X` is nonnegative on `ℕ` and negative on
`(0,1)`), and §7.4's (7.64) is needed for exactly that class of `P`.  But `NonnegOnNat P` with
`2 ≤ P.natDegree` does give `0 < P.leadingCoeff`
(`Work.BourgainPlan.Maximal.leadingCoeff_pos_of_nonnegOnNat`, `kernel_l2.lean`), so the statement
here covers every `P` in the target's class, and the degree `≤ 1` case is settled separately by
`deg_le_one`.

Proving it: the proof of `polyGeneral_window_maximal_lp` uses `hP` in exactly two places — the call
`poly_dilation_lp P hP` and the helper `genBlock_slice_lp P hP …` (whose body never uses `hP`, it
only consumes the dilation-maximal bound as a parameter).  So one must restate `genBlock_slice_lp`
with `hP` dropped (body unchanged) and re-instantiate the §7.1 input with the PROVED
`Work.BourgainPlan.Maximal.poly_dilation_lp_leading` (`poly_dilation_lp_leading.lean`), which gives
Bourgain (7.17) under `0 < P.leadingCoeff` alone.  Bourgain's Lemma 7.20 imposes no sign condition.

This is precisely the generalisation requested by the reviewer of `subtwo_of_windowWeakType`, who
observed that the only formalised §7.2 required `P ≥ 0` on `[0,∞)`. -/
theorem polyGeneral_window_lp_leading (P : Polynomial ℤ)
    (hP : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree)
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
  obtain ⟨C_p, hC_ppos, hC_p⟩ := poly_dilation_lp_leading P hP (by omega) (p := p) hp
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
          genBlock_slice_lp_leading P hp hφ hφs hC₀pos hC₀ hC₂pos hC_ppos hC₂ hC_p q hq D hD hDq
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



end Work.BourgainPlan.Maximal
