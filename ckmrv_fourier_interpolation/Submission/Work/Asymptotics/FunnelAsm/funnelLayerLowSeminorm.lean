import Mathlib
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Asymptotics.HalfFunnel.funnelFlat
import Submission.Work.Asymptotics.jInvariant_level_null
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.measurable_Kfun_snd_all
import Submission.Work.Asymptotics.MFix.Cusp0Flat

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology ContDiff

namespace Work.Asymptotics

open Work.Kernels

/-- The imaginary-axis point with coordinate `t > 0`, as an element of `ℍ`, agrees with the
value of Mathlib's partial homeomorphism `ofComplex` there. -/
private lemma imagAxis_eq_ofComplex (t : ℝ) (ht : 0 < t) :
    imagAxis t ht = (UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) : ℍ) := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos]
  · exact UpperHalfPlane.ext rfl
  · simpa [Complex.mul_im] using ht

/-- The `r`-seminorms of the `low` piece of the CKMRV layer are bounded by `c · (scale τ)^N` on
the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}`.  This is `Work.Asymptotics.layerLow_seminorm` with its flatness
hypothesis relaxed to the a.e. (clean) form supplied by `Work.Asymptotics.HalfFunnel.funnelFlat`
and `Work.Asymptotics.jInvariant_level_null`. -/
theorem funnelLayerLowSeminorm (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      Funnel τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
        ≤ c * (scale τ) ^ N := by
  obtain ⟨C₀, c₀, m₀, hC₀pos, hc₀pos, hm₀0, hflat₀⟩ := HalfFunnel.funnelFlat ℓ d hd
  intro k l
  obtain ⟨Γ, hΓ0, hΓ⟩ := sinSq_gauss_seminorm k l
  -- The exponential decay `e^{-c₀/t}` beats the polynomial factor `t^{-j}` on `(0,1]`.
  have key : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (1 + 1 / t) ^ m₀ * Real.exp (-(c₀ / t)) * (t ^ j)⁻¹ ≤ B := by
    intro j
    obtain ⟨K, hKpos, hK⟩ := MFix.exp_neg_div_le_mul_rpow c₀ (m₀ + (j : ℝ)) hc₀pos
    refine ⟨(2 : ℝ) ^ m₀ * K, by positivity, fun t ht0 ht1 => ?_⟩
    have htinv : (1 : ℝ) ≤ 1 / t := (one_le_div ht0).mpr ht1
    have hle2 : 1 + 1 / t ≤ 2 / t := by
      rw [show (2 : ℝ) / t = 2 * (1 / t) by ring]; linarith
    have h1 : (1 + 1 / t) ^ m₀ ≤ (2 / t) ^ m₀ :=
      Real.rpow_le_rpow (by positivity) hle2 hm₀0
    have h2 : (2 / t) ^ m₀ = (2 : ℝ) ^ m₀ * (t ^ m₀)⁻¹ := by
      rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow ht0.le]
    have h3 : Real.exp (-(c₀ / t)) ≤ K * t ^ (m₀ + (j : ℝ)) := hK t ht0 ht1
    have hcancel : t ^ (m₀ + (j : ℝ)) * (t ^ m₀)⁻¹ = t ^ j := by
      rw [Real.rpow_add ht0, Real.rpow_natCast]
      field_simp
    have hcancel2 : t ^ j * (t ^ j)⁻¹ = 1 := by field_simp
    have hpos1 : (0 : ℝ) ≤ (2 : ℝ) ^ m₀ * (t ^ m₀)⁻¹ := by positivity
    have hpos2 : (0 : ℝ) ≤ K * t ^ (m₀ + (j : ℝ)) := by positivity
    have hpos3 : (0 : ℝ) ≤ (t ^ j)⁻¹ := by positivity
    rw [h2] at h1
    calc (1 + 1 / t) ^ m₀ * Real.exp (-(c₀ / t)) * (t ^ j)⁻¹
        ≤ ((2 : ℝ) ^ m₀ * (t ^ m₀)⁻¹) * (K * t ^ (m₀ + (j : ℝ))) * (t ^ j)⁻¹ :=
          mul_le_mul (mul_le_mul h1 h3 (Real.exp_nonneg _) hpos1) le_rfl hpos3
            (mul_nonneg hpos1 hpos2)
      _ = (2 : ℝ) ^ m₀ * K * (t ^ (m₀ + (j : ℝ)) * (t ^ m₀)⁻¹ * (t ^ j)⁻¹) := by ring
      _ = (2 : ℝ) ^ m₀ * K * ((t ^ j) * (t ^ j)⁻¹) := by rw [hcancel]
      _ = (2 : ℝ) ^ m₀ * K := by rw [hcancel2, mul_one]
  obtain ⟨B, hB0, hB⟩ := key (k + l)
  refine ⟨C₀ * (2 : ℝ) ^ m₀ * B * Γ, 0, by positivity, le_rfl, ?_⟩
  intro τ r hτ
  obtain ⟨hτD, hτ2⟩ := hτ
  have hflat_ae : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖Kaxis (Kfun ℓ d) τ u‖ ≤ C₀ * (1 + 1 / u) ^ m₀ * Real.exp (-(c₀ / u)) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp (jInvariant_level_null τ))] with u hu huIoc
    have hu0 : 0 < u := huIoc.1
    refine hflat₀ τ u hu0 hτD hτ2 huIoc.2 ?_
    rw [imagAxis_eq_ofComplex u hu0]
    exact fun hc => hu ⟨hu0, hc⟩
  have hKmeas : Measurable (fun u : ℝ => Kaxis (Kfun ℓ d) τ u) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) τ (measurable_Kfun_snd_all ℓ d hd τ)
  set G : ℝ → ℝ → ℂ := fun u x => Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ))) with hGdef
  set kfun : ℝ → ℝ → ℂ := fun x u => Kaxis (Kfun ℓ d) τ u * (G u x * sinSq x) with hkfundef
  have hlayer : ∀ x : ℝ, layerLow ℓ d τ x = ∫ u in (0 : ℝ)..1, kfun x u := by
    intro x
    rw [layerLow, hkfundef, hGdef]
    have h1 : (fun u : ℝ => Kaxis (Kfun ℓ d) τ u
          * (Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ))) * sinSq x))
        = fun u : ℝ => (Kaxis (Kfun ℓ d) τ u
          * Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ)))) * sinSq x := by
      funext u; ring
    rw [h1, intervalIntegral.integral_mul_const]
    ring
  have hopR : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hsinSmooth : ContDiff ℝ ∞ (fun x : ℝ => sinSq x) := by
    rw [show (fun x : ℝ => sinSq x) = fun x : ℝ => 2
        - Complex.exp (-((-Complex.I * Real.pi) * (x : ℂ) ^ 2))
        - Complex.exp (-((Complex.I * Real.pi) * (x : ℂ) ^ 2)) by
      funext x; exact sinSq_eq_complex x]
    fun_prop
  have hGsmooth : ∀ u : ℝ, ContDiff ℝ ∞ (fun x : ℝ => G u x * sinSq x) := by
    intro u
    have hGu : ContDiff ℝ ∞ (fun x : ℝ => G u x) := by rw [hGdef]; fun_prop
    exact hGu.mul hsinSmooth
  have hmeas_kfun : ∀ x : ℝ, Measurable (fun u : ℝ => kfun x u) := by
    intro x
    have h1 : (fun u : ℝ => kfun x u)
        = fun u : ℝ => (Kaxis (Kfun ℓ d) τ u * G u x) * sinSq x := by
      funext u
      simp only [hkfundef]
      ring
    rw [h1]
    exact (hKmeas.mul (by fun_prop)).mul_const _
  have hkfun_smooth : ∀ u : ℝ, ContDiff ℝ ∞ (fun x : ℝ => kfun x u) := by
    intro u
    have h1 : (fun x : ℝ => kfun x u)
        = fun x : ℝ => Kaxis (Kfun ℓ d) τ u * (G u x * sinSq x) := by
      funext x
      simp only [hkfundef]
    rw [h1]
    exact contDiff_const.mul (hGsmooth u)
  have hdom : ∀ j ≤ l, ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc (0 : ℝ) 1) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ∀ r : ℝ,
        ‖iteratedDeriv j (fun r' : ℝ => kfun r' u) r‖ ≤ bd u := by
    intro j _
    obtain ⟨Γj, hΓj0, hΓj⟩ := sinSq_gauss_seminorm 0 j
    obtain ⟨Bj, hBj0, hBj⟩ := key j
    refine ⟨fun _ => C₀ * Bj * Γj, integrableOn_const (by simp), ?_⟩
    filter_upwards [hflat_ae, self_mem_ae_restrict measurableSet_Ioc] with u hle huIoc
    have hu0 : 0 < u := huIoc.1
    have hu1 : u ≤ 1 := huIoc.2
    intro r
    have hstep1 : iteratedDeriv j (fun r' : ℝ => kfun r' u) r
        = Kaxis (Kfun ℓ d) τ u * iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r := by
      rw [hkfundef]
      exact iteratedDeriv_const_mul _ ((hGsmooth u).contDiffAt.of_le
        (WithTop.coe_le_coe.mpr le_top))
    rw [hstep1, norm_mul]
    have hb2 : ‖iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r‖ ≤ Γj * (u ^ j)⁻¹ := by
      have hsin' : (fun r' : ℝ => G u r' * sinSq r') = fun r' : ℝ => sinSq r' * G u r' := by
        funext x; ring
      rw [hsin']
      simpa using hΓj u hu0 hu1 r
    have hcomb : (1 + 1 / u) ^ m₀ * Real.exp (-(c₀ / u)) * (u ^ j)⁻¹ ≤ Bj := hBj u hu0 hu1
    have hunt : ‖Kaxis (Kfun ℓ d) τ u‖ * ‖iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r‖
        ≤ (C₀ * (1 + 1 / u) ^ m₀ * Real.exp (-(c₀ / u))) * (Γj * (u ^ j)⁻¹) :=
      mul_le_mul hle hb2 (norm_nonneg _) (by positivity)
    calc ‖Kaxis (Kfun ℓ d) τ u‖ * ‖iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r‖
        ≤ (C₀ * (1 + 1 / u) ^ m₀ * Real.exp (-(c₀ / u))) * (Γj * (u ^ j)⁻¹) := hunt
      _ = C₀ * ((1 + 1 / u) ^ m₀ * Real.exp (-(c₀ / u)) * (u ^ j)⁻¹) * Γj := by ring
      _ ≤ C₀ * Bj * Γj :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomb hC₀pos.le) hΓj0
  have hdiff := iteratedDeriv_intervalIntegral_of_meas_bound kfun l hmeas_kfun hkfun_smooth
    hdom l le_rfl
  have hfun_eq : (fun s : ℝ => layerLow ℓ d τ s) = fun s : ℝ => ∫ u in (0 : ℝ)..1, kfun s u :=
    funext hlayer
  rw [hfun_eq, hdiff, Real.rpow_zero, mul_one]
  have hpt : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      |r| ^ k * ‖iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖
        ≤ C₀ * (2 : ℝ) ^ m₀ * B * Γ := by
    filter_upwards [hflat_ae, self_mem_ae_restrict measurableSet_Ioc] with u hle huIoc
    have hu0 : 0 < u := huIoc.1
    have hu1 : u ≤ 1 := huIoc.2
    have hstep1 : iteratedDeriv l (fun r' : ℝ => kfun r' u) r
        = Kaxis (Kfun ℓ d) τ u * iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') r := by
      rw [hkfundef]
      exact iteratedDeriv_const_mul _ ((hGsmooth u).contDiffAt.of_le
        (WithTop.coe_le_coe.mpr le_top))
    rw [hstep1, norm_mul]
    have hb2 : |r| ^ k * ‖iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') r‖
        ≤ Γ * (u ^ (k + l))⁻¹ := by
      have hsin' : (fun r' : ℝ => G u r' * sinSq r') = fun r' : ℝ => sinSq r' * G u r' := by
        funext x; ring
      rw [hsin']
      simpa using hΓ u hu0 hu1 r
    have hcomb : (1 + 1 / u) ^ m₀ * Real.exp (-(c₀ / u)) * (u ^ (k + l))⁻¹ ≤ B :=
      hB u hu0 hu1
    have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m₀ := Real.one_le_rpow (by norm_num) hm₀0
    have hC2 : (0 : ℝ) ≤ C₀ * (2 : ℝ) ^ m₀ * B * Γ := by positivity
    calc |r| ^ k * (‖Kaxis (Kfun ℓ d) τ u‖
            * ‖iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') r‖)
        = ‖Kaxis (Kfun ℓ d) τ u‖
            * (|r| ^ k * ‖iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') r‖) := by ring
      _ ≤ (C₀ * (1 + 1 / u) ^ m₀ * Real.exp (-(c₀ / u))) * (Γ * (u ^ (k + l))⁻¹) :=
          mul_le_mul hle hb2 (by positivity) (by positivity)
      _ = C₀ * ((1 + 1 / u) ^ m₀ * Real.exp (-(c₀ / u)) * (u ^ (k + l))⁻¹) * Γ := by ring
      _ ≤ C₀ * B * Γ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomb hC₀pos.le) hΓ0
      _ ≤ C₀ * (2 : ℝ) ^ m₀ * B * Γ := by
          have h0 : (0 : ℝ) ≤ C₀ * B * Γ := by positivity
          nlinarith [h0, h2m]
  have hIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      ‖((((|r| ^ k : ℝ)) : ℂ)) • iteratedDeriv l (fun r' : ℝ => kfun r' x) r‖
        ≤ C₀ * (2 : ℝ) ^ m₀ * B * Γ := by
    refine ((ae_restrict_iff' measurableSet_Ioc).mp hpt).mono ?_
    intro x hx hxIoc
    rw [hIoc] at hxIoc
    have hnc : ‖(((|r| ^ k : ℝ)) : ℂ)‖ = |r| ^ k := by
      have h : ‖(((|r| ^ k : ℝ)) : ℂ)‖ = |(|r| ^ k : ℝ)| := RCLike.norm_ofReal (K := ℂ) (|r| ^ k)
      rw [h]
      exact abs_of_nonneg (by positivity)
    rw [norm_smul, hnc]
    exact hx hxIoc
  calc |r| ^ k * ‖∫ x in (0 : ℝ)..1, iteratedDeriv l (fun r' : ℝ => kfun r' x) r‖
      = ‖∫ x in (0 : ℝ)..1,
          ((((|r| ^ k : ℝ)) : ℂ)) • iteratedDeriv l (fun r' : ℝ => kfun r' x) r‖ := by
        rw [intervalIntegral.integral_smul, norm_smul]
        have h : ‖(((|r| ^ k : ℝ)) : ℂ)‖ = |r| ^ k := by
          have h2 : ‖(((|r| ^ k : ℝ)) : ℂ)‖ = |(|r| ^ k : ℝ)| :=
            RCLike.norm_ofReal (K := ℂ) (|r| ^ k)
          rw [h2]
          exact abs_of_nonneg (by positivity)
        rw [h]
    _ ≤ C₀ * (2 : ℝ) ^ m₀ * B * Γ * |1 - (0 : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const_ae hae
    _ = C₀ * (2 : ℝ) ^ m₀ * B * Γ := by norm_num

end Work.Asymptotics
