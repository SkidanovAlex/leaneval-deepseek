import Mathlib
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DomainD

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open Work.Kernels
open scoped Topology ContDiff

namespace Work.Asymptotics

/-- **The `r`-seminorm bound for the `low` piece of the CKMRV layer on a compact `K ⊆ 𝒟`.**

Adaptation of `Work.Asymptotics.layerLow_seminorm` (`Submission/Work/Asymptotics/layerLow_seminorm.lean`)
to a compact set: the flatness hypothesis is only assumed for `τ ∈ K`, and the conclusion carries a
single constant (no `(scale τ)^N` factor, since the flatness input already holds with exponent
`N' = 0` in `c * (scale τ)^N' * t^N`, i.e. as plain `c * t^N`).

Strategy: copy the proof of `Work.Asymptotics.layerLow_seminorm`, which uses the generic
`Work.Asymptotics.iteratedDeriv_intervalIntegral_of_meas_bound` and
`Work.Asymptotics.sinSq_gauss_seminorm`; take the flatness exponent `N = k + l + 1` from `hflatK`
(so that `hflat' τ t hτ ht1 ht2 : ‖Kaxis (Kfun ℓ d) τ t‖ ≤ c₀ * t ^ (k+l+1)` after
`Real.rpow_zero, mul_one`), and delete all the `(scale τ) ^ N'` factors from the final estimate;
`measurable_Kaxis_Kfun`/`measurable_Kfun_snd_all` give the measurability of the integrand. -/
theorem layerLow_local_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane}
    (hflatK : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N) :
    ∀ k l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖ ≤ c := by
  intro k l
  obtain ⟨Γ, hΓ0, hΓ⟩ := sinSq_gauss_seminorm k l
  set P : ℝ := ((k + l : ℕ) : ℝ) + 1 with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hPnat : P = ((k + l + 1 : ℕ) : ℝ) := by rw [hPdef]; push_cast; ring
  obtain ⟨c₀, hc₀, hflat'⟩ := hflatK P hP0
  refine ⟨c₀ * Γ, mul_nonneg hc₀.le hΓ0, ?_⟩
  intro τ r hτ
  have hw_meas : Measurable (fun u : ℝ => Kaxis (Kfun ℓ d) τ u) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) τ (measurable_Kfun_snd_all ℓ d hd τ)
  set w : ℝ → ℂ := fun u => Kaxis (Kfun ℓ d) τ u with hwdef
  have hw_meas' : Measurable w := by rw [hwdef]; exact hw_meas
  set G : ℝ → ℝ → ℂ := fun u x => Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ))) with hGdef
  set kfun : ℝ → ℝ → ℂ := fun x u => w u * (G u x * sinSq x) with hkfundef
  have hlayer : ∀ x : ℝ, layerLow ℓ d τ x = ∫ u in (0 : ℝ)..1, kfun x u := by
    intro x
    rw [layerLow, hkfundef, hwdef, hGdef]
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
  have hGsin_smooth : ∀ u : ℝ, ContDiff ℝ ∞ (fun x : ℝ => G u x * sinSq x) := by
    intro u
    have hGu : ContDiff ℝ ∞ (fun x : ℝ => G u x) := by rw [hGdef]; fun_prop
    exact hGu.mul hsinSmooth
  have hmeas_kfun : ∀ x : ℝ, Measurable (fun u : ℝ => kfun x u) := by
    intro x
    have h1 : (fun u : ℝ => kfun x u) = fun u : ℝ => (w u * G u x) * sinSq x := by
      funext u; rw [hkfundef]; ring
    rw [h1]
    exact (hw_meas'.mul (by fun_prop)).mul_const _
  have hkfun_smooth : ∀ u : ℝ, ContDiff ℝ ∞ (fun x : ℝ => kfun x u) := by
    intro u
    have h1 : (fun x : ℝ => kfun x u) = fun x : ℝ => w u * (G u x * sinSq x) := by
      funext x; rw [hkfundef]
    rw [h1]
    exact contDiff_const.mul (hGsin_smooth u)
  -- dominations
  have hdom : ∀ j ≤ l, ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc (0 : ℝ) 1) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ∀ r : ℝ,
        ‖iteratedDeriv j (fun r' : ℝ => kfun r' u) r‖ ≤ bd u := by
    intro j hj
    obtain ⟨Γj, hΓj0, hΓj⟩ := sinSq_gauss_seminorm 0 j
    refine ⟨fun _ => c₀ * Γj, ?_, ?_⟩
    · exact integrableOn_const (by simp)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
      obtain ⟨hu1, hu2⟩ := hu
      intro x
      -- step 1: factor out `w u`
      have hG_at : ContDiffAt ℝ ((j : ℕ∞) : ℕ∞ω) (fun r' : ℝ => G u r' * sinSq r') x :=
        ((hGsin_smooth u).contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
      have hstep1 : iteratedDeriv j (fun r' : ℝ => kfun r' u) x
          = w u * iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') x := by
        have h1 : (fun r' : ℝ => kfun r' u) = fun r' : ℝ => w u * (G u r' * sinSq r') := by
          funext y; rw [hkfundef]
        rw [h1, iteratedDeriv_const_mul (w u) hG_at]
      rw [hstep1, norm_mul]
      -- step 2: bound `‖w u‖`
      have hw' : ‖w u‖ ≤ c₀ * u ^ P := by
        rw [hwdef]; exact hflat' τ u hτ hu1 hu2
      -- step 3: bound the second factor
      have hsin' : (fun r' : ℝ => G u r' * sinSq r') = fun r' : ℝ => sinSq r' * G u r' := by
        funext y; ring
      have hb2 : ‖iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') x‖ ≤ Γj * (u ^ j)⁻¹ := by
        rw [hsin']
        have h := hΓj u hu1 hu2 x
        simpa using h
      -- step 4: `u^P * (u^j)⁻¹ ≤ 1`
      have hup : u ^ P * (u ^ j)⁻¹ ≤ 1 := by
        rw [hPnat, Real.rpow_natCast]
        have h1 : k + l + 1 = (k + l + 1 - j) + j := by omega
        rw [h1, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero j (ne_of_gt hu1)), mul_one]
        exact pow_le_one₀ hu1.le hu2
      -- combine
      calc ‖w u‖ * ‖iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') x‖
          ≤ (c₀ * u ^ P) * (Γj * (u ^ j)⁻¹) :=
            mul_le_mul hw' hb2 (norm_nonneg _) (mul_nonneg hc₀.le (by positivity))
        _ = c₀ * Γj * (u ^ P * (u ^ j)⁻¹) := by ring
        _ ≤ c₀ * Γj := by
            have hC : (0 : ℝ) ≤ c₀ * Γj := mul_nonneg hc₀.le hΓj0
            nlinarith [hup, hC]
  -- apply the parametric-differentiation theorem
  have hfun_eq : (fun s : ℝ => layerLow ℓ d τ s) = fun s : ℝ => ∫ u in (0 : ℝ)..1, kfun s u :=
    funext hlayer
  rw [hfun_eq,
    iteratedDeriv_intervalIntegral_of_meas_bound kfun l hmeas_kfun hkfun_smooth hdom l le_rfl]
  -- pointwise weighted bound for the differentiated integrand
  have hptw : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ℝ,
      |x| ^ k * ‖iteratedDeriv l (fun r' : ℝ => kfun r' u) x‖ ≤ c₀ * (Γ * u) := by
    intro u hu x
    obtain ⟨hu1, hu2⟩ := hu
    have hG_at : ContDiffAt ℝ ((l : ℕ∞) : ℕ∞ω) (fun r' : ℝ => G u r' * sinSq r') x :=
      ((hGsin_smooth u).contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
    have hstep1 : iteratedDeriv l (fun r' : ℝ => kfun r' u) x
        = w u * iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') x := by
      have h1 : (fun r' : ℝ => kfun r' u) = fun r' : ℝ => w u * (G u r' * sinSq r') := by
        funext y; rw [hkfundef]
      rw [h1, iteratedDeriv_const_mul (w u) hG_at]
    rw [hstep1, norm_mul]
    have hw' : ‖w u‖ ≤ c₀ * u ^ P := by
      rw [hwdef]; exact hflat' τ u hτ hu1 hu2
    have hsin' : (fun r' : ℝ => G u r' * sinSq r') = fun r' : ℝ => sinSq r' * G u r' := by
      funext y; ring
    have hb2 : |x| ^ k * ‖iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') x‖
        ≤ Γ * (u ^ (k + l))⁻¹ := by
      rw [hsin']
      have h := hΓ u hu1 hu2 x
      simpa using h
    have hup : u ^ P * (u ^ (k + l))⁻¹ ≤ u := by
      rw [hPnat, Real.rpow_natCast, pow_succ, mul_comm (u ^ (k + l)) u, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero (k + l) (ne_of_gt hu1)), mul_one]
    calc |x| ^ k * (‖w u‖ * ‖iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') x‖)
        = ‖w u‖ * (|x| ^ k * ‖iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') x‖) := by
          ring
      _ ≤ (c₀ * u ^ P) * (Γ * (u ^ (k + l))⁻¹) :=
          mul_le_mul hw' hb2 (mul_nonneg (by positivity) (norm_nonneg _))
            (mul_nonneg hc₀.le (by positivity))
      _ = c₀ * Γ * (u ^ P * (u ^ (k + l))⁻¹) := by ring
      _ ≤ c₀ * Γ * u :=
          mul_le_mul_of_nonneg_left hup (mul_nonneg hc₀.le hΓ0)
      _ = c₀ * (Γ * u) := by ring
  -- bound the integral
  have hIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hg_bound : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖((((|r| ^ k : ℝ)) : ℂ)) • iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖
        ≤ c₀ * Γ := by
    intro u hu
    have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := hIoc ▸ hu
    have hnc : ‖((((|r| ^ k : ℝ)) : ℂ))‖ = |r| ^ k := by
      have h : ‖(((|r| ^ k : ℝ)) : ℂ)‖ = |(|r| ^ k : ℝ)| := RCLike.norm_ofReal (K := ℂ) (|r| ^ k)
      rw [h, abs_of_nonneg (by positivity)]
    rw [norm_smul, hnc]
    have h := hptw u hu' r
    have hu3 : Γ * u ≤ Γ := by
      nlinarith [hΓ0, hu'.1.le, hu'.2]
    calc |r| ^ k * ‖iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖
        ≤ c₀ * (Γ * u) := h
      _ ≤ c₀ * Γ := mul_le_mul_of_nonneg_left hu3 hc₀.le
  calc |r| ^ k * ‖∫ u in (0 : ℝ)..1, iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖
      = ‖∫ u in (0 : ℝ)..1, ((((|r| ^ k : ℝ)) : ℂ)) • iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖ := by
        have hnc : ‖((((|r| ^ k : ℝ)) : ℂ))‖ = |r| ^ k := by
          have h : ‖(((|r| ^ k : ℝ)) : ℂ)‖ = |(|r| ^ k : ℝ)| := RCLike.norm_ofReal (K := ℂ) (|r| ^ k)
          rw [h, abs_of_nonneg (by positivity)]
        rw [intervalIntegral.integral_smul, norm_smul, hnc]
    _ ≤ c₀ * Γ * |1 - (0 : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hg_bound
    _ = c₀ * Γ := by norm_num

end Work.Asymptotics
