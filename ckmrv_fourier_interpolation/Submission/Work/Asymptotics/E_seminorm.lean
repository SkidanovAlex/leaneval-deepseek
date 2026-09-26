import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Asymptotics.exists_bound_iteratedDeriv_tailIntegral_two_regime
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound
import Submission.Work.Asymptotics.ae_bound_of_two_regime
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.paperLayer_seminorm
import Submission.Work.Asymptotics.psi1_contDiff_omega
import Submission.Work.Asymptotics.kernelTransform_seminorm_of_layer
import Submission.Work.Asymptotics.iteratedDeriv_comp_quad_bounded
import Submission.Work.Asymptotics.abs_pow_mul_exp_le
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.E_F2_agreement
import Submission.Work.Asymptotics.E_TailClosed_seminorm
import Submission.Work.Asymptotics.E_TailClosed

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open Work.Kernels
open scoped Topology ContDiff

namespace Work.Asymptotics

theorem E_layerLow_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.KEpsilon → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ c * (Work.Kernels.scale τ) ^ N' * t ^ N) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ Work.Asymptotics.KEpsilon →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
        ≤ c * (Work.Kernels.scale τ) ^ N := by
  intro k l
  obtain ⟨Γ, hΓ0, hΓ⟩ := sinSq_gauss_seminorm k l
  set P : ℝ := ((k + l : ℕ) : ℝ) + 1 with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hPnat : P = ((k + l + 1 : ℕ) : ℝ) := by rw [hPdef]; push_cast; ring
  obtain ⟨c₀, N', hc₀, hflat'⟩ := hflat P hP0
  refine ⟨c₀ * Γ, N', mul_nonneg hc₀ hΓ0, ?_⟩
  intro τ r hτ
  have hscale : (0 : ℝ) ≤ (scale τ) ^ N' := Real.rpow_nonneg (le_of_lt (scale_pos τ)) N'
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
    refine ⟨fun _ => c₀ * (scale τ) ^ N' * Γj, ?_, ?_⟩
    · exact integrableOn_const (by simp)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
      obtain ⟨hu1, hu2⟩ := hu
      intro r
      -- step 1: factor out `w u`
      have hG_at : ContDiffAt ℝ ((j : ℕ∞) : ℕ∞ω) (fun r' : ℝ => G u r' * sinSq r') r :=
        ((hGsin_smooth u).contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
      have hstep1 : iteratedDeriv j (fun r' : ℝ => kfun r' u) r
          = w u * iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r := by
        have h1 : (fun r' : ℝ => kfun r' u) = fun r' : ℝ => w u * (G u r' * sinSq r') := by
          funext x; rw [hkfundef]
        rw [h1, iteratedDeriv_const_mul (w u) hG_at]
      rw [hstep1, norm_mul]
      -- step 2: bound `‖w u‖`
      have hw' : ‖w u‖ ≤ c₀ * (scale τ) ^ N' * u ^ P := by
        rw [hwdef]; exact hflat' τ u hτ hu1 hu2
      -- step 3: bound the second factor
      have hsin' : (fun r' : ℝ => G u r' * sinSq r') = fun r' : ℝ => sinSq r' * G u r' := by
        funext x; ring
      have hb2 : ‖iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r‖ ≤ Γj * (u ^ j)⁻¹ := by
        rw [hsin']
        have h := hΓj u hu1 hu2 r
        simpa using h
      -- step 4: `u^P * (u^j)⁻¹ ≤ 1`
      have hup : u ^ P * (u ^ j)⁻¹ ≤ 1 := by
        rw [hPnat, Real.rpow_natCast]
        have h1 : k + l + 1 = (k + l + 1 - j) + j := by omega
        rw [h1, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero j (ne_of_gt hu1)), mul_one]
        exact pow_le_one₀ hu1.le hu2
      -- combine
      calc ‖w u‖ * ‖iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r‖
          ≤ (c₀ * (scale τ) ^ N' * u ^ P) * (Γj * (u ^ j)⁻¹) :=
            mul_le_mul hw' hb2 (norm_nonneg _)
              (mul_nonneg (mul_nonneg hc₀ hscale) (by positivity))
        _ = c₀ * (scale τ) ^ N' * Γj * (u ^ P * (u ^ j)⁻¹) := by ring
        _ ≤ c₀ * (scale τ) ^ N' * Γj := by
            have hC : (0 : ℝ) ≤ c₀ * (scale τ) ^ N' * Γj :=
              mul_nonneg (mul_nonneg hc₀ (by positivity)) hΓj0
            nlinarith [hup, hC]
  -- apply the parametric-differentiation theorem
  have hfun_eq : (fun s : ℝ => layerLow ℓ d τ s) = fun s : ℝ => ∫ u in (0 : ℝ)..1, kfun s u :=
    funext hlayer
  rw [hfun_eq,
    iteratedDeriv_intervalIntegral_of_meas_bound kfun l hmeas_kfun hkfun_smooth hdom l le_rfl]
  -- pointwise weighted bound for the differentiated integrand
  have hptw : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ℝ,
      |x| ^ k * ‖iteratedDeriv l (fun r' : ℝ => kfun r' u) x‖
        ≤ c₀ * (scale τ) ^ N' * (Γ * u) := by
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
    have hw' : ‖w u‖ ≤ c₀ * (scale τ) ^ N' * u ^ P := by
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
      _ ≤ (c₀ * (scale τ) ^ N' * u ^ P) * (Γ * (u ^ (k + l))⁻¹) :=
          mul_le_mul hw' hb2 (mul_nonneg (by positivity) (norm_nonneg _))
            (mul_nonneg (mul_nonneg hc₀ hscale) (by positivity))
      _ = c₀ * (scale τ) ^ N' * Γ * (u ^ P * (u ^ (k + l))⁻¹) := by ring
      _ ≤ c₀ * (scale τ) ^ N' * Γ * u :=
          mul_le_mul_of_nonneg_left hup (mul_nonneg (mul_nonneg hc₀ hscale) hΓ0)
      _ = c₀ * (scale τ) ^ N' * (Γ * u) := by ring
  -- bound the integral
  have hIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hg_bound : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖((((|r| ^ k : ℝ)) : ℂ)) • iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖
        ≤ c₀ * (scale τ) ^ N' * Γ := by
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
        ≤ c₀ * (scale τ) ^ N' * (Γ * u) := h
      _ ≤ c₀ * (scale τ) ^ N' * Γ := mul_le_mul_of_nonneg_left hu3 (mul_nonneg hc₀ hscale)
  calc |r| ^ k * ‖∫ u in (0 : ℝ)..1, iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖
      = ‖∫ u in (0 : ℝ)..1, ((((|r| ^ k : ℝ)) : ℂ)) • iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖ := by
        have hnc : ‖((((|r| ^ k : ℝ)) : ℂ))‖ = |r| ^ k := by
          have h : ‖(((|r| ^ k : ℝ)) : ℂ)‖ = |(|r| ^ k : ℝ)| := RCLike.norm_ofReal (K := ℂ) (|r| ^ k)
          rw [h, abs_of_nonneg (by positivity)]
        rw [intervalIntegral.integral_smul, norm_smul, hnc]
    _ ≤ c₀ * (scale τ) ^ N' * Γ * |1 - (0 : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hg_bound
    _ = (c₀ * Γ) * (scale τ) ^ N' := by norm_num; ring


theorem E_kernelTransform_seminorm_of_layer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (F₂ : UpperHalfPlane → ℝ → ℂ)
    (hagree : ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.KEpsilon →
      (r = 0 ∨ d = 8 ∨ 2 < r ^ 2) →
        F₂ τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r)
    (hagree' : ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.KEpsilon →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
        F₂ τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r)
    (hsemi : ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.KEpsilon →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => F₂ τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.KEpsilon →
        (|r| ^ k) * ‖iteratedDeriv l
            (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  have _hd : d = 8 ∨ d = 24 := hd
  intro k l
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hbound⟩ := hsemi k l
  refine ⟨α, β, γ, δ, hα, hβ, hγ, hδ, ?_⟩
  intro τ r hτ
  set K : UpperHalfPlane → UpperHalfPlane → ℂ := Work.Kernels.Kfun ℓ d with hK
  set G : ℝ → ℂ := fun s => F₂ τ s with hG
  set gg : ℝ → ℂ := fun s => Work.Kernels.kernelTransform K τ s with hgg
  set P : ℝ → Prop := fun s => MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) with hP
  have hPdef : ∀ s, P s = MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := fun s => rfl
  have hRHSnn : (0:ℝ) ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
    have h1 : 0 ≤ α * (τ.im) ^ (-β) := mul_nonneg hα (Real.rpow_nonneg τ.im_pos.le _)
    have h2 : 0 ≤ γ * (‖(τ : ℂ)‖) ^ δ := mul_nonneg hγ (Real.rpow_nonneg (norm_nonneg _) _)
    linarith
  have hboundG : ∀ s : ℝ, (|s| ^ k) * ‖iteratedDeriv l G s‖
      ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := fun s => hbound τ s hτ
  have hP0 : ∀ s, ¬ P s → gg s = 0 := by
    intro s hs
    have hI : ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => Work.Kernels.Kaxis K τ t
          * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
      rwa [hPdef s] at hs
    have hz : (∫ t in Set.Ioi (0:ℝ), Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) = 0 :=
      integral_undef hI
    rw [hgg]
    simp only [Work.Kernels.kernelTransform, hz, mul_zero]
  have hP1 : ∀ s, P s → gg s = G s := by
    intro s hs
    rw [hgg, hG]
    exact (hagree' τ s hτ hs).symm
  have hgg0 : gg 0 = G 0 := by
    rw [hgg, hG]
    exact (hagree τ 0 hτ (Or.inl rfl)).symm
  have hmono : ∀ s s', P s → |s| ≤ |s'| → P s' := by
    intro s s' hs hsle
    rw [hPdef s'] 
    exact integrableOn_kaxis_exp_mono_abs (K := K) τ hsle (by rwa [hPdef s] at hs)
  by_cases hne : ∃ s, P s
  · set S : Set ℝ := {b | ∃ s, P s ∧ b = |s|} with hS
    have hmemS : ∀ b, b ∈ S ↔ ∃ s, P s ∧ b = |s| := fun b => Iff.rfl
    have hSne : S.Nonempty := by
      obtain ⟨s, hs⟩ := hne; exact ⟨|s|, s, hs, rfl⟩
    have hSbdd : BddBelow S := ⟨0, by rintro b ⟨s, _, rfl⟩; positivity⟩
    set ρ : ℝ := sInf S with hρ
    have hρnn : 0 ≤ ρ := by
      rw [hρ]
      exact le_csInf hSne (by rintro b ⟨s, _, rfl⟩; positivity)
    have hbig : ∀ s, ρ < |s| → P s := by
      intro s hs
      have hlt : sInf S < |s| := by rw [← hρ]; exact hs
      obtain ⟨b, hbS, hblt⟩ := (csInf_lt_iff hSbdd hSne).mp hlt
      obtain ⟨s₀, hPs₀, hb_eq⟩ := hbS
      exact hmono s₀ s hPs₀ (le_of_lt (by rw [hb_eq] at hblt; exact hblt))
    have hsmall : ∀ s, |s| < ρ → ¬ P s := by
      intro s hs hPs
      have hle : ρ ≤ |s| := by
        rw [hρ]
        exact csInf_le hSbdd ⟨s, hPs, rfl⟩
      linarith
    have hzero : ∀ s, |s| < ρ → gg s = 0 := fun s hs => hP0 s (hsmall s hs)
    have hgood : ∀ s, ρ < |s| → gg s = G s := fun s hs => hP1 s (hbig s hs)
    rcases eq_or_lt_of_le hρnn with hρ0 | hρpos
    · -- threshold 0: the transform agrees with `F₂` everywhere
      have hggG : gg = G := by
        funext s
        rcases eq_or_ne s 0 with h | h
        · subst h; exact hgg0
        · exact hgood s (by rw [← hρ0]; exact abs_pos.mpr h)
      rw [hggG]
      exact hboundG r
    · -- threshold `ρ > 0`
      rcases lt_trichotomy r ρ with hr | hr | hr
      · rcases lt_trichotomy r (-ρ) with hr' | hr' | hr'
        · -- r < -ρ : interior of the "good" half-line
          have habs : ρ < |r| := by rw [abs_of_neg (by linarith)]; linarith
          have hGG : gg =ᶠ[𝓝 r] G := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
          exact hboundG r
        · -- r = -ρ
          subst hr'
          rcases l with _ | l'
          · simp only [iteratedDeriv_zero]
            by_cases hP : P (-ρ)
            · rw [hP1 (-ρ) hP]
              simpa only [iteratedDeriv_zero] using hboundG (-ρ)
            · rw [hP0 (-ρ) hP, norm_zero, mul_zero]
              exact hRHSnn
          · have hz : iteratedDeriv (l' + 1) gg (-ρ) = 0 :=
              iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right (by linarith : -ρ < ρ)
                (fun y hy => hzero y (by
                  rw [abs_lt]; exact ⟨by linarith [hy.1], hy.2⟩)) l'
            rw [hz, norm_zero, mul_zero]
            exact hRHSnn
        · -- -ρ < r < ρ : interior of the vanishing interval
          have habs : |r| < ρ := by rw [abs_lt]; exact ⟨by linarith, hr⟩
          have hGG : gg =ᶠ[𝓝 r] (fun _ => (0:ℂ)) := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hzero s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l, iteratedDeriv_zeroFun]
          simp only [norm_zero, mul_zero]
          exact hRHSnn
      · -- r = ρ
        subst hr
        rcases l with _ | l'
        · simp only [iteratedDeriv_zero]
          by_cases hP : P ρ
          · rw [hP1 ρ hP]
            simpa only [iteratedDeriv_zero] using hboundG ρ
          · rw [hP0 ρ hP, norm_zero, mul_zero]
            exact hRHSnn
        · have hz : iteratedDeriv (l' + 1) gg ρ = 0 :=
            iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left hρpos
              (fun y hy => hzero y (by rw [abs_of_pos hy.1]; exact hy.2)) l'
          rw [hz, norm_zero, mul_zero]
          exact hRHSnn
      · -- r > ρ : interior of the "good" half-line
        have habs : ρ < |r| := by rw [abs_of_pos (by linarith)]; linarith
        have hGG : gg =ᶠ[𝓝 r] G := by
          refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
          exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
        rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
        exact hboundG r
  · -- no integrable point at all: the transform vanishes identically
    have hnone : ∀ s, ¬ P s := fun s hs => hne ⟨s, hs⟩
    have hg0 : gg = fun _ => (0:ℂ) := funext (fun s => hP0 s (hnone s))
    rw [hg0, iteratedDeriv_zeroFun]
    simp only [norm_zero, mul_zero]
    exact hRHSnn



theorem E_kernelTransform_seminorm_of_layer0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (F₂ : UpperHalfPlane → ℝ → ℂ)
    (hagree : ∀ (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.KEpsilon →
        F₂ τ 0 = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ 0)
    (hagree' : ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.KEpsilon →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
        F₂ τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r)
    (hsemi : ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.KEpsilon →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => F₂ τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.KEpsilon →
        (|r| ^ k) * ‖iteratedDeriv l
            (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  have _hd : d = 8 ∨ d = 24 := hd
  intro k l
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hbound⟩ := hsemi k l
  refine ⟨α, β, γ, δ, hα, hβ, hγ, hδ, ?_⟩
  intro τ r hτ
  set K : UpperHalfPlane → UpperHalfPlane → ℂ := Work.Kernels.Kfun ℓ d with hK
  set G : ℝ → ℂ := fun s => F₂ τ s with hG
  set gg : ℝ → ℂ := fun s => Work.Kernels.kernelTransform K τ s with hgg
  set P : ℝ → Prop := fun s => MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) with hP
  have hPdef : ∀ s, P s = MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := fun s => rfl
  have hRHSnn : (0:ℝ) ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
    have h1 : 0 ≤ α * (τ.im) ^ (-β) := mul_nonneg hα (Real.rpow_nonneg τ.im_pos.le _)
    have h2 : 0 ≤ γ * (‖(τ : ℂ)‖) ^ δ := mul_nonneg hγ (Real.rpow_nonneg (norm_nonneg _) _)
    linarith
  have hboundG : ∀ s : ℝ, (|s| ^ k) * ‖iteratedDeriv l G s‖
      ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := fun s => hbound τ s hτ
  have hP0 : ∀ s, ¬ P s → gg s = 0 := by
    intro s hs
    have hI : ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => Work.Kernels.Kaxis K τ t
          * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
      rwa [hPdef s] at hs
    have hz : (∫ t in Set.Ioi (0:ℝ), Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) = 0 :=
      integral_undef hI
    rw [hgg]
    simp only [Work.Kernels.kernelTransform, hz, mul_zero]
  have hP1 : ∀ s, P s → gg s = G s := by
    intro s hs
    rw [hgg, hG]
    exact (hagree' τ s hτ hs).symm
  have hgg0 : gg 0 = G 0 := by
    rw [hgg, hG]
    exact (hagree τ hτ).symm
  have hmono : ∀ s s', P s → |s| ≤ |s'| → P s' := by
    intro s s' hs hsle
    rw [hPdef s'] 
    exact integrableOn_kaxis_exp_mono_abs (K := K) τ hsle (by rwa [hPdef s] at hs)
  by_cases hne : ∃ s, P s
  · set S : Set ℝ := {b | ∃ s, P s ∧ b = |s|} with hS
    have hmemS : ∀ b, b ∈ S ↔ ∃ s, P s ∧ b = |s| := fun b => Iff.rfl
    have hSne : S.Nonempty := by
      obtain ⟨s, hs⟩ := hne; exact ⟨|s|, s, hs, rfl⟩
    have hSbdd : BddBelow S := ⟨0, by rintro b ⟨s, _, rfl⟩; positivity⟩
    set ρ : ℝ := sInf S with hρ
    have hρnn : 0 ≤ ρ := by
      rw [hρ]
      exact le_csInf hSne (by rintro b ⟨s, _, rfl⟩; positivity)
    have hbig : ∀ s, ρ < |s| → P s := by
      intro s hs
      have hlt : sInf S < |s| := by rw [← hρ]; exact hs
      obtain ⟨b, hbS, hblt⟩ := (csInf_lt_iff hSbdd hSne).mp hlt
      obtain ⟨s₀, hPs₀, hb_eq⟩ := hbS
      exact hmono s₀ s hPs₀ (le_of_lt (by rw [hb_eq] at hblt; exact hblt))
    have hsmall : ∀ s, |s| < ρ → ¬ P s := by
      intro s hs hPs
      have hle : ρ ≤ |s| := by
        rw [hρ]
        exact csInf_le hSbdd ⟨s, hPs, rfl⟩
      linarith
    have hzero : ∀ s, |s| < ρ → gg s = 0 := fun s hs => hP0 s (hsmall s hs)
    have hgood : ∀ s, ρ < |s| → gg s = G s := fun s hs => hP1 s (hbig s hs)
    rcases eq_or_lt_of_le hρnn with hρ0 | hρpos
    · -- threshold 0: the transform agrees with `F₂` everywhere
      have hggG : gg = G := by
        funext s
        rcases eq_or_ne s 0 with h | h
        · subst h; exact hgg0
        · exact hgood s (by rw [← hρ0]; exact abs_pos.mpr h)
      rw [hggG]
      exact hboundG r
    · -- threshold `ρ > 0`
      rcases lt_trichotomy r ρ with hr | hr | hr
      · rcases lt_trichotomy r (-ρ) with hr' | hr' | hr'
        · -- r < -ρ : interior of the "good" half-line
          have habs : ρ < |r| := by rw [abs_of_neg (by linarith)]; linarith
          have hGG : gg =ᶠ[𝓝 r] G := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
          exact hboundG r
        · -- r = -ρ
          subst hr'
          rcases l with _ | l'
          · simp only [iteratedDeriv_zero]
            by_cases hP : P (-ρ)
            · rw [hP1 (-ρ) hP]
              simpa only [iteratedDeriv_zero] using hboundG (-ρ)
            · rw [hP0 (-ρ) hP, norm_zero, mul_zero]
              exact hRHSnn
          · have hz : iteratedDeriv (l' + 1) gg (-ρ) = 0 :=
              iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right (by linarith : -ρ < ρ)
                (fun y hy => hzero y (by
                  rw [abs_lt]; exact ⟨by linarith [hy.1], hy.2⟩)) l'
            rw [hz, norm_zero, mul_zero]
            exact hRHSnn
        · -- -ρ < r < ρ : interior of the vanishing interval
          have habs : |r| < ρ := by rw [abs_lt]; exact ⟨by linarith, hr⟩
          have hGG : gg =ᶠ[𝓝 r] (fun _ => (0:ℂ)) := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hzero s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l, iteratedDeriv_zeroFun]
          simp only [norm_zero, mul_zero]
          exact hRHSnn
      · -- r = ρ
        subst hr
        rcases l with _ | l'
        · simp only [iteratedDeriv_zero]
          by_cases hP : P ρ
          · rw [hP1 ρ hP]
            simpa only [iteratedDeriv_zero] using hboundG ρ
          · rw [hP0 ρ hP, norm_zero, mul_zero]
            exact hRHSnn
        · have hz : iteratedDeriv (l' + 1) gg ρ = 0 :=
            iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left hρpos
              (fun y hy => hzero y (by rw [abs_of_pos hy.1]; exact hy.2)) l'
          rw [hz, norm_zero, mul_zero]
          exact hRHSnn
      · -- r > ρ : interior of the "good" half-line
        have habs : ρ < |r| := by rw [abs_of_pos (by linarith)]; linarith
        have hGG : gg =ᶠ[𝓝 r] G := by
          refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
          exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
        rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
        exact hboundG r
  · -- no integrable point at all: the transform vanishes identically
    have hnone : ∀ s, ¬ P s := fun s hs => hne ⟨s, hs⟩
    have hg0 : gg = fun _ => (0:ℂ) := funext (fun s => hP0 s (hnone s))
    rw [hg0, iteratedDeriv_zeroFun]
    simp only [norm_zero, mul_zero]
    exact hRHSnn



theorem E_tail_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (N₀ C N M : ℝ) (hN₀ : 0 ≤ N₀) (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hwin : ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon → 0 < t →
      t ≤ (scale w) ^ N₀ →
      ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon →
      (scale w) ^ N₀ ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp G w t‖
        ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t))) :
    ∀ k l : ℕ, ∃ c N' : ℝ, 0 ≤ c ∧ 0 ≤ N' ∧ ∀ (w : UpperHalfPlane),
      w ∈ KEpsilon → ∀ r : ℝ,
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => sinSq s *
          tailIntegral (fun t : ℝ =>
            if t < (scale w) ^ N₀ then Kaxis (Kfun ℓ d) w t
            else Kaxis (Kfun ℓ d) w t - Aexp G w t)
          (s ^ 2)) r‖
          ≤ c * (scale w) ^ N' := by
  intro k l
  obtain ⟨c4, hc4, h4⟩ := exists_seminorm_bound_of_iteratedDeriv_bound k l
  obtain ⟨c6, N6, hc6, hN6, h6⟩ :=
    exists_bound_iteratedDeriv_tailIntegral_two_regime l N₀ C N M C N M
      hC.le hN hM hC.le hN hM hN₀
  refine ⟨c4 * c6, N6, mul_nonneg hc4 hc6, hN6, ?_⟩
  intro w hw r
  have hA1 : 1 ≤ scale w := one_le_scale w
  have hA0 : (0 : ℝ) < scale w := scale_pos w
  set h : ℝ → ℂ := fun t => if t < (scale w) ^ N₀ then Kaxis (Kfun ℓ d) w t
    else Kaxis (Kfun ℓ d) w t - Aexp G w t with hhdef
  have hKmeas : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) w (measurable_Kfun_snd_all ℓ d hd w)
  have hAexp : Measurable (fun t : ℝ => Aexp G w t) := by unfold Aexp; fun_prop
  have hhmeas : AEStronglyMeasurable h (volume.restrict (Set.Ici (1 : ℝ))) := by
    rw [hhdef]
    exact (hKmeas.ite measurableSet_Iio (hKmeas.sub hAexp)).aestronglyMeasurable
  have hw2 : ∀ t : ℝ, 1 ≤ t → t ≤ (scale w) ^ N₀ →
      ‖h t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M := by
    intro t ht1 htB
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    by_cases hlt : t < (scale w) ^ N₀
    · rw [hhdef]; simp only [hlt, if_true]
      exact hwin w t hw ht0 htB
    · rw [hhdef]; simp only [hlt, if_false]
      have htge : (scale w) ^ N₀ ≤ t := not_lt.mp hlt
      have hb := htail w t hw htge
      have he : t ^ M * Real.exp (-(Real.pi * t)) ≤ (1 + t) ^ M := by
        have h3 : Real.exp (-(Real.pi * t)) ≤ 1 := by
          rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht0])
        have h4 : t ^ M ≤ (1 + t) ^ M :=
          Real.rpow_le_rpow ht0.le (by linarith) hM
        have h5 : (0 : ℝ) ≤ t ^ M := Real.rpow_nonneg ht0.le M
        nlinarith [h3, h4, h5, Real.exp_pos (-(Real.pi * t))]
      calc ‖Kaxis (Kfun ℓ d) w t - Aexp G w t‖
          ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t)) := hb
        _ = C * (scale w) ^ N * (t ^ M * Real.exp (-(Real.pi * t))) := by ring
        _ ≤ C * (scale w) ^ N * (1 + t) ^ M :=
            mul_le_mul_of_nonneg_left he (mul_nonneg hC.le (Real.rpow_nonneg hA0.le N))
  have ht2 : ∀ t : ℝ, (scale w) ^ N₀ ≤ t →
      ‖h t‖ ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t)) := by
    intro t htB
    have hnot : ¬ t < (scale w) ^ N₀ := not_lt.mpr htB
    rw [hhdef]; simp only [hnot, if_false]
    exact htail w t hw htB
  obtain ⟨Cg, Mg, hCg, hMg, hglob⟩ :=
    ae_bound_of_two_regime h (Real.one_le_rpow hA1 hN₀)
      (mul_nonneg hC.le (Real.rpow_nonneg hA0.le N))
      (mul_nonneg hC.le (Real.rpow_nonneg hA0.le N)) hM hM hw2 ht2
  have hglob_ae : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖h t‖ ≤ Cg * t ^ Mg * Real.exp (-(Real.pi * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht1
    exact hglob t (Set.mem_Ici.mp ht1)
  have hcont : ContDiffOn ℝ (l : ℕ∞ω) (tailIntegral h) (Set.Ioi (-1)) :=
    tailIntegral_contDiffOn l h hhmeas hCg hMg hglob_ae
  have hderiv : ∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (tailIntegral h) x‖
        ≤ (c6 * (scale w) ^ N6) * Real.exp (-(Real.pi * x)) :=
    fun m hm x hx =>
      h6 h (scale w) Cg Mg hA1 hCg hMg hhmeas hglob_ae hw2 ht2 m hm x hx
  have hmain := h4 (tailIntegral h) (c6 * (scale w) ^ N6) (by positivity) hcont hderiv r
  have hfun : (fun s : ℝ => sinSq s * tailIntegral h (s ^ 2))
      = fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2) := by
    funext s; rw [sinSq_eq]
  rw [hfun]
  calc (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2)) r‖
      ≤ c4 * (c6 * (scale w) ^ N6) := hmain
    _ = (c4 * c6) * (scale w) ^ N6 := by ring



/-! ## The cusp-`0` layer `E_F₂`: integrability and agreement with the contour integral -/

/-- A non-zero affine function of `t` times `e^{-dt}` with `d ≤ 0` is not integrable on
`(B, ∞)`: the exponential does not decay and the affine factor stays away from `0`. -/
lemma E_eq_zero_of_integrableOn_affine_exp_Ioi {d : ℝ} (hd : d ≤ 0) (B : ℝ) {a b : ℂ}
    (h : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(d : ℂ) * (t : ℂ))) (Set.Ioi B)) :
    a = 0 ∧ b = 0 := by
  by_contra hcon
  obtain ⟨T, ε, hε, hT⟩ : ∃ T ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, T ≤ t → ε ≤ ‖a + (t : ℂ) * Complex.I * b‖ := by
    rcases eq_or_ne b 0 with hb | hb
    · subst hb
      refine ⟨0, ‖a‖, norm_pos_iff.mpr ?_, fun t _ => ?_⟩
      · intro h0; exact hcon ⟨h0, rfl⟩
      · simp
    · have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
      refine ⟨(‖a‖ + 1) / ‖b‖, 1, one_pos, fun t ht => ?_⟩
      have hTpos : 0 < (‖a‖ + 1) / ‖b‖ := div_pos (by positivity) hbpos
      have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le hTpos ht)
      have h1 : ‖a‖ + 1 ≤ t * ‖b‖ := (div_le_iff₀ hbpos).mp ht
      have h3 : ‖(t : ℂ) * Complex.I * b‖ - ‖a‖ ≤ ‖a + (t : ℂ) * Complex.I * b‖ := by
        have h4 := norm_sub_le (a + (t : ℂ) * Complex.I * b) a
        rw [add_sub_cancel_left] at h4
        linarith
      have h5 : ‖(t : ℂ) * Complex.I * b‖ = t * ‖b‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
        congr 1
        simp [abs_of_nonneg ht0]
      rw [h5] at h3
      linarith
  set T' : ℝ := max (max T B) 0 with hT'def
  have hBT' : B ≤ T' := le_trans (le_max_right T B) (le_max_left _ 0)
  have hTT' : T ≤ T' := le_trans (le_max_left T B) (le_max_left _ 0)
  have hT'0 : 0 ≤ T' := le_max_right _ 0
  have hpoint : ∀ t ∈ Set.Ioi T', ε * Real.exp (-d * t) ≤
      ‖(a + (t : ℂ) * Complex.I * b) * Complex.exp (-(d : ℂ) * (t : ℂ))‖ := by
    intro t ht
    have htT : T ≤ t := le_trans hTT' (le_of_lt (Set.mem_Ioi.mp ht))
    have ht0 : 0 ≤ t := le_trans hT'0 (le_of_lt (Set.mem_Ioi.mp ht))
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(d : ℂ) * (t : ℂ)).re = -d * t := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hT t htT) (Real.exp_nonneg _)
  have hint1 : MeasureTheory.IntegrableOn (fun t : ℝ => ε * Real.exp (-d * t)) (Set.Ioi T') := by
    refine Integrable.mono' (h.mono_set (Set.Ioi_subset_Ioi hBT')).norm ?_ ?_
    · exact (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_of_nonneg (mul_nonneg hε.le (Real.exp_nonneg _))]
      exact hpoint t ht
  have hint2 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-d * t)) (Set.Ioi T') := by
    have h2 : MeasureTheory.IntegrableOn (fun x : ℝ => ε⁻¹ * (ε * Real.exp (-d * x)))
        (Set.Ioi T') := Integrable.const_mul hint1 (ε⁻¹)
    exact MeasureTheory.IntegrableOn.congr_fun h2
      (fun t _ => inv_mul_cancel_left₀ hε.ne' (Real.exp (-d * t))) measurableSet_Ioi
  exact absurd hint2 (not_integrableOn_exp_neg_of_nonpos hd T')

/-- The same, on the half-line `[B, ∞)`. -/
lemma E_eq_zero_of_integrableOn_affine_exp_Ici {d : ℝ} (hd : d ≤ 0) (B : ℝ) {a b : ℂ}
    (h : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (a + (t : ℂ) * Complex.I * b) * Complex.exp (-(d : ℂ) * (t : ℂ))) (Set.Ici B)) :
    a = 0 ∧ b = 0 :=
  E_eq_zero_of_integrableOn_affine_exp_Ioi hd B (h.mono_set Set.Ioi_subset_Ici_self)

/-- Splitting `Aexp G w t · e^{-L t}` into its two affine moments, with the shifted exponent
`L - 2π` on the `e^{2πt}` part. -/
lemma E_Aexp_exp_decomp (G : Fin 2 → Fin 2 → ℍ → ℂ) (w : ℍ) (L : ℝ) (t : ℝ) :
    Aexp G w t * Complex.exp (-(L : ℂ) * (t : ℂ))
      = (G 0 0 w + (t : ℂ) * Complex.I * G 0 1 w) * Complex.exp (-(L : ℂ) * (t : ℂ))
        + (G 1 0 w + (t : ℂ) * Complex.I * G 1 1 w)
          * Complex.exp (-((L - 2 * Real.pi : ℝ) : ℂ) * (t : ℂ)) := by
  have hexp : Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))
      = Complex.exp (-((L - 2 * Real.pi : ℝ) : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [Aexp]
  rw [add_mul, add_mul]
  rw [show (Complex.exp (2 * Real.pi * t) * (G 1 0 w + (t : ℂ) * Complex.I * G 1 1 w))
        * Complex.exp (-(L : ℂ) * (t : ℂ))
      = (G 1 0 w + (t : ℂ) * Complex.I * G 1 1 w)
        * (Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))) from by ring,
    hexp]

/-- If the contour integrand `Kaxis·e^{-πr²t}` is integrable on `(0,∞)`, then so is its
non-decaying part `Aexp·e^{-πr²t}` on `(B,∞)`, where `B = (scale w)^{N₀}` is the threshold of
the two regimes. -/
lemma E_integrableOn_Aexp_exp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {N₀ C N M : ℝ} (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M) {w : ℍ} {r : ℝ}
    (hB1 : 1 ≤ E_Bw N₀ w)
    (htail : ∀ t : ℝ, E_Bw N₀ w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t)))
    (hInt : MeasureTheory.IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Aexp (Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi (E_Bw N₀ w)) := by
  set L : ℝ := Real.pi * r ^ 2 with hLdef
  have hB0 : 0 < E_Bw N₀ w := lt_of_lt_of_le zero_lt_one hB1
  have hFeq : (fun t : ℝ => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = fun t : ℝ => Kaxis (Kfun ℓ d) w t * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    funext t
    congr 2
    rw [hLdef]; push_cast; ring
  rw [hFeq] at hInt
  have hF_intB : MeasureTheory.IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (E_Bw N₀ w)) :=
    hInt.mono_set (fun t ht => lt_trans hB0 (Set.mem_Ioi.mp ht))
  have hmeasK : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) w (measurable_Kfun_snd_all ℓ d hd w)
  have hmeasA : Measurable (fun t : ℝ => Aexp (Gcusp ℓ d) w t) := by unfold Aexp; fun_prop
  have hmeasE : Measurable (fun t : ℝ => Complex.exp (-(L : ℂ) * (t : ℂ))) := by fun_prop
  have hDiff_int : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t) * Complex.exp (-(L : ℂ) * (t : ℂ)))
      (Set.Ioi (E_Bw N₀ w)) := by
    have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ M * Real.exp (-(Real.pi * t)))
        (Set.Ioi (E_Bw N₀ w)) :=
      (integrableOn_rpow_mul_exp_neg M Real.pi hM Real.pi_pos).mono_set
        (fun t ht => le_trans hB1 (le_of_lt ht))
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => C * (scale w) ^ N * (t ^ M * Real.exp (-(Real.pi * t))))
        (Set.Ioi (E_Bw N₀ w)) := hbase.const_mul (C * (scale w) ^ N)
    refine Integrable.mono' hdom ((hmeasK.sub hmeasA).mul hmeasE).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hb := htail t (le_of_lt ht)
    have ht0 : 0 ≤ t := le_trans hB0.le (le_of_lt ht)
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(L : ℂ) * (t : ℂ)).re = -(L * t) := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      ring
    rw [hre]
    have hLt : 0 ≤ L * t := mul_nonneg (by rw [hLdef]; positivity) ht0
    have he1 : Real.exp (-(L * t)) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    calc ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖ * Real.exp (-(L * t))
        ≤ (C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t))) * 1 :=
          mul_le_mul hb he1 (Real.exp_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (scale_pos w).le N))
              (Real.rpow_nonneg ht0 M)) (Real.exp_nonneg _))
      _ = C * (scale w) ^ N * (t ^ M * Real.exp (-(Real.pi * t))) := by ring
  have hsub := hF_intB.sub hDiff_int
  refine MeasureTheory.IntegrableOn.congr_fun hsub (fun t _ => ?_) measurableSet_Ioi
  have harg : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = -(L : ℂ) * (t : ℂ) := by
    rw [hLdef]; push_cast; ring
  rw [harg]
  simp only [Pi.sub_apply]
  ring


/-! ## Evenness and analyticity of the layer pieces -/

lemma E_layerLow_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) :
    layerLow ℓ d w (-r) = layerLow ℓ d w r := by
  have hsq : ((-r : ℝ) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by rw [Complex.ofReal_neg, neg_sq]
  rw [layerLow, layerLow]
  rw [show (fun t : ℝ => Kaxis (Kfun ℓ d) w t
        * Complex.exp (-(Real.pi * ((-r : ℝ) : ℂ) ^ 2 * (t : ℂ))))
      = fun t : ℝ => Kaxis (Kfun ℓ d) w t
        * Complex.exp (-(Real.pi * ((r : ℝ) : ℂ) ^ 2 * (t : ℂ))) from by
    funext t; rw [hsq]]
  congr 1
  simp only [sinSq, hsq]

lemma E_TailT_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (N₀ : ℝ) (w : ℍ) (r : ℝ) :
    E_TailT ℓ d N₀ w (-r) = E_TailT ℓ d N₀ w r := by
  have hsq : ((-r : ℝ) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by rw [Complex.ofReal_neg, neg_sq]
  have hsq' : (-r) ^ 2 = r ^ 2 := by ring
  rw [E_TailT, E_TailT, hsq']
  congr 1
  simp only [sinSq, hsq]

lemma E_Expr_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (N₀ : ℝ) (w : ℍ) (r : ℝ) :
    E_Expr ℓ d N₀ w (-r) = E_Expr ℓ d N₀ w r := by
  rw [E_Expr, E_Expr, E_layerLow_neg, E_TailT_neg, E_TailClosed_neg]

/-- Analyticity of `layerLow` on `E`, from the flatness `EFlat`. -/
lemma E_contDiff_omega_layerLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : Work.Asymptotics.EFlat ℓ d) {w : ℍ} (hw : w ∈ Work.Asymptotics.KEpsilon) :
    ContDiff ℝ ω (fun s : ℝ => layerLow ℓ d w s) := by
  obtain ⟨c, N', hc, hflat'⟩ := hflat 0 (le_refl 0)
  have hscale : 0 < scale w := scale_pos w
  have hmeasK : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) w (measurable_Kfun_snd_all ℓ d hd w)
  have hlow : ContDiff ℝ ω (fun r : ℝ => ∫ t in (0:ℝ)..1,
      Kaxis (Kfun ℓ d) w t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    refine contDiff_omega_intervalIntegral_exp (B := c * (scale w) ^ N')
      (mul_nonneg hc (Real.rpow_nonneg hscale.le _)) hmeasK.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have := hflat' w t hw ht.1 ht.2
    rwa [Real.rpow_zero, mul_one] at this
  simpa only [layerLow] using contDiff_omega_sinSq.mul hlow

/-- Analyticity of the `trunc` piece `E_TailT` of the layer, from the two regimes. -/
lemma E_contDiff_omega_TailT (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {N₀ C N M : ℝ} (hN₀ : 0 ≤ N₀) (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    {w : ℍ} (hw : w ∈ Work.Asymptotics.KEpsilon)
    (hwin : ∀ t : ℝ, 0 < t → t ≤ (scale w) ^ N₀ →
      ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ t : ℝ, (scale w) ^ N₀ ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t))) :
    ContDiff ℝ ω (fun s : ℝ => E_TailT ℓ d N₀ w s) := by
  have hA1 : 1 ≤ scale w := one_le_scale w
  have hA0 : 0 < scale w := scale_pos w
  have hB1 : 1 ≤ E_Bw N₀ w := by rw [E_Bw]; exact Real.one_le_rpow hA1 hN₀
  have hKmeas : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) w (measurable_Kfun_snd_all ℓ d hd w)
  have hAmeas : Measurable (fun t : ℝ => Aexp (Gcusp ℓ d) w t) := by unfold Aexp; fun_prop
  have hhmeas : AEStronglyMeasurable (fun t : ℝ => if t < E_Bw N₀ w then Kaxis (Kfun ℓ d) w t
      else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t) (volume.restrict (Set.Ici (1:ℝ))) :=
    (hKmeas.ite measurableSet_Iio (hKmeas.sub hAmeas)).aestronglyMeasurable
  have hw2 : ∀ t : ℝ, 1 ≤ t → t ≤ E_Bw N₀ w →
      ‖(if t < E_Bw N₀ w then Kaxis (Kfun ℓ d) w t
        else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M := by
    intro t ht1 htB
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    rcases lt_or_eq_of_le htB with h | h
    · rw [if_pos h]; exact hwin t ht0 htB
    · rw [if_neg (by rw [h]; exact lt_irrefl _)]
      have hb := htail t (le_of_eq h.symm)
      have he : t ^ M * Real.exp (-(Real.pi * t)) ≤ (1 + t) ^ M := by
        have h3 : Real.exp (-(Real.pi * t)) ≤ 1 := by
          rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht0])
        have h4 : t ^ M ≤ (1 + t) ^ M := Real.rpow_le_rpow ht0.le (by linarith) hM
        have h5 : (0 : ℝ) ≤ t ^ M := Real.rpow_nonneg ht0.le M
        nlinarith [h3, h4, h5, Real.exp_pos (-(Real.pi * t))]
      calc ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
          ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t)) := hb
        _ = C * (scale w) ^ N * (t ^ M * Real.exp (-(Real.pi * t))) := by ring
        _ ≤ C * (scale w) ^ N * (1 + t) ^ M :=
            mul_le_mul_of_nonneg_left he (mul_nonneg hC.le (Real.rpow_nonneg hA0.le N))
  have ht2 : ∀ t : ℝ, E_Bw N₀ w ≤ t →
      ‖(if t < E_Bw N₀ w then Kaxis (Kfun ℓ d) w t
        else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)‖
        ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t)) := by
    intro t htB
    rw [if_neg (not_lt.mpr htB)]
    exact htail t htB
  obtain ⟨Cg, Mg, hCg, hMg, hglob⟩ := ae_bound_of_two_regime _
    (B := E_Bw N₀ w) hB1
    (mul_nonneg hC.le (Real.rpow_nonneg hA0.le N))
    (mul_nonneg hC.le (Real.rpow_nonneg hA0.le N)) hM hM hw2 ht2
  have hglob_ae : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
      ‖(if t < E_Bw N₀ w then Kaxis (Kfun ℓ d) w t
        else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)‖
        ≤ max Cg 1 * t ^ Mg * Real.exp (-(Real.pi * t)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1:ℝ) ≤ t := Set.mem_Ici.mp ht
    refine le_trans (hglob t ht1) ?_
    have htm : (0:ℝ) ≤ t ^ Mg := Real.rpow_nonneg (by linarith) Mg
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Cg 1) htm) (Real.exp_nonneg _)
  have hcd : ContDiff ℝ ω (fun r : ℝ => ∫ t in Set.Ici 1,
      (if t < E_Bw N₀ w then Kaxis (Kfun ℓ d) w t
        else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) :=
    contDiff_omega_integral_Ici_exp (C := max Cg 1) (M := Mg)
      (lt_of_lt_of_le zero_lt_one (le_max_right Cg 1)) hMg hhmeas hglob_ae
  have hfun : (fun s : ℝ => E_TailT ℓ d N₀ w s)
      = fun s : ℝ => sinSq s * ∫ t in Set.Ici 1,
          (if t < E_Bw N₀ w then Kaxis (Kfun ℓ d) w t
            else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)
          * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))) := by
    funext s
    rw [E_TailT, tailIntegral]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
    congr 1
    rw [show -(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * s ^ 2 * t) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_exp]
  rw [hfun]
  exact contDiff_omega_sinSq.mul hcd

lemma E_contDiff_omega_Expr (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : Work.Asymptotics.EFlat ℓ d) {N₀ C N M : ℝ} (hN₀ : 0 ≤ N₀) (hC : 0 < C)
    (hN : 0 ≤ N) (hM : 0 ≤ M) {w : ℍ} (hw : w ∈ Work.Asymptotics.KEpsilon)
    (hwin : ∀ t : ℝ, 0 < t → t ≤ (scale w) ^ N₀ →
      ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ t : ℝ, (scale w) ^ N₀ ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t))) :
    ContDiff ℝ ω (fun s : ℝ => E_Expr ℓ d N₀ w s) := by
  have h1 := E_contDiff_omega_layerLow ℓ d hd hflat hw
  have h2 := E_contDiff_omega_TailT ℓ d hd hN₀ hC hN hM hw hwin htail
  have h3 := contDiff_E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w
  exact (h1.add h2).add h3

/-- The seminorm bound for the layer expression `E_Expr` on the convergence region. -/
lemma E_Expr_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : Work.Asymptotics.EFlat ℓ d) {N₀ C N M : ℝ} (hN₀ : 0 ≤ N₀) (hC : 0 < C)
    (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hwin : ∀ (w : ℍ) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon → 0 < t →
      t ≤ (scale w) ^ N₀ → ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ (w : ℍ) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon → (scale w) ^ N₀ ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t)))
    (hGcusp : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.KEpsilon
      (Gcusp ℓ d i j))
    (k l : ℕ) :
    ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
      E_R ℓ d w r →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_Expr ℓ d N₀ w s) r‖
        ≤ c * (scale w) ^ N' := by
  obtain ⟨c1, N1, hc1, hb1⟩ := E_layerLow_seminorm ℓ d hd hflat k l
  obtain ⟨c2, N2, hc2, hN2, hb2⟩ :=
    E_tail_seminorm ℓ d hd (Gcusp ℓ d) N₀ C N M hN₀ hC hN hM hwin htail k l
  obtain ⟨c3, N3, hc3, hN3, hb3⟩ := E_TailClosed_seminorm (Gcusp ℓ d) hGcusp N₀ hN₀ k l
  set Nc : ℝ := max (max N1 N2) N3 with hNcdef
  refine ⟨c1 + c2 + c3, Nc, by linarith, ?_⟩
  intro w hw r hR
  have hlow_cd : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => layerLow ℓ d w s) r :=
    ((E_contDiff_omega_layerLow ℓ d hd hflat hw).contDiffAt).of_le le_top
  have htail_cd : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => E_TailT ℓ d N₀ w s) r :=
    ((E_contDiff_omega_TailT ℓ d hd hN₀ hC hN hM hw (fun t ht0 htB => hwin w t hw ht0 htB)
      (fun t htB => htail w t hw htB)).contDiffAt).of_le le_top
  have htc_cd : ContDiffAt ℝ (l : ℕ∞)
      (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w s) r :=
    ((contDiff_E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w).contDiffAt).of_le le_top
  have hsplit : iteratedDeriv l (fun s : ℝ => E_Expr ℓ d N₀ w s) r
      = iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => E_TailT ℓ d N₀ w s) r
        + iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w s) r := by
    have hsplit1 : iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s + E_TailT ℓ d N₀ w s) r
        = iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => E_TailT ℓ d N₀ w s) r := by
      change iteratedDeriv l ((fun s : ℝ => layerLow ℓ d w s)
        + fun s : ℝ => E_TailT ℓ d N₀ w s) r = _
      exact iteratedDeriv_add hlow_cd htail_cd
    have hsplit2 : iteratedDeriv l (fun s : ℝ => E_Expr ℓ d N₀ w s) r
        = iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s + E_TailT ℓ d N₀ w s) r
          + iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w s) r := by
      change iteratedDeriv l ((fun s : ℝ => layerLow ℓ d w s + E_TailT ℓ d N₀ w s)
        + fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w s) r = _
      exact iteratedDeriv_add (hlow_cd.add htail_cd) htc_cd
    rw [hsplit2, hsplit1]
  have h1 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r‖
      ≤ c1 * (scale w) ^ N1 := hb1 w r hw
  have h2 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_TailT ℓ d N₀ w s) r‖
      ≤ c2 * (scale w) ^ N2 := hb2 w hw r
  have h3 : (|r| ^ k) * ‖iteratedDeriv l
      (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w s) r‖
      ≤ c3 * (scale w) ^ N3 := hb3 w hw r hR
  rw [hsplit]
  have hs1 : 1 ≤ scale w := one_le_scale w
  have hN1 : N1 ≤ Nc := by rw [hNcdef]; exact le_trans (le_max_left N1 N2) (le_max_left _ N3)
  have hN2 : N2 ≤ Nc := by rw [hNcdef]; exact le_trans (le_max_right N1 N2) (le_max_left _ N3)
  have hN3 : N3 ≤ Nc := by rw [hNcdef]; exact le_max_right _ N3
  have e1 : c1 * (scale w) ^ N1 ≤ c1 * (scale w) ^ Nc :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN1) hc1
  have e2 : c2 * (scale w) ^ N2 ≤ c2 * (scale w) ^ Nc :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN2) hc2
  have e3 : c3 * (scale w) ^ N3 ≤ c3 * (scale w) ^ Nc :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN3) hc3
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => E_TailT ℓ d N₀ w s) r
        + iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w s) r‖
      ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => E_TailT ℓ d N₀ w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w s) r‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h2' : ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
              + iteratedDeriv l (fun s : ℝ => E_TailT ℓ d N₀ w s) r‖
            ≤ ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r‖
              + ‖iteratedDeriv l (fun s : ℝ => E_TailT ℓ d N₀ w s) r‖ := norm_add_le _ _
        linarith [norm_add_le
          (iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
            + iteratedDeriv l (fun s : ℝ => E_TailT ℓ d N₀ w s) r)
          (iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w s) r), h2']
    _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r‖
          + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_TailT ℓ d N₀ w s) r‖
          + (|r| ^ k) * ‖iteratedDeriv l
              (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_Bw N₀ w) w s) r‖ := by ring
    _ ≤ c1 * (scale w) ^ N1 + c2 * (scale w) ^ N2 + c3 * (scale w) ^ N3 := by linarith
    _ ≤ (c1 + c2 + c3) * (scale w) ^ Nc := by
        have hsum : c1 * (scale w) ^ Nc + c2 * (scale w) ^ Nc + c3 * (scale w) ^ Nc
            = (c1 + c2 + c3) * (scale w) ^ Nc := by ring
        linarith [e1, e2, e3]


/-- The seminorm bound for the punctured layer `E_F₂`, in `scale`-form. -/
lemma E_F₂_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : Work.Asymptotics.EFlat ℓ d) {N₀ C N M : ℝ} (hN₀ : 0 ≤ N₀) (hC : 0 < C)
    (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hwin : ∀ (w : ℍ) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon → 0 < t →
      t ≤ (scale w) ^ N₀ → ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ (w : ℍ) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon → (scale w) ^ N₀ ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t)))
    (hGcusp : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.KEpsilon
      (Gcusp ℓ d i j))
    (k l : ℕ) :
    ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_F₂ ℓ d N₀ w s) r‖
        ≤ c * (scale w) ^ N' := by
  obtain ⟨c, Nc, hc, hb⟩ := E_Expr_bound ℓ d hd hflat hN₀ hC hN hM hwin htail hGcusp k l
  refine ⟨c, Nc, hc, ?_⟩
  intro w hw r
  have hcN : (0:ℝ) ≤ c * (scale w) ^ Nc := mul_nonneg hc (Real.rpow_nonneg (scale_pos w).le Nc)
  by_cases hR : r ≠ 0 ∧ E_R ℓ d w r
  · rcases hR with ⟨hr0, hRw⟩
    have hev : (fun s : ℝ => E_F₂ ℓ d N₀ w s) =ᶠ[𝓝 r] (fun s : ℝ => E_Expr ℓ d N₀ w s) := by
      rcases hRw with hlt | hz
      · have hnb : ∀ᶠ s in 𝓝 r, 2 < s ^ 2 :=
          (isOpen_lt continuous_const (by fun_prop : Continuous fun s : ℝ => s ^ 2)).mem_nhds hlt
        filter_upwards [hnb, isOpen_ne.mem_nhds hr0] with s hs2 hs0
        exact E_F₂_of_R ℓ d N₀ w s ⟨hs0, Or.inl hs2⟩
      · filter_upwards [isOpen_ne.mem_nhds hr0] with s hs0
        exact E_F₂_of_R ℓ d N₀ w s ⟨hs0, Or.inr hz⟩
    rw [iteratedDeriv_congr_of_eventuallyEq hev l]
    exact hb w hw r hRw
  · rcases eq_or_ne r 0 with h0 | hr0
    · subst h0
      by_cases hz : E_R ℓ d w 0
      · -- the contact point `r = 0` with `G 1 j = 0`: puncture argument
        have hz' : Gcusp ℓ d 1 0 w = 0 ∧ Gcusp ℓ d 1 1 w = 0 := by
          rcases hz with h | h
          · exact absurd h (by norm_num)
          · exact h
        rcases l with _ | l'
        · rw [iteratedDeriv_zero, E_F₂_of_not_R ℓ d N₀ w 0 hR, norm_zero, mul_zero]
          exact hcN
        · have hF₂eq : (fun s : ℝ => E_F₂ ℓ d N₀ w s)
              = fun s : ℝ => if s = 0 then 0 else E_Expr ℓ d N₀ w s := by
            funext s
            by_cases hs : s = 0
            · subst hs; rw [E_F₂_of_not_R ℓ d N₀ w 0 hR]; simp
            · rw [E_F₂_of_R ℓ d N₀ w s ⟨hs, Or.inr hz'⟩]; simp [hs]
          rw [hF₂eq]
          rw [punctured_iteratedDeriv (E_Expr_neg ℓ d N₀ w)
            ((E_contDiff_omega_Expr ℓ d hd hflat hN₀ hC hN hM hw
              (fun t ht0 htB => hwin w t hw ht0 htB)
              (fun t htB => htail w t hw htB)).differentiable (by simp)) (l' + 1) (by omega)]
          exact hb w hw 0 hz
      · -- `G 1 j ≠ 0`: the layer vanishes on a neighbourhood of `0`
        have hnb : ∀ᶠ s in 𝓝 (0:ℝ), ¬ (s ≠ 0 ∧ E_R ℓ d w s) := by
          have hnb2 : ∀ᶠ s in 𝓝 (0:ℝ), s ^ 2 < 2 :=
            (isOpen_lt (by fun_prop : Continuous fun s : ℝ => s ^ 2) continuous_const).mem_nhds
              (by norm_num)
          filter_upwards [hnb2] with s hs
          rintro ⟨_, hsR⟩
          rcases hsR with h | h
          · exact absurd hs (not_lt.mpr (le_of_lt h))
          · exact hz (Or.inr h)
        have hev : (fun s : ℝ => E_F₂ ℓ d N₀ w s) =ᶠ[𝓝 (0:ℝ)] (fun _ => (0:ℂ)) := by
          filter_upwards [hnb] with s hs
          exact E_F₂_of_not_R ℓ d N₀ w s hs
        rw [iteratedDeriv_congr_of_eventuallyEq hev l, iteratedDeriv_zeroFun]
        simp only [norm_zero, mul_zero]
        exact hcN
    · have hRw : ¬ E_R ℓ d w r := fun hE => hR ⟨hr0, hE⟩
      rw [E_R_iff] at hRw
      obtain ⟨hnot2, hz⟩ := not_or.mp hRw
      have hr2 : r ^ 2 ≤ 2 := not_lt.mp hnot2
      rcases lt_or_eq_of_le hr2 with hlt2 | heq2
      · have hnb : ∀ᶠ s in 𝓝 r, ¬ (s ≠ 0 ∧ E_R ℓ d w s) := by
          have hnb2 : ∀ᶠ s in 𝓝 r, s ^ 2 < 2 :=
            (isOpen_lt (by fun_prop : Continuous fun s : ℝ => s ^ 2) continuous_const).mem_nhds hlt2
          filter_upwards [hnb2] with s hs
          rintro ⟨_, hsR⟩
          rcases hsR with h | h
          · exact absurd hs (not_lt.mpr (le_of_lt h))
          · exact hz h
        have hev : (fun s : ℝ => E_F₂ ℓ d N₀ w s) =ᶠ[𝓝 r] (fun _ => (0:ℂ)) := by
          filter_upwards [hnb] with s hs
          exact E_F₂_of_not_R ℓ d N₀ w s hs
        rw [iteratedDeriv_congr_of_eventuallyEq hev l, iteratedDeriv_zeroFun]
        simp only [norm_zero, mul_zero]
        exact hcN
      · -- the threshold points `r = ±√2`
        rcases l with _ | l'
        · rw [iteratedDeriv_zero, E_F₂_of_not_R ℓ d N₀ w r hR, norm_zero, mul_zero]
          exact hcN
        · have h2sq : r ^ 2 = (Real.sqrt 2) ^ 2 := by
            rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; exact heq2
          have hsqrt2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
          rcases (sq_eq_sq_iff_eq_or_eq_neg (a := r) (b := Real.sqrt 2)).mp h2sq with hsq | hsq
          · subst hsq
            have hzero : ∀ y ∈ Set.Ioo (0:ℝ) (Real.sqrt 2), E_F₂ ℓ d N₀ w y = 0 := by
              intro y hy
              refine E_F₂_of_not_R ℓ d N₀ w y ?_
              rintro ⟨_, hyR⟩
              rcases hyR with h | h
              · have hy2 : y ^ 2 < 2 := by
                  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hy.1, hy.2]
                exact absurd hy2 (not_lt.mpr (le_of_lt h))
              · exact hz h
            rw [iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left hsqrt2 hzero l']
            simp only [norm_zero, mul_zero]
            exact hcN
          · subst hsq
            have hzero : ∀ y ∈ Set.Ioo (-Real.sqrt 2) (0:ℝ), E_F₂ ℓ d N₀ w y = 0 := by
              intro y hy
              refine E_F₂_of_not_R ℓ d N₀ w y ?_
              rintro ⟨_, hyR⟩
              rcases hyR with h | h
              · have hy2 : y ^ 2 < 2 := by
                  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hy.1, hy.2]
                exact absurd hy2 (not_lt.mpr (le_of_lt h))
              · exact hz h
            rw [iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right
              (by linarith [hsqrt2] : -Real.sqrt 2 < (0:ℝ)) hzero l']
            simp only [norm_zero, mul_zero]
            exact hcN

/-- **The seminorm bound for `K` on the cusp-`0` neighbourhood `E = S(𝓕)`.**

This is the cusp-`0` form of CKMRV Proposition 4.6: from the flatness of the kernel at the cusp
`0` (`EFlat`) and the two regimes of the cusp-`i∞` expansion of `z ↦ K(w,z)` (`ERegimes`) at the
common threshold `(scale w)^{N₀}`, the `r`-seminorms of the contour transform
`Work.Kernels.kernelTransform (Kfun ℓ d) w ·` grow at most moderately in `w`. -/
theorem E_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : Work.Asymptotics.EFlat ℓ d) (hreg : Work.Asymptotics.ERegimes ℓ d) :
    Work.Asymptotics.SeminormK_E ℓ d := by

  obtain ⟨N₀, C, N, M, hN₀, hC, hN, hM, hwin, htail⟩ := hreg
  have hGcusp : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.KEpsilon
      (Gcusp ℓ d i j) := fun i j => (GcuspInP ℓ d i j).mono KEpsilon_subset_DomainD
  have hB1 : ∀ w : ℍ, 1 ≤ E_Bw N₀ w := fun w => by
    rw [E_Bw]; exact Real.one_le_rpow (one_le_scale w) hN₀
  refine E_kernelTransform_seminorm_of_layer0 ℓ d hd (E_F₂ ℓ d N₀) ?_ ?_ ?_
  · -- agreement at `r = 0`
    intro w hw
    rw [E_F₂_of_not_R ℓ d N₀ w 0 (fun h => h.1 rfl), Work.Kernels.kernelTransform]
    simp
  · -- agreement on the convergence region
    intro w r hw hInt
    by_cases hr : r = 0
    · subst hr
      rw [E_F₂_of_not_R ℓ d N₀ w 0 (fun h => h.1 rfl), Work.Kernels.kernelTransform]
      simp
    · by_cases hR : E_R ℓ d w r
      · rw [E_F₂_of_R ℓ d N₀ w r ⟨hr, hR⟩]
        exact E_F2_agreement ℓ d hd N₀ C N M hN₀ hC hN hM hwin htail w r hw hr hInt
      · exfalso
        rw [E_R_iff] at hR
        obtain ⟨hnot, hz⟩ := not_or.mp hR
        have hLpos : 0 < Real.pi * r ^ 2 := by positivity
        have hmu : Real.pi * r ^ 2 - 2 * Real.pi ≤ 0 := by
          nlinarith [Real.pi_pos, not_lt.mp hnot]
        have hAexp_int := E_integrableOn_Aexp_exp ℓ d hd hC hN hM (hB1 w)
          (fun t ht => htail w t hw ht) hInt
        set L : ℝ := Real.pi * r ^ 2 with hLdef
        have hAexp_int' : MeasureTheory.IntegrableOn (fun t : ℝ => Aexp (Gcusp ℓ d) w t
            * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (E_Bw N₀ w)) := by
          refine MeasureTheory.IntegrableOn.congr_fun hAexp_int (fun t _ => ?_) measurableSet_Ioi
          have harg : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = -(L : ℂ) * (t : ℂ) := by
            rw [hLdef]; push_cast; ring
          rw [← harg]
        have hP_int : MeasureTheory.IntegrableOn (fun t : ℝ =>
            (Gcusp ℓ d 0 0 w + (t : ℂ) * Complex.I * Gcusp ℓ d 0 1 w)
              * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (E_Bw N₀ w)) := by
          refine (integrableOn_affine_mul_exp_neg_mul_complex L ?_ _ _).mono_set
            (Set.Ioi_subset_Ioi (hB1 w))
          rw [hLdef]; positivity
        have hPQ := MeasureTheory.IntegrableOn.congr_fun hAexp_int' (fun t _ =>
          (E_Aexp_exp_decomp (Gcusp ℓ d) w L t)) measurableSet_Ioi
        have hQ_int := hPQ.sub hP_int
        have hQ_int' : MeasureTheory.IntegrableOn (fun t : ℝ =>
            (Gcusp ℓ d 1 0 w + (t : ℂ) * Complex.I * Gcusp ℓ d 1 1 w)
              * Complex.exp (-((L - 2 * Real.pi : ℝ) : ℂ) * (t : ℂ)))
            (Set.Ioi (E_Bw N₀ w)) :=
          MeasureTheory.IntegrableOn.congr_fun hQ_int (fun t _ => by
            simp only [Pi.sub_apply]; ring) measurableSet_Ioi
        exact hz (E_eq_zero_of_integrableOn_affine_exp_Ioi hmu (E_Bw N₀ w) hQ_int')
  · -- the seminorm bound
    intro k l
    obtain ⟨c, N', hc, hb⟩ := E_F₂_bound ℓ d hd hflat hN₀ hC hN hM hwin htail hGcusp k l
    refine ⟨c * 3 ^ max N' 0, max N' 0, c * 3 ^ max N' 0, max N' 0,
      by positivity, le_max_right _ _, by positivity, le_max_right _ _, ?_⟩
    intro w r hw
    have h1 := hb w hw r
    have hM0 : (0:ℝ) ≤ max N' 0 := le_max_right _ _
    have hle : N' ≤ max N' 0 := le_max_left _ _
    have e1 : (scale w) ^ N' ≤ (scale w) ^ (max N' 0) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_scale w) hle
    have e2 : c * (scale w) ^ N' ≤ c * (scale w) ^ (max N' 0) :=
      mul_le_mul_of_nonneg_left e1 hc
    have e3 := paperLayer_scale_rpow_le (τ := w) hM0
    refine le_trans h1 ?_
    calc c * (scale w) ^ N' ≤ c * (scale w) ^ (max N' 0) := e2
      _ ≤ c * (3 ^ (max N' 0) * ((w.im) ^ (-(max N' 0)) + ‖(w : ℂ)‖ ^ (max N' 0))) :=
          mul_le_mul_of_nonneg_left e3 hc
      _ = c * 3 ^ (max N' 0) * (w.im) ^ (-(max N' 0))
          + c * 3 ^ (max N' 0) * ‖(w : ℂ)‖ ^ (max N' 0) := by ring

end Work.Asymptotics
