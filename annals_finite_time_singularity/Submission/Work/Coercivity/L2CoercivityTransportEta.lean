import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Coercivity.L12_z_byparts
import Submission.Work.Coercivity.EfEta_eq_wip
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.sq_integral_mul_le
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Spaces.sin_rpow_le_majorant_pi
import Submission.Work.Spaces.integrableOn_majorant_rpow
import Submission.Work.Spaces.integral_majorant_rpow
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HProductRule_Zsummand
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Coercivity.L12f_continuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Numerical bounds for the angular weight `sin(2θ)^{-η}` -/

/-- On `Iθ`, `sin θ · cos²θ ≤ 1`. -/
theorem sin_mul_cos_sq_le_one {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
  have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    have h := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
    simpa using h
  have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  nlinarith

/-- `(1/2)^{99/100} ≤ 3/5`. -/
theorem half_rpow_eta_le : ((1 : ℝ) / 2) ^ Spaces.eta ≤ 3 / 5 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have heq : ((1 : ℝ) / 2) ^ Spaces.eta = (2 : ℝ) ^ (-Spaces.eta) := by
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (x := 2) (le_of_lt h2) Spaces.eta,
      ← Real.rpow_neg (x := 2) (le_of_lt h2) Spaces.eta]
  rw [heq]
  have hstep : (2 : ℝ) ^ (-Spaces.eta) ≤ (2 : ℝ) ^ (-(4 / 5 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    rw [Spaces.eta]; norm_num
  refine hstep.trans ?_
  have hiff := Real.rpow_le_rpow_iff (x := (2 : ℝ) ^ (-(4 / 5 : ℝ))) (y := (3 : ℝ) / 5)
    (z := (5 : ℝ)) (by positivity) (by norm_num) (by norm_num)
  rw [← hiff]
  have hpow : ((2 : ℝ) ^ (-(4 / 5 : ℝ))) ^ (5 : ℝ) = 1 / 16 := by
    rw [(Real.rpow_mul (x := 2) (le_of_lt h2) (-(4 / 5 : ℝ)) (5 : ℝ)).symm,
      show (-(4 / 5 : ℝ)) * 5 = -4 by norm_num,
      Real.rpow_neg (x := 2) (le_of_lt h2)]
    norm_num
  rw [hpow]
  norm_num

/-- The angular weight estimate `∫_{Iθ} sin(2θ)^{-η} ≤ 189`, from the Jordan majorant
`sin(2θ)^{-η} ≤ (π/4)^η (θ^{-η} + (π/2 - θ)^{-η})` whose integral over `Iθ` is
`π (1/2)^η /(1-η) = 100 π (1/2)^η ≤ 100 · 3.15 · (3/5) = 189`. -/
theorem etaWeight_integral_le :
    ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta) ≤ 189 := by
  have hη0 : 0 < Spaces.eta := by rw [Spaces.eta]; norm_num
  have hη1 : Spaces.eta < 1 := by rw [Spaces.eta]; norm_num
  have hmaj : IntegrableOn (fun θ : ℝ => (Real.pi / 4) ^ Spaces.eta *
      (θ ^ (-Spaces.eta) + (Real.pi / 2 - θ) ^ (-Spaces.eta))) Spaces.Iθ :=
    Work.Spaces.integrableOn_majorant_rpow Spaces.eta hη0 hη1
  have hval : (∫ θ in Spaces.Iθ, (Real.pi / 4) ^ Spaces.eta *
      (θ ^ (-Spaces.eta) + (Real.pi / 2 - θ) ^ (-Spaces.eta)))
      = Real.pi * (1 / 2) ^ Spaces.eta / (1 - Spaces.eta) :=
    Work.Spaces.integral_majorant_rpow Spaces.eta hη0 hη1
  have hpt : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta))
      ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ : ℝ => (Real.pi / 4) ^ Spaces.eta *
        (θ ^ (-Spaces.eta) + (Real.pi / 2 - θ) ^ (-Spaces.eta))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Work.Spaces.sin_rpow_le_majorant_pi Spaces.eta θ hη0 hθ
  have hnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have h₁ : ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta)
      ≤ Real.pi * (1 / 2) ^ Spaces.eta / (1 - Spaces.eta) := by
    calc ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ ∫ θ in Spaces.Iθ, (Real.pi / 4) ^ Spaces.eta *
            (θ ^ (-Spaces.eta) + (Real.pi / 2 - θ) ^ (-Spaces.eta)) :=
          integral_mono_of_nonneg hnn hmaj hpt
      _ = Real.pi * (1 / 2) ^ Spaces.eta / (1 - Spaces.eta) := hval
  have h2 : Real.pi * (1 / 2) ^ Spaces.eta / (1 - Spaces.eta) ≤ 189 := by
    have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
    have hhalf : (1 / 2 : ℝ) ^ Spaces.eta ≤ 3 / 5 := half_rpow_eta_le
    have hden : (1 : ℝ) - Spaces.eta = 1 / 100 := by rw [Spaces.eta]; norm_num
    rw [hden]
    have hmul : Real.pi * (1 / 2) ^ Spaces.eta ≤ 3.15 * (3 / 5) :=
      mul_le_mul hpi hhalf (by positivity) (by norm_num)
    have hdiv : Real.pi * (1 / 2) ^ Spaces.eta / (1 / 100)
        = 100 * (Real.pi * (1 / 2) ^ Spaces.eta) := by ring
    rw [hdiv]
    nlinarith [hmul]
  linarith

/-- `∫_{Iθ} (Γ(θ)/c(α))² sin(2θ)^{-η} ≤ 18900`: pointwise `Γ ≤ 1` and `c ≥ 1/10`
give `(Γ/c)² ≤ 100`, and the angular integral is `≤ 189`. -/
theorem Gam_div_c_sq_eta_integral_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) ≤ 18900 := by
  have hη0 : 0 < Spaces.eta := by rw [Spaces.eta]; norm_num
  have hη1 : Spaces.eta < 1 := by rw [Spaces.eta]; norm_num
  have hc : (1 : ℝ) / 10 ≤ Spaces.c α := (Spaces.c_bounds α hα hα1).1
  have hcp : 0 < Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hsinle : ∀ θ ∈ Spaces.Iθ, (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    intro θ hθ
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hpt : ∀ θ ∈ Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ 100 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    intro θ hθ
    have hG1 : Spaces.Gam α θ ≤ 1 := by
      rw [Spaces.Gam]
      exact Real.rpow_le_one
        (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _))
        (sin_mul_cos_sq_le_one hθ) (le_of_lt (by positivity : (0:ℝ) < α / 3))
    have hG0 : 0 ≤ Spaces.Gam α θ := by
      rw [Spaces.Gam]
      exact Real.rpow_nonneg (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)) _
    have hsq : (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 100 := by
      rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < (Spaces.c α) ^ 2)]
      have h1 : Spaces.Gam α θ ^ 2 ≤ 1 := by
        have := mul_self_le_mul_self hG0 hG1
        nlinarith [this]
      have h2 : (1:ℝ) ≤ 100 * (Spaces.c α) ^ 2 := by
        have := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/10) hc
        nlinarith [this]
      linarith
    exact mul_le_mul_of_nonneg_right hsq (hsinle θ hθ)
  have hInt2 : IntegrableOn (fun θ : ℝ => 100 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ :=
    ((Work.Spaces.sin_two_rpow (-Spaces.eta) (by linarith) (by linarith)).1).const_mul 100
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (volume.restrict Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    unfold Spaces.Gam
    fun_prop
  have hIntL : IntegrableOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ := by
    refine Integrable.mono' hInt2 hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hsinle θ hθ))]
    exact hpt θ hθ
  have hmono : ∫ θ in Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      ≤ ∫ θ in Spaces.Iθ, 100 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    refine integral_mono_of_nonneg ?_ hInt2 ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (hsinle θ hθ)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hpt θ hθ
  calc ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      ≤ ∫ θ in Spaces.Iθ, 100 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := hmono
    _ = 100 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta) := integral_const_mul _ _
    _ ≤ 100 * 189 := by
        have := etaWeight_integral_le; linarith
    _ = 18900 := by norm_num

/-- For `0 ≤ s ≤ 1` and `η ≤ γ`, the negative powers satisfy `s^{-η} ≤ s^{-γ}`. -/
theorem rpow_neg_eta_le_gam {s γ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hγ : Spaces.eta ≤ γ) :
    s ^ (-Spaces.eta) ≤ s ^ (-γ) := by
  have hηne : (-Spaces.eta) ≠ 0 := by rw [Spaces.eta]; norm_num
  have hγne : (-γ) ≠ 0 := by rintro h; rw [neg_eq_zero] at h; rw [h] at hγ; rw [Spaces.eta] at hγ; norm_num at hγ
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow hηne, Real.zero_rpow hγne]
  · have h1 : s ^ (-Spaces.eta) = s⁻¹ ^ Spaces.eta := by
      rw [Real.inv_rpow (le_of_lt h), Real.rpow_neg (le_of_lt h)]
    have h2 : s ^ (-γ) = s⁻¹ ^ γ := by
      rw [Real.inv_rpow (le_of_lt h), Real.rpow_neg (le_of_lt h)]
    rw [h1, h2]
    exact Real.rpow_le_rpow_of_exponent_le ((one_le_inv₀ h).mpr hs1) hγ

/-- The product of the restrictions of Lebesgue measure is the restriction to the product set. -/
theorem prod_restrict_eq (s t : Set ℝ) :
    (volume.restrict s).prod (volume.restrict t) = volume.restrict (s ×ˢ t) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- The open quadrant is contained in the smoothness neighbourhood `nbhU`. -/
theorem Qd_subset_nbhU' : Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi/2) ⊆ Work.Spaces.nbhU := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact Work.Spaces.mem_nbhU (Set.mem_Ici.mpr (le_of_lt hz))
    (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-- `f` and its angular derivative `D_θ f` are a.e. strongly measurable on the domain,
for a function smooth on a neighbourhood of the closed quadrant. -/
theorem aesm_f_Dth {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
        (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) ∧
      AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2)
        (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) := by
  have cont_f : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) :=
    hsm.continuousOn.mono Qd_subset_nbhU'
  have cont_th : ContinuousOn (fun p : ℝ × ℝ => Spaces.pth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) :=
    ((Work.Spaces.contDiffOn_uncurry_pth (V := Work.Spaces.nbhU) Work.Spaces.isOpen_nbhU hsm).continuousOn).mono
      Qd_subset_nbhU'
  have cont_Dth : ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) := by
    show ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Spaces.pth f p.1 p.2) _
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).mul cont_th
  refine ⟨?_, ?_⟩
  · have h := Work.Spaces.aesm_of_continuousOn_Qd _ cont_f
    rwa [prod_restrict_eq] at h
  · have h := Work.Spaces.aesm_of_continuousOn_Qd _ cont_Dth
    rwa [prod_restrict_eq] at h

/-- `L₁₂(f)` (a function of `z` alone) is a.e. strongly measurable on the domain when it is
continuous on `(0,∞)`. -/
theorem aesm_L12f {f : ℝ → ℝ → ℝ} (hL : ContinuousOn (fun z : ℝ => L12f f z) (Set.Ioi 0)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => L12f f p.1)
      (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) := by
  have cont_L : ContinuousOn (fun p : ℝ × ℝ => L12f f p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) :=
    hL.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have h := Work.Spaces.aesm_of_continuousOn_Qd _ cont_L
  rwa [prod_restrict_eq] at h

/-- `(D_θ f)² w² sin(2θ)^{-η}` is integrable on the domain: it is dominated by the
`intDthGam` integrand, since `s^{-η} ≤ s^{-γ}` for `s = sin(2θ) ∈ [0,1]` and `γ = gam α ≥ η`. -/
theorem etaDth_sq_integrable (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        Spaces.Dth f z θ ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
  have hγ : Spaces.eta ≤ Spaces.gam α := by rw [Spaces.eta, Spaces.gam]; linarith
  have hmem : ∀ᵐ p ∂(volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)), p ∈ Spaces.Iz ×ˢ Spaces.Iθ :=
    ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  have hAESM : AEStronglyMeasurable
      (Function.uncurry (fun z θ =>
        Spaces.Dth f z θ ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
      (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) := by
    have h1 : AEStronglyMeasurable
        (Function.uncurry (fun z θ =>
          Spaces.Dth f z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.gam α)))
        (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) := hi.intDthGam.aestronglyMeasurable
    have h2 : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Spaces.gam α - Spaces.eta)) := by
      fun_prop
    refine (h1.mul h2.aestronglyMeasurable).congr ?_
    filter_upwards [hmem] with p hp
    obtain ⟨hz, hθ⟩ := hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Pi.mul_apply]
    by_cases hs : Real.sin (2 * θ) = 0
    · rw [hs, Real.zero_rpow (by norm_num [Spaces.eta] : (-Spaces.eta) ≠ 0),
        Real.zero_rpow (by norm_num [Spaces.eta, Spaces.gam]; linarith : (-Spaces.gam α) ≠ 0),
        Real.zero_rpow (by norm_num [Spaces.eta, Spaces.gam]; linarith : (Spaces.gam α - Spaces.eta) ≠ 0)]
      ring
    · have hspos : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) (Ne.symm hs)
      rw [show Spaces.Dth f z θ * Spaces.Dth f z θ = Spaces.Dth f z θ ^ 2 from by ring]
      calc Spaces.Dth f z θ ^ 2 * Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-Spaces.gam α)
            * Real.sin (2 * θ) ^ (Spaces.gam α - Spaces.eta)
          = Spaces.Dth f z θ ^ 2 * Spaces.w z ^ 2
              * (Real.sin (2 * θ) ^ (-Spaces.gam α) * Real.sin (2 * θ) ^ (Spaces.gam α - Spaces.eta)) := by
            ring
        _ = Spaces.Dth f z θ ^ 2 * Spaces.w z ^ 2
              * Real.sin (2 * θ) ^ (-Spaces.gam α + (Spaces.gam α - Spaces.eta)) := by
            rw [Real.rpow_add hspos]
        _ = Spaces.Dth f z θ ^ 2 * Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-Spaces.eta) := by
            rw [show -Spaces.gam α + (Spaces.gam α - Spaces.eta) = -Spaces.eta by ring]
  refine Integrable.mono' hi.intDthGam hAESM ?_
  filter_upwards [hmem] with p hp
  obtain ⟨hz, hθ⟩ := hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry_apply_pair]
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hle : (Real.sin (2 * θ)) ^ (-Spaces.eta) ≤ (Real.sin (2 * θ)) ^ (-Spaces.gam α) :=
    rpow_neg_eta_le_gam hs0 hs1 hγ
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg hs0 _)),
    show Spaces.Dth f z θ * Spaces.Dth f z θ = Spaces.Dth f z θ ^ 2 from by ring]
  exact mul_le_mul_of_nonneg_left hle (by positivity)


/-- `2|ab| ≤ a² + b²`. -/
theorem two_mul_abs_mul_le (a b : ℝ) : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]


/-- Pointwise AM-GM estimate for the transport term: for `ρ ≥ 0` and `z ≥ 0`,
`|3abρ/(1+z)| ≤ (3/2)(a²ρ + b²ρ)`. -/
theorem trf_pointwise (a b ρ z : ℝ) (hρ : 0 ≤ ρ) (hz : 0 ≤ z) :
    |3 * a / (1 + z) * b * ρ| ≤ (3 / 2) * (a ^ 2 * ρ + b ^ 2 * ρ) := by
  have h1z : 0 < 1 + z := by linarith
  have habs : |3 * a / (1 + z) * b * ρ| = 3 * |a| * |b| * ρ / (1 + z) := by
    simp only [abs_mul, abs_div, abs_of_pos h1z, abs_of_nonneg hρ,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
    ring
  rw [habs]
  have hble : 3 * |a| * |b| * ρ / (1 + z) ≤ 3 * |a| * |b| * ρ := by
    rw [div_le_iff₀ h1z]
    have h1 : 0 ≤ 3 * |a| * |b| * ρ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg a)) (abs_nonneg b)) hρ
    nlinarith [mul_nonneg h1 hz]
  have hamgm : 3 * |a| * |b| * ρ ≤ (3 / 2) * (a ^ 2 * ρ + b ^ 2 * ρ) := by
    have hkey := mul_le_mul_of_nonneg_left (two_mul_abs_mul_le a b) (by positivity : (0:ℝ) ≤ 3 / 2 * ρ)
    nlinarith [hkey]
  linarith

/-- Pointwise estimate for the `L₁₂` term: for `|C| ≤ 10` and `a·b` with the weight split,
`|Cab| ≤ 5(a² + b²)`. -/
theorem psiA_pointwise (C a b : ℝ) (hC : |C| ≤ 10) :
    |C * a * b| ≤ 5 * (a ^ 2 + b ^ 2) := by
  have h1 : |C * a * b| = |C| * |a| * |b| := by rw [abs_mul, abs_mul]
  rw [h1]
  have h3 : |C| * |a| * |b| ≤ 10 * |a| * |b| := by
    have h := mul_le_mul_of_nonneg_right hC (by positivity : (0:ℝ) ≤ |a| * |b|)
    linarith [h]
  have h2 : 10 * |a| * |b| ≤ 5 * (a ^ 2 + b ^ 2) := by
    have := two_mul_abs_mul_le a b
    linarith
  linarith

/-- Pointwise AM-GM estimate for the projector term: `|a b| ≤ (a² + b²)/2`. -/
theorem gPsi_pointwise (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h := two_mul_abs_mul_le a b
  rw [abs_mul]
  linarith

/-- `(D_θ f) · f · w² · sin(2θ)^{-η}/(1+z)` is integrable on the domain: it is dominated by
`(3/2)((D_θ f)² w² sin^{-η} + f² w² sin^{-η})`. -/
theorem etaW_Trf_integrable (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (hf : IBP f) (hi : CoerciveData α f)
    (hD : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        Spaces.Dth f z θ ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        3 * Spaces.Dth f z θ / (1 + z) * f z θ * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
  have hmem : ∀ᵐ p ∂(volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)), p ∈ Spaces.Iz ×ˢ Spaces.Iθ :=
    ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (3 / 2) * (Spaces.Dth f p.1 p.2 ^ 2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta)
        + f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta)))
      (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) :=
    (hD.add hi.intFeta).const_mul (3 / 2)
  refine Integrable.mono' hdom ?_ ?_
  · have hfac : (Function.uncurry (fun z θ =>
        3 * Spaces.Dth f z θ / (1 + z) * f z θ * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
        = (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2) * (fun p : ℝ × ℝ => f p.1 p.2)
          * (fun p : ℝ × ℝ => 3 * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)
              / (1 + p.1)) := by
      funext p
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair, Pi.mul_apply]
      ring
    rw [hfac]
    have hw : Measurable (fun p : ℝ × ℝ =>
        3 * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta) / (1 + p.1)) := by
      unfold Spaces.w
      fun_prop
    exact ((aesm_f_Dth hf.smooth).2.mul (aesm_f_Dth hf.smooth).1).mul hw.aestronglyMeasurable
  · filter_upwards [hmem] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    simp only [Function.uncurry_apply_pair]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hρ : 0 ≤ Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    have hkey := trf_pointwise (Spaces.Dth f z θ) (f z θ)
      (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) z hρ (Set.mem_Ici.mp hz)
    rw [Real.norm_eq_abs]
    have hgoal : |3 * Spaces.Dth f z θ / (1 + z) * f z θ * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta)|
        = |3 * Spaces.Dth f z θ / (1 + z) * f z θ
          * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))| := by
      congr 1
      ring
    rw [hgoal]
    refine hkey.trans (le_of_eq ?_)
    ring



/-- `(s^{-η/2})² = s^{-η}` for `s ≥ 0`. -/
theorem rpow_half_sq (s : ℝ) (hs : 0 ≤ s) :
    (s ^ (-Spaces.eta / 2)) ^ 2 = s ^ (-Spaces.eta) := by
  rw [sq]
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow (by norm_num [Spaces.eta] : (-Spaces.eta / 2) ≠ 0),
      Real.zero_rpow (by norm_num [Spaces.eta] : (-Spaces.eta) ≠ 0)]
    ring
  · rw [← Real.rpow_add h, show -Spaces.eta / 2 + -Spaces.eta / 2 = -Spaces.eta by ring]

/-- `(Γ/c)(w/z) L₁₂(f) f sin(2θ)^{-η}` is integrable on the domain: it is dominated by
`5((L₁₂(f)/z)² sin^{-η} + f² w² sin^{-η})`. -/
theorem etaW_psiA_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hi : CoerciveData α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        (Spaces.Gam α θ / Spaces.c α) * (Spaces.w z / z) * L12f f z * f z θ
          * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
  have hmem : ∀ᵐ p ∂(volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)), p ∈ Spaces.Iz ×ˢ Spaces.Iθ :=
    ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  have hLc : ContinuousOn (fun z : ℝ => L12f f z) (Set.Ioi 0) := L12f_continuousOn f hfH
  have hL2a : MeasureTheory.IntegrableOn (fun z : ℝ => (L12f f z / z) ^ 2) (Set.Ioi 0) := by
    have h := hfH.intA 1 (by norm_num)
    refine h.congr_fun (fun z _ => ?_) measurableSet_Ioi
    rw [div_pow]
    norm_num
  have hIzeq : volume.restrict Spaces.Iz = volume.restrict (Set.Ioi 0) := by
    rw [Spaces.Iz]
    exact (Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0:ℝ)))).symm
  have hL2 : MeasureTheory.IntegrableOn (fun z : ℝ => (L12f f z / z) ^ 2) Spaces.Iz := by
    change Integrable (fun z : ℝ => (L12f f z / z) ^ 2) (volume.restrict Spaces.Iz)
    rw [hIzeq]
    exact hL2a
  have hEta : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-Spaces.eta) (by rw [Spaces.eta]; norm_num)
      (by rw [Spaces.eta]; norm_num)).1
  have hprod : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (L12f f p.1 / p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    have h := hL2.mul_prod hEta
    rwa [prod_restrict_eq] at h
  have hdom : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      5 * ((L12f f p.1 / p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)
        + f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := (hprod.add hi.intFeta).const_mul 5
  refine Integrable.mono' hdom ?_ ?_
  · have hfac : (Function.uncurry (fun z θ =>
        (Spaces.Gam α θ / Spaces.c α) * (Spaces.w z / z) * L12f f z * f z θ
          * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
        = (fun p : ℝ × ℝ => L12f f p.1)
          * ((fun p : ℝ × ℝ => Spaces.Gam α p.2 / Spaces.c α * (Spaces.w p.1 / p.1)
                * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) * (fun p : ℝ × ℝ => f p.1 p.2)) := by
      funext p
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair, Pi.mul_apply]
      ring
    rw [hfac]
    have hw : Measurable (fun p : ℝ × ℝ => Spaces.Gam α p.2 / Spaces.c α * (Spaces.w p.1 / p.1)
        * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) := by
      unfold Spaces.Gam Spaces.w
      fun_prop
    exact (aesm_L12f hLc).mul (hw.aestronglyMeasurable.mul (aesm_f_Dth hf.smooth).1)
  · filter_upwards [hmem] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    simp only [Function.uncurry_apply_pair]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hC : |Spaces.Gam α θ / Spaces.c α| ≤ 10 := Gam_div_c_bound hα hα1 hθ
    have hsh : (Real.sin (2 * θ)) ^ (-Spaces.eta / 2) * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2)
        = (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      rw [← rpow_half_sq (Real.sin (2 * θ)) hs0, sq]
    have hkey := psiA_pointwise (Spaces.Gam α θ / Spaces.c α)
      ((L12f f z / z) * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2))
      (Spaces.w z * f z θ * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2)) hC
    have hkey2 : |(Spaces.Gam α θ / Spaces.c α) * (Spaces.w z / z) * L12f f z * f z θ
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)|
        = |(Spaces.Gam α θ / Spaces.c α)
            * ((L12f f z / z) * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2))
            * ((Spaces.w z * f z θ) * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2))| := by
      congr 1
      rw [← hsh]; ring
    rw [Real.norm_eq_abs, hkey2]
    refine hkey.trans (le_of_eq ?_)
    have hsq1 : ((L12f f z / z) * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2)) ^ 2
        = (L12f f z / z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      rw [mul_pow, rpow_half_sq _ hs0]
    have hsq2 : (Spaces.w z * f z θ * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2)) ^ 2
        = Spaces.w z ^ 2 * f z θ ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      rw [mul_pow, mul_pow, rpow_half_sq _ hs0]
    rw [hsq1, hsq2]
    ring


/-- `(Γ/c)(2z²/(1+z)³) f w² sin(2θ)^{-η}` is integrable on the domain: it is dominated by
`(1/2)(((Γ/c)(2z²/(1+z)³))² w² sin^{-η} + f² w² sin^{-η})`, the two pieces being a
`(θ,z)`-separated product and `CoerciveData.intFeta`. -/
theorem etaW_gPsi_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (hf : IBP f)
    (hi : CoerciveData α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
          * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
  have hmem : ∀ᵐ p ∂(volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)), p ∈ Spaces.Iz ×ˢ Spaces.Iθ :=
    ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  have hc : (1 : ℝ) / 10 ≤ Spaces.c α := (Spaces.c_bounds α hα hα1).1
  have hEta : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-Spaces.eta) (by rw [Spaces.eta]; norm_num)
      (by rw [Spaces.eta]; norm_num)).1
  have hθ2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ := by
    refine Integrable.mono' (Integrable.const_mul hEta 100) ?_ ?_
    · unfold Spaces.Gam
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
      have hG1 : Spaces.Gam α θ ≤ 1 := by
        rw [Spaces.Gam]
        exact Real.rpow_le_one (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)) (sin_mul_cos_sq_le_one hθ)
          (le_of_lt (by positivity : (0:ℝ) < α / 3))
      have hG0 : 0 ≤ Spaces.Gam α θ := by
        rw [Spaces.Gam]
        exact Real.rpow_nonneg (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)) _
      have hsq : (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 100 := by
        rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < (Spaces.c α) ^ 2)]
        have h1 : Spaces.Gam α θ ^ 2 ≤ 1 := by
          have := mul_self_le_mul_self hG0 hG1
          nlinarith [this]
        have h2 : (1:ℝ) ≤ 100 * (Spaces.c α) ^ 2 := by
          have := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/10) hc
          nlinarith [this]
        linarith
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)
  have hz2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2) Spaces.Iz := by
    refine Integrable.mono' (Integrable.const_mul integrable_Iz_one_div_sq 4) ?_ ?_
    · unfold Spaces.w
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      have hz0 : (0:ℝ) ≤ z := Set.mem_Ici.mp hz
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rcases eq_or_ne z 0 with h | h
      · rw [h]
        norm_num
      · have hkey : (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2
            = 4 * (1 / (1 + z) ^ 2) := by
          rw [Spaces.w]
          field_simp
          ring
        rw [hkey]
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      ((Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))
        * ((2 * p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 * Spaces.w p.1 ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    have h := hz2.mul_prod hθ2
    rw [prod_restrict_eq] at h
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry_apply_pair]
    ring
  have hdom : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (1 / 2) * (((Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))
        * ((2 * p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 * Spaces.w p.1 ^ 2)
        + f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := Integrable.const_mul (hprod.add hi.intFeta) (1 / 2)
  refine Integrable.mono' hdom ?_ ?_
  · have hfac : (Function.uncurry (fun z θ =>
        (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
          * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
        = (fun p : ℝ × ℝ => (Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
            * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)))
          * (fun p : ℝ × ℝ => f p.1 p.2) := by
      funext p
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair, Pi.mul_apply]
      ring
    rw [hfac]
    have hw : Measurable (fun p : ℝ × ℝ => (Spaces.Gam α p.2 / Spaces.c α)
        * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * (Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) := by
      unfold Spaces.Gam Spaces.w
      fun_prop
    exact hw.aestronglyMeasurable.mul (aesm_f_Dth hf.smooth).1
  · filter_upwards [hmem] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    simp only [Function.uncurry_apply_pair]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hρ : 0 ≤ Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    have hkey := gPsi_pointwise ((Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3))
      (f z θ)
    have h2 := mul_le_mul_of_nonneg_right hkey hρ
    rw [Real.norm_eq_abs,
      show (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)
          = ((Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ)
            * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) from by ring,
      abs_mul, abs_of_nonneg hρ]
    refine h2.trans (le_of_eq ?_)
    ring

/-- `wip` is additive in its first argument: the four-term linearity used to split the
`η`-weighted pairing of `𝓛_Γ^T` into its four pieces.  This is `wip_eq_integral_prod`
(the Fubini bridge) plus additivity of the Bochner integral on the product measure. -/
theorem wip_sub_add (ρ a₁ a₂ a₃ a₄ b : ℝ → ℝ → ℝ)
    (h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => a₁ z θ * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => a₂ z θ * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => a₃ z θ * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (h4 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => a₄ z θ * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    wip ρ (fun z θ => a₁ z θ - a₂ z θ - a₃ z θ + a₄ z θ) b
      = wip ρ a₁ b - wip ρ a₂ b - wip ρ a₃ b + wip ρ a₄ b := by
  set m : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hm
  have e1 : Integrable (fun p : ℝ × ℝ => a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
    integrableOn_prod h1
  have e2 : Integrable (fun p : ℝ × ℝ => a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
    integrableOn_prod h2
  have e3 : Integrable (fun p : ℝ × ℝ => a₃ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
    integrableOn_prod h3
  have e4 : Integrable (fun p : ℝ × ℝ => a₄ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
    integrableOn_prod h4
  have eS : Integrable (fun p : ℝ × ℝ =>
      (a₁ p.1 p.2 - a₂ p.1 p.2 - a₃ p.1 p.2 + a₄ p.1 p.2) * b p.1 p.2 * ρ p.1 p.2) m := by
    refine (((e1.sub e2).sub e3).add e4).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (a₁ z θ - a₂ z θ - a₃ z θ + a₄ z θ) * b z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    show Integrable (Function.uncurry (fun z θ =>
      (a₁ z θ - a₂ z θ - a₃ z θ + a₄ z θ) * b z θ * ρ z θ))
      (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ))
    rw [volume_restrict_prod, ← hm]
    exact eS
  have key : (∫ p, ((a₁ p.1 p.2 - a₂ p.1 p.2 - a₃ p.1 p.2 + a₄ p.1 p.2)
        * b p.1 p.2 * ρ p.1 p.2) ∂m)
      = (∫ p, a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 ∂m)
        - (∫ p, a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 ∂m)
        - (∫ p, a₃ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 ∂m)
        + (∫ p, a₄ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 ∂m) := by
    have h12 : Integrable (fun p : ℝ × ℝ => a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2
        - a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m := e1.sub e2
    have h123 : Integrable (fun p : ℝ × ℝ => (a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2
        - a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) - a₃ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) m :=
      h12.sub e3
    rw [show (fun p : ℝ × ℝ => (a₁ p.1 p.2 - a₂ p.1 p.2 - a₃ p.1 p.2 + a₄ p.1 p.2)
          * b p.1 p.2 * ρ p.1 p.2)
        = fun p => ((a₁ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 - a₂ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2)
          - a₃ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2) + a₄ p.1 p.2 * b p.1 p.2 * ρ p.1 p.2 from by
      funext p; ring]
    rw [integral_add h123 e4, integral_sub h12 e3, integral_sub e1 e2]
  rw [wip_eq_integral_prod _ _ _ hS, wip_eq_integral_prod _ _ _ h1, wip_eq_integral_prod _ _ _ h2,
    wip_eq_integral_prod _ _ _ h3, wip_eq_integral_prod _ _ _ h4]
  rw [hm] at key
  exact key

/-- The `L₁₂`-summand of the `𝓛`-decomposition, in the two forms in which it occurs:
`(2zΓ/(c(1+z)²))·w² = 2·(Γ/c)·(w/z)`, so `(2zΓ/(c(1+z)²))L₁₂(f)·f·w² = 2(Γ/c)(w/z)L₁₂(f)·f`
— the integrand of `etaW_psiA_integrable`, doubled. -/
theorem psiA_shift (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z * f z θ * Spaces.w z ^ 2
      = 2 * ((Spaces.Gam α θ / Spaces.c α) * (Spaces.w z / z) * L12f f z * f z θ) := by
  rcases eq_or_ne z 0 with h | h
  · subst h
    simp [Spaces.w]
  · rw [Spaces.w]
    field_simp

/-- `𝓛 f · f · w² sin^{-η}` is integrable on the domain.  On `Iz` the operator splits as
`𝓛 = 𝓛_Γ^T + (2zΓ/(c(1+z)²))L₁₂(f) + 3D_θf/(1+z) − (Γ/c)(2z²/(1+z)³)L₁₂(Transport f)(0)`,
and each of the four pieces is integrable against `f w² sin^{-η}` (`intLGTeta`,
`etaW_psiA_integrable` doubled via `psiA_shift`, `etaW_Trf_integrable`,
`etaW_gPsi_integrable`). -/
theorem Lf_etaW_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hi : CoerciveData α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => L f z θ * f z θ * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
  have hPsi := etaW_psiA_integrable α hα hα1 f hf hfH hi
  have hPsi2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      2 * ((Spaces.Gam α θ / Spaces.c α) * (Spaces.w z / z) * L12f f z * f z θ
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)))) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    Integrable.const_mul hPsi 2
  have hT := etaW_Trf_integrable α hα f hf hi (etaDth_sq_integrable α hα f hi)
  have hG' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * (L12f (Transport f) 0)
        * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine (Integrable.const_mul (etaW_gPsi_integrable α hα hα1 f hf hi)
      (L12f (Transport f) 0)).congr (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  refine ((hi.intLGTeta.add hPsi2).add hT).sub hG' |>.congr_fun (fun p hp => ?_)
    (measurableSet_Ici.prod measurableSet_Icc)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry_apply_pair, Pi.add_apply, Pi.sub_apply]
  have h3 : L f z θ = LGammaT α f z θ
      + (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z
      + 3 * Spaces.Dth f z θ / (1 + z)
      - (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * (L12f (Transport f) 0) := by
    simp only [L, LGammaT, LGamma, Proj, Transport, Spaces.Dz, Spaces.pz]
    ring_nf
  have h4 : 2 * ((Spaces.Gam α θ / Spaces.c α) * (Spaces.w z / z) * L12f f z * f z θ
      * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      = (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z * f z θ
        * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    linear_combination (Real.sin (2 * θ)) ^ (-Spaces.eta) * (psiA_shift α f z θ).symm
  rw [h3, h4]
  ring

/-- The `η`-weighted self-adjointness of `𝓛`: `⟨𝓛 f, f⟩ = ½⟨f, f⟩`.  This is the
`z`-integration by parts of §6 of the paper, with the angular weight `sin(2θ)^{-η}`. -/
theorem wip_Lf_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hi : CoerciveData α f) :
    wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) (L f) f
      = (1 / 2) * EfEta f := by
  have hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ ^ 2 * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine hi.intFeta.congr_fun (fun p hp => ?_) (measurableSet_Ici.prod measurableSet_Icc)
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  have h2 := wip_L_self f hf (fun θ => (Real.sin (2 * θ)) ^ (-Spaces.eta)) hint
    (Lf_etaW_integrable α hα hα1 f hf hfH hi)
  rw [h2, ← EfEta_eq_wip f]

/-- On `[π/12,π/6]` the product `ΓK` is at least `3/16`: there
`u = sinθ cos²θ ≥ (1/6)·(3/4) = 1/8` (`sinθ ≥ sin(π/12) ≥ (2/π)(π/12) = 1/6` by Jordan's
inequality and `cos²θ ≥ cos²(π/6) = 3/4`), while `ΓK = 3u^{1+α/3} ≥ 3u^{4/3}` and
`(1/8)^{4/3} = 1/16`. -/
theorem gamK_lower_twelfth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (π / 12) (π / 6)) : (3 : ℝ) / 16 ≤ Spaces.Gam α θ * Spaces.K θ := by
  have hsin1 : (1 / 6 : ℝ) ≤ Real.sin θ := by
    have h1 : Real.sin (π / 12) ≤ Real.sin θ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos]) hθ.1
    have h2 : (2 / Real.pi) * (π / 12) ≤ Real.sin (π / 12) :=
      Real.mul_le_sin (by positivity) (by linarith [Real.pi_pos])
    have h3 : (2 / Real.pi) * (π / 12) = 1 / 6 := by field_simp <;> norm_num
    linarith [h1, h2, h3]
  have hcos2 : (3 / 4 : ℝ) ≤ Real.cos θ ^ 2 := by
    have h1 : Real.cos (π / 6) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [Real.pi_pos]) hθ.2
    rw [Real.cos_pi_div_six] at h1
    have hsq : (Real.sqrt 3 / 2) ^ 2 = (3 / 4 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
    have h2 : (Real.sqrt 3 / 2) ^ 2 ≤ (Real.cos θ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    linarith [h2, hsq]
  have hsin0 : 0 ≤ Real.sin θ := by linarith [hsin1]
  have hcos0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := by positivity
  have hu : (1 / 8 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := by nlinarith [hsin1, hcos2, hcos0]
  have hu0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := le_trans (by norm_num) hu
  have hu1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 :=
    sin_mul_cos_sq_le_one ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hGK : Spaces.Gam α θ * Spaces.K θ
      = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 + 1) := by
    rw [Spaces.Gam, Spaces.K, Real.rpow_add' hu0 (by positivity : α / 3 + 1 ≠ 0), Real.rpow_one]
    ring
  have hrpow : ((1 : ℝ) / 8) ^ ((4 : ℝ) / 3) = 1 / 16 := by
    have h8 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    rw [← h8, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc (3 : ℝ) / 16 = 3 * ((1 : ℝ) / 8) ^ ((4 : ℝ) / 3) := by rw [hrpow]; norm_num
    _ ≤ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ ((4 : ℝ) / 3) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num) hu (by norm_num))
          (by norm_num)
    _ ≤ Spaces.Gam α θ * Spaces.K θ := by
        rw [hGK]
        have h := Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 (by positivity : (0 : ℝ) ≤ α / 3 + 1)
          (by linarith : α / 3 + 1 ≤ (4 : ℝ) / 3)
        linarith

/-- On `[π/6,π/3]` the product `ΓK` is at least `1/4`.  There
`u = sinθ cos²θ = (sinθ cosθ)·cosθ ≥ (√3/4)·(1/2) = √3/8 ≥ 1/6`
(`sinθcosθ = sin(2θ)/2` with `sin(2θ) ≥ √3/2` on `2θ ∈ [π/3,2π/3]`, and
`cosθ ≥ cos(π/3) = 1/2`), while `ΓK = 3u^{1+α/3} ≥ 3u^{4/3} ≥ 3(1/6)^{4/3} ≥ 1/4`. -/
theorem gamK_lower_third (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (π / 6) (π / 3)) : (1 : ℝ) / 4 ≤ Spaces.Gam α θ * Spaces.K θ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hsin2 : Real.sqrt 3 / 2 ≤ Real.sin (2 * θ) := by
    have h1 : π / 3 ≤ 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ ≤ 2 * π / 3 := by linarith [hθ.2]
    have h3 : Real.sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
    by_cases h : θ ≤ π / 4
    · have hle : Real.sin (π / 3) ≤ Real.sin (2 * θ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) h1
      rwa [h3] at hle
    · have hx1 : π / 3 ≤ π - 2 * θ := by linarith
      have hx2 : π - 2 * θ ≤ π / 2 := by linarith
      have hle : Real.sin (π / 3) ≤ Real.sin (π - 2 * θ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx2 hx1
      rw [Real.sin_pi_sub] at hle
      rwa [h3] at hle
  have hsincos : Real.sqrt 3 / 4 ≤ Real.sin θ * Real.cos θ := by
    have h2m : Real.sin (2 * θ) = 2 * (Real.sin θ * Real.cos θ) := by
      rw [Real.sin_two_mul]; ring
    rw [h2m] at hsin2
    linarith
  have hcos : (1 : ℝ) / 2 ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith) hθ.2
    rwa [Real.cos_pi_div_three] at h
  have hcos0 : 0 ≤ Real.cos θ := le_trans (by norm_num) hcos
  have hu : (1 : ℝ) / 6 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : Real.sqrt 3 / 4 * (1 / 2) ≤ (Real.sin θ * Real.cos θ) * Real.cos θ :=
      mul_le_mul hsincos hcos (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (le_trans (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 4) hsincos)
    have h2 : (1 : ℝ) / 6 ≤ Real.sqrt 3 / 4 * (1 / 2) := by
      have h3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    have h3 : (Real.sin θ * Real.cos θ) * Real.cos θ = Real.sin θ * Real.cos θ ^ 2 := by ring
    linarith
  have hu0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := le_trans (by norm_num) hu
  have hu1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 :=
    sin_mul_cos_sq_le_one ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hGK : Spaces.Gam α θ * Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 + 1) := by
    rw [Spaces.Gam, Spaces.K, Real.rpow_add' hu0 (by positivity : α / 3 + 1 ≠ 0), Real.rpow_one]
    ring
  have hrpow : (1 : ℝ) / 12 ≤ ((1 : ℝ) / 6) ^ ((4 : ℝ) / 3) := by
    rw [show ((1 : ℝ) / 6) ^ ((4 : ℝ) / 3) = (((1 : ℝ) / 6) ^ (4 : ℕ)) ^ ((1 : ℝ) / 3) by
      rw [← Real.rpow_natCast ((1 : ℝ) / 6) 4, ← Real.rpow_mul (by norm_num)]; norm_num]
    have h : ((1 : ℝ) / 12) ^ (3 : ℕ) ≤ ((1 : ℝ) / 6) ^ (4 : ℕ) := by norm_num
    have h2 : (((1 : ℝ) / 12) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = (1 : ℝ) / 12 := by
      rw [← Real.rpow_natCast ((1 : ℝ) / 12) 3, ← Real.rpow_mul (by norm_num)]; norm_num
    calc (1 : ℝ) / 12 = (((1 : ℝ) / 12) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) := h2.symm
      _ ≤ (((1 : ℝ) / 6) ^ (4 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) h (by norm_num)
  calc (1 : ℝ) / 4 ≤ 3 * ((1 : ℝ) / 6) ^ ((4 : ℝ) / 3) := by linarith [hrpow]
    _ ≤ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ ((4 : ℝ) / 3) := by
        refine mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by norm_num) hu (by norm_num)) (by norm_num)
    _ ≤ Spaces.Gam α θ * Spaces.K θ := by
        rw [hGK]
        have h := Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 (by positivity : (0 : ℝ) ≤ α / 3 + 1)
          (by linarith : α / 3 + 1 ≤ (4 : ℝ) / 3)
        linarith

/-- `1/8 ≤ c(α)`: on `[π/6,π/3]` we have `ΓK ≥ 1/4`, so
`c ≥ (1/4)·volume.real (Icc (π/6) (π/3)) = (1/4)·(π/6) = π/24 ≥ 1/8`. -/
theorem c_lower_bound_one_eighth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) / 8 ≤ Spaces.c α := by
  have h_int : MeasureTheory.IntegrableOn (fun θ : ℝ => Spaces.Gam α θ * Spaces.K θ)
      Spaces.Iθ := Spaces.CAux.integrableOn_GamK α hα
  have hfin : volume (Set.Icc (π / 6) (π / 3)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hsub : Set.Icc (π / 6) (π / 3) ⊆ Spaces.Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : (1 / 4 : ℝ) * volume.real (Set.Icc (π / 6) (π / 3))
      ≤ ∫ θ in Set.Icc (π / 6) (π / 3), Spaces.Gam α θ * Spaces.K θ :=
    MeasureTheory.setIntegral_ge_of_const_le_real measurableSet_Icc hfin
      (fun θ hθ => gamK_lower_third α hα hα1 hθ) (h_int.mono_set hsub)
  have hmono : ∫ θ in Set.Icc (π / 6) (π / 3), Spaces.Gam α θ * Spaces.K θ ≤ Spaces.c α := by
    have hnn : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), (0 : ℝ) ≤ Spaces.Gam α θ * Spaces.K θ := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact (Spaces.gamK_bounds α θ hα hθ).1
    have hst : Set.Icc (π / 6) (π / 3) ≤ᵐ[volume] Spaces.Iθ := by
      filter_upwards with θ hθ
      exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    exact MeasureTheory.setIntegral_mono_set h_int hnn hst
  have hvol : volume.real (Set.Icc (π / 6) (π / 3)) = π / 6 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hnum : (1 : ℝ) / 8 ≤ (1 / 4) * (π / 6) := by
    nlinarith [Real.pi_gt_three]
  calc (1 : ℝ) / 8 ≤ (1 / 4) * (π / 6) := hnum
    _ = (1 / 4) * volume.real (Set.Icc (π / 6) (π / 3)) := by rw [hvol]
    _ ≤ ∫ θ in Set.Icc (π / 6) (π / 3), Spaces.Gam α θ * Spaces.K θ := h1
    _ ≤ Spaces.c α := hmono

/-- `∫_θ (Γ/c)² sin(2θ)^{-η} ≤ 12100` (with `12100 = 64·189`): pointwise `Γ ≤ 1` and
`c ≥ 1/8` give `(Γ/c)² ≤ 64`, and the angular integral is `≤ 189`. -/
theorem Gam_div_c_sq_eta_integral_le_12100 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) ≤ 12100 := by
  have hc : (1 : ℝ) / 8 ≤ Spaces.c α := c_lower_bound_one_eighth α hα hα1
  have hη0 : 0 < Spaces.eta := by rw [Spaces.eta]; norm_num
  have hη1 : Spaces.eta < 1 := by rw [Spaces.eta]; norm_num
  have hsinle : ∀ θ ∈ Spaces.Iθ, (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    intro θ hθ
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hpt : ∀ θ ∈ Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ 64 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    intro θ hθ
    have hG1 : Spaces.Gam α θ ≤ 1 := by
      rw [Spaces.Gam]
      exact Real.rpow_le_one
        (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _))
        (sin_mul_cos_sq_le_one hθ) (le_of_lt (by positivity : (0:ℝ) < α / 3))
    have hG0 : 0 ≤ Spaces.Gam α θ := by
      rw [Spaces.Gam]
      exact Real.rpow_nonneg (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)) _
    have hsq : (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 64 := by
      rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < (Spaces.c α) ^ 2)]
      have h1 : Spaces.Gam α θ ^ 2 ≤ 1 := by
        have := mul_self_le_mul_self hG0 hG1
        nlinarith [this]
      have h2 : (1:ℝ) ≤ 64 * (Spaces.c α) ^ 2 := by
        have := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/8) hc
        nlinarith [this]
      linarith
    exact mul_le_mul_of_nonneg_right hsq (hsinle θ hθ)
  have hInt2 : IntegrableOn (fun θ : ℝ => 64 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ :=
    ((Work.Spaces.sin_two_rpow (-Spaces.eta) (by linarith) (by linarith)).1).const_mul 64
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (volume.restrict Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    unfold Spaces.Gam
    fun_prop
  have hIntL : IntegrableOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ := by
    refine Integrable.mono' hInt2 hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hsinle θ hθ))]
    exact hpt θ hθ
  have hmono : ∫ θ in Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      ≤ ∫ θ in Spaces.Iθ, 64 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    refine integral_mono_of_nonneg ?_ hInt2 ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (hsinle θ hθ)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hpt θ hθ
  calc ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      ≤ ∫ θ in Spaces.Iθ, 64 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := hmono
    _ = 64 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-Spaces.eta) := integral_const_mul _ _
    _ ≤ 64 * 189 := by
        have := etaWeight_integral_le; linarith
    _ ≤ 12100 := by norm_num

/-- **The projector-correction pairing.**  With the Cauchy–Schwarz split of
`(Γ/c)(2z²/(1+z)³)Λ f w² s^{-η}` into `A = (Γ/c)(2z²/(1+z)³)w s^{-η/2}` and
`B = f w s^{-η/2}` one gets `|·| ≤ |Λ|√(4·hX)·√(EfEta f) ≤ 220|Λ|√(EfEta f)`. -/
theorem gPsi_eta_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (Λ : ℝ)
    (hf : IBP f) (hi : CoerciveData α f) :
    |wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        (fun z θ => (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f|
      ≤ 220 * |Λ| * Real.sqrt (EfEta f) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  set A : ℝ × ℝ → ℝ := fun p => (Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
      * Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-Spaces.eta / 2) with hA
  set B : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-Spaces.eta / 2) with hB
  have hsin0 : ∀ θ ∈ Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- ### Step 1: the weighted pairing as a product-measure integral of `Λ * (A * B)`
  have hgint : IntegrableOn (Function.uncurry (fun z θ =>
      (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    etaW_gPsi_integrable α hα hα1 f hf hi
  have hIntOn : IntegrableOn (Function.uncurry (fun z θ =>
      (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ * f z θ * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    IntegrableOn.congr_fun (Integrable.const_mul hgint Λ) (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  have hIntOn' : IntegrableOn (Function.uncurry (fun z θ =>
      ((Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) * f z θ
        * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))))
      (Spaces.Iz ×ˢ Spaces.Iθ) :=
    IntegrableOn.congr_fun hIntOn (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  have hwip : wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (fun z θ => (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f
      = ∫ p, Λ * (A p * B p) ∂P := by
    rw [wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (fun z θ => (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f hIntOn', ← hP]
    refine integral_congr_ae ?_
    filter_upwards [ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hA, hB, Function.uncurry_apply_pair]
    have hss : (Real.sin (2 * θ)) ^ (-Spaces.eta / 2) * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2)
        = (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      rw [← rpow_half_sq _ hs0]; ring
    rw [← hss]
    ring
  -- ### Step 2: a.e. strong measurability of `A` and `B`
  have hsin_esm : AEStronglyMeasurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Spaces.eta / 2)) P := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hAesm : AEStronglyMeasurable A P := by
    rw [hA]
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.Gam α p.2 / Spaces.c α)
        * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * Spaces.w p.1) P := by
      apply Measurable.aestronglyMeasurable
      unfold Spaces.Gam Spaces.w
      fun_prop
    exact h1.mul hsin_esm
  have hBesm : AEStronglyMeasurable B P := by
    rw [hB]
    exact (aesm_f_mul_w hf.smooth).mul hsin_esm
  -- ### Step 3: square-integrability of `A` and `B`
  have ha : IntegrableOn (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2)
      Spaces.Iz := by
    refine Integrable.mono' (Integrable.const_mul integrable_Iz_one_div_sq 4) ?_ ?_
    · unfold Spaces.w
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rcases eq_or_ne z 0 with h | h
      · rw [h]; norm_num
      · have h1z : (1 : ℝ) + z ≠ 0 := by linarith [Set.mem_Ici.mp hz]
        have hkey : (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2 = 4 * (1 / (1 + z) ^ 2) := by
          rw [Spaces.w]; field_simp; ring
        rw [hkey]
  have hb : IntegrableOn (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := by
    refine Integrable.mono' (Integrable.const_mul (Work.Spaces.sin_two_rpow (-Spaces.eta)
      (by linarith [Spaces.eta_lt_one]) (by linarith [Spaces.eta_pos])).1 100) ?_ ?_
    · unfold Spaces.Gam
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 := hsin0 θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
      have hG : |Spaces.Gam α θ / Spaces.c α| ≤ 10 := Gam_div_c_bound hα hα1 hθ
      have hsq : (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 100 := by
        nlinarith [hG, abs_nonneg (Spaces.Gam α θ / Spaces.c α),
          sq_abs (Spaces.Gam α θ / Spaces.c α)]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)
  have hA2 : Integrable (fun p => A p ^ 2) P := by
    rw [hP]
    refine ((ha.mul_prod hb).congr ?_)
    filter_upwards [ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hA]
    rw [mul_pow, mul_pow, mul_pow, rpow_half_sq _ hs0]
    ring
  have hB2 : Integrable (fun p => B p ^ 2) P := by
    rw [hP]
    refine ((integrableOn_prod hi.intFeta).congr ?_)
    filter_upwards [ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, rpow_half_sq _ hs0]
    ring
  -- ### Step 4: the Cauchy–Schwarz bound
  have hCS := sq_integral_mul_le P A B hAesm hBesm hA2 hB2
  have hA2nn : 0 ≤ ∫ p, A p ^ 2 ∂P := integral_nonneg fun p => sq_nonneg _
  have habs : |∫ p, A p * B p ∂P| ≤ Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P) := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hA2nn]
    exact Real.sqrt_le_sqrt hCS
  -- ### Step 5: the values of the two square-integrals
  have hzsq : ∫ z in Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2 = 4 := by
    have hI : (∫ z in Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2 := by
      rw [show Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
      exact (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [hI]
    have hcongr : (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun z => 4 * (1 / (1 + z) ^ 2)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : z ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hz)
      have h1z : (1 : ℝ) + z ≠ 0 := by have := Set.mem_Ioi.mp hz; linarith
      have hkey : (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2 = 4 * (1 / (1 + z) ^ 2) := by
        rw [Spaces.w]; field_simp; ring
      rw [hkey]
    rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_const_mul]
    have h1 : (∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2) = 1 := by
      rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
      exact integral_Iz_one_div_sq
    rw [h1]
    norm_num
  have hBval : ∫ p, B p ^ 2 ∂P = EfEta f := by
    have hF : IntegrableOn (Function.uncurry (fun z θ => f z θ * f z θ
        * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))) (Spaces.Iz ×ˢ Spaces.Iθ) :=
      IntegrableOn.congr_fun hi.intFeta (fun p hp => by
        obtain ⟨z, θ⟩ := p
        simp only [Function.uncurry_apply_pair]
        ring) (measurableSet_Ici.prod measurableSet_Icc)
    rw [EfEta_eq_wip, wip_eq_integral_prod
      (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) f f hF, ← hP]
    refine integral_congr_ae ?_
    filter_upwards [ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, rpow_half_sq _ hs0]
    ring
  have hAval : ∫ p, A p ^ 2 ∂P = (∫ z in Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2)
      * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
    have hcongr : (fun p : ℝ × ℝ => A p ^ 2)
        =ᵐ[P] (fun p : ℝ × ℝ => ((2 * p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 * Spaces.w p.1 ^ 2)
          * ((Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) := by
      filter_upwards [ae_prod_quadrant] with p hp
      obtain ⟨z, θ⟩ := p
      obtain ⟨hz, hθ⟩ := hp
      have hs0 := hsin0 θ hθ
      simp only [hA]
      rw [mul_pow, mul_pow, mul_pow, rpow_half_sq _ hs0]
      ring
    rw [MeasureTheory.integral_congr_ae hcongr, hP]
    rw [integral_prod_sep (a := fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2)
      (b := fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      ha hb]
  -- ### Step 6: numerical conclusion
  have hX := Gam_div_c_sq_eta_integral_le_12100 α hα hα1
  have hXnn : 0 ≤ ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin0 θ hθ) _)
  have hsq_le : Real.sqrt (4 * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta))) ≤ 220 := by
    have h110 : Real.sqrt (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)) ≤ 110 := by
      rw [show (110 : ℝ) = Real.sqrt 12100 by
        rw [show (12100 : ℝ) = 110^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hX
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
    nlinarith [h110, Real.sqrt_nonneg (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta))]
  calc |wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        (fun z θ => (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f|
      = |∫ p, Λ * (A p * B p) ∂P| := by rw [hwip]
    _ = |Λ| * |∫ p, A p * B p ∂P| := by
        rw [MeasureTheory.integral_const_mul, abs_mul]
    _ ≤ |Λ| * (Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P)) :=
        mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = |Λ| * (Real.sqrt ((∫ z in Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Spaces.w z ^ 2)
          * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta))) * Real.sqrt (EfEta f)) := by
        rw [hAval, hBval]
    _ = |Λ| * (Real.sqrt (4 * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta))) * Real.sqrt (EfEta f)) := by
        rw [hzsq]
    _ ≤ |Λ| * (220 * Real.sqrt (EfEta f)) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right hsq_le (Real.sqrt_nonneg _)
    _ = 220 * |Λ| * Real.sqrt (EfEta f) := by ring

/-- **The angular transport pairing.**  The `θ`-integration by parts
`∫_θ D_θf·f·s^{-η} = (η-1)∫_θ cos(2θ)f²s^{-η}` (`slice_ibp_eta`) turns the transport term
into `((η-1)cos(2θ))/(1+z) ≤ (1-η)` times the energy density, giving
`wip (w²s^{-η}) (3D_θf/(1+z)) f ≤ 3(1-η)EfEta f`. -/
theorem Trf_eta_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hi : CoerciveData α f) :
    wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        (fun z θ => 3 * Spaces.Dth f z θ / (1 + z)) f
      ≤ 3 * (1 - Spaces.eta) * EfEta f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  have hsin0 : ∀ θ ∈ Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have heta : Spaces.eta - 1 ≤ 0 := by have := Spaces.eta_lt_one; linarith
  have heta' : (0 : ℝ) ≤ 1 - Spaces.eta := by have := Spaces.eta_lt_one; linarith
  have hpos : ∀ᵐ z ∂(volume.restrict Spaces.Iz), 0 < z := by
    have h : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 < z :=
      (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun z hz => hz
    rw [Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h
    exact h
  -- a.e. strong measurability of `f` itself
  have haesm_f : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2) P := by
    have h := aesm_f_mul_w hf.smooth
    have hw : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.w p.1)⁻¹) P := by
      apply Measurable.aestronglyMeasurable
      unfold Spaces.w
      fun_prop
    refine (h.mul hw).congr ?_
    filter_upwards [ae_prod_pos] with p hp
    simp only [Pi.mul_apply]
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (w_pos hp)), mul_one]
  -- integrability of the weighted transport integrand, `wip` and product-measure forms
  have hInt : IntegrableOn (Function.uncurry (fun z θ => (3 * Spaces.Dth f z θ / (1 + z)) * f z θ
      * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    etaW_Trf_integrable α hα f hf hi (etaDth_sq_integrable α hα f hi)
  have hInt' : IntegrableOn (Function.uncurry (fun z θ => (3 * Spaces.Dth f z θ / (1 + z)) * f z θ
      * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    IntegrableOn.congr_fun hInt (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  have hFeta : IntegrableOn (Function.uncurry (fun z θ => f z θ * f z θ
      * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    IntegrableOn.congr_fun hi.intFeta (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  -- the dominating density and the `cos` integrand
  have hdomint : Integrable (fun p : ℝ × ℝ => 3 * (1 - Spaces.eta) * (f p.1 p.2 * f p.1 p.2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) P := by
    rw [hP]
    exact Integrable.const_mul (integrableOn_prod hi.intFeta) _
  have hYleq : ∀ p : ℝ × ℝ, p.1 ∈ Spaces.Iz → p.2 ∈ Spaces.Iθ →
      |(3 * Spaces.w p.1 ^ 2 / (1 + p.1)) * ((Spaces.eta - 1) * (Real.cos (2 * p.2)
          * (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)))|
        ≤ 3 * (1 - Spaces.eta) * (f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) := by
    intro p hz hθ
    obtain ⟨z, θ⟩ := p
    show |(3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * (Real.cos (2 * θ)
          * (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))|
        ≤ 3 * (1 - Spaces.eta) * (f z θ * f z θ * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta))
    have hz0 : (0 : ℝ) ≤ z := Set.mem_Ici.mp hz
    have hs0 := hsin0 θ hθ
    have hk0 : (0 : ℝ) ≤ (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    have hA0 : (0 : ℝ) ≤ 3 * Spaces.w z ^ 2 / (1 + z) := by positivity
    have h1z : (0 : ℝ) < 1 + z := by linarith
    have hw2 : (0 : ℝ) ≤ Spaces.w z ^ 2 := sq_nonneg _
    have h2 : (3 * Spaces.w z ^ 2 / (1 + z)) * (1 - Spaces.eta)
        ≤ 3 * Spaces.w z ^ 2 * (1 - Spaces.eta) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h1z]
      have h3nn : (0 : ℝ) ≤ 3 * Spaces.w z ^ 2 * (1 - Spaces.eta) :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) heta'
      nlinarith [mul_nonneg h3nn hz0, h3nn, hz0]
    have hcoef : (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * Real.cos (2 * θ))
        ≤ 3 * (1 - Spaces.eta) * Spaces.w z ^ 2 := by
      have hle : (Spaces.eta - 1) * Real.cos (2 * θ) ≤ (1 - Spaces.eta) := by
        have h1 : (Spaces.eta - 1) * Real.cos (2 * θ) ≤ (Spaces.eta - 1) * (-1) :=
          mul_le_mul_of_nonpos_left (Real.neg_one_le_cos _) heta
        linarith
      calc (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * Real.cos (2 * θ))
          ≤ (3 * Spaces.w z ^ 2 / (1 + z)) * (1 - Spaces.eta) :=
            mul_le_mul_of_nonneg_left hle hA0
        _ ≤ 3 * Spaces.w z ^ 2 * (1 - Spaces.eta) := h2
        _ = 3 * (1 - Spaces.eta) * Spaces.w z ^ 2 := by ring
    have hge : (Spaces.eta - 1) ≤ (Spaces.eta - 1) * Real.cos (2 * θ) := by
      have h1 : (Spaces.eta - 1) * 1 ≤ (Spaces.eta - 1) * Real.cos (2 * θ) :=
        mul_le_mul_of_nonpos_left (Real.cos_le_one _) heta
      simpa using h1
    rw [abs_le]
    constructor
    · -- lower bound: `-B ≤ Y`
      have hAb : (3 * Spaces.w z ^ 2 / (1 + z)) * (1 - Spaces.eta) * ((f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          ≤ 3 * (1 - Spaces.eta) * (f z θ * f z θ * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
        calc (3 * Spaces.w z ^ 2 / (1 + z)) * (1 - Spaces.eta) * ((f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-Spaces.eta))
            = ((3 * Spaces.w z ^ 2 / (1 + z)) * (1 - Spaces.eta)) * ((f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by ring
          _ ≤ (3 * Spaces.w z ^ 2 * (1 - Spaces.eta)) * ((f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := mul_le_mul_of_nonneg_right h2 hk0
          _ = 3 * (1 - Spaces.eta) * (f z θ * f z θ * Spaces.w z ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by ring
      have hmid : (3 * Spaces.w z ^ 2 / (1 + z)) * (Spaces.eta - 1) * ((f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          ≤ (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * (Real.cos (2 * θ) * (f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta))) := by
        have hk' : (Spaces.eta - 1) * ((f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
            ≤ (Spaces.eta - 1) * (Real.cos (2 * θ) * ((f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-Spaces.eta))) := by
          have h1 := mul_le_mul_of_nonneg_right hge hk0
          nlinarith [h1]
        calc (3 * Spaces.w z ^ 2 / (1 + z)) * (Spaces.eta - 1) * ((f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-Spaces.eta))
            = (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * ((f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.eta))) := by ring
          _ ≤ (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * (Real.cos (2 * θ)
                * ((f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))) :=
              mul_le_mul_of_nonneg_left hk' hA0
          _ = (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * (Real.cos (2 * θ) * (f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-Spaces.eta))) := by ring
      have hneg : -(3 * (1 - Spaces.eta) * (f z θ * f z θ * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
          ≤ (3 * Spaces.w z ^ 2 / (1 + z)) * (Spaces.eta - 1) * ((f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by linarith [hAb]
      exact hneg.trans hmid
    · -- upper bound: `Y ≤ B`
      calc (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * (Real.cos (2 * θ) * (f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
          = ((3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * Real.cos (2 * θ)))
            * ((f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by ring
        _ ≤ (3 * (1 - Spaces.eta) * Spaces.w z ^ 2) * ((f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := mul_le_mul_of_nonneg_right hcoef hk0
        _ = 3 * (1 - Spaces.eta) * (f z θ * f z θ * Spaces.w z ^ 2
              * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by ring
  have hjoin : Integrable (fun p : ℝ × ℝ => (3 * Spaces.w p.1 ^ 2 / (1 + p.1))
      * ((Spaces.eta - 1) * (Real.cos (2 * p.2) * (f p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta)))) P := by
    have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => (3 * Spaces.w p.1 ^ 2 / (1 + p.1))
        * ((Spaces.eta - 1) * (Real.cos (2 * p.2) * (f p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-Spaces.eta)))) P := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (3 * Spaces.w p.1 ^ 2 / (1 + p.1))) P := by
        apply Measurable.aestronglyMeasurable
        unfold Spaces.w
        fun_prop
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.eta - 1)
          * (Real.cos (2 * p.2) * (f p.1 p.2) ^ 2
              * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) P := by
        have hf2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) P := by
          refine (haesm_f.mul haesm_f).congr ?_
          filter_upwards with p
          simp only [Pi.mul_apply, sq]
        have hc : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.cos (2 * p.2)) P := by
          apply Measurable.aestronglyMeasurable
          fun_prop
        have hs : AEStronglyMeasurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Spaces.eta)) P := by
          apply Measurable.aestronglyMeasurable
          fun_prop
        exact ((hc.mul hf2).mul hs).const_mul _
      exact h1.mul h2
    refine Integrable.mono' hdomint haesm ?_
    filter_upwards [ae_prod_quadrant] with p hp
    exact hYleq p hp.1 hp.2
  -- ### Step 1: `wip` as a product-measure integral
  have hwip : wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (fun z θ => 3 * Spaces.Dth f z θ / (1 + z)) f
      = ∫ p, (3 * Spaces.Dth f p.1 p.2 / (1 + p.1)) * f p.1 p.2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta) ∂P := by
    rw [wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (fun z θ => 3 * Spaces.Dth f z θ / (1 + z)) f hInt', ← hP]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  -- ### Step 2: Fubini, the `θ`-integration by parts, and Fubini again
  have hXint : Integrable (fun p : ℝ × ℝ => (3 * Spaces.Dth f p.1 p.2 / (1 + p.1)) * f p.1 p.2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) P := by
    rw [hP]
    exact (integrableOn_prod hInt').congr (Filter.Eventually.of_forall fun p => by ring)
  have hinner : ∀ z : ℝ, (∫ θ in Spaces.Iθ, (3 * Spaces.Dth f z θ / (1 + z)) * f z θ
        * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      = (3 * Spaces.w z ^ 2 / (1 + z)) * (∫ θ in Spaces.Iθ, Spaces.Dth f z θ * f z θ
          * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
    intro z
    have hfun : (fun θ : ℝ => (3 * Spaces.Dth f z θ / (1 + z)) * f z θ * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        = fun θ : ℝ => (3 * Spaces.w z ^ 2 / (1 + z)) * (Spaces.Dth f z θ * f z θ
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
      funext θ
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
  have hstep : (∫ p, (3 * Spaces.Dth f p.1 p.2 / (1 + p.1)) * f p.1 p.2 * Spaces.w p.1 ^ 2
        * (Real.sin (2 * p.2)) ^ (-Spaces.eta) ∂P)
      = ∫ p, (3 * Spaces.w p.1 ^ 2 / (1 + p.1)) * ((Spaces.eta - 1) * (Real.cos (2 * p.2)
          * (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) ∂P := by
    rw [hP]
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => (3 * Spaces.Dth f p.1 p.2 / (1 + p.1))
      * f p.1 p.2 * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) hXint]
    rw [← hP]
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => (3 * Spaces.w p.1 ^ 2 / (1 + p.1))
      * ((Spaces.eta - 1) * (Real.cos (2 * p.2) * (f p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta)))) hjoin]
    refine integral_congr_ae ?_
    filter_upwards [hpos] with z hz
    rw [hinner z, slice_ibp_eta f hf.smooth hz]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  -- ### Step 3: the pointwise comparison on the product measure
  have hmono : (∫ p, (3 * Spaces.w p.1 ^ 2 / (1 + p.1)) * ((Spaces.eta - 1) * (Real.cos (2 * p.2)
          * (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) ∂P)
      ≤ ∫ p, 3 * (1 - Spaces.eta) * (f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) ∂P := by
    refine MeasureTheory.integral_mono_ae hjoin hdomint ?_
    filter_upwards [ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hz0 : (0 : ℝ) ≤ z := Set.mem_Ici.mp hz
    have hs0 := hsin0 θ hθ
    have hk0 : (0 : ℝ) ≤ (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    have h1z : (0 : ℝ) < 1 + z := by linarith
    have h2 : (3 * Spaces.w z ^ 2 / (1 + z)) * (1 - Spaces.eta)
        ≤ 3 * Spaces.w z ^ 2 * (1 - Spaces.eta) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h1z]
      have h3nn : (0 : ℝ) ≤ 3 * Spaces.w z ^ 2 * (1 - Spaces.eta) :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) heta'
      nlinarith [mul_nonneg h3nn hz0, h3nn, hz0]
    have hcoef : (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * Real.cos (2 * θ))
        ≤ 3 * (1 - Spaces.eta) * Spaces.w z ^ 2 := by
      have hle : (Spaces.eta - 1) * Real.cos (2 * θ) ≤ (1 - Spaces.eta) := by
        have h1 : (Spaces.eta - 1) * Real.cos (2 * θ) ≤ (Spaces.eta - 1) * (-1) :=
          mul_le_mul_of_nonpos_left (Real.neg_one_le_cos _) heta
        linarith
      calc (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * Real.cos (2 * θ))
          ≤ (3 * Spaces.w z ^ 2 / (1 + z)) * (1 - Spaces.eta) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ 3 * Spaces.w z ^ 2 * (1 - Spaces.eta) := h2
        _ = 3 * (1 - Spaces.eta) * Spaces.w z ^ 2 := by ring
    calc (3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * (Real.cos (2 * θ) * (f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
        = ((3 * Spaces.w z ^ 2 / (1 + z)) * ((Spaces.eta - 1) * Real.cos (2 * θ)))
          * ((f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by ring
      _ ≤ (3 * (1 - Spaces.eta) * Spaces.w z ^ 2) * ((f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := mul_le_mul_of_nonneg_right hcoef hk0
      _ = 3 * (1 - Spaces.eta) * (f z θ * f z θ * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by ring
  -- ### Step 4: the value of the dominating integral
  have hval : (∫ p, 3 * (1 - Spaces.eta) * (f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
        * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) ∂P) = 3 * (1 - Spaces.eta) * EfEta f := by
    rw [EfEta_eq_wip, wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      f f hFeta, ← hP]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  calc wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        (fun z θ => 3 * Spaces.Dth f z θ / (1 + z)) f
      = ∫ p, (3 * Spaces.Dth f p.1 p.2 / (1 + p.1)) * f p.1 p.2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta) ∂P := hwip
    _ = ∫ p, (3 * Spaces.w p.1 ^ 2 / (1 + p.1)) * ((Spaces.eta - 1) * (Real.cos (2 * p.2)
          * (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) ∂P := hstep
    _ ≤ ∫ p, 3 * (1 - Spaces.eta) * (f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) ∂P := hmono
    _ = 3 * (1 - Spaces.eta) * EfEta f := hval

/-- **The `η`-weighted `L₁₂` pairing.**  With the Cauchy–Schwarz split of
`(2zΓ/(c(1+z)²))L₁₂(f)f w² s^{-η}` into `A = (Γ/c)(L₁₂(f)/z)s^{-η/2}` and `B = f w s^{-η/2}`
one gets `|·| ≤ 2√(hX·EL12z)·√(EfEta f) ≤ 220√(EL12z f)√(EfEta f)`. -/
theorem psiA_eta_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hi : CoerciveData α f) :
    |wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        (fun z θ => (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z) f|
      ≤ 220 * Real.sqrt (EL12z f) * Real.sqrt (EfEta f) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  set A : ℝ × ℝ → ℝ := fun p => (Spaces.Gam α p.2 / Spaces.c α) * (L12f f p.1 / p.1)
      * (Real.sin (2 * p.2)) ^ (-Spaces.eta / 2) with hA
  set B : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-Spaces.eta / 2) with hB
  have hsin0 : ∀ θ ∈ Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hc : Spaces.c α ≠ 0 := c_ne_zero hα hα1
  -- ### Step 1: `wip` as the product-measure integral of `2 * (A * B)`
  have hpsi := etaW_psiA_integrable α hα hα1 f hf hfH hi
  have hIntOn : IntegrableOn (Function.uncurry (fun z θ =>
      ((2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z) * f z θ
        * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine IntegrableOn.congr_fun (Integrable.const_mul hpsi 2) (fun p hp => ?_)
      (measurableSet_Ici.prod measurableSet_Icc)
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    simp only [Function.uncurry_apply_pair]
    rcases eq_or_ne z 0 with h | h
    · subst h; simp [Spaces.w]
    · have h1z : (1 : ℝ) + z ≠ 0 := by linarith [Set.mem_Ici.mp hz]
      rw [Spaces.w]; field_simp
  have hwip : wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (fun z θ => (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z) f
      = ∫ p, 2 * (A p * B p) ∂P := by
    rw [wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (fun z θ => (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z) f hIntOn, ← hP]
    refine integral_congr_ae ?_
    filter_upwards [ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    have hss : (Real.sin (2 * θ)) ^ (-Spaces.eta / 2) * (Real.sin (2 * θ)) ^ (-Spaces.eta / 2)
        = (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      rw [← rpow_half_sq _ hs0]; ring
    simp only [hA, hB, Function.uncurry_apply_pair]
    rw [← hss]
    rcases eq_or_ne z 0 with h | h
    · subst h; simp [Spaces.w]
    · have h1z : (1 : ℝ) + z ≠ 0 := by linarith [Set.mem_Ici.mp hz]
      rw [Spaces.w]; field_simp
  -- ### Step 2: a.e. strong measurability of `A` and `B`
  have hsin_esm : AEStronglyMeasurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Spaces.eta / 2)) P := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hLesm : AEStronglyMeasurable (fun p : ℝ × ℝ => L12f f p.1) P := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => L12f f p.1) (volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) :=
      aesm_L12f (L12f_continuousOn f hfH)
    rwa [← prod_restrict_eq] at h1
  have hAesm : AEStronglyMeasurable A P := by
    have hbase : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.Gam α p.2 / Spaces.c α)
        * (L12f f p.1 * (p.1)⁻¹) * (Real.sin (2 * p.2)) ^ (-Spaces.eta / 2)) P := by
      have hG : AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Gam α p.2 / Spaces.c α) P := by
        apply Measurable.aestronglyMeasurable
        unfold Spaces.Gam
        fun_prop
      have hi : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1)⁻¹) P := by
        apply Measurable.aestronglyMeasurable
        fun_prop
      exact (hG.mul (hLesm.mul hi)).mul hsin_esm
    refine hbase.congr (Filter.Eventually.of_forall fun p => ?_)
    show (Spaces.Gam α p.2 / Spaces.c α) * (L12f f p.1 * (p.1)⁻¹)
        * (Real.sin (2 * p.2)) ^ (-Spaces.eta / 2) = A p
    rw [hA, div_eq_mul_inv]
    rfl
  have hBesm : AEStronglyMeasurable B P := by
    rw [hB]
    exact (aesm_f_mul_w hf.smooth).mul hsin_esm
  -- ### Step 3: square-integrability of `A` and `B`
  have ha : IntegrableOn (fun z : ℝ => (L12f f z / z) ^ 2) Spaces.Iz := by
    have h1 := hfH.intA 1 (by norm_num : (1 : ℕ) ≤ 2)
    have h2 : IntegrableOn (fun z : ℝ => (L12f f z / z) ^ 2) (Set.Ioi (0 : ℝ)) := by
      refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
      show (L12f f z) ^ 2 / z ^ (2 * ((1 : ℕ) : ℝ)) = (L12f f z / z) ^ 2
      have hz : (z : ℝ) ^ (2 * ((1 : ℕ) : ℝ)) = z ^ (2 : ℕ) := by
        rw [show (2 * ((1 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hz, div_pow]
    show Integrable (fun z : ℝ => (L12f f z / z) ^ 2) (volume.restrict (Set.Ici (0 : ℝ)))
    rw [← Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact h2
  have hb : IntegrableOn (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := by
    refine Integrable.mono' (Integrable.const_mul (Work.Spaces.sin_two_rpow (-Spaces.eta)
      (by linarith [Spaces.eta_lt_one]) (by linarith [Spaces.eta_pos])).1 100) ?_ ?_
    · unfold Spaces.Gam
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 := hsin0 θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
      have hG : |Spaces.Gam α θ / Spaces.c α| ≤ 10 := Gam_div_c_bound hα hα1 hθ
      have hsq : (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 100 := by
        nlinarith [hG, abs_nonneg (Spaces.Gam α θ / Spaces.c α),
          sq_abs (Spaces.Gam α θ / Spaces.c α)]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)
  have hA2 : Integrable (fun p => A p ^ 2) P := by
    rw [hP]
    refine ((ha.mul_prod hb).congr ?_)
    filter_upwards [ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hA]
    rw [mul_pow, mul_pow, rpow_half_sq _ hs0]
    ring
  have hB2 : Integrable (fun p => B p ^ 2) P := by
    rw [hP]
    have hF : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
        * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) ((volume.restrict Spaces.Iz).prod
          (volume.restrict Spaces.Iθ)) :=
      integrableOn_prod hi.intFeta
    refine (hF.congr ?_)
    filter_upwards [ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, rpow_half_sq _ hs0]
    ring
  -- ### Step 4: the Cauchy–Schwarz bound
  have hCS := sq_integral_mul_le P A B hAesm hBesm hA2 hB2
  have hA2nn : 0 ≤ ∫ p, A p ^ 2 ∂P := integral_nonneg fun p => sq_nonneg _
  have habs : |∫ p, A p * B p ∂P| ≤ Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P) := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hA2nn]
    exact Real.sqrt_le_sqrt hCS
  -- ### Step 5: the values of the two square-integrals
  have hBval : ∫ p, B p ^ 2 ∂P = EfEta f := by
    have hF : IntegrableOn (Function.uncurry (fun z θ => f z θ * f z θ
        * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))) (Spaces.Iz ×ˢ Spaces.Iθ) :=
      IntegrableOn.congr_fun hi.intFeta (fun p hp => by
        obtain ⟨z, θ⟩ := p
        simp only [Function.uncurry_apply_pair]
        ring) (measurableSet_Ici.prod measurableSet_Icc)
    rw [EfEta_eq_wip, wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      f f hF, ← hP]
    refine integral_congr_ae ?_
    filter_upwards [ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, rpow_half_sq _ hs0]
    ring
  have hAval : ∫ p, A p ^ 2 ∂P = EL12z f * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
    have hcongr : (fun p : ℝ × ℝ => A p ^ 2)
        =ᵐ[P] (fun p : ℝ × ℝ => (L12f f p.1 / p.1) ^ 2
          * ((Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) := by
      filter_upwards [ae_prod_quadrant] with p hp
      obtain ⟨z, θ⟩ := p
      obtain ⟨hz, hθ⟩ := hp
      have hs0 := hsin0 θ hθ
      simp only [hA]
      rw [mul_pow, mul_pow, rpow_half_sq _ hs0]
      ring
    rw [MeasureTheory.integral_congr_ae hcongr, hP]
    rw [integral_prod_sep (a := fun z : ℝ => (L12f f z / z) ^ 2)
      (b := fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)) ha hb]
    rfl
  -- ### Step 6: numerical conclusion
  have hX := Gam_div_c_sq_eta_integral_le_12100 α hα hα1
  have hELnn : 0 ≤ EL12z f := by
    rw [EL12z, L2Sqz]
    exact integral_nonneg fun z => sq_nonneg _
  have hEfnn : 0 ≤ EfEta f := by
    rw [EfEta, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hsqrt : Real.sqrt (EL12z f) * Real.sqrt (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) ≤ 110 * Real.sqrt (EL12z f) := by
    have h110 : Real.sqrt (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)) ≤ 110 := by
      rw [show (110 : ℝ) = Real.sqrt 12100 by
        rw [show (12100 : ℝ) = 110^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hX
    calc Real.sqrt (EL12z f) * Real.sqrt (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        ≤ Real.sqrt (EL12z f) * 110 := mul_le_mul_of_nonneg_left h110 (Real.sqrt_nonneg _)
      _ = 110 * Real.sqrt (EL12z f) := by ring
  calc |wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        (fun z θ => (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z) f|
      = |∫ p, 2 * (A p * B p) ∂P| := by rw [hwip]
    _ = 2 * |∫ p, A p * B p ∂P| := by
        rw [MeasureTheory.integral_const_mul, abs_mul]
        norm_num
    _ ≤ 2 * (Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P)) :=
        mul_le_mul_of_nonneg_left habs (by norm_num)
    _ = 2 * (Real.sqrt (EL12z f * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta))) * Real.sqrt (EfEta f)) := by
        rw [hAval, hBval]
    _ = 2 * (Real.sqrt (EL12z f) * Real.sqrt (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)) * Real.sqrt (EfEta f)) := by
        rw [Real.sqrt_mul hELnn]
    _ ≤ 2 * ((110 * Real.sqrt (EL12z f)) * Real.sqrt (EfEta f)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
    _ = 220 * Real.sqrt (EL12z f) * Real.sqrt (EfEta f) := by ring

/-- Young's inequality in the form `Kuv ≤ δu² + K²v²/(4δ)`. -/
theorem young_abs (K δ u v : ℝ) (hδ : 0 < δ) :
    K * u * v ≤ δ * u ^ 2 + K ^ 2 / (4 * δ) * v ^ 2 := by
  have h1 : 0 ≤ (2 * δ * u - K * v) ^ 2 := sq_nonneg _
  have h2 : 0 < 4 * δ := by linarith
  have h3 : δ * u ^ 2 + K ^ 2 / (4 * δ) * v ^ 2
      = (4 * δ ^ 2 * u ^ 2 + K ^ 2 * v ^ 2) / (4 * δ) := by
    field_simp
  rw [h3, le_div_iff₀ h2]
  nlinarith [h1]

/-- **The `L²` coercivity of `𝓛_Γ^T` in the `η`-weighted space.**

This is Proposition `prop:L2CoercivityTransport2` of T. M. Elgindi, *Finite-time
singularity formation for `C^{1,α}` solutions to the incompressible Euler
equations on `ℝ³`*, Annals of Math. 194 (3) 2021.  The stated estimate is the
paper's with the *error terms enlarged*: the source subtracts only
`10⁵·|z⁻¹L₁₂f|²_{L²_z}`, and since `EL12z f`, `EDthW f` and `Ef f` are integrals of
squares (hence nonnegative), subtracting `10⁵(EL12z f + EDthW f + Ef f)` instead
gives a strictly weaker — and therefore safe — statement. -/
theorem L2CoercivityTransportEta (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hΓ : GammaL2Bnd α) (hi : CoerciveData α f) :
    (1 / 5) * EfEta f - 100000 * (EL12z f + EDthW f + Ef f)
      ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          (LGammaT α f) f := by
  set ρ : ℝ → ℝ → ℝ := fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) with hρ
  set psiA : ℝ → ℝ → ℝ := fun z θ =>
    (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z with hpsiA
  set Trf : ℝ → ℝ → ℝ := fun z θ => 3 * Spaces.Dth f z θ / (1 + z) with hTrf
  set cf : ℝ → ℝ → ℝ := fun z θ =>
    (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * (L12f (Transport f) 0) with hcf
  -- integrability of the four summands against `f ρ`
  have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => L f z θ * f z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine IntegrableOn.congr_fun (Lf_etaW_integrable α hα hα1 f hf hfH hi)
      (fun p hp => ?_) (measurableSet_Ici.prod measurableSet_Icc)
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, hρ]
    ring
  have h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => psiA z θ * f z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine IntegrableOn.congr_fun (Integrable.const_mul (etaW_psiA_integrable α hα hα1 f hf hfH hi) 2)
      (fun p hp => ?_) (measurableSet_Ici.prod measurableSet_Icc)
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    simp only [Function.uncurry_apply_pair, hρ, hpsiA]
    rcases eq_or_ne z 0 with h | h
    · subst h; simp [Spaces.w]
    · have h1z : (1 : ℝ) + z ≠ 0 := by linarith [Set.mem_Ici.mp hz]
      rw [Spaces.w]; field_simp <;> ring
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => Trf z θ * f z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine IntegrableOn.congr_fun
      (etaW_Trf_integrable α hα f hf hi (etaDth_sq_integrable α hα f hi))
      (fun p hp => ?_) (measurableSet_Ici.prod measurableSet_Icc)
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, hρ, hTrf]
    ring
  have h4 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => cf z θ * f z θ * ρ z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine IntegrableOn.congr_fun
      (Integrable.const_mul (etaW_gPsi_integrable α hα hα1 f hf hi) (L12f (Transport f) 0))
      (fun p hp => ?_) (measurableSet_Ici.prod measurableSet_Icc)
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, hρ, hcf]
    ring
  -- the pointwise decomposition of `𝓛_Γ^T`
  have hfun : LGammaT α f = fun z θ => L f z θ - psiA z θ - Trf z θ + cf z θ := by
    funext z θ
    simp only [hpsiA, hTrf, hcf, LGammaT, LGamma, Proj, Transport]
    ring_nf
  have hsplit := wip_sub_add ρ (L f) psiA Trf cf f h1 h2 h3 h4
  have hLGT : wip ρ (LGammaT α f) f
      = wip ρ (L f) f - wip ρ psiA f - wip ρ Trf f + wip ρ cf f := by
    rw [hfun, hsplit]
  -- the four estimates
  have hbase : wip ρ (L f) f = (1 / 2) * EfEta f := by
    rw [hρ]; exact wip_Lf_eq α hα hα1 f hf hfH hi
  have hpsi := psiA_eta_abs_le α hα hα1 f hf hfH hi
  have hpsi' : |wip ρ psiA f| ≤ 220 * Real.sqrt (EL12z f) * Real.sqrt (EfEta f) := by
    rw [hρ, hpsiA]; exact hpsi
  have htrf := Trf_eta_le α hα hα1 f hf hi
  have htrf' : wip ρ Trf f ≤ 3 * (1 - Spaces.eta) * EfEta f := by
    rw [hρ, hTrf]; exact htrf
  have hC0 : (C0 f) ^ 2 ≤ EDthW f := C0_sq_le_EDthW f hf.smooth hi.intDth
  have hLam : |L12f (Transport f) 0| ≤ Real.sqrt (EDthW f) := by
    have h : |C0 f| ≤ Real.sqrt (EDthW f) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hC0
    exact h
  have hcorr := gPsi_eta_abs_le α hα hα1 f (L12f (Transport f) 0) hf hi
  have hcorr' : |wip ρ cf f| ≤ 220 * Real.sqrt (EDthW f) * Real.sqrt (EfEta f) := by
    rw [hρ, hcf]
    have hEfE : (0 : ℝ) ≤ Real.sqrt (EfEta f) := Real.sqrt_nonneg _
    have hstep : 220 * |L12f (Transport f) 0| * Real.sqrt (EfEta f)
        ≤ 220 * Real.sqrt (EDthW f) * Real.sqrt (EfEta f) := by
      have h1 : 220 * |L12f (Transport f) 0| ≤ 220 * Real.sqrt (EDthW f) :=
        mul_le_mul_of_nonneg_left hLam (by norm_num)
      exact mul_le_mul_of_nonneg_right h1 hEfE
    exact hcorr.trans hstep
  -- nonnegativity
  have hEfnn : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEfEta_nn : 0 ≤ EfEta f := by
    rw [EfEta, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hELnn : 0 ≤ EL12z f := by
    rw [EL12z, L2Sqz]
    exact integral_nonneg fun z => sq_nonneg _
  have hEDnn : 0 ≤ EDthW f := by
    rw [EDthW, wip]
    exact integral_nonneg fun z => integral_nonneg fun θ => mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
  -- Young's inequalities
  have hyoung1 : 220 * Real.sqrt (EL12z f) * Real.sqrt (EfEta f)
      ≤ (1 / 8) * EfEta f + (96800 : ℝ) * EL12z f := by
    have h := young_abs 220 (1/8) (Real.sqrt (EfEta f)) (Real.sqrt (EL12z f)) (by norm_num)
    rw [Real.sq_sqrt hEfEta_nn, Real.sq_sqrt hELnn] at h
    have h2 : (220:ℝ)^2 / (4 * (1/8)) = 96800 := by norm_num
    rw [h2] at h
    calc 220 * Real.sqrt (EL12z f) * Real.sqrt (EfEta f)
        = 220 * Real.sqrt (EfEta f) * Real.sqrt (EL12z f) := by ring
      _ ≤ (1 / 8) * EfEta f + 96800 * EL12z f := h
  have hyoung2 : 220 * Real.sqrt (EDthW f) * Real.sqrt (EfEta f)
      ≤ (1 / 8) * EfEta f + (96800 : ℝ) * EDthW f := by
    have h := young_abs 220 (1/8) (Real.sqrt (EfEta f)) (Real.sqrt (EDthW f)) (by norm_num)
    rw [Real.sq_sqrt hEfEta_nn, Real.sq_sqrt hEDnn] at h
    have h2 : (220:ℝ)^2 / (4 * (1/8)) = 96800 := by norm_num
    rw [h2] at h
    calc 220 * Real.sqrt (EDthW f) * Real.sqrt (EfEta f)
        = 220 * Real.sqrt (EfEta f) * Real.sqrt (EDthW f) := by ring
      _ ≤ (1 / 8) * EfEta f + 96800 * EDthW f := h
  -- the numerical assembly
  have hcoef : (1 / 5 : ℝ) ≤ 1 / 2 - 3 * (1 - Spaces.eta) - 1 / 8 - 1 / 8 := by
    rw [Spaces.eta]; norm_num
  have key : (1 / 5) * EfEta f - 100000 * (EL12z f + EDthW f)
      ≤ wip ρ (L f) f - wip ρ psiA f - wip ρ Trf f + wip ρ cf f := by
    have hb2 : wip ρ psiA f ≤ 220 * Real.sqrt (EL12z f) * Real.sqrt (EfEta f) := by
      linarith [le_abs_self (wip ρ psiA f), hpsi']
    have hb4 : -(220 * Real.sqrt (EDthW f) * Real.sqrt (EfEta f)) ≤ wip ρ cf f := by
      linarith [neg_abs_le (wip ρ cf f), hcorr']
    have hcoef' : (1 / 2 - 3 * (1 - Spaces.eta) - 1 / 8 - 1 / 8) ≥ (1 / 5 : ℝ) := hcoef
    have hcoefE : (1 / 5) * EfEta f
        ≤ (1 / 2 - 3 * (1 - Spaces.eta) - 1 / 8 - 1 / 8) * EfEta f :=
      mul_le_mul_of_nonneg_right hcoef' hEfEta_nn
    linarith [hbase, hb2, hb4, htrf', hyoung1, hyoung2, hcoefE]
  calc (1 / 5) * EfEta f - 100000 * (EL12z f + EDthW f + Ef f)
      ≤ (1 / 5) * EfEta f - 100000 * (EL12z f + EDthW f) := by linarith
    _ ≤ wip ρ (L f) f - wip ρ psiA f - wip ρ Trf f + wip ρ cf f := key
    _ = wip ρ (LGammaT α f) f := hLGT.symm
    _ = wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
          (LGammaT α f) f := by rw [hρ]

end Work.Coercivity
