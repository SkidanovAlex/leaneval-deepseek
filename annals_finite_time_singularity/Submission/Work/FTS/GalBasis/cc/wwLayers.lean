import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.GalBasis.cc.wwBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem sharp_layer_le {γ : ℝ} (hγ : 1 < γ) {G M : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t) (ht2 : 2 * t ≤ Real.pi / 4)
    (hderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt G (M θ / Real.sin (2 * θ)) θ)
    (hcont : ContinuousOn G (Set.Ioo 0 (π / 2)))
    (htend : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hint : IntervalIntegrable (fun θ => M θ / Real.sin (2 * θ)) volume 0 (2 * t))
    (hInt1 : IntegrableOn (fun θ => M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
      (Set.Ioc 0 (2 * t)))
    (hInt2 : IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (γ - 2)) (Set.Ioc 0 (2 * t))) :
    ∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ) * G θ ^ 2
      ≤ (max 1 (2 ^ (γ - 2)) / (γ - 1) * (Real.pi / 4) ^ γ)
        * (∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) := by
  have hγ0 : 0 ≤ γ := by linarith
  have ht2t : t ≤ 2 * t := by linarith
  have hCnn : 0 ≤ max 1 (2 ^ (γ - 2)) / (γ - 1) :=
    div_nonneg (le_of_lt (lt_max_of_lt_left one_pos)) (by linarith)
  have hIntB : IntervalIntegrable (fun θ => M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
      volume 0 (2 * t) := intervalIntegrable_of_integrableOn_Ioc (by linarith) hInt1
  have hBnn : 0 ≤ ∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ) :=
    intervalIntegral.integral_nonneg (by linarith) (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [hθ.1]) (by linarith [hθ.2, ht2, Real.pi_pos])) _))
  have hpt : ∀ θ' ∈ Set.Icc t (2 * t),
      (Real.sin (2 * θ')) ^ (-γ) * G θ' ^ 2
        ≤ (Real.sin (2 * θ')) ^ (-γ)
          * ((∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
            * (max 1 (2 ^ (γ - 2)) / (γ - 1) * θ' ^ (γ - 1))) := by
    intro θ' hθ'
    have hθ'0 : 0 < θ' := by linarith [hθ'.1]
    have hθ'π : θ' ≤ Real.pi / 4 := by linarith [hθ'.2, ht2]
    have hsub : Set.uIcc 0 θ' ⊆ Set.uIcc 0 (2 * t) := by
      rw [uIcc_of_le hθ'0.le, uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc le_rfl hθ'.2
    have hs := slice_sharp hγ hθ'0 hθ'π hderiv hcont htend (hint.mono_set hsub)
      (hInt1.mono_set (fun x hx => ⟨hx.1, le_trans hx.2 hθ'.2⟩))
      (hInt2.mono_set (fun x hx => ⟨hx.1, le_trans hx.2 hθ'.2⟩))
    have hmono : (∫ θ in (0 : ℝ)..θ', M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
        ≤ ∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ) := by
      refine intervalIntegral.integral_mono_interval le_rfl hθ'0.le hθ'.2 ?_ hIntB
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [hθ.1]) (by linarith [hθ.2, ht2, Real.pi_pos])) _)
    have h4 : (∫ θ in (0 : ℝ)..θ', M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
          * (max 1 (2 ^ (γ - 2)) * θ' ^ (γ - 1) / (γ - 1))
          = max 1 (2 ^ (γ - 2)) / (γ - 1)
            * ((∫ θ in (0 : ℝ)..θ', M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
              * θ' ^ (γ - 1)) := by ring
    rw [h4] at hs
    have h5 : (∫ θ in (0 : ℝ)..θ', M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) * θ' ^ (γ - 1)
        ≤ (∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
          * θ' ^ (γ - 1) :=
      mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (le_of_lt hθ'0) _)
    have h6 : max 1 (2 ^ (γ - 2)) / (γ - 1)
          * ((∫ θ in (0 : ℝ)..θ', M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) * θ' ^ (γ - 1))
        ≤ max 1 (2 ^ (γ - 2)) / (γ - 1)
          * ((∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
            * θ' ^ (γ - 1)) :=
      mul_le_mul_of_nonneg_left h5 hCnn
    have h7 : max 1 (2 ^ (γ - 2)) / (γ - 1)
          * ((∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
            * θ' ^ (γ - 1))
        = (∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
          * (max 1 (2 ^ (γ - 2)) / (γ - 1) * θ' ^ (γ - 1)) := by ring
    have h8 : max 1 (2 ^ (γ - 2)) / (γ - 1)
          * ((∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
            * θ' ^ (γ - 1))
        ≤ (∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
          * (max 1 (2 ^ (γ - 2)) / (γ - 1) * θ' ^ (γ - 1)) := le_of_eq h7
    have h9 : G θ' ^ 2
        ≤ (∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
          * (max 1 (2 ^ (γ - 2)) / (γ - 1) * θ' ^ (γ - 1)) := le_trans hs (le_trans h6 h8)
    exact mul_le_mul_of_nonneg_left h9 (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ'0
      (by linarith [hθ'π, Real.pi_pos]))) _)
  have hcontL : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ) * G θ ^ 2)
      (Set.uIcc t (2 * t)) := by
    rw [Set.uIcc_of_le ht2t]
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.rpow_const
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
      intro θ hθ; left
      exact ne_of_gt (sin_two_pos (by linarith [hθ.1]) (by linarith [hθ.2, ht2, Real.pi_pos]))
    · exact ((hcont.mono (fun θ hθ => ⟨by linarith [hθ.1],
        by linarith [hθ.2, ht2, Real.pi_pos]⟩))).pow 2
  have hcontR : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ)
      * ((∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
        * (max 1 (2 ^ (γ - 2)) / (γ - 1) * θ ^ (γ - 1)))) (Set.uIcc t (2 * t)) := by
    rw [Set.uIcc_of_le ht2t]
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.rpow_const
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
      intro θ hθ; left
      exact ne_of_gt (sin_two_pos (by linarith [hθ.1]) (by linarith [hθ.2, ht2, Real.pi_pos]))
    · refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.rpow_const continuousOn_id ?_
      intro θ hθ; left; exact ne_of_gt (by linarith [hθ.1])
  have hmono := intervalIntegral.integral_mono_on ht2t hcontL.intervalIntegrable
    (hcontR.intervalIntegrable (μ := volume)) hpt
  have hmono2 : ∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ)
      * ((∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
        * (max 1 (2 ^ (γ - 2)) / (γ - 1) * θ ^ (γ - 1)))
      = (∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
        * (max 1 (2 ^ (γ - 2)) / (γ - 1))
        * (∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ) * θ ^ (γ - 1)) := by
    rw [show (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ)
          * ((∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
            * (max 1 (2 ^ (γ - 2)) / (γ - 1) * θ ^ (γ - 1))))
        = (fun θ : ℝ => ((∫ θ in (0 : ℝ)..(2 * t), M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
            * (max 1 (2 ^ (γ - 2)) / (γ - 1))) * ((Real.sin (2 * θ)) ^ (-γ) * θ ^ (γ - 1)))
        from funext (fun θ => by ring)]
    exact intervalIntegral.integral_const_mul _ _
  rw [hmono2] at hmono
  have hpow := layer_int_pow_le hγ0 ht ht2
  exact le_trans hmono (le_trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg hBnn hCnn))
    (le_of_eq (by ring)))

/-- **Crude layer bound** (for `γ ≤ 1`, where the Hardy weight is not integrable). -/
theorem crude_layer_le {γ : ℝ} {G M : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t) (ht8 : 2 * t ≤ Real.pi / 8)
    (hderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt G (M θ / Real.sin (2 * θ)) θ)
    (hcont : ContinuousOn G (Set.Ioo 0 (π / 2)))
    (hIntM1 : IntegrableOn (fun θ => M θ / Real.sin (2 * θ)) (Set.Ioc t (Real.pi / 4)))
    (hIntM2 : IntegrableOn (fun θ => (M θ / Real.sin (2 * θ)) ^ 2) (Set.Ioc 0 (Real.pi / 2)))
    (hIntG : IntegrableOn (fun θ => G θ ^ 2) (Set.Ioc t (Real.pi / 4))) :
    ∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ) * G θ ^ 2
      ≤ (∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ))
        * (16 / Real.pi * (∫ θ in (Real.pi / 8)..(Real.pi / 4), G θ ^ 2)
          + Real.pi / 2 * (∫ θ in (0 : ℝ)..(Real.pi / 2),
              (M θ / Real.sin (2 * θ)) ^ 2)) := by
  have ht_pi8 : t < Real.pi / 8 := by linarith
  have ht_pi4 : t < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpos8 : (0 : ℝ) < Real.pi / 8 := by linarith [Real.pi_pos]
  have hle84 : Real.pi / 8 ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have hvol : ∀ {a b : ℝ}, volume (Set.Ioc a b) ≠ ⊤ := fun {a b} => by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hIntG' : IntegrableOn (fun θ => G θ ^ 2) (Set.Ioc (Real.pi / 8) (Real.pi / 4)) :=
    hIntG.mono_set (fun x hx => ⟨lt_trans ht_pi8 hx.1, hx.2⟩)
  set A := ∫ θ in (Real.pi / 8)..(Real.pi / 4), G θ ^ 2 with hA
  set D := ∫ θ in (0 : ℝ)..(Real.pi / 2), (M θ / Real.sin (2 * θ)) ^ 2 with hD
  have hAn : 0 ≤ A := intervalIntegral.integral_nonneg hle84 (fun θ _ => sq_nonneg _)
  have hDn : 0 ≤ D := intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    (fun θ _ => sq_nonneg _)
  have hptσ : ∀ θ' ∈ Set.Icc t (2 * t), ∀ σ ∈ Set.Icc (Real.pi / 8) (Real.pi / 4),
      G θ' ^ 2 ≤ 2 * G σ ^ 2 + Real.pi / 2 * D := by
    intro θ' hθ' σ hσ
    have hθ'0 : 0 < θ' := lt_of_lt_of_le ht hθ'.1
    have hθ'σ : θ' ≤ σ := by linarith [hθ'.2, ht8, hσ.1]
    have hσ2 : σ < Real.pi / 2 := by linarith [hσ.2, Real.pi_pos]
    have hIntM1w : IntervalIntegrable (fun θ => M θ / Real.sin (2 * θ)) volume t (Real.pi / 4) :=
      intervalIntegrable_of_integrableOn_Ioc ht_pi4.le hIntM1
    have hIntM2w : IntervalIntegrable (fun θ => (M θ / Real.sin (2 * θ)) ^ 2)
        volume 0 (Real.pi / 2) :=
      intervalIntegrable_of_integrableOn_Ioc (by linarith [Real.pi_pos]) hIntM2
    have hFTC : ∫ x in θ'..σ, M x / Real.sin (2 * x) = G σ - G θ' := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ'σ ?_ ?_ ?_
      · exact hcont.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, hσ2]⟩)
      · intro x hx; exact hderiv x ⟨by linarith [hx.1], by linarith [hx.2, hσ2]⟩
      · refine hIntM1w.mono_set ?_
        rw [uIcc_of_le hθ'σ, uIcc_of_le ht_pi4.le]
        exact fun x hx => ⟨le_trans hθ'.1 hx.1, le_trans hx.2 hσ.2⟩
    have hcs : (∫ x in θ'..σ, M x / Real.sin (2 * x)) ^ 2
        ≤ (σ - θ') * (∫ x in θ'..σ, (M x / Real.sin (2 * x)) ^ 2) := by
      have hu : IntegrableOn (fun x => (M x / Real.sin (2 * x)) ^ 2) (Set.Ioc θ' σ) :=
        hIntM2.mono_set (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, hσ2]⟩)
      have hv : IntegrableOn (fun x => (1 : ℝ) ^ 2) (Set.Ioc θ' σ) :=
        integrableOn_const (hvol (a := θ') (b := σ))
      simpa [mul_comm] using cs_interval hθ'σ hu hv
    have hDle : (∫ x in θ'..σ, (M x / Real.sin (2 * x)) ^ 2) ≤ D := by
      rw [hD]
      exact intervalIntegral.integral_mono_interval (by linarith [Real.pi_pos]) hθ'σ
        (le_of_lt hσ2) (Filter.Eventually.of_forall fun x => sq_nonneg _) hIntM2w
    have h1 : (G σ - G θ') ^ 2 ≤ (σ - θ') * D := by
      rw [← hFTC]
      exact le_trans hcs (mul_le_mul_of_nonneg_left hDle (by linarith))
    have h2 : (σ - θ') * D ≤ Real.pi / 4 * D :=
      mul_le_mul_of_nonneg_right (by linarith [hσ.2, hθ'0]) hDn
    have h3 : (G σ - G θ') ^ 2 ≤ Real.pi / 4 * D := le_trans h1 h2
    have h4 : G θ' ^ 2 ≤ 2 * G σ ^ 2 + 2 * (G σ - G θ') ^ 2 := by
      nlinarith [sq_nonneg (2 * G σ - G θ')]
    have h5 : 2 * (G σ - G θ') ^ 2 ≤ Real.pi / 2 * D := by linarith
    linarith
  have havg : ∀ θ' ∈ Set.Icc t (2 * t),
      G θ' ^ 2 * (Real.pi / 8) ≤ 2 * A + Real.pi / 2 * D * (Real.pi / 8) := by
    intro θ' hθ'
    have hint1 : IntervalIntegrable (fun _ : ℝ => G θ' ^ 2) volume (Real.pi / 8)
        (Real.pi / 4) :=
      intervalIntegrable_of_integrableOn_Ioc hle84
        (integrableOn_const (hvol (a := Real.pi / 8) (b := Real.pi / 4)))
    have hint2 : IntervalIntegrable (fun σ => 2 * G σ ^ 2 + Real.pi / 2 * D) volume
        (Real.pi / 8) (Real.pi / 4) :=
      intervalIntegrable_of_integrableOn_Ioc hle84
        ((hIntG'.const_mul 2).add
          (integrableOn_const (hvol (a := Real.pi / 8) (b := Real.pi / 4))))
    have hmono := intervalIntegral.integral_mono_on hle84 hint1 hint2
      (fun σ hσ => hptσ θ' hθ' σ hσ)
    have hL : ∫ σ in (Real.pi / 8)..(Real.pi / 4), G θ' ^ 2
        = G θ' ^ 2 * (Real.pi / 8) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hIntG'' : IntervalIntegrable (fun σ => 2 * G σ ^ 2) volume (Real.pi / 8)
        (Real.pi / 4) :=
      intervalIntegrable_of_integrableOn_Ioc hle84 (hIntG'.const_mul 2)
    have hIntD'' : IntervalIntegrable (fun _ : ℝ => Real.pi / 2 * D) volume (Real.pi / 8)
        (Real.pi / 4) :=
      intervalIntegrable_of_integrableOn_Ioc hle84
        (integrableOn_const (hvol (a := Real.pi / 8) (b := Real.pi / 4)))
    have hR : ∫ σ in (Real.pi / 8)..(Real.pi / 4), (2 * G σ ^ 2 + Real.pi / 2 * D)
        = 2 * A + Real.pi / 2 * D * (Real.pi / 8) := by
      rw [intervalIntegral.integral_add hIntG'' hIntD'', intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul, hA]
      ring
    rw [hL, hR] at hmono
    exact hmono
  have hstep : ∀ θ ∈ Set.Icc t (2 * t),
      (Real.sin (2 * θ)) ^ (-γ) * G θ ^ 2
        ≤ (Real.sin (2 * θ)) ^ (-γ) * (2 * (Real.pi / 8)⁻¹ * A + Real.pi / 2 * D) := by
    intro θ hθ
    have h1 : G θ ^ 2 ≤ 2 * (Real.pi / 8)⁻¹ * A + Real.pi / 2 * D := by
      have hkey := havg θ ⟨hθ.1, hθ.2⟩
      have h7 : G θ ^ 2 * (Real.pi / 8) * (Real.pi / 8)⁻¹ = G θ ^ 2 := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos8), mul_one]
      have h8 : (2 * A + Real.pi / 2 * D * (Real.pi / 8)) * (Real.pi / 8)⁻¹
          = 2 * (Real.pi / 8)⁻¹ * A + Real.pi / 2 * D := by
        field_simp
      have h9 := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr hpos8.le)
      rw [h7, h8] at h9
      exact h9
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [hθ.1]) (by linarith [hθ.2, ht8, Real.pi_pos])) _)
  have ht2t : t ≤ 2 * t := by linarith
  have hcontL : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ) * G θ ^ 2)
      (Set.uIcc t (2 * t)) := by
    rw [Set.uIcc_of_le ht2t]
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.rpow_const
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
      intro θ hθ; left
      exact ne_of_gt (sin_two_pos (by linarith [hθ.1]) (by linarith [hθ.2, ht8, Real.pi_pos]))
    · exact ((hcont.mono (fun θ hθ => ⟨by linarith [hθ.1],
        by linarith [hθ.2, ht8, Real.pi_pos]⟩))).pow 2
  have hcontR : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ)
      * (2 * (Real.pi / 8)⁻¹ * A + Real.pi / 2 * D)) (Set.uIcc t (2 * t)) := by
    rw [Set.uIcc_of_le ht2t]
    refine ContinuousOn.mul ?_ continuousOn_const
    refine ContinuousOn.rpow_const
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
    intro θ hθ; left
    exact ne_of_gt (sin_two_pos (by linarith [hθ.1]) (by linarith [hθ.2, ht8, Real.pi_pos]))
  have hmono := intervalIntegral.integral_mono_on ht2t hcontL.intervalIntegrable
    (hcontR.intervalIntegrable (μ := volume)) hstep
  have hmono2 : ∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ)
      * (2 * (Real.pi / 8)⁻¹ * A + Real.pi / 2 * D)
      = (2 * (Real.pi / 8)⁻¹ * A + Real.pi / 2 * D)
        * (∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ)) := by
    rw [show (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ)
          * (2 * (Real.pi / 8)⁻¹ * A + Real.pi / 2 * D))
        = (fun θ : ℝ => (2 * (Real.pi / 8)⁻¹ * A + Real.pi / 2 * D)
          * (Real.sin (2 * θ)) ^ (-γ)) from funext (fun θ => by ring)]
    exact intervalIntegral.integral_const_mul _ _
  rw [hmono2] at hmono
  refine le_trans hmono ?_
  have hpi : 2 * (Real.pi / 8)⁻¹ = 16 / Real.pi := by
    rw [show (Real.pi / 8)⁻¹ = 8 / Real.pi by rw [inv_div]]
    ring
  rw [hpi, mul_comm]

end Work.FTS.GalBasis.cc
