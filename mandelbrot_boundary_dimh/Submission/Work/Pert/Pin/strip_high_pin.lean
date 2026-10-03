import Mathlib
import Submission.Work.Pert.goodP_high_strip
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.Ksub2.walk_explicit
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.Ksub2.Xc_sharp_on_strip
import Submission.Work.Pert.qadm
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.PinFromCoord.gate_aux
import Submission.Work.Pert.Pin.Phi_dev_gate_strip_v2
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.Pin

open MandelDim Complex Set Metric
open scoped Topology

set_option maxHeartbeats 4000000

private lemma sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- The arithmetic of the Rouché covering at `w`: with the deviation bound
`Cdm (1 + log (2+M) + log (2+|Im w|)) + |Im w|/20` and the clearance `|Im w| - Ξ - 1 ≥ 2`, the
covering radius `(H - Ξ - 1)/(8√2)` dominates the deviation as soon as
`H ≥ Ξ + Cthr (1 + log M)` and `Cthr` dominates `270 Cdm`, `60 (Ξ+1)` and `129600 Cdm²`. -/
private lemma strip_arith {Ξ H Cdm Cthr M : ℝ}
    (hΞ : 0 < Ξ) (hCdm : 0 < Cdm) (hCthr : 0 < Cthr) (hM2 : 2 ≤ M) (hH2 : 2 ≤ H)
    (hH : Ξ + Cthr * (1 + Real.log M) ≤ H)
    (hA : 270 * Cdm ≤ Cthr) (hB : 60 * (Ξ + 1) ≤ Cthr) (hC : 129600 * Cdm ^ 2 ≤ Cthr) :
    Cdm * (1 + Real.log (2 + M) + Real.log (2 + H)) + H / 20 + (Ξ + 1) / (8 * Real.sqrt 2)
      < H / (8 * Real.sqrt 2) := by
  have hsq2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  set θ : ℝ := 1 / (8 * Real.sqrt 2) - 1 / 20 with hθdef
  have hθ30 : 1 / 30 ≤ θ := by
    have h1 : 8 * Real.sqrt 2 ≤ 12 := by nlinarith [sqrt_two_le_three_halves]
    have h2 : (1 : ℝ) / 12 ≤ 1 / (8 * Real.sqrt 2) :=
      one_div_le_one_div_of_le (by positivity) h1
    rw [hθdef]; linarith
  have hθpos : 0 < θ := by linarith
  have hHC : Cthr ≤ H := by
    have h1 : Cthr * 1 ≤ Cthr * (1 + Real.log M) :=
      mul_le_mul_of_nonneg_left (by linarith) hCthr.le
    linarith
  have hTH : θ * Cthr ≤ θ * H := mul_le_mul_of_nonneg_left hHC hθpos.le
  -- ## bound 1
  have hb1 : Cdm * (1 + Real.log (2 + M)) ≤ θ * H / 3 := by
    have hlog2M : 1 + Real.log (2 + M) ≤ 3 * (1 + Real.log M) := by
      have h1 : Real.log (2 + M) ≤ Real.log (2 * M) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_mul (by norm_num) (by linarith : (M : ℝ) ≠ 0)] at h1
      linarith
    have h3 : 3 * Cdm ≤ θ * Cthr / 3 := by
      have h4 : (1 / 30 : ℝ) * Cthr ≤ θ * Cthr := mul_le_mul_of_nonneg_right hθ30 hCthr.le
      linarith
    have h4 : Cdm * (3 * (1 + Real.log M)) ≤ (θ * Cthr / 3) * (1 + Real.log M) := by
      rw [show Cdm * (3 * (1 + Real.log M)) = (3 * Cdm) * (1 + Real.log M) from by ring]
      exact mul_le_mul_of_nonneg_right h3 (by linarith)
    have h5 : (θ * Cthr / 3) * (1 + Real.log M) ≤ θ * H / 3 := by
      have h6 : Cthr * (1 + Real.log M) ≤ H := by linarith
      nlinarith [hθpos, h6]
    have h7 : Cdm * (1 + Real.log (2 + M)) ≤ Cdm * (3 * (1 + Real.log M)) :=
      mul_le_mul_of_nonneg_left hlog2M hCdm.le
    linarith
  -- ## bound 2
  have hb2 : Cdm * Real.log (2 + H) ≤ θ * H / 3 := by
    have h1 : Real.log (2 + H) ≤ 2 * Real.sqrt (2 + H) := by
      have h := Real.log_le_rpow_div (x := 2 + H) (ε := 1 / 2) (by positivity) (by norm_num)
      have h2 : (2 + H) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * Real.sqrt (2 + H) := by
        rw [Real.sqrt_eq_rpow]; ring
      linarith [h2.le, h2.ge]
    have h2 : 12 * Cdm / θ ≤ Real.sqrt (2 + H) := by
      have h3 : (12 * Cdm / θ) ^ 2 ≤ 2 + H := by
        have h4 : (12 * Cdm / θ) ^ 2 = 144 * Cdm ^ 2 / θ ^ 2 := by ring
        rw [h4, div_le_iff₀ (by positivity : (0 : ℝ) < θ ^ 2)]
        have h5 : (1 / 30 : ℝ) ^ 2 ≤ θ ^ 2 := by nlinarith [hθ30, hθpos]
        have h6 : 144 * Cdm ^ 2 ≤ Cthr * (1 / 30 : ℝ) ^ 2 := by
          have h7 : Cthr * (1 / 30 : ℝ) ^ 2 = Cthr / 900 := by ring
          rw [h7, le_div_iff₀ (by norm_num : (0:ℝ) < 900)]
          nlinarith [hC]
        nlinarith [h6, h5, hCthr.le, hHC]
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 12 * Cdm / θ)]
      exact Real.sqrt_le_sqrt h3
    have h10 : 12 * Cdm ≤ θ * Real.sqrt (2 + H) := by
      have h11 := (div_le_iff₀ hθpos).mp h2
      linarith [h11]
    have h12 : 2 * Cdm * Real.sqrt (2 + H) ≤ θ * (2 + H) / 6 := by
      have h13 := mul_le_mul_of_nonneg_right h10
        (by positivity : (0 : ℝ) ≤ Real.sqrt (2 + H) / 6)
      have h14 : Real.sqrt (2 + H) * Real.sqrt (2 + H) = 2 + H := by
        rw [← sq, Real.sq_sqrt (by positivity)]
      nlinarith [h13, h14, hθpos]
    have h15 : θ * (2 + H) / 6 ≤ θ * H / 3 := by nlinarith [hθpos, hH2]
    have h16 : Cdm * Real.log (2 + H) ≤ Cdm * (2 * Real.sqrt (2 + H)) :=
      mul_le_mul_of_nonneg_left h1 hCdm.le
    linarith
  -- ## bound 3
  have hb3 : (Ξ + 1) / (8 * Real.sqrt 2) < θ * H / 3 := by
    have h1 : 2 * (Ξ + 1) / 3 ≤ θ * Cthr / 3 := by
      have h2 : (1 / 30 : ℝ) * Cthr ≤ θ * Cthr := mul_le_mul_of_nonneg_right hθ30 hCthr.le
      linarith
    have h3 : θ * Cthr / 3 ≤ θ * H / 3 := by linarith [hTH]
    have h4 : (Ξ + 1) / (8 * Real.sqrt 2) < 2 * (Ξ + 1) / 3 := by
      have h5 : (1 : ℝ) / (8 * Real.sqrt 2) < 2 / 3 := by
        rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * Real.sqrt 2)
          (by norm_num : (0 : ℝ) < 3)]
        nlinarith [hsq2pos, Real.one_lt_sqrt_two]
      have h6 : 0 < Ξ + 1 := by linarith
      calc (Ξ + 1) / (8 * Real.sqrt 2) = (Ξ + 1) * (1 / (8 * Real.sqrt 2)) := by ring
        _ < (Ξ + 1) * (2 / 3) := mul_lt_mul_of_pos_left h5 h6
        _ = 2 * (Ξ + 1) / 3 := by ring
    linarith [h1, h3, h4]
  -- ## assembly
  have hkey : Cdm * (1 + Real.log (2 + M) + Real.log (2 + H)) + H / 20
        + (Ξ + 1) / (8 * Real.sqrt 2) < θ * H + H / 20 := by
    have hsplit : Cdm * (1 + Real.log (2 + M) + Real.log (2 + H))
        = Cdm * (1 + Real.log (2 + M)) + Cdm * Real.log (2 + H) := by ring
    have hsum : θ * H / 3 + θ * H / 3 + θ * H / 3 = θ * H := by ring
    linarith [hsplit, hsum, hb1, hb2, hb3]
  have hfinal : θ * H + H / 20 = H / (8 * Real.sqrt 2) := by rw [hθdef]; ring_nf
  linarith [hkey, hfinal]

/-- HIGH BAND (heights `Ξ + C (1 + log M) ≤ |Im w|`): the Rouché covering at `w` gives
`w ∈ Φm '' (Qm Ξ α)`, hence level 0 and `w ∈ DphiP`. -/
theorem strip_high_pin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 0 < Ξ)
    {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀)
    {y₁ : ℝ} (hy₁ : d.η₀ < y₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ Ms : ℝ, 0 < Ms ∧ ∀ M : ℝ, Ms ≤ M →
      ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ Metric.closedBall (0 : ℂ) rr ⊆ L ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
        ∀ Φm : ℂ → ℂ, MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α) →
          Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α →
          Φm (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) →
          ∀ w : ℂ, Ξ + C * (1 + Real.log M) ≤ |w.im| → |w.re| ≤ 1 →
            w ∈ Work.Pert.DphiP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) := by
  obtain ⟨Rde, C₁, C₂, hRdepos, hC₁pos, hC₂pos, hDE⟩ := hF.2.2.2.2.1
  obtain ⟨r₀, hr₀pos, hr₀D, Csm, hCsmpos, hsmallC⟩ := Work.Pert.small_of_nearOn hd
  obtain ⟨Csh, hCshpos, Msh, hMshpos, hXcsh⟩ := Work.Pert.Ksub2.Xc_sharp_on_strip d
  -- ## the constants
  set Kp : ℝ := Csh with hKpdef
  have hKp0 : 0 ≤ Kp := by rw [hKpdef]; exact le_of_lt hCshpos
  set Cdm : ℝ := (Kp + 1 + C₂) * (2 : ℝ) ^ 44 * (1 + Ξ + 1 / Ξ + 1 / rr) with hCdmdef
  have hCdmpos : 0 < Cdm := by rw [hCdmdef]; positivity
  clear_value Cdm
  set S : ℝ := Ξ + 1 + Cdm + Rde + C₂ + Kp + 1 / Ξ + 1 / rr + (2:ℝ)^10 * Rde with hSdef
  clear_value S
  have hinvΞ : 0 < 1 / Ξ := one_div_pos.mpr hΞ
  have hinvrr : 0 < 1 / rr := one_div_pos.mpr hrr
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith
  have hSnn : 0 ≤ S := by linarith
  have hSD : Cdm ≤ S := by rw [hSdef]; linarith
  have hSR : Rde ≤ S := by rw [hSdef]; linarith
  have hS2 : C₂ ≤ S := by rw [hSdef]; linarith
  have hSX : Ξ + 1 ≤ S := by rw [hSdef]; linarith
  set Cthr : ℝ := (2 : ℝ) ^ 40 * S ^ 2 + 2 ^ 40 with hCthrdef
  have hCthrpos : 0 < Cthr := by rw [hCthrdef]; positivity
  clear_value Cthr
  have hCthrS : (2 : ℝ) ^ 40 * S ^ 2 ≤ Cthr := by rw [hCthrdef]; linarith
  have hCthrS1 : (2 : ℝ) ^ 40 * S ^ 2 + 1 ≤ Cthr := by rw [hCthrdef]; linarith
  have hSsq1 : (1 : ℝ) ≤ S ^ 2 := by nlinarith [hS1]
  have hpowS : S ≤ (2 : ℝ) ^ 40 * S ^ 2 := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ 40 * S := by nlinarith [h2, hS1]
    calc S = 1 * S := by ring
      _ ≤ ((2 : ℝ) ^ 40 * S) * S := mul_le_mul_of_nonneg_right h1 hSnn
      _ = (2 : ℝ) ^ 40 * S ^ 2 := by ring
  have hCdm_ge : (2 : ℝ) ^ 44 ≤ Cdm := by
    have h1 : (1 : ℝ) ≤ Kp + 1 + C₂ := by linarith
    have h2 : (1 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by linarith
    have h3 : (1 : ℝ) ≤ (Kp + 1 + C₂) * (1 + Ξ + 1 / Ξ + 1 / rr) := by nlinarith [h1, h2]
    have h4 : (2 : ℝ) ^ 44 ≤ (2 : ℝ) ^ 44 * ((Kp + 1 + C₂) * (1 + Ξ + 1 / Ξ + 1 / rr)) :=
      le_mul_of_one_le_right (by positivity) h3
    rw [hCdmdef]
    have heq : (Kp + 1 + C₂) * (2 : ℝ) ^ 44 * (1 + Ξ + 1 / Ξ + 1 / rr)
        = (2 : ℝ) ^ 44 * ((Kp + 1 + C₂) * (1 + Ξ + 1 / Ξ + 1 / rr)) := by ring
    rw [heq]
    exact h4
  -- basic comparisons with `Cthr`
  have hCthr2 : (2 : ℝ) ≤ Cthr := by
    have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ 40 * S ^ 2 := by
      calc (2 : ℝ) ≤ (2 : ℝ) ^ 40 := h3
        _ = (2 : ℝ) ^ 40 * 1 := by ring
        _ ≤ (2 : ℝ) ^ 40 * S ^ 2 := mul_le_mul_of_nonneg_left hSsq1 (by positivity)
    linarith [h1, hCthrS]
  have hAbig : 270 * Cdm ≤ Cthr := by
    have h270 : (270 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
    rcases lt_or_ge Cdm 1 with h | h
    · have h6 : 270 * Cdm ≤ 270 := by linarith
      have h7 : (270 : ℝ) ≤ (2 : ℝ) ^ 40 * S ^ 2 := by
        calc (270 : ℝ) ≤ (2 : ℝ) ^ 40 := h270
          _ = (2 : ℝ) ^ 40 * 1 := by ring
          _ ≤ (2 : ℝ) ^ 40 * S ^ 2 := mul_le_mul_of_nonneg_left hSsq1 (by positivity)
      linarith [h6, h7, hCthrS]
    · have h1 : Cdm ≤ Cdm ^ 2 := by
        calc Cdm = Cdm * 1 := by ring
          _ ≤ Cdm * Cdm := mul_le_mul_of_nonneg_left h hCdmpos.le
          _ = Cdm ^ 2 := by ring
      have h2 : Cdm ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hCdmpos.le hSD 2
      have h3 : 270 * Cdm ≤ 270 * Cdm ^ 2 := by linarith
      have h4 : 270 * Cdm ^ 2 ≤ (2 : ℝ) ^ 40 * Cdm ^ 2 :=
        mul_le_mul_of_nonneg_right h270 (sq_nonneg Cdm)
      have h5 : (2 : ℝ) ^ 40 * Cdm ^ 2 ≤ (2 : ℝ) ^ 40 * S ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith [h3, h4, h5, hCthrS]
  have hBbig : 60 * (Ξ + 1) ≤ Cthr := by
    have h60 : (60 : ℝ) ≤ S := by
      have h5 : (60 : ℝ) ≤ (2 : ℝ) ^ 44 := by norm_num
      linarith [h5, hCdm_ge, hSD]
    have h1 : 60 * (Ξ + 1) ≤ 60 * S := mul_le_mul_of_nonneg_left hSX (by norm_num)
    have h2 : 60 * S ≤ S ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right h60 hSnn
    have h3 : S ^ 2 ≤ (2 : ℝ) ^ 40 * S ^ 2 := by
      have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
      calc S ^ 2 = 1 * S ^ 2 := by ring
        _ ≤ (2 : ℝ) ^ 40 * S ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg S)
    linarith [h1, h2, h3, hCthrS]
  have hCbig : 129600 * Cdm ^ 2 ≤ Cthr := by
    have h1 : Cdm ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hCdmpos.le hSD 2
    have h2 : 129600 * Cdm ^ 2 ≤ (2 : ℝ) ^ 40 * S ^ 2 := by
      have h3 : (129600 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
      calc 129600 * Cdm ^ 2 ≤ (2 : ℝ) ^ 40 * Cdm ^ 2 :=
            mul_le_mul_of_nonneg_right h3 (sq_nonneg Cdm)
        _ ≤ (2 : ℝ) ^ 40 * S ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith [h2, hCthrS]
  set Ms : ℝ := max Msh (max 1024 (max (4 * Real.sqrt 2 * Rde)
      (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8)))) with hMsdef
  have hMspos : 0 < Ms := by rw [hMsdef]; positivity
  refine ⟨Cthr, hCthrpos, Ms, hMspos, ?_⟩
  intro M hM
  have hmax1 : Msh ≤ Ms := by
    rw [hMsdef]
    exact le_max_left Msh (max 1024 (max (4 * Real.sqrt 2 * Rde)
      (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8))))
  have hmax2 : 1024 ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left 1024 (max (4 * Real.sqrt 2 * Rde)
        (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8))))
      (le_max_right Msh (max 1024 (max (4 * Real.sqrt 2 * Rde)
        (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8)))))
  have hmaxX : 4 * Real.sqrt 2 * Rde ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left (4 * Real.sqrt 2 * Rde)
        (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8)))
      (le_trans (le_max_right 1024 (max (4 * Real.sqrt 2 * Rde)
          (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8))))
        (le_max_right Msh (max 1024 (max (4 * Real.sqrt 2 * Rde)
          (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8))))))
  have hmaxY : 512 * Kp ^ 2 + 8 * Kp ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8))
      (le_trans (le_max_right (4 * Real.sqrt 2 * Rde)
          (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8)))
        (le_trans (le_max_right 1024 (max (4 * Real.sqrt 2 * Rde)
            (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8))))
          (le_max_right Msh (max 1024 (max (4 * Real.sqrt 2 * Rde)
            (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8)))))))
  have hmaxZ : 4 * Ξ + 4 * Real.sqrt 2 * Rde + 8 ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_right (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8))
      (le_trans (le_max_right (4 * Real.sqrt 2 * Rde)
          (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8)))
        (le_trans (le_max_right 1024 (max (4 * Real.sqrt 2 * Rde)
            (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8))))
          (le_max_right Msh (max 1024 (max (4 * Real.sqrt 2 * Rde)
            (max (512 * Kp ^ 2 + 8 * Kp) (4 * Ξ + 4 * Real.sqrt 2 * Rde + 8)))))))
  have hMsh : Msh ≤ M := by linarith [hmax1, hM]
  have hM1024 : 1024 ≤ M := by linarith [hmax2, hM]
  have hMsqrtRde : 4 * Real.sqrt 2 * Rde ≤ M := by linarith [hmaxX, hM]
  have hMKp : 512 * Kp ^ 2 + 8 * Kp ≤ M := by linarith [hmaxY, hM]
  have hMΞRde : 4 * Ξ + 4 * Real.sqrt 2 * Rde + 8 ≤ M := by linarith [hmaxZ, hM]
  -- the pin-clearance hypothesis of the strip deviation lemma
  have hpincl : Ξ + 2 * Kp * (1 + Real.log (2 + M)) + Real.sqrt 2 * Rde ≤ M := by
    have hKpnn : 0 ≤ Kp := hKp0
    have h1 : Real.log (2 + M) ≤ 2 * Real.sqrt (2 * M) := by
      have h2 := Real.log_le_rpow_div (x := 2 + M) (ε := (1 : ℝ) / 2)
        (by linarith) (by norm_num)
      have h3 : (2 + M : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (2 + M) :=
        (Real.sqrt_eq_rpow (2 + M)).symm
      rw [h3] at h2
      have h4 : Real.sqrt (2 + M) ≤ Real.sqrt (2 * M) := by
        apply Real.sqrt_le_sqrt; linarith
      linarith
    have h5 : Real.sqrt (2 * M) = Real.sqrt 2 * Real.sqrt M := Real.sqrt_mul (by norm_num) M
    have h9 : 16 * Real.sqrt 2 * Kp ≤ Real.sqrt M := by
      have hs : (16 * Real.sqrt 2 * Kp) ^ 2 ≤ M := by
        rw [show (16 * Real.sqrt 2 * Kp) ^ 2 = 512 * Kp ^ 2 from by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring]
        linarith [hMKp]
      have h10 := Real.sqrt_le_sqrt hs
      rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 16 * Real.sqrt 2 * Kp)] at h10
    have h12 : 4 * Real.sqrt 2 * Kp * Real.sqrt M ≤ M / 4 := by
      have h13 := mul_le_mul_of_nonneg_right h9 (by positivity : (0 : ℝ) ≤ Real.sqrt M / 4)
      have h14 : Real.sqrt M * (Real.sqrt M / 4) = M / 4 := by
        have h14' := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ M)
        nlinarith [h14']
      linarith [h13, h14]
    have h6 : 2 * Kp * Real.log (2 + M) ≤ M / 4 := by
      have h15 : 2 * Kp * (2 * Real.sqrt (2 * M)) = 4 * Real.sqrt 2 * Kp * Real.sqrt M := by
        rw [h5]; ring
      have h16 : 2 * Kp * Real.log (2 + M) ≤ 2 * Kp * (2 * Real.sqrt (2 * M)) := by
        apply mul_le_mul_of_nonneg_left h1; linarith
      linarith [h15, h16, h12]
    have h10 : 2 * Kp * 1 ≤ M / 4 := by nlinarith [hMKp, hKpnn]
    have h11 : Ξ + Real.sqrt 2 * Rde ≤ M / 2 := by nlinarith [hMΞRde]
    have h17 : 2 * Kp * (1 + Real.log (2 + M)) = 2 * Kp * 1 + 2 * Kp * Real.log (2 + M) := by
      ring
    linarith [h6, h10, h11, h17]
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hM2 : (2 : ℝ) ≤ M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  -- ## the compact `L` and the tolerance `δ₀`
  set ρs : ℝ := min r₀ rr with hρsdef
  have hρspos : 0 < ρs := by rw [hρsdef]; exact lt_min hr₀pos hrr
  have hρsr₀ : ρs ≤ r₀ := by rw [hρsdef]; exact min_le_left _ _
  have hρsrr : ρs ≤ rr := by rw [hρsdef]; exact min_le_right _ _
  set δ₀ : ℝ := min (ρs / 4) (ρs / (Csm * 32 * (M + 2 + Ξ))) with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact lt_min (by linarith) (div_pos hρspos (by positivity))
  have hδ₀2ρ : 2 * δ₀ ≤ ρs := by
    have h := min_le_left (ρs / 4) (ρs / (Csm * 32 * (M + 2 + Ξ)))
    rw [hδ₀def]; linarith
  have hδ₀small : Csm * δ₀ / ρs ≤ 1 / (32 * (M + 2 + Ξ)) := by
    have h2 := min_le_right (ρs / 4) (ρs / (Csm * 32 * (M + 2 + Ξ)))
    have h3 : Csm * (ρs / (Csm * 32 * (M + 2 + Ξ))) / ρs = 1 / (32 * (M + 2 + Ξ)) := by
      field_simp
    calc Csm * δ₀ / ρs ≤ Csm * (ρs / (Csm * 32 * (M + 2 + Ξ))) / ρs := by
          apply div_le_div_of_nonneg_right _ hρspos.le
          rw [hδ₀def]
          exact mul_le_mul_of_nonneg_left h2 hCsmpos.le
      _ = 1 / (32 * (M + 2 + Ξ)) := h3
  refine ⟨Metric.closedBall (0 : ℂ) rr, isCompact_closedBall (0:ℂ) rr, hrrD,
    Set.Subset.rfl, δ₀, hδ₀pos, ?_⟩
  intro f Df u σ α hNear hf0 hInF1 hαeq hDiffu hBndu hForm hNorm hτQ hQAdm hNT Φm hΦm hz₀ hpin
  intro w hw hwre
  -- ## smallness of the perturbation data
  have hNearρ : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρs) δ₀ :=
    ⟨hNear.1, fun z hz => hNear.2.1 (Metric.closedBall_subset_closedBall hρsrr hz), hNear.2.2.1,
      fun z hz => hNear.2.2.2 z (Metric.closedBall_subset_closedBall hρsrr hz)⟩
  obtain ⟨hU1, hσ1, hA1⟩ := hsmallC (f := f) (Df := Df) (ρ := ρs) (δ₀ := δ₀) (rr := rr)
    (u := u) (σ := σ) hρspos hρsr₀ hδ₀pos hδ₀2ρ hrr hNearρ hf0 hDiffu hBndu hForm
  have hαnorm : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)) := by
    rw [hαeq]
    exact le_trans hA1 hδ₀small
  have hInF1α : MandelDim.InF1 α := by rw [hαeq]; exact hInF1
  have himinv : |(1 / α).im| ≤ (1 / α).re := Work.Pert.PinFromCoord.im_inv_le_re hInF1α
  -- ## the pin is normalized near `-M`
  have hpinbd : ‖Work.Pert.Xc d (((-M : ℝ)) : ℂ) + (((M : ℝ)) : ℂ)‖
      ≤ Kp * (1 + Real.log (2 + M)) := by
    have h1 := (hXcsh M hMsh 0 (by linarith : (0 : ℝ) ≤ M / 160)).1
    have h2 : Work.Pert.Xc d (((-M : ℝ)) : ℂ) + (((M : ℝ)) : ℂ)
        = Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ) := by
      push_cast; ring
    rw [h2]
    refine le_trans h1 ?_
    have h3 : Real.log M ≤ Real.log (2 + M) := Real.log_le_log (by linarith) (by linarith)
    have h5 : Csh * (1 + Real.log M) ≤ Kp * (1 + Real.log (2 + M)) := by
      rw [hKpdef]
      exact mul_le_mul_of_nonneg_left (by linarith) hKp0
    exact h5
  -- ## `σ ≠ 0`
  have hσne : σ ≠ 0 := by
    intro hσ0
    subst hσ0
    have hz1mem : (Complex.I * (((Ξ + 1 : ℝ)) : ℂ)) ∈ Work.Pert.Qm Ξ α := by
      rw [Work.Pert.mem_Qm_iff_marg]
      have hre : (Complex.I * (((Ξ + 1 : ℝ)) : ℂ)).re = 0 := by simp
      have him : (Complex.I * (((Ξ + 1 : ℝ)) : ℂ)).im = Ξ + 1 := by simp
      constructor
      · have h2 : Ξ + 1 - |(1 / α).im| ≤ |Ξ + 1 + (1 / α).im| := by
          simpa only [abs_neg, sub_neg_eq_add,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ Ξ + 1)] using
            abs_sub_abs_le_abs_sub (Ξ + 1) (-(1 / α).im)
        simp only [Work.Pert.margA, hre, him]
        linarith [h2, himinv, hΞ]
      · simp only [Work.Pert.margB, hre, him,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ Ξ + 1)]
        linarith
    have hself : Work.Pert.liftF u 0 α (Complex.I * (((Ξ + 1 : ℝ)) : ℂ))
        = Complex.I * (((Ξ + 1 : ℝ)) : ℂ) := by
      simp [Work.Pert.liftF, Work.Pert.sfun]
    have hb := (hNT.1.2 _ hz1mem).1
    rw [hself] at hb
    have h1 : ‖(Complex.I * (((Ξ + 1 : ℝ)) : ℂ)) - (Complex.I * (((Ξ + 1 : ℝ)) : ℂ) + 1)‖
        = 1 := by
      rw [show Complex.I * (((Ξ + 1 : ℝ)) : ℂ)
          - (Complex.I * (((Ξ + 1 : ℝ)) : ℂ) + 1) = -1 by ring, norm_neg, norm_one]
    rw [h1] at hb
    norm_num at hb
  -- ## the deviation bound on the strip (delegated)
  obtain ⟨Cdev, hCdevpos, hCdevle, hdev⟩ :=
    Work.Pert.Pin.Phi_dev_gate_strip_v2 d hF hΞ hrr
      (by norm_num at hM1024 ⊢; linarith) hKp0 hRdepos hC₁pos hC₂pos hpincl
      hInF1α hαnorm hQAdm hσne hNorm hDiffu hBndu hτQ hNT hΦm hDE hz₀ hpin hpinbd
  -- ## the covering point `w`
  set H : ℝ := |w.im| with hHdef
  clear_value H
  have hHge : Ξ + Cthr * (1 + Real.log M) ≤ H := hw
  have hHge2 : Ξ + Cthr ≤ H := by
    have h1 : Cthr * 1 ≤ Cthr * (1 + Real.log M) :=
      mul_le_mul_of_nonneg_left (by linarith) hCthrpos.le
    linarith
  have hHgt : Ξ + 1 ≤ H := by linarith [hHge2, hΞ, hCthr2]
  have hH2 : 2 ≤ H := by linarith [hHge2, hCthr2]
  -- ## `w ∈ Qm Ξ α` and the clearance
  have hmargA : H - Ξ - 1 ≤ Work.Pert.margA Ξ α w := by
    have hwre1 : -(1 : ℝ) ≤ w.re := (abs_le.mp hwre).1
    have h := abs_sub_abs_le_abs_sub w.im (-(1 / α).im)
    have h1 : H - |(1 / α).im| ≤ |w.im + (1 / α).im| := by
      rw [abs_neg, sub_neg_eq_add] at h
      rw [hHdef]
      linarith
    simp only [Work.Pert.margA]
    linarith [h1, himinv, hwre1, hΞ]
  have hmargB : H - Ξ - 1 ≤ Work.Pert.margB Ξ α w := by
    have hwre2 : w.re ≤ 1 := (abs_le.mp hwre).2
    simp only [Work.Pert.margB, ← hHdef]
    linarith
  have hclr : H - Ξ - 1 ≤ min (Work.Pert.margA Ξ α w) (Work.Pert.margB Ξ α w) :=
    le_min hmargA hmargB
  have hwQ : w ∈ Work.Pert.Qm Ξ α := by
    rw [Work.Pert.mem_Qm_iff_marg]
    constructor
    · linarith [hmargA, hHgt, hΞ]
    · linarith [hmargB, hHgt, hΞ]
  set r : ℝ := (H - Ξ - 1) / (2 * Real.sqrt 2) with hrdef
  have hHΞ1 : 0 < H - Ξ - 1 := by linarith [hH2, hΞ]
  have hsq2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hrpos : 0 < r := by
    have h2 : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
    exact div_pos hHΞ1 h2
  clear_value r
  have hr2 : 2 * r = (H - Ξ - 1) / Real.sqrt 2 := by
    rw [hrdef]; field_simp
  have hball2 : Metric.ball w (2 * r) ⊆ Work.Pert.Qm Ξ α := by
    rw [hr2]
    refine Work.Pert.ball_subset_Qm_of_marg_le (by positivity) ?_
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hsq2pos)]
    exact hclr
  have hclosedQ : Metric.closedBall w r ⊆ Work.Pert.Qm Ξ α := by
    intro z hz
    apply hball2
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  -- ## the derivative condition on the covering ball
  have hRdeC : 2 * Real.sqrt 2 * Rde + 1 ≤ Cthr := by
    have h1 : 2 * Real.sqrt 2 ≤ 4 := by nlinarith [hsq2pos, sqrt_two_le_three_halves]
    have h2 : 2 * Real.sqrt 2 * Rde ≤ 4 * Rde := mul_le_mul_of_nonneg_right h1 hRdepos.le
    have h3 : 4 * Rde ≤ 4 * S := mul_le_mul_of_nonneg_left hSR (by norm_num)
    have h4 : 4 * S ≤ (2 : ℝ) ^ 40 * S ^ 2 := by
      have h5 : (4 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
      have h6 : 4 * S ≤ (2 : ℝ) ^ 40 * S := mul_le_mul_of_nonneg_right h5 hSnn
      have h7 : (2 : ℝ) ^ 40 * S ≤ (2 : ℝ) ^ 40 * S ^ 2 := by
        calc (2 : ℝ) ^ 40 * S = ((2 : ℝ) ^ 40 * S) * 1 := by ring
          _ ≤ ((2 : ℝ) ^ 40 * S) * S := mul_le_mul_of_nonneg_left hS1 (by positivity)
          _ = (2 : ℝ) ^ 40 * S ^ 2 := by ring
      linarith
    linarith [h2, h3, h4, hCthrS1]
  have hC2C : 128 * Real.sqrt 2 * C₂ + 1 ≤ Cthr := by
    have h1 : 128 * Real.sqrt 2 ≤ 256 := by nlinarith [hsq2pos, sqrt_two_le_three_halves]
    have h2 : 128 * Real.sqrt 2 * C₂ ≤ 256 * C₂ := mul_le_mul_of_nonneg_right h1 hC₂pos.le
    have h3 : 256 * C₂ ≤ 256 * S := mul_le_mul_of_nonneg_left hS2 (by norm_num)
    have h4 : 256 * S ≤ (2 : ℝ) ^ 40 * S ^ 2 := by
      have h5 : (256 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
      have h6 : 256 * S ≤ (2 : ℝ) ^ 40 * S := mul_le_mul_of_nonneg_right h5 hSnn
      have h7 : (2 : ℝ) ^ 40 * S ≤ (2 : ℝ) ^ 40 * S ^ 2 := by
        calc (2 : ℝ) ^ 40 * S = ((2 : ℝ) ^ 40 * S) * 1 := by ring
          _ ≤ ((2 : ℝ) ^ 40 * S) * S := mul_le_mul_of_nonneg_left hS1 (by positivity)
          _ = (2 : ℝ) ^ 40 * S ^ 2 := by ring
      linarith
    linarith [h2, h3, h4, hCthrS1]
  have hRdeC₂ : max Rde (64 * C₂) ≤ r := by
    have hHm : Cthr - 1 ≤ H - Ξ - 1 := by linarith [hHge2]
    rw [hrdef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)]
    rcases le_total Rde (64 * C₂) with h | h
    · rw [max_eq_right h]
      have h2 : 64 * C₂ * (2 * Real.sqrt 2) + 1 ≤ Cthr := by
        rw [show 64 * C₂ * (2 * Real.sqrt 2) = 128 * Real.sqrt 2 * C₂ by ring]
        exact hC2C
      linarith [h2, hHm]
    · rw [max_eq_left h]
      have h2 : Rde * (2 * Real.sqrt 2) + 1 ≤ Cthr := by
        rw [show Rde * (2 * Real.sqrt 2) = 2 * Real.sqrt 2 * Rde by ring]
        exact hRdeC
      linarith [h2, hHm]
  have hder1 : ∀ ζ ∈ Metric.closedBall w r, ‖deriv Φm ζ - 1‖ ≤ 1 / 2 := by
    intro ζ hζ
    have hballζ : Metric.ball ζ r ⊆ Work.Pert.Qm Ξ α := by
      intro z hz
      apply hball2
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_closedBall] at hζ
      have h2 : dist z w ≤ dist z ζ + dist ζ w := dist_triangle _ _ _
      linarith
    have h1 := Work.Pert.Ksub2.deriv_Phi_sub_one_le (F := Work.Pert.liftF u σ α) (Φ := Φm)
      (α := α) (ξ₁ := Ξ) hRdepos hC₁pos hC₂pos hDE hNT hΦm ζ r hRdeC₂ hballζ
    have h2 : C₂ / r ≤ 1 / 64 := by
      rw [div_le_iff₀ hrpos]
      have h3 : 64 * C₂ ≤ max Rde (64 * C₂) := le_max_right _ _
      linarith [hRdeC₂]
    linarith
  have hdiff1 : ∀ ζ ∈ Metric.closedBall w r, DifferentiableAt ℂ Φm ζ := fun ζ hζ =>
    hΦm.1.differentiableAt ((Work.Pert.isOpen_Qm' Ξ α).mem_nhds (hclosedQ hζ))
  -- ## the covering
  have hcover := Work.Pert.image_cover_centered (Φ := Φm) (z₀ := w) (r := r) hrpos hdiff1 hder1
  have hdevw : ‖Φm w - w‖ ≤ Cdm * (1 + Real.log (2 + M) + Real.log (2 + H)) + H / 20 := by
    have hwr1 : -(1 : ℝ) ≤ w.re := (abs_le.mp hwre).1
    have hwr2 : w.re ≤ 1 := (abs_le.mp hwre).2
    have h4Rde : Ξ + 2 + Real.sqrt 2 * Rde ≤ H := by
      have h2S : (2 : ℝ) ≤ S := le_trans (by norm_num : (2 : ℝ) ≤ (2 : ℝ) ^ 44)
        (le_trans hCdm_ge hSD)
      have hSbig : Real.sqrt 2 ≤ S := le_trans sqrt_two_le_three_halves
        (le_trans (by norm_num : (3 : ℝ) / 2 ≤ 2) h2S)
      have h6 : Real.sqrt 2 * Rde ≤ S * S :=
        le_trans (mul_le_mul_of_nonneg_left hSR (by positivity))
          (mul_le_mul_of_nonneg_right hSbig hSnn)
      have h9 : (2 : ℝ) ≤ S * S := by nlinarith [h2S]
      have h10 : 2 + Real.sqrt 2 * Rde ≤ 4 * (S * S) := by
        have h10a : 2 + Real.sqrt 2 * Rde ≤ S * S + S * S := add_le_add h9 h6
        have h10b : S * S + S * S = 2 * (S * S) := by ring
        have h10c : (2 : ℝ) * (S * S) ≤ 4 * (S * S) :=
          mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) (by positivity)
        linarith [h10a, h10b, h10c]
      have h11 : 4 * (S * S) ≤ (2 : ℝ) ^ 40 * (S * S) :=
        mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ (2 : ℝ) ^ 40) (by positivity)
      have h13 : (2 : ℝ) ^ 40 * (S * S) = (2 : ℝ) ^ 40 * S ^ 2 := by ring
      have h5 : 2 + Real.sqrt 2 * Rde ≤ Cthr :=
        le_trans (le_trans h10 h11) (le_trans (le_of_eq h13) hCthrS)
      have hlog1 : (1 : ℝ) ≤ 1 + Real.log M := by linarith
      calc Ξ + 2 + Real.sqrt 2 * Rde = Ξ + (2 + Real.sqrt 2 * Rde) := by ring
        _ ≤ Ξ + Cthr := add_le_add (le_refl Ξ) h5
        _ ≤ Ξ + Cthr * (1 + Real.log M) :=
            add_le_add (le_refl Ξ) (le_mul_of_one_le_right hCthrpos.le hlog1)
        _ ≤ H := hHge
    have h1 := hdev w hwQ (by linarith [hwr1, hΞ]) (by linarith [hwr2])
      (by rw [← hHdef]; exact h4Rde)
    refine le_trans h1 ?_
    have hnn : (0 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + |w.im|) := by
      have h6 : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
      have h7 : 0 ≤ Real.log (2 + |w.im|) := Real.log_nonneg (by linarith [abs_nonneg w.im])
      linarith
    have h2 : Cdev * (1 + Real.log (2 + M) + Real.log (2 + |w.im|))
        ≤ Cdm * (1 + Real.log (2 + M) + Real.log (2 + |w.im|)) := by
      rw [hCdmdef]
      exact mul_le_mul_of_nonneg_right hCdevle hnn
    rw [hHdef]
    linarith [h2]
  have hkey := strip_arith (Ξ := Ξ) (H := H) (Cdm := Cdm) (Cthr := Cthr) (M := M)
    hΞ hCdmpos hCthrpos hM2 hH2 hHge hAbig hBbig hCbig
  have hkey2 : Cdm * (1 + Real.log (2 + M) + Real.log (2 + H)) + H / 20
      < (H - Ξ - 1) / (8 * Real.sqrt 2) := by
    have heq : H / (8 * Real.sqrt 2) - (Ξ + 1) / (8 * Real.sqrt 2)
        = (H - Ξ - 1) / (8 * Real.sqrt 2) := by
      rw [div_sub_div_same]; ring
    linarith [hkey, heq]
  have hwmem : w ∈ Metric.ball (Φm w) (r / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev, hrdef, div_div,
      show (2 * Real.sqrt 2) * 4 = 8 * Real.sqrt 2 by ring]
    linarith [hdevw, hkey2]
  obtain ⟨ζ, hζ, hζΦ⟩ := hcover hwmem
  exact Work.Pert.mem_DphiP.mpr (Work.Pert.goodP_of_mem_image ⟨ζ, hclosedQ hζ, hζΦ⟩)

end Work.Pert.Pin
