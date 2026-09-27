import Mathlib
import Submission.Work.Drive.N2Lead.upperArcToolkit

/-!
# The level coordinate `σ` of the planar model is decreasing with the correct slope bound

`Work.Drive.N2Lead.upperArcSigmaDeriv` is the calculus input used to show that the two model arcs
`α`, `β` of the upper level of the Möbius saddle move strictly in the `x`-direction: it controls the
derivative of the level coordinate

`σ w = uaSig η δ s w = modelSigma η δ s w = s + saddleM δ w * (-η - s)`

on the window `(0, 2]` under the hypotheses `0 < s ≤ η < 1/10`, `0 < δ < 1/10` and the smallness
condition `4 C₀ η ≤ δ`, where `C₀` bounds `|deriv Real.smoothTransition|`.

The two claims are

* `deriv σ w ≤ 0` (σ is decreasing, because `saddleM δ` is increasing on `[0,2]`: on that window the
  second factor `1 - smoothTransition (|w| - 2)` of `saddleMu δ` equals one and `saddleM δ` is the
  transition bump `smoothTransition ((w - (2 - 4δ)) / (2δ))`);
* `0 < w + deriv σ w * (σ w + ‖ζ w‖)` — the quantitative form of "the arc `w ↦ √(σ w + i w)` turns
  to the right": with `c := deriv Real.smoothTransition ((w - (2 - 4δ)) / (2δ))` one has
  `deriv σ w = -c (η + s)/(2δ)` and `σ w + ‖ζ w‖ ≤ w + 2η`, so the claimed inequality follows from
  `c (η + s)/(2δ) ≤ C₀ η/δ ≤ 1/4` and `(w + 2η)/4 < w` — the smallness hypothesis is used exactly
  for the middle inequality.

Everything is proved for the (stable) `modelSigma` and transported to `uaSig`, which is that same
function by definition.
-/

namespace Work.Drive.N2Lead

open Real Filter
open scoped Topology
open Work.Drive.N2

noncomputable section

/-! ## The derivative of `Real.smoothTransition` at the left end -/

/-- `deriv Real.smoothTransition 0 = 0`: the transition function is flat at the left end. -/
lemma uasd_st_deriv_zero : deriv Real.smoothTransition 0 = 0 := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    ContDiff.continuous_deriv (Real.smoothTransition.contDiff (n := ⊤)) (by simp)
  have hleft : deriv Real.smoothTransition =ᶠ[𝓝[<] (0:ℝ)] (fun _ => (0:ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [Filter.EventuallyEq.deriv_eq h, deriv_const]
  have htend : Tendsto (deriv Real.smoothTransition) (𝓝[<] (0:ℝ)) (𝓝 0) :=
    Tendsto.congr' hleft.symm tendsto_const_nhds
  exact tendsto_nhds_unique (l := 𝓝[<] (0:ℝ))
    (hcont.continuousAt.tendsto.mono_left inf_le_left) htend

/-- `deriv Real.smoothTransition` vanishes on `(-∞, 0]`. -/
lemma uasd_st_deriv_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    deriv Real.smoothTransition y = 0 := by
  rcases lt_or_eq_of_le hy with hy' | h0
  · have h : Real.smoothTransition =ᶠ[𝓝 y] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hy'] with z hz
      exact Real.smoothTransition.zero_of_nonpos hz.le
    rw [Filter.EventuallyEq.deriv_eq h, deriv_const]
  · rw [h0]; exact uasd_st_deriv_zero

lemma uasd_differentiableAt_st (y : ℝ) : DifferentiableAt ℝ Real.smoothTransition y :=
  ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)) y

lemma uasd_hasDerivAt_st (y : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition y) y :=
  (uasd_differentiableAt_st y).hasDerivAt

/-! ## The derivative of the plateau `saddleM δ` on `(0, 2]` -/

/-- On `(-∞, 2]` the second factor of `saddleMu δ` is constantly one (and its derivative vanishes),
so `saddleMu δ = smoothTransition ((· - (2 - 4δ)) / (2δ))` there and the derivative at `t ≤ 2` is
`deriv smoothTransition ((t - (2-4δ))/(2δ)) / (2δ)`. -/
lemma uasd_hasDerivAt_saddleMu {δ t : ℝ} (ht : t ≤ 2) :
    HasDerivAt (saddleMu δ)
      (deriv Real.smoothTransition ((t - (2 - 4 * δ)) / (2 * δ)) / (2 * δ)) t := by
  have hin1 : HasDerivAt (fun y : ℝ => (y - (2 - 4 * δ)) / (2 * δ)) (1 / (2 * δ)) t :=
    ((hasDerivAt_id t).sub_const (2 - 4 * δ)).div_const (2 * δ)
  have h1 : HasDerivAt (fun y : ℝ => Real.smoothTransition ((y - (2 - 4 * δ)) / (2 * δ)))
      (deriv Real.smoothTransition ((t - (2 - 4 * δ)) / (2 * δ)) * (1 / (2 * δ))) t := by
    have h := (uasd_hasDerivAt_st ((t - (2 - 4 * δ)) / (2 * δ))).comp t hin1
    simpa only [Function.comp_def] using h
  have hin2 : HasDerivAt (fun y : ℝ => y - 2) 1 t := (hasDerivAt_id t).sub_const 2
  have h2a : HasDerivAt (fun y : ℝ => Real.smoothTransition (y - 2))
      (deriv Real.smoothTransition (t - 2) * 1) t := by
    have h := (uasd_hasDerivAt_st (t - 2)).comp t hin2
    simpa only [Function.comp_def] using h
  have h2 : HasDerivAt (fun y : ℝ => 1 - Real.smoothTransition (y - 2))
      (0 - deriv Real.smoothTransition (t - 2) * 1) t :=
    (hasDerivAt_const t (1:ℝ)).sub h2a
  have hprod := h1.mul h2
  have hz : Real.smoothTransition (t - 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hz' : deriv Real.smoothTransition (t - 2) = 0 :=
    uasd_st_deriv_eq_zero_of_nonpos (by linarith)
  have hval : deriv Real.smoothTransition ((t - (2 - 4 * δ)) / (2 * δ)) * (1 / (2 * δ)) *
        (1 - Real.smoothTransition (t - 2))
      + Real.smoothTransition ((t - (2 - 4 * δ)) / (2 * δ)) *
          (0 - deriv Real.smoothTransition (t - 2) * 1)
      = deriv Real.smoothTransition ((t - (2 - 4 * δ)) / (2 * δ)) / (2 * δ) := by
    rw [hz, hz']; ring
  rw [hval] at hprod
  exact hprod

/-- Near a strictly positive point, `saddleM δ = saddleMu δ ∘ |·|` is `saddleMu δ` itself. -/
lemma uasd_eq_saddleMu_eventually {δ w : ℝ} (hw0 : 0 < w) :
    saddleM δ =ᶠ[𝓝 w] saddleMu δ := by
  filter_upwards [Metric.ball_mem_nhds w hw0] with y hy
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
  rw [saddleM, abs_of_pos (show (0:ℝ) < y by linarith [hy.1])]

/-- The derivative of the plateau `saddleM δ` on `(0, 2]`. -/
lemma uasd_hasDerivAt_saddleM {δ : ℝ} {w : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 2) :
    HasDerivAt (saddleM δ)
      (deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) / (2 * δ)) w :=
  (Filter.EventuallyEq.hasDerivAt_iff (uasd_eq_saddleMu_eventually hw0)).mpr
    (uasd_hasDerivAt_saddleMu hw2)

lemma uasd_deriv_saddleM {δ : ℝ} {w : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 2) :
    deriv (saddleM δ) w = deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) / (2 * δ) :=
  (uasd_hasDerivAt_saddleM hw0 hw2).deriv

/-- The derivative of the level coordinate `modelSigma η δ s` (the function underlying `uaSig`). -/
lemma uasd_deriv_modelSigma {η δ s : ℝ} {w : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 2) :
    deriv (modelSigma η δ s) w
      = deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) / (2 * δ) * (-η - s) := by
  have hM := uasd_hasDerivAt_saddleM (δ := δ) hw0 hw2
  have h := ((hasDerivAt_const w s).add (hM.mul_const (-η - s))).deriv
  have h' : deriv ((fun x : ℝ => s) + fun y : ℝ => saddleM δ y * (-η - s)) w
      = deriv (modelSigma η δ s) w := rfl
  rw [h'] at h
  simpa using h

/-! ## Elementary bounds on `σ` and `ζ` -/

lemma uasd_saddleMu_mem_Icc (δ t : ℝ) : saddleMu δ t ∈ Set.Icc (0:ℝ) 1 := by
  rw [saddleMu]
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _)
      (sub_nonneg.mpr (Real.smoothTransition.le_one _)), ?_⟩
  refine mul_le_one₀ (Real.smoothTransition.le_one _)
    (sub_nonneg.mpr (Real.smoothTransition.le_one _)) ?_
  linarith [Real.smoothTransition.nonneg (t - 2)]

lemma uasd_saddleM_mem_Icc (δ w : ℝ) : saddleM δ w ∈ Set.Icc (0:ℝ) 1 :=
  uasd_saddleMu_mem_Icc δ |w|

lemma uasd_modelSigma_le_s {η δ s : ℝ} (hη : 0 < η) (hs : 0 < s) (w : ℝ) :
    modelSigma η δ s w ≤ s := by
  have hM := (uasd_saddleM_mem_Icc δ w).1
  have hmul : saddleM δ w * (-η - s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hM (by linarith)
  rw [modelSigma_eq]
  linarith

lemma uasd_abs_modelSigma_le {η δ s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsη : s ≤ η) (w : ℝ) :
    |modelSigma η δ s w| ≤ η := by
  have hM := uasd_saddleM_mem_Icc δ w
  have hc : -η - s ≤ 0 := by linarith
  rw [abs_le]
  constructor
  · have h1 : (1:ℝ) * (-η - s) ≤ saddleM δ w * (-η - s) :=
      mul_le_mul_of_nonpos_right hM.2 hc
    rw [modelSigma_eq]
    linarith
  · exact le_trans (uasd_modelSigma_le_s hη hs w) hsη

lemma uasd_norm_modelZeta_le {η δ s : ℝ} {w : ℝ} (hw : 0 ≤ w) :
    ‖modelZeta η δ s w‖ ≤ |modelSigma η δ s w| + w := by
  rw [norm_modelZeta]
  have hsq : modelSigma η δ s w ^ 2 + w ^ 2 ≤ (|modelSigma η δ s w| + w) ^ 2 := by
    nlinarith [abs_nonneg (modelSigma η δ s w), sq_abs (modelSigma η δ s w)]
  calc Real.sqrt (modelSigma η δ s w ^ 2 + w ^ 2)
      ≤ Real.sqrt ((|modelSigma η δ s w| + w) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |modelSigma η δ s w| + w := Real.sqrt_sq (by linarith [abs_nonneg (modelSigma η δ s w)])

/-! ## The main estimate -/

/-- The content of `upperArcSigmaDeriv`, stated for `modelSigma` (which is `uaSig` by definition). -/
theorem uasd_main {η δ s C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η)
    (hη' : η < 1 / 10) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ) :
    ∀ w ∈ Set.Ioc (0:ℝ) 2,
      deriv (modelSigma η δ s) w ≤ 0 ∧
      0 < w + deriv (modelSigma η δ s) w * (modelSigma η δ s w + ‖modelZeta η δ s w‖) := by
  intro w hw
  obtain ⟨hw0, hw2⟩ := hw
  have h2δ : (0:ℝ) < 2 * δ := by linarith
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    rw [uasd_st_deriv_zero, abs_zero] at h
    exact h
  set c : ℝ := deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) with hc
  have hderiv : deriv (modelSigma η δ s) w = c / (2 * δ) * (-η - s) := by
    rw [hc]; exact uasd_deriv_modelSigma hw0 hw2
  have hcnn : 0 ≤ c := by rw [hc]; exact Monotone.deriv_nonneg Real.smoothTransition.monotone
  have hcle : c ≤ C₀ := by rw [hc]; exact (abs_le.mp (hC₀ _)).2
  have hσ_le : modelSigma η δ s w ≤ η := le_trans (uasd_modelSigma_le_s hη hs w) hsη
  have hσ_abs : |modelSigma η δ s w| ≤ η := uasd_abs_modelSigma_le hη hs hsη w
  have hζ : ‖modelZeta η δ s w‖ ≤ |modelSigma η δ s w| + w := uasd_norm_modelZeta_le hw0.le
  have hC_le : modelSigma η δ s w + ‖modelZeta η δ s w‖ ≤ w + 2 * η := by linarith
  constructor
  · rw [hderiv]
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hcnn h2δ.le) (by linarith)
  · rw [hderiv]
    have hηs : η + s ≤ 2 * η := by linarith
    have hηsnn : 0 ≤ η + s := by linarith
    have hcoeffnn : 0 ≤ c / (2 * δ) * (η + s) :=
      mul_nonneg (div_nonneg hcnn h2δ.le) hηsnn
    have hbase : c / (2 * δ) * (η + s) * (w + 2 * η) < w := by
      by_cases hc0 : c = 0
      · rw [hc0, zero_div, zero_mul, zero_mul]
        linarith
      · have hcpos : 0 < c := lt_of_le_of_ne hcnn (Ne.symm hc0)
        have hwa : 2 - 4 * δ < w := by
          have hy : 0 < (w - (2 - 4 * δ)) / (2 * δ) := by
            by_contra hle
            have hle' : (w - (2 - 4 * δ)) / (2 * δ) ≤ 0 := le_of_not_gt hle
            have hzero := uasd_st_deriv_eq_zero_of_nonpos hle'
            rw [hc] at hcpos
            rw [hzero] at hcpos
            exact absurd hcpos (lt_irrefl 0)
          have hm : 0 < ((w - (2 - 4 * δ)) / (2 * δ)) * (2 * δ) := mul_pos hy h2δ
          rw [div_mul_cancel₀ _ (ne_of_gt h2δ)] at hm
          linarith
        have hcoeff : c / (2 * δ) * (η + s) ≤ 1 / 4 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ h2δ]
          have hcs : c * (η + s) ≤ C₀ * (2 * η) := mul_le_mul hcle hηs hηsnn hC₀nn
          linarith
        have hw2η : 0 ≤ w + 2 * η := by linarith
        calc c / (2 * δ) * (η + s) * (w + 2 * η)
            ≤ (1 / 4) * (w + 2 * η) := mul_le_mul_of_nonneg_right hcoeff hw2η
          _ < w := by nlinarith [hδ', hη']
    have hT : c / (2 * δ) * (η + s) * (modelSigma η δ s w + ‖modelZeta η δ s w‖) < w :=
      calc c / (2 * δ) * (η + s) * (modelSigma η δ s w + ‖modelZeta η δ s w‖)
          ≤ c / (2 * δ) * (η + s) * (w + 2 * η) := mul_le_mul_of_nonneg_left hC_le hcoeffnn
        _ < w := hbase
    calc (0:ℝ) < w - c / (2 * δ) * (η + s) * (modelSigma η δ s w + ‖modelZeta η δ s w‖) := by
          linarith
      _ = w + c / (2 * δ) * (-η - s) * (modelSigma η δ s w + ‖modelZeta η δ s w‖) := by ring

end

theorem upperArcSigmaDeriv {η δ s C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η)
    (hη' : η < 1 / 10) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ) :
    ∀ w ∈ Set.Ioc (0:ℝ) 2,
      deriv (Work.Drive.N2Lead.uaSig η δ s) w ≤ 0 ∧
      0 < w + deriv (Work.Drive.N2Lead.uaSig η δ s) w *
        (Work.Drive.N2Lead.uaSig η δ s w + ‖Work.Drive.N2Lead.modelZeta η δ s w‖) := by
  rw [show Work.Drive.N2Lead.uaSig η δ s = modelSigma η δ s from rfl]
  exact uasd_main hδ hδ' hη hη' hs hsη hC₀ hsmall

end Work.Drive.N2Lead
