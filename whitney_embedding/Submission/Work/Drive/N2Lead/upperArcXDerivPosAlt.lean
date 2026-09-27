import Mathlib
import Submission.Work.Drive.N2Lead.upperArcToolkit
import Submission.Work.Drive.N2Lead.upperArcsYSigns

/-!
# `deriv uaX > 0` on `[-2,2]` (the `x`-monotonicity of the two untwisted arcs)

Alternative (own) proof of the `x`-monotonicity conjunct of `Work.Drive.N2Lead.mobius_upperArcs`,
interfacing through the derivative values `uaAD`, `uaBD`, `uaXD` of `upperArcToolkit.lean`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

variable {η δ s a' : ℝ}

/-! ## 1. The derivative of `σ` -/

/-- On `(0, ∞)` the plateau is the explicit product. -/
lemma saddleM_eq_of_pos {δ : ℝ} {y : ℝ} (hy : 0 < y) :
    Work.Drive.N2.saddleM δ y
      = Real.smoothTransition ((y - (2 - 4 * δ)) / (2 * δ))
        * (1 - Real.smoothTransition (y - 2)) := by
  rw [Work.Drive.N2.saddleM, Work.Drive.N2.saddleMu, abs_of_pos hy]

lemma hasDerivAt_smoothTransition (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x := by
  have h : DifferentiableAt ℝ Real.smoothTransition x :=
    (Real.smoothTransition.contDiff (n := ⊤)).contDiffAt.differentiableAt (by simp)
  exact h.hasDerivAt

/-- The derivative of the plateau at a positive point. -/
lemma hasDerivAt_saddleM_of_pos (hδ : 0 < δ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (Work.Drive.N2.saddleM δ)
      (deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) * (1 / (2 * δ))
          * (1 - Real.smoothTransition (w - 2))
        + Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ))
          * (-(deriv Real.smoothTransition (w - 2)))) w := by
  have h1 : HasDerivAt (fun y : ℝ => Real.smoothTransition ((y - (2 - 4 * δ)) / (2 * δ)))
      (deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) * (1 / (2 * δ))) w := by
    have hinner : HasDerivAt (fun y : ℝ => (y - (2 - 4 * δ)) / (2 * δ)) (1 / (2 * δ)) w := by
      have h0 : HasDerivAt (fun y : ℝ => y - (2 - 4 * δ)) 1 w :=
        (hasDerivAt_id w).sub_const (2 - 4 * δ)
      have := h0.div_const (2 * δ)
      simpa using this
    have := (hasDerivAt_smoothTransition ((w - (2 - 4 * δ)) / (2 * δ))).comp w hinner
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun y : ℝ => 1 - Real.smoothTransition (y - 2))
      (-(deriv Real.smoothTransition (w - 2))) w := by
    have hinner : HasDerivAt (fun y : ℝ => y - 2) 1 w := (hasDerivAt_id w).sub_const 2
    have hcomp : HasDerivAt (fun y : ℝ => Real.smoothTransition (y - 2))
        (deriv Real.smoothTransition (w - 2)) w := by
      have := (hasDerivAt_smoothTransition (w - 2)).comp w hinner
      simpa [Function.comp_def] using this
    exact hcomp.const_sub 1
  have hprod := h1.mul h2
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hw] with y hy
  simpa only [Pi.mul_apply] using saddleM_eq_of_pos hy

/-- The derivative of `σ` at a positive point. -/
lemma hasDerivAt_uaSig_of_pos (hδ : 0 < δ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (uaSig η δ s)
      ((deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) * (1 / (2 * δ))
          * (1 - Real.smoothTransition (w - 2))
        + Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ))
          * (-(deriv Real.smoothTransition (w - 2)))) * (-η - s)) w := by
  have hM := hasDerivAt_saddleM_of_pos (δ := δ) hδ hw
  have hfun : uaSig η δ s = fun y : ℝ => s + Work.Drive.N2.saddleM δ y * (-η - s) := by
    funext y; rw [uaSig_eq_affine]
  rw [hfun]
  refine (hasDerivAt_const_add_iff s).mpr ?_
  exact hM.mul_const (-η - s)

lemma deriv_uaSig_eq_of_pos (hδ : 0 < δ) {w : ℝ} (hw : 0 < w) :
    deriv (uaSig η δ s) w
      = (deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) * (1 / (2 * δ))
          * (1 - Real.smoothTransition (w - 2))
        + Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ))
          * (-(deriv Real.smoothTransition (w - 2)))) * (-η - s) :=
  (hasDerivAt_uaSig_of_pos (η := η) (s := s) hδ hw).deriv

/-- On `(0, 2 - 4δ)` the level coordinate is locally constant, hence its derivative vanishes. -/
lemma deriv_uaSig_eq_zero_of_lt (hδ : 0 < δ) (hδ' : δ < 1 / 10) {w : ℝ} (hw0 : 0 < w)
    (hw : w < 2 - 4 * δ) : deriv (uaSig η δ s) w = 0 := by
  have hev : uaSig η δ s =ᶠ[𝓝 w] (fun _ => s) := by
    filter_upwards [Ioo_mem_nhds (by linarith : w / 2 < w) hw] with y hy
    have hy0 : 0 < y := by linarith [hy.1, hw0]
    rw [uaSig_eq_affine,
      Work.Drive.N2.saddleM_eq_zero_of_abs_le hδ (by rw [abs_of_pos hy0]; exact le_of_lt hy.2)]
    ring
  rw [hev.deriv_eq, deriv_const]

/-- `deriv σ ≤ 0` on `(0, 2]`. -/
lemma deriv_uaSig_nonpos (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hs : 0 < s)
    {w : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 2) : deriv (uaSig η δ s) w ≤ 0 := by
  have hST2 : deriv Real.smoothTransition (w - 2) = 0 := by
    rcases lt_or_eq_of_le hw2 with h | h
    · have hev : Real.smoothTransition =ᶠ[𝓝 (w - 2)] (fun _ => (0:ℝ)) := by
        filter_upwards [Iio_mem_nhds (by linarith : w - 2 < 0)] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      rw [hev.deriv_eq, deriv_const]
    · simpa [h] using st_deriv_zero
  have hB : 1 - Real.smoothTransition (w - 2) = 1 := by
    rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    ring
  have h1 : 0 ≤ deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) :=
    st_deriv_nonneg _
  have h2δ : (0:ℝ) < 2 * δ := by linarith
  rw [deriv_uaSig_eq_of_pos (η := η) (s := s) hδ hw0, hST2, hB]
  simp only [mul_zero, neg_zero, add_zero, mul_one]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h1 (by positivity)) (by linarith)

/-- The bound `|deriv σ| ≤ 1/2` in the transition zone. -/
lemma abs_deriv_uaSig_le {C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hs : 0 < s)
    (hsη : s ≤ η) (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀)
    (hsmall : 4 * C₀ * η ≤ δ) {w : ℝ} (hw0 : 0 < w) :
    |deriv (uaSig η δ s) w| ≤ 1 / 2 := by
  have h2δ : (0:ℝ) < 2 * δ := by linarith
  have hpos2δ : (0:ℝ) < 1 / (2 * δ) := div_pos one_pos h2δ
  have hC₀0 : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ 0)
  have hA : |deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ))| ≤ C₀ := hC₀ _
  have hB : |1 - Real.smoothTransition (w - 2)| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [Real.smoothTransition.le_one (w - 2)],
      by linarith [Real.smoothTransition.nonneg (w - 2)]⟩
  have hS : |Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ))| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hC : |deriv Real.smoothTransition (w - 2)| ≤ C₀ := hC₀ _
  have hprod : |deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) * (1 / (2 * δ))
        * (1 - Real.smoothTransition (w - 2))
      + Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ))
        * (-(deriv Real.smoothTransition (w - 2)))|
      ≤ C₀ * (1 / (2 * δ)) + C₀ := by
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |deriv Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ)) * (1 / (2 * δ))
        * (1 - Real.smoothTransition (w - 2))| ≤ C₀ * (1 / (2 * δ)) := by
      rw [abs_mul, abs_mul, abs_of_pos (div_pos one_pos h2δ)]
      calc |deriv Real.smoothTransition _| * (1 / (2 * δ)) * |1 - Real.smoothTransition (w - 2)|
          ≤ C₀ * (1 / (2 * δ)) * 1 :=
            mul_le_mul (mul_le_mul hA le_rfl (le_of_lt hpos2δ) hC₀0) hB
              (abs_nonneg _) (mul_nonneg hC₀0 (le_of_lt hpos2δ))
        _ = C₀ * (1 / (2 * δ)) := by ring
    have h2' : |Real.smoothTransition ((w - (2 - 4 * δ)) / (2 * δ))
        * (-(deriv Real.smoothTransition (w - 2)))| ≤ C₀ := by
      rw [abs_mul, abs_neg]
      calc |Real.smoothTransition _| * |deriv Real.smoothTransition (w - 2)|
          ≤ 1 * C₀ := mul_le_mul hS hC (abs_nonneg _) (by norm_num)
        _ = C₀ := one_mul _
    linarith
  have hCη : C₀ * η ≤ δ / 4 := by linarith [hsmall]
  have hηs : η + s ≤ 2 * η := by linarith
  have h1 : (η + s) * C₀ ≤ δ / 2 := by nlinarith [hCη, hηs, hη, hC₀0, hδ]
  have h2 : (η + s) * C₀ * (1 / (2 * δ)) ≤ 1 / 4 := by
    rw [show (η + s) * C₀ * (1 / (2 * δ)) = (η + s) * C₀ / (2 * δ) by ring]
    rw [div_le_iff₀ h2δ]
    nlinarith [h1, hδ]
  have h3 : (η + s) * C₀ ≤ 1 / 2 := by linarith
  have habs : |-η - s| = η + s := by
    rw [abs_of_nonpos (by linarith : -η - s ≤ 0)]
    ring
  rw [deriv_uaSig_eq_of_pos (η := η) (s := s) hδ hw0, abs_mul, habs]
  calc |_| * (η + s) ≤ (C₀ * (1 / (2 * δ)) + C₀) * (η + s) :=
        mul_le_mul_of_nonneg_right hprod (by linarith)
    _ ≤ 1 / 2 := by
        have : (C₀ * (1 / (2 * δ)) + C₀) * (η + s)
            = C₀ * (1 / (2 * δ)) * (η + s) + C₀ * (η + s) := by ring
        rw [this]
        linarith [h2, h3]

/-- The key estimate: `w + σ' (σ + ‖ζ‖) > 0` on `(0,2]`, and `σ' ≤ 0`. -/
theorem upperArcSigmaDerivAlt {C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η)
    (hη' : η < 1 / 10) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ) :
    ∀ w ∈ Set.Ioc (0:ℝ) 2,
      deriv (uaSig η δ s) w ≤ 0 ∧
      0 < w + deriv (uaSig η δ s) w * (uaSig η δ s w + ‖modelZeta η δ s w‖) := by
  intro w hw
  have hw0 : 0 < w := hw.1
  have hw2 : w ≤ 2 := hw.2
  refine ⟨deriv_uaSig_nonpos hδ hδ' hη hs hw0 hw2, ?_⟩
  have hN : ‖modelZeta η δ s w‖ < 21 / 10 := by
    refine norm_modelZeta_lt hη hη' hs hsη ?_
    rw [abs_of_pos hw0]; linarith
  have hσs : uaSig η δ s w ≤ η := le_trans (uaSig_le_s hη hs w) hsη
  rcases lt_or_ge w (2 - 4 * δ) with hlt | hge
  · rw [deriv_uaSig_eq_zero_of_lt hδ hδ' hw0 hlt, zero_mul, add_zero]
    linarith
  · have hb := abs_deriv_uaSig_le (η := η) (s := s) hδ hδ' hη hs hsη hC₀ hsmall hw0
    have hw16 : (8 / 5 : ℝ) ≤ w := by
      have hδ1 : δ < 1 / 10 := hδ'
      linarith
    have hsum : uaSig η δ s w + ‖modelZeta η δ s w‖ < 11 / 5 := by linarith
    have hle : deriv (uaSig η δ s) w ≤ 0 := deriv_uaSig_nonpos hδ hδ' hη hs hw0 hw2
    have hneg : -(1 / 2 : ℝ) ≤ deriv (uaSig η δ s) w := by
      have := abs_le.mp hb; linarith [this.1]
    have h1 : (-(1 / 2 : ℝ)) * (11 / 5) ≤ deriv (uaSig η δ s) w * (11 / 5) :=
      mul_le_mul_of_nonneg_right hneg (by norm_num)
    have h2' : deriv (uaSig η δ s) w * (11 / 5)
        ≤ deriv (uaSig η δ s) w * (uaSig η δ s w + ‖modelZeta η δ s w‖) :=
      mul_le_mul_of_nonpos_left (le_of_lt hsum) hle
    linarith [le_trans h1 h2']

/-! ## 2. The signs of `uaAD` and `uaBD` -/

lemma uaA_zero (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hη : 0 < η) (hs : 0 < s) :
    uaA η δ s 0 = Real.sqrt s := by
  have hs0 : uaSig η δ s 0 = s := by
    rw [uaSig_eq_affine, saddleM_zero_of_lt_half hδ hδ₂]
    ring
  have hN0 : ‖modelZeta η δ s 0‖ = s := by
    rw [norm_modelZeta, modelSigma_eq_uaSig, hs0]
    rw [show s ^ 2 + (0:ℝ) ^ 2 = s ^ 2 by ring, Real.sqrt_sq hs.le]
  rw [uaA_eq_sqrt, hN0, hs0]
  norm_num

lemma uaAD_pos_of_pos {C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hη' : η < 1 / 10)
    (hs : 0 < s) (hsη : s ≤ η) (hδ₂ : δ < 1 / 2)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ)
    {w : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 2) : 0 < uaAD η δ s w := by
  have hnum : 0 < w + deriv (uaSig η δ s) w * (uaSig η δ s w + ‖modelZeta η δ s w‖) :=
    (upperArcSigmaDerivAlt hδ hδ' hη hη' hs hsη hC₀ hsmall w ⟨hw0, hw2⟩).2
  have hA := uaA_pos hδ hη hs hδ₂ w
  have hN := norm_modelZeta_pos (η := η) (s := s) hδ hδ₂ hs w
  rw [uaAD]
  exact div_pos hnum (by positivity)

lemma uaAD_neg_of_neg {C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hη' : η < 1 / 10)
    (hs : 0 < s) (hsη : s ≤ η) (hδ₂ : δ < 1 / 2)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ)
    {w : ℝ} (hw2 : -2 ≤ w) (hw0 : w < 0) : uaAD η δ s w < 0 := by
  have h := deriv_uaA_neg (η := η) (s := s) hδ hδ' hη hs hδ₂ (-w)
  simp only [neg_neg] at h
  rw [deriv_uaA_eq hδ hδ' hη hs hδ₂ w, deriv_uaA_eq hδ hδ' hη hs hδ₂ (-w)] at h
  have hpos : 0 < uaAD η δ s (-w) :=
    uaAD_pos_of_pos hδ hδ' hη hη' hs hsη hδ₂ hC₀ hsmall (by linarith) (by linarith)
  linarith

lemma uaBD_pos_of_pos {C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hη' : η < 1 / 10)
    (hs : 0 < s) (hsη : s ≤ η) (hδ₂ : δ < 1 / 2)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ)
    {w : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 2) : 0 < uaBD η δ s w := by
  have hA := uaA_pos hδ hη hs hδ₂ w
  have hN := norm_modelZeta_pos (η := η) (s := s) hδ hδ₂ hs w
  have hN2 : ‖modelZeta η δ s w‖ ^ 2 = uaSig η δ s w ^ 2 + w ^ 2 := by
    rw [norm_modelZeta, modelSigma_eq_uaSig]
    exact Real.sq_sqrt (by positivity)
  have hsum_pos : 0 < ‖modelZeta η δ s w‖ + uaSig η δ s w := uaA_plus_pos hδ hη hs hδ₂ w
  have hsum0 : 0 ≤ uaSig η δ s w + ‖modelZeta η δ s w‖ := by linarith
  have hσ' : deriv (uaSig η δ s) w ≤ 0 :=
    (upperArcSigmaDerivAlt hδ hδ' hη hη' hs hsη hC₀ hsmall w ⟨hw0, hw2⟩).1
  have hnum_le : w + deriv (uaSig η δ s) w * (uaSig η δ s w + ‖modelZeta η δ s w‖) ≤ w := by
    have := mul_nonpos_of_nonpos_of_nonneg hσ' hsum0
    linarith
  have hNsq : 0 < (‖modelZeta η δ s w‖ + uaSig η δ s w) ^ 2 := by positivity
  have hNsq' : 4 * uaA η δ s w ^ 2 * ‖modelZeta η δ s w‖ - w ^ 2
      = (‖modelZeta η δ s w‖ + uaSig η δ s w) ^ 2 := by
    rw [uaA_sq hδ hη hs hδ₂ w]
    nlinarith [hN2]
  have hw2' : w * (w + deriv (uaSig η δ s) w * (uaSig η δ s w + ‖modelZeta η δ s w‖)) ≤ w ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hnum_le hw0.le
  have hden : 0 < 4 * uaA η δ s w * ‖modelZeta η δ s w‖ := by positivity
  have hnumpos : 0 < 4 * uaA η δ s w ^ 2 * ‖modelZeta η δ s w‖
      - w * (w + deriv (uaSig η δ s) w * (uaSig η δ s w + ‖modelZeta η δ s w‖)) := by
    nlinarith [hNsq, hNsq', hw2']
  have hgoal : uaBD η δ s w
      = (4 * uaA η δ s w ^ 2 * ‖modelZeta η δ s w‖
          - w * (w + deriv (uaSig η δ s) w * (uaSig η δ s w + ‖modelZeta η δ s w‖)))
        / (8 * uaA η δ s w ^ 3 * ‖modelZeta η δ s w‖) := by
    rw [uaBD, uaAD]
    field_simp
    ring
  rw [hgoal]
  exact div_pos hnumpos (by positivity)

lemma uaBD_pos_of_neg {C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hη' : η < 1 / 10)
    (hs : 0 < s) (hsη : s ≤ η) (hδ₂ : δ < 1 / 2)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ)
    {w : ℝ} (hw2 : -2 ≤ w) (hw0 : w < 0) : 0 < uaBD η δ s w := by
  have h := deriv_uaB_neg (η := η) (s := s) hδ hδ' hη hs hδ₂ (-w)
  simp only [neg_neg] at h
  rw [deriv_uaB_eq hδ hδ' hη hs hδ₂ w, deriv_uaB_eq hδ hδ' hη hs hδ₂ (-w)] at h
  rw [h]
  exact uaBD_pos_of_pos hδ hδ' hη hη' hs hsη hδ₂ hC₀ hsmall (by linarith) (by linarith)

/-! ## 3. The derivative of `uaX` and the theorem -/

lemma hasDerivAt_uaX (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hs : 0 < s)
    (hδ₂ : δ < 1 / 2) (ha' : 0 < a') (w : ℝ) :
    HasDerivAt (uaX η δ s a') (uaXD η δ s a' w) w := by
  have hA := hasDerivAt_uaA (s := s) hδ hδ' hη hs hδ₂ w
  have hB := hasDerivAt_uaB (s := s) hδ hδ' hη hs hδ₂ w
  have hU : HasDerivAt (fun y : ℝ => (a' - uaB η δ s y) / (2 * a'))
      ((0 - uaBD η δ s w) / (2 * a')) w := by
    have h0 : HasDerivAt (fun y : ℝ => a' - uaB η δ s y) (0 - uaBD η δ s w) w :=
      (hasDerivAt_const w a').sub hB
    exact h0.div_const (2 * a')
  have hSTu : HasDerivAt (fun y : ℝ => Real.smoothTransition ((a' - uaB η δ s y) / (2 * a')))
      (deriv Real.smoothTransition ((a' - uaB η δ s w) / (2 * a'))
        * ((0 - uaBD η δ s w) / (2 * a'))) w := by
    have := (hasDerivAt_smoothTransition ((a' - uaB η δ s w) / (2 * a'))).comp w hU
    simpa [Function.comp_def] using this
  have hT : HasDerivAt (fun y : ℝ => uaTh η δ s a' y)
      (Real.pi * (deriv Real.smoothTransition ((a' - uaB η δ s w) / (2 * a'))
        * ((0 - uaBD η δ s w) / (2 * a')))) w := by
    have hfun : (fun y : ℝ => uaTh η δ s a' y)
        = fun y : ℝ => Real.pi * Real.smoothTransition ((a' - uaB η δ s y) / (2 * a')) := by
      funext y; rw [uaTh]
    rw [hfun]
    exact hSTu.const_mul Real.pi
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (uaTh η δ s a' y))
      (-Real.sin (uaTh η δ s a' w) * (Real.pi * (deriv Real.smoothTransition
        ((a' - uaB η δ s w) / (2 * a')) * ((0 - uaBD η δ s w) / (2 * a'))))) w := by
    have := (Real.hasDerivAt_cos (uaTh η δ s a' w)).comp w hT
    simpa [Function.comp_def] using this
  have hmul := hA.mul hcos
  have hfun : uaX η δ s a'
      = fun y : ℝ => uaA η δ s y * Real.cos (uaTh η δ s a' y) := rfl
  rw [hfun]
  refine hmul.congr_deriv ?_
  rw [uaXD]
  ring

lemma uaXD_zero (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hδ₂ : δ < 1 / 2) (hη : 0 < η) (hs : 0 < s)
    (ha' : 0 < a') : uaXD η δ s a' 0 = Real.pi / (2 * a') := by
  have hAD0 : uaAD η δ s 0 = 0 := by
    have h := deriv_uaA_neg (η := η) (s := s) hδ hδ' hη hs hδ₂ 0
    simp only [neg_zero] at h
    rw [deriv_uaA_eq hδ hδ' hη hs hδ₂ 0] at h
    linarith
  have hst : deriv Real.smoothTransition ((a' - uaB η δ s 0) / (2 * a')) = 2 := by
    rw [uaB_zero (δ := δ) hδ hη hs hδ₂]
    have h : (a' - 0) / (2 * a') = 1 / 2 := by field_simp; ring
    rw [h, st_deriv_half]
  have hA0 := uaA_zero (η := η) (s := s) hδ hδ₂ hη hs
  have hBD0 : uaBD η δ s 0 = 1 / (2 * Real.sqrt s) := by
    rw [uaBD, hAD0, hA0]
    have hsne : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
    field_simp
    ring
  rw [uaXD, uaTh_zero (δ := δ) hδ hδ₂ hη hs ha', hAD0, hst, hBD0, hA0,
    Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, zero_add, mul_one]
  have hsne : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  field_simp
  try ring

theorem upperArcXDerivPosAlt {C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η)
    (hη' : η < 1 / 10) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ)
    (ha' : 0 < a') :
    ∀ w ∈ Set.Icc (-2) 2, 0 < deriv (fun w : ℝ => uaX η δ s a' w) w := by
  have hδ₂ : δ < 1 / 2 := by linarith
  intro w hw
  rw [(hasDerivAt_uaX (η := η) (s := s) (a' := a') hδ hδ' hη hs hδ₂ ha' w).deriv]
  have hsin : 0 ≤ Real.sin (uaTh η δ s a' w) := sin_uaTh_nonneg ha' w
  have hST' : 0 ≤ deriv Real.smoothTransition ((a' - uaB η δ s w) / (2 * a')) :=
    st_deriv_nonneg _
  rcases lt_trichotomy w 0 with hlt | heq | hgt
  · have hcos : Real.cos (uaTh η δ s a' w) < 0 :=
      (cos_pi_st_div_neg_iff ha').mpr ((uaB_neg_iff hδ hη hs hδ₂).mpr hlt)
    have hAD : uaAD η δ s w < 0 :=
      uaAD_neg_of_neg hδ hδ' hη hη' hs hsη hδ₂ hC₀ hsmall hw.1 hlt
    have hBD : 0 < uaBD η δ s w :=
      uaBD_pos_of_neg hδ hδ' hη hη' hs hsη hδ₂ hC₀ hsmall hw.1 hlt
    have hfirst : 0 < uaAD η δ s w * Real.cos (uaTh η δ s a' w) := mul_pos_of_neg_of_neg hAD hcos
    have hsecond : 0 ≤ uaA η δ s w * Real.sin (uaTh η δ s a' w)
        * (Real.pi * deriv Real.smoothTransition ((a' - uaB η δ s w) / (2 * a'))
          * uaBD η δ s w / (2 * a')) := by
      have hAa : 0 < uaA η δ s w := uaA_pos hδ hη hs hδ₂ w
      have h3 : 0 ≤ Real.pi * deriv Real.smoothTransition ((a' - uaB η δ s w) / (2 * a'))
          * uaBD η δ s w / (2 * a') := by positivity
      have h2 := mul_nonneg hAa.le hsin
      exact mul_nonneg h2 h3
    rw [uaXD]
    linarith
  · rw [heq]
    rw [uaXD_zero (η := η) (s := s) hδ hδ' hδ₂ hη hs ha']
    positivity
  · have hcos : 0 < Real.cos (uaTh η δ s a' w) :=
      (cos_pi_st_div_pos_iff ha').mpr ((uaB_pos_iff hδ hη hs hδ₂).mpr hgt)
    have hAD : 0 < uaAD η δ s w :=
      uaAD_pos_of_pos hδ hδ' hη hη' hs hsη hδ₂ hC₀ hsmall hgt hw.2
    have hBD : 0 < uaBD η δ s w :=
      uaBD_pos_of_pos hδ hδ' hη hη' hs hsη hδ₂ hC₀ hsmall hgt hw.2
    have hfirst : 0 < uaAD η δ s w * Real.cos (uaTh η δ s a' w) := mul_pos hAD hcos
    have hsecond : 0 ≤ uaA η δ s w * Real.sin (uaTh η δ s a' w)
        * (Real.pi * deriv Real.smoothTransition ((a' - uaB η δ s w) / (2 * a'))
          * uaBD η δ s w / (2 * a')) := by
      have hAa : 0 < uaA η δ s w := uaA_pos hδ hη hs hδ₂ w
      have h3 : 0 ≤ Real.pi * deriv Real.smoothTransition ((a' - uaB η δ s w) / (2 * a'))
          * uaBD η δ s w / (2 * a') := by positivity
      have h2 := mul_nonneg hAa.le hsin
      exact mul_nonneg h2 h3
    rw [uaXD]
    linarith

end

end Work.Drive.N2Lead
