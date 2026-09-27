import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi

namespace Work.Drive.N2Lead

open Work.Drive.N2

/-! ## The saddle model arc `w ↦ Im √(σ w + i w)`

Throughout, `σ w := saddleSigma η δ (s, w) = s + saddleM δ w * (-η - s)` is the level coordinate of
the saddle model at the fixed level `s`, and `ζ w := σ w + i w`.  We prove that the imaginary part of
the principal square root of `ζ w` is strictly increasing on `[-2, 2]`, under the hypotheses
`0 < δ`, `δ < 1/2`, `0 < η`, `0 < s`.

The proof is elementary.  On `[0,2]` the second factor `1 - smoothTransition (|w| - 2)` of `saddleMu`
is constantly `1`, so `saddleM δ` is the `smoothTransition` bump alone, hence nondecreasing in `|w|`;
as `-η - s < 0`, `σ` is antitone on `[0,2]`.  For `w ≥ 0`, writing `a + i b := √(ζ w)` with `b ≥ 0`
(principal branch, `Im ζ w = w ≥ 0`) we have `b² = Φ w / 2` with
`Φ w := ‖ζ w‖ - σ w = √(σ w² + w²) - σ w`; and `Φ` is strictly increasing because
`(c, w) ↦ √(c² + w²) - c` is strictly decreasing in `c` and strictly increasing in `w ≥ 0`.
Finally `w ↦ (√(ζ w)).im` is odd, because `σ` is even, which extends the monotonicity to `[-2,2]`. -/

/-- The level coordinate of the saddle movie at the fixed level `s`. -/
noncomputable def modelSigma (η δ s : ℝ) (w : ℝ) : ℝ := saddleSigma η δ (s, w)

/-- `ζ w = σ w + i w`. -/
noncomputable def modelZeta (η δ s : ℝ) (w : ℝ) : ℂ :=
  (modelSigma η δ s w : ℂ) + (w : ℂ) * Complex.I

/-- `Φ w = ‖ζ w‖ - σ w`, twice the square of the imaginary part of `√(ζ w)`. -/
noncomputable def modelPhi (η δ s : ℝ) (w : ℝ) : ℝ :=
  ‖modelZeta η δ s w‖ - modelSigma η δ s w

/-- The model arc `w ↦ Im √(ζ w)`. -/
noncomputable def modelArcIm (η δ s : ℝ) (w : ℝ) : ℝ := (modelZeta η δ s w).sqrt.im

lemma modelSigma_eq (η δ s w : ℝ) : modelSigma η δ s w = s + saddleM δ w * (-η - s) := rfl

lemma modelSigma_even (η δ s w : ℝ) : modelSigma η δ s (-w) = modelSigma η δ s w := by
  rw [modelSigma_eq, modelSigma_eq]
  simp only [saddleM, abs_neg]

lemma modelZeta_re (η δ s w : ℝ) : (modelZeta η δ s w).re = modelSigma η δ s w := by
  simp [modelZeta]

lemma modelZeta_im (η δ s w : ℝ) : (modelZeta η δ s w).im = w := by
  simp [modelZeta]

lemma modelZeta_neg (η δ s w : ℝ) : modelZeta η δ s (-w) = star (modelZeta η δ s w) := by
  rw [modelZeta, modelZeta, modelSigma_even]
  simp [Complex.conj_ofReal]

lemma norm_modelZeta (η δ s w : ℝ) :
    ‖modelZeta η δ s w‖ = Real.sqrt (modelSigma η δ s w ^ 2 + w ^ 2) := by
  rw [show ‖modelZeta η δ s w‖ = Real.sqrt (Complex.normSq (modelZeta η δ s w)) from by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]
  congr 1
  rw [Complex.normSq_apply, modelZeta_re, modelZeta_im]
  ring

lemma norm_modelZeta_neg (η δ s w : ℝ) :
    ‖modelZeta η δ s (-w)‖ = ‖modelZeta η δ s w‖ := by
  rw [norm_modelZeta, norm_modelZeta, modelSigma_even, neg_sq]

lemma modelPhi_even (η δ s w : ℝ) : modelPhi η δ s (-w) = modelPhi η δ s w := by
  rw [modelPhi, modelPhi, norm_modelZeta_neg, modelSigma_even]

/-! ## The imaginary part of the principal square root -/

/-- The imaginary part of the principal square root: the branch is selected by the sign of the
imaginary part. -/
lemma sqrt_im_eq (z : ℂ) :
    z.sqrt.im = (if 0 ≤ z.im then (1 : ℝ) else -1) * Real.sqrt ((‖z‖ - z.re) / 2) := by
  rw [Complex.sqrt_eq_real_add_ite]
  split_ifs <;> simp

/-- The model arc off the branch cut: `Im √(ζ w) = ±√(Φ w / 2)`. -/
lemma modelArcIm_eq_general (η δ s : ℝ) (w : ℝ) :
    modelArcIm η δ s w
      = (if 0 ≤ w then (1 : ℝ) else -1) * Real.sqrt (modelPhi η δ s w / 2) := by
  simp only [modelArcIm, modelPhi, sqrt_im_eq, modelZeta_im, modelZeta_re]

lemma modelArcIm_eq_of_nonneg {η δ s : ℝ} {w : ℝ} (hw : 0 ≤ w) :
    modelArcIm η δ s w = Real.sqrt (modelPhi η δ s w / 2) := by
  rw [modelArcIm_eq_general, if_pos hw, one_mul]

/-! ## Monotonicity of `c ↦ √(c² + w²) - c` -/

lemma abs_lt_sqrt_sq_add_sq {c w : ℝ} (hw : 0 < w) : |c| < Real.sqrt (c ^ 2 + w ^ 2) := by
  have h : Real.sqrt (c ^ 2) < Real.sqrt (c ^ 2 + w ^ 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  rwa [Real.sqrt_sq_eq_abs] at h

/-- For `w > 0` the map `c ↦ √(c² + w²) - c` is strictly decreasing. -/
lemma strictAnti_sqrt_sq_add_sq_sub (w : ℝ) (hw : 0 < w) :
    StrictAnti (fun c : ℝ => Real.sqrt (c ^ 2 + w ^ 2) - c) := by
  intro c₁ c₂ hc
  set A := Real.sqrt (c₁ ^ 2 + w ^ 2) with hA
  set B := Real.sqrt (c₂ ^ 2 + w ^ 2) with hB
  have hA2 : A ^ 2 = c₁ ^ 2 + w ^ 2 := by rw [hA]; exact Real.sq_sqrt (by positivity)
  have hB2 : B ^ 2 = c₂ ^ 2 + w ^ 2 := by rw [hB]; exact Real.sq_sqrt (by positivity)
  have hAp : 0 < A := by rw [hA]; exact Real.sqrt_pos.mpr (by positivity)
  have hBp : 0 < B := by rw [hB]; exact Real.sqrt_pos.mpr (by positivity)
  have hsum : c₁ + c₂ < A + B := by
    have h1 : |c₁| < A := by rw [hA]; exact abs_lt_sqrt_sq_add_sq hw
    have h2 : |c₂| < B := by rw [hB]; exact abs_lt_sqrt_sq_add_sq hw
    linarith [le_abs_self c₁, le_abs_self c₂]
  have hAB : 0 < A + B := by linarith
  change B - c₂ < A - c₁
  have key : B - c₂ - (A - c₁) = (c₂ - c₁) * (c₁ + c₂ - (A + B)) / (A + B) := by
    rw [eq_div_iff (ne_of_gt hAB)]
    have h3 : (B - A) * (A + B) = (c₂ - c₁) * (c₁ + c₂) := by nlinarith [hA2, hB2]
    nlinarith [h3]
  have hneg : (c₂ - c₁) * (c₁ + c₂ - (A + B)) / (A + B) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) hAB
  linarith [key, hneg]

/-- For `0 ≤ w₁ < w₂` the map `w ↦ √(c² + w²) - c` is strictly increasing. -/
lemma sqrt_sq_add_sq_sub_lt {c w₁ w₂ : ℝ} (h0 : 0 ≤ w₁) (h : w₁ < w₂) :
    Real.sqrt (c ^ 2 + w₁ ^ 2) - c < Real.sqrt (c ^ 2 + w₂ ^ 2) - c := by
  have hlt : Real.sqrt (c ^ 2 + w₁ ^ 2) < Real.sqrt (c ^ 2 + w₂ ^ 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  linarith

/-! ## The level coordinate is antitone on `[0,2]` -/

/-- On `[0,2]` the second factor of `saddleMu` is constantly `1`, so `saddleM δ` is the
`smoothTransition` bump alone, hence nondecreasing. -/
lemma saddleM_monotoneOn_Icc {δ : ℝ} (hδ : 0 < δ) :
    MonotoneOn (saddleM δ) (Set.Icc 0 2) := by
  intro w₁ h₁ w₂ h₂ hle
  have e₁ : saddleM δ w₁ = Real.smoothTransition ((w₁ - (2 - 4 * δ)) / (2 * δ)) := by
    rw [saddleM, abs_of_nonneg h₁.1, saddleMu,
      Real.smoothTransition.zero_of_nonpos (show w₁ - 2 ≤ 0 by linarith [h₁.2]), sub_zero, mul_one]
  have e₂ : saddleM δ w₂ = Real.smoothTransition ((w₂ - (2 - 4 * δ)) / (2 * δ)) := by
    rw [saddleM, abs_of_nonneg h₂.1, saddleMu,
      Real.smoothTransition.zero_of_nonpos (show w₂ - 2 ≤ 0 by linarith [h₂.2]), sub_zero, mul_one]
  rw [e₁, e₂]
  refine Real.smoothTransition.monotone ?_
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

lemma modelSigma_antitoneOn_Icc {η δ s : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) :
    AntitoneOn (modelSigma η δ s) (Set.Icc 0 2) := by
  intro w₁ h₁ w₂ h₂ hle
  have hM : saddleM δ w₁ ≤ saddleM δ w₂ := saddleM_monotoneOn_Icc hδ h₁ h₂ hle
  have hc : -η - s ≤ 0 := by linarith
  have hmul : saddleM δ w₂ * (-η - s) ≤ saddleM δ w₁ * (-η - s) :=
    mul_le_mul_of_nonpos_right hM hc
  rw [modelSigma_eq, modelSigma_eq]
  linarith

/-! ## The key estimate: `Φ` is strictly increasing on `[0,2]` -/

lemma strictMonoOn_modelPhi {η δ s : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) :
    StrictMonoOn (modelPhi η δ s) (Set.Icc 0 2) := by
  intro w₁ h₁ w₂ h₂ hlt
  rw [modelPhi, modelPhi, norm_modelZeta, norm_modelZeta]
  have hσ : modelSigma η δ s w₂ ≤ modelSigma η δ s w₁ :=
    modelSigma_antitoneOn_Icc (η := η) (s := s) hδ hη hs h₁ h₂ (le_of_lt hlt)
  have hw₂ : 0 < w₂ := lt_of_le_of_lt h₁.1 hlt
  have h₁' : Real.sqrt (modelSigma η δ s w₁ ^ 2 + w₂ ^ 2) - modelSigma η δ s w₁
      ≤ Real.sqrt (modelSigma η δ s w₂ ^ 2 + w₂ ^ 2) - modelSigma η δ s w₂ :=
    (strictAnti_sqrt_sq_add_sq_sub w₂ hw₂).antitone hσ
  have h₂' : Real.sqrt (modelSigma η δ s w₁ ^ 2 + w₁ ^ 2) - modelSigma η δ s w₁
      < Real.sqrt (modelSigma η δ s w₁ ^ 2 + w₂ ^ 2) - modelSigma η δ s w₁ :=
    sqrt_sq_add_sq_sub_lt h₁.1 hlt
  linarith

/-! ## The model arc is strictly increasing on `[0,2]` -/

lemma strictMonoOn_modelArc_of_nonneg {η δ s : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) :
    StrictMonoOn (modelArcIm η δ s) (Set.Icc 0 2) := by
  intro w₁ h₁ w₂ h₂ hlt
  rw [modelArcIm_eq_of_nonneg h₁.1,
    modelArcIm_eq_of_nonneg (le_of_lt (lt_of_le_of_lt h₁.1 hlt))]
  have hΦ := strictMonoOn_modelPhi (η := η) (δ := δ) (s := s) hδ hη hs h₁ h₂ hlt
  refine Real.sqrt_lt_sqrt ?_ (by linarith)
  have hle := Complex.re_le_norm (modelZeta η δ s w₁)
  rw [modelZeta_re] at hle
  rw [modelPhi]
  linarith

/-! ## The value at `0` and the odd symmetry -/

lemma saddleM_zero_of_lt_half {δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) : saddleM δ 0 = 0 := by
  rw [saddleM, abs_zero]
  exact saddleMu_eq_zero_of_le hδ (by linarith)

lemma modelArcIm_at_zero {η δ s : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s) :
    modelArcIm η δ s 0 = 0 := by
  have hσ : modelSigma η δ s 0 = s := by
    rw [modelSigma_eq, saddleM_zero_of_lt_half hδ hδ₂]
    ring
  have hζ : modelZeta η δ s 0 = (s : ℂ) := by
    rw [modelZeta, hσ]
    simp
  have hΦ : modelPhi η δ s 0 = 0 := by
    rw [modelPhi, hζ, hσ]
    simp [abs_of_nonneg hs.le]
  rw [modelArcIm_eq_general, if_pos le_rfl, hΦ]
  simp

/-- The model arc is odd on `[-2,2]`. -/
lemma modelArcIm_neg {η δ s : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s)
    {w : ℝ} (_hw : w ∈ Set.Icc (-2) 2) :
    modelArcIm η δ s (-w) = - modelArcIm η δ s w := by
  rcases lt_trichotomy w 0 with h | h | h
  · have h1 : ¬ (0 ≤ w) := not_le.mpr h
    have h2 : 0 ≤ -w := by linarith
    rw [modelArcIm_eq_general, modelArcIm_eq_general, if_neg h1, if_pos h2, modelPhi_even]
    ring
  · subst h
    rw [neg_zero, modelArcIm_at_zero hδ hδ₂ hs, neg_zero]
  · have h1 : 0 ≤ w := le_of_lt h
    have h2 : ¬ (0 ≤ -w) := not_le.mpr (by linarith)
    rw [modelArcIm_eq_general, modelArcIm_eq_general, if_pos h1, if_neg h2, modelPhi_even]
    ring

/-! ## The theorem -/

theorem modelArc_im_strictMonoOn {η δ s : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hη : 0 < η)
    (hs : 0 < s) :
    StrictMonoOn (fun w : ℝ =>
      (Complex.sqrt ((Work.Drive.N2.saddleSigma η δ (s, w) : ℂ) + (w : ℂ) * Complex.I)).im)
      (Set.Icc (-2) 2) := by
  change StrictMonoOn (modelArcIm η δ s) (Set.Icc (-2) 2)
  have hmono : StrictMonoOn (modelArcIm η δ s) (Set.Icc 0 2) :=
    strictMonoOn_modelArc_of_nonneg (η := η) (δ := δ) (s := s) hδ hη hs
  have hzero : modelArcIm η δ s 0 = 0 := modelArcIm_at_zero hδ hδ₂ hs
  intro a ha b hb hab
  rcases lt_or_ge a 0 with ha0 | ha0
  · rcases lt_or_ge 0 b with hb0 | hb0
    · -- `a < 0 ≤ b`: the arc is negative at `a` and positive at `b`
      have h1 : (0 : ℝ) ∈ Set.Icc 0 2 := ⟨le_refl 0, by norm_num⟩
      have h2 : (-a) ∈ Set.Icc 0 2 := ⟨by linarith, by linarith [ha.1]⟩
      have hpos : 0 < modelArcIm η δ s (-a) := by
        have hh := hmono h1 h2 (by linarith : (0 : ℝ) < -a)
        rwa [hzero] at hh
      have hna : modelArcIm η δ s a < 0 := by
        have hh := modelArcIm_neg (η := η) (δ := δ) (s := s) hδ hδ₂ hs ha
        linarith
      have hbpos : 0 < modelArcIm η δ s b := by
        have hh := hmono h1 ⟨le_of_lt hb0, hb.2⟩ hb0
        rwa [hzero] at hh
      linarith
    · -- `a < b ≤ 0`: reflect through the origin, where the arc is odd
      have h1 : (-b) ∈ Set.Icc 0 2 := ⟨by linarith [hb0], by linarith [ha.1, hab]⟩
      have h2 : (-a) ∈ Set.Icc 0 2 := ⟨by linarith [hb0], by linarith [ha.1]⟩
      have hstep := hmono h1 h2 (by linarith : -b < -a)
      rw [modelArcIm_neg (η := η) (δ := δ) (s := s) hδ hδ₂ hs hb,
        modelArcIm_neg (η := η) (δ := δ) (s := s) hδ hδ₂ hs ha] at hstep
      linarith
  · -- `0 ≤ a < b`, both in `[0,2]`: the half-line statement applies
    exact hmono ⟨ha0, ha.2⟩ ⟨le_trans ha0 hab.le, hb.2⟩ hab

end Work.Drive.N2Lead
