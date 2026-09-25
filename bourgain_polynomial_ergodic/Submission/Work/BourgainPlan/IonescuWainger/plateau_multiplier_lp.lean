import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.cutoff
import Submission.Work.BourgainPlan.IonescuWainger.smoothTransition_mikhlin
import Submission.Work.BourgainPlan.IonescuWainger.rescaled_mikhlin_multiplier_lp

/-!
# The `L^p` bound for the plateau multiplier, uniformly in the smoothing scale

For `1 < p < ∞` there is a constant `C`, independent of `ε ∈ (0, 1/2]`, such that the multiplier
operator with symbol `plateau ε` maps `L^p(ℝ)` boundedly into itself with norm at most `C`:

`‖ 𝓕⁻ (plateau ε · 𝓕 G) ‖_{L^p} ≤ C ‖ G ‖_{L^p}`  for every Schwartz function `G`.

The proof writes `plateau ε` as the difference of its two (smooth) edges,
`plateau ε ξ = smoothTransition ((ξ + 1/2)/ε) - smoothTransition ((ξ - 1/2 + ε)/ε)`,
each of which is a *rescaled* Mikhlin symbol (a translate by a centre `c` and a dilation by `ε`
of the fixed profile `smoothTransition`).  The rescaled Mikhlin theorem
(`rescaled_mikhlin_multiplier_lp`) then bounds the two edge operators uniformly in `ε` and `c`,
and the operator of a difference is dominated by the sum of the two edge operators.
-/

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

noncomputable section

/-- `‖z‖ₑ = ENNReal.ofReal ‖z‖` for complex numbers. -/
private lemma enorm_eq_ofReal_norm (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← coe_nnnorm z, ENNReal.ofReal_coe_nnreal]

/-- The plateau is the difference of its two (smoothed) edges, as a pointwise identity in `ξ`. -/
private lemma plateau_eq_edge_sub (ε ξ : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1/2) :
    plateau ε ξ = Real.smoothTransition ((ξ + 1/2)/ε) - Real.smoothTransition ((ξ - 1/2 + ε)/ε) := by
  unfold plateau
  have key : Real.smoothTransition ((ξ - 1/2 + ε)/ε) * (Real.smoothTransition ((ξ + 1/2)/ε) - 1) = 0 := by
    by_cases hb : Real.smoothTransition ((ξ - 1/2 + ε)/ε) = 0
    · rw [hb]; ring
    · have hpos : 0 < (ξ - 1/2 + ε)/ε := by
        by_contra h
        exact hb (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
      have hgt : 0 < ξ - 1/2 + ε := by
        rw [div_pos_iff] at hpos
        rcases hpos with ⟨h1, _⟩ | ⟨h1, h2⟩
        · linarith
        · linarith
      have ha : Real.smoothTransition ((ξ + 1/2)/ε) = 1 := by
        apply Real.smoothTransition.one_of_one_le
        rw [le_div_iff₀ hε]
        linarith
      rw [ha]; ring
  linear_combination (-1) * key

/-- Linearity of the inverse Fourier transform: the norm of the transform of a difference is at
most the sum of the norms of the transforms. -/
private lemma norm_fourierInv_sub_le {A B : ℝ → ℂ} (hA : Integrable A) (hB : Integrable B)
    (x : ℝ) :
    ‖FourierTransformInv.fourierInv (fun ξ => A ξ - B ξ) x‖
      ≤ ‖FourierTransformInv.fourierInv A x‖ + ‖FourierTransformInv.fourierInv B x‖ := by
  have hesm : AEStronglyMeasurable
      (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I)) volume :=
    (by fun_prop : Continuous
      (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I))).aestronglyMeasurable
  have h1 : Integrable
      (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • A ξ) := by
    have h := hA.bdd_mul (c := 1) hesm
      (Filter.Eventually.of_forall (fun ξ => by rw [Complex.norm_exp_ofReal_mul_I]))
    simpa [smul_eq_mul] using h
  have h2 : Integrable
      (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • B ξ) := by
    have h := hB.bdd_mul (c := 1) hesm
      (Filter.Eventually.of_forall (fun ξ => by rw [Complex.norm_exp_ofReal_mul_I]))
    simpa [smul_eq_mul] using h
  rw [Real.fourierInv_eq', Real.fourierInv_eq', Real.fourierInv_eq']
  rw [show (fun ξ : ℝ => Complex.exp (↑(2*Real.pi*inner ℝ ξ x)*Complex.I) • (A ξ - B ξ))
        = fun ξ : ℝ => Complex.exp (↑(2*Real.pi*inner ℝ ξ x)*Complex.I) • A ξ
            - Complex.exp (↑(2*Real.pi*inner ℝ ξ x)*Complex.I) • B ξ by
      funext ξ; rw [smul_sub]]
  rw [MeasureTheory.integral_sub h1 h2]
  exact norm_sub_le _ _

/-- The inverse Fourier transform of an integrable function is continuous. -/
private lemma continuous_fourierInv {g : ℝ → ℂ} (hg : Integrable g) :
    Continuous (fun x : ℝ => FourierTransformInv.fourierInv g x) := by
  have h := Commons.Analysis.Integral.continuous_integral_czE_smul g hg
  refine h.congr (fun x => ?_)
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  simp only [Real.inner_apply, smul_eq_mul]
  congr 1
  push_cast
  ring_nf

/-- The elementary `ENNReal` arithmetic behind the final constant: the sum of two identical
operator bounds, weighted by `2 ^ (p - 1)`, is dominated by the bound with the constant `4 * q`. -/
private lemma ennreal_arith (p : ℝ) (hp : 1 < p) (q : ℝ) (hq : 0 < q) (J : ℝ≥0∞) :
    2 ^ (p - 1) * (ENNReal.ofReal (q ^ p) * J + ENNReal.ofReal (q ^ p) * J)
      ≤ ENNReal.ofReal ((4 * q) ^ p) * J := by
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hq0 : (0:ℝ) ≤ q := hq.le
  have hX : ENNReal.ofReal (q ^ p) * J + ENNReal.ofReal (q ^ p) * J
      = 2 * (ENNReal.ofReal (q^p) * J) := by rw [two_mul]
  rw [hX]
  have hpow : (2:ℝ≥0∞) ^ (p-1) * 2 = (2:ℝ≥0∞)^p := by
    have h1 : (2:ℝ≥0∞)^p = 2^((p-1)+1) := by congr 1; ring
    rw [h1, ENNReal.rpow_add (p-1) 1 (by norm_num) (by norm_num), ENNReal.rpow_one]
  have hstep : (2:ℝ≥0∞)^(p-1) * (2 * (ENNReal.ofReal (q^p)*J))
      = (2:ℝ≥0∞)^p * (ENNReal.ofReal (q^p) * J) := by
    rw [← hpow]; ring
  rw [hstep]
  have h2p : (2:ℝ≥0∞)^p = ENNReal.ofReal (2^p) := by
    rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ENNReal.ofReal_rpow_of_nonneg (by norm_num) hp0.le]
  rw [h2p]
  rw [show ENNReal.ofReal (2^p) * (ENNReal.ofReal (q^p) * J)
        = (ENNReal.ofReal (2^p) * ENNReal.ofReal (q^p)) * J by ring]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) p)]
  rw [← Real.mul_rpow (by norm_num) hq0]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le : (0:ℝ≥0∞) ≤ J)
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow (by positivity) _ hp0.le
  linarith

theorem plateau_multiplier_lp (p : ℝ) (hp : 1 < p) : ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1/2 → ∀ (G : SchwartzMap ℝ ℂ), ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv (fun ξ : ℝ => ((Work.BourgainPlan.IonescuWainger.plateau ε ξ : ℝ) : ℂ) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ p ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x : ℝ, ‖(G : ℝ → ℂ) x‖ₑ ^ p := by
  obtain ⟨A, hA0, hACD, hAbdd, hAd1, hAd2⟩ := smoothTransition_mikhlin
  obtain ⟨Cq, hCqpos, hCq⟩ := rescaled_mikhlin_multiplier_lp p hp
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hp1 : (1:ℝ) ≤ p := le_of_lt hp
  have hA1 : (1:ℝ) ≤ A := by
    have h := hAbdd 1
    rw [Real.smoothTransition.one_of_one_le (le_refl (1:ℝ))] at h
    simpa using h
  have hCqA : 0 < Cq * A := mul_pos hCqpos (lt_of_lt_of_le zero_lt_one hA1)
  refine ⟨4 * (Cq * A), by linarith, ?_⟩
  intro ε hε hε2 G
  have hVint : Integrable (FourierTransform.fourier (G : ℝ → ℂ)) := by
    rw [← SchwartzMap.fourier_coe G]
    exact (FourierTransform.fourier G).integrable
  set BL : ℝ → ℂ := fun ξ => ((Real.smoothTransition ((ξ + 1/2)/ε) : ℝ) : ℂ)
      * FourierTransform.fourier (G : ℝ → ℂ) ξ with hBL
  set BH : ℝ → ℂ := fun ξ => ((Real.smoothTransition ((ξ - 1/2 + ε)/ε) : ℝ) : ℂ)
      * FourierTransform.fourier (G : ℝ → ℂ) ξ with hBH
  set BP : ℝ → ℂ := fun ξ => ((plateau ε ξ : ℝ) : ℂ)
      * FourierTransform.fourier (G : ℝ → ℂ) ξ with hBP
  have hBLnorm : ∀ ξ : ℝ, ‖(((Real.smoothTransition ((ξ + 1/2)/ε) : ℝ)) : ℂ)‖ ≤ (1:ℝ) := by
    intro ξ
    have h1 : ‖(((Real.smoothTransition ((ξ + 1/2)/ε) : ℝ)) : ℂ)‖
        = |Real.smoothTransition ((ξ + 1/2)/ε)| := RCLike.norm_ofReal _
    rw [h1, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hBHnorm : ∀ ξ : ℝ, ‖(((Real.smoothTransition ((ξ - 1/2 + ε)/ε) : ℝ)) : ℂ)‖ ≤ (1:ℝ) := by
    intro ξ
    have h1 : ‖(((Real.smoothTransition ((ξ - 1/2 + ε)/ε) : ℝ)) : ℂ)‖
        = |Real.smoothTransition ((ξ - 1/2 + ε)/ε)| := RCLike.norm_ofReal _
    rw [h1, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hBLint : Integrable BL := by
    rw [hBL]
    refine hVint.bdd_mul (c := 1)
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards with ξ
    exact hBLnorm ξ
  have hBHint : Integrable BH := by
    rw [hBH]
    refine hVint.bdd_mul (c := 1)
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards with ξ
    exact hBHnorm ξ
  -- the pointwise identity `plateau ε = edgeLo - edgeHi`
  have hfun : BL - BH = BP := by
    funext ξ
    simp only [Pi.sub_apply, hBL, hBH, hBP]
    rw [← sub_mul, ← Complex.ofReal_sub, ← plateau_eq_edge_sub ε ξ hε hε2]
  have hpt : ∀ x : ℝ, ‖FourierTransformInv.fourierInv BP x‖
      ≤ ‖FourierTransformInv.fourierInv BL x‖ + ‖FourierTransformInv.fourierInv BH x‖ := by
    intro x
    rw [← hfun]
    exact norm_fourierInv_sub_le hBLint hBHint x
  have hcontL : Continuous (fun x : ℝ => FourierTransformInv.fourierInv BL x) :=
    continuous_fourierInv hBLint
  have hcontH : Continuous (fun x : ℝ => FourierTransformInv.fourierInv BH x) :=
    continuous_fourierInv hBHint
  have hmeasL : Measurable (fun x : ℝ => ‖FourierTransformInv.fourierInv BL x‖ₑ ^ p) :=
    (ENNReal.continuous_rpow_const.comp (continuous_enorm.comp hcontL)).measurable
  have hmeasH : Measurable (fun x : ℝ => ‖FourierTransformInv.fourierInv BH x‖ₑ ^ p) :=
    (ENNReal.continuous_rpow_const.comp (continuous_enorm.comp hcontH)).measurable
  have hpt' : ∀ x : ℝ, ‖FourierTransformInv.fourierInv BP x‖ₑ
      ≤ ‖FourierTransformInv.fourierInv BL x‖ₑ + ‖FourierTransformInv.fourierInv BH x‖ₑ := by
    intro x
    calc ‖FourierTransformInv.fourierInv BP x‖ₑ
        = ENNReal.ofReal ‖FourierTransformInv.fourierInv BP x‖ := enorm_eq_ofReal_norm _
      _ ≤ ENNReal.ofReal (‖FourierTransformInv.fourierInv BL x‖
            + ‖FourierTransformInv.fourierInv BH x‖) := ENNReal.ofReal_le_ofReal (hpt x)
      _ = ENNReal.ofReal ‖FourierTransformInv.fourierInv BL x‖
            + ENNReal.ofReal ‖FourierTransformInv.fourierInv BH x‖ :=
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
      _ = ‖FourierTransformInv.fourierInv BL x‖ₑ
            + ‖FourierTransformInv.fourierInv BH x‖ₑ := by
          rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm]
  -- the two rescaled-Mikhlin edge bounds
  have hLo := hCq (fun ξ : ℝ => (Real.smoothTransition ξ : ℂ)) A hA0 hACD hAbdd hAd1 hAd2
    ε (-(1/2)) hε G
  have hsymLo : (fun ξ : ℝ => ((Real.smoothTransition ((ξ - (-(1/2)))/ε) : ℝ) : ℂ)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ)
      = (fun ξ : ℝ => ((Real.smoothTransition ((ξ + 1/2)/ε) : ℝ) : ℂ)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ) := by
    funext ξ; rw [show (ξ - (-(1/2)))/ε = (ξ + 1/2)/ε by ring]
  rw [hsymLo, ← hBL] at hLo
  have hHi := hCq (fun ξ : ℝ => (Real.smoothTransition ξ : ℂ)) A hA0 hACD hAbdd hAd1 hAd2
    ε (1/2 - ε) hε G
  have hsymHi : (fun ξ : ℝ => ((Real.smoothTransition ((ξ - (1/2 - ε))/ε) : ℝ) : ℂ)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ)
      = (fun ξ : ℝ => ((Real.smoothTransition ((ξ - 1/2 + ε)/ε) : ℝ) : ℂ)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ) := by
    funext ξ; rw [show (ξ - (1/2 - ε))/ε = (ξ - 1/2 + ε)/ε by ring]
  rw [hsymHi, ← hBH] at hHi
  calc ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv BP x‖ₑ ^ p
      ≤ ∫⁻ x : ℝ, (‖FourierTransformInv.fourierInv BL x‖ₑ
          + ‖FourierTransformInv.fourierInv BH x‖ₑ) ^ p :=
        lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpt' x) hp0.le)
    _ ≤ ∫⁻ x : ℝ, 2 ^ (p - 1) * (‖FourierTransformInv.fourierInv BL x‖ₑ ^ p
          + ‖FourierTransformInv.fourierInv BH x‖ₑ ^ p) :=
        lintegral_mono (fun x => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp1)
    _ = 2 ^ (p - 1) * ∫⁻ x : ℝ, (‖FourierTransformInv.fourierInv BL x‖ₑ ^ p
          + ‖FourierTransformInv.fourierInv BH x‖ₑ ^ p) :=
        lintegral_const_mul _ (hmeasL.add hmeasH)
    _ = 2 ^ (p - 1) * ((∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv BL x‖ₑ ^ p)
          + (∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv BH x‖ₑ ^ p)) := by
        rw [lintegral_add_left hmeasL]
    _ ≤ 2 ^ (p - 1) * ((ENNReal.ofReal ((Cq * A) ^ p) * (∫⁻ x : ℝ, ‖(G : ℝ → ℂ) x‖ₑ ^ p))
          + (ENNReal.ofReal ((Cq * A) ^ p) * (∫⁻ x : ℝ, ‖(G : ℝ → ℂ) x‖ₑ ^ p))) :=
        mul_le_mul_of_nonneg_left (add_le_add hLo hHi) (zero_le : (0:ℝ≥0∞) ≤ 2 ^ (p - 1))
    _ ≤ ENNReal.ofReal ((4 * (Cq * A)) ^ p) * (∫⁻ x : ℝ, ‖(G : ℝ → ℂ) x‖ₑ ^ p) :=
        ennreal_arith p hp (Cq * A) hCqA _

end

end Work.BourgainPlan.IonescuWainger