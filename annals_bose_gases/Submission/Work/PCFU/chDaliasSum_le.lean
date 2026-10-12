import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseBoxFock.PCFU.ChDKernelDefs
import Submission.Work.BoseBoxFock.W1fun_L1_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.PCFU.chDaliasSum_le` — the alias (image) sum of the `(D)`-slot kernel

The `(D)`-channel alias slot pairs the low-momentum slot function against the `z`-kernel
`F = KχfrU − Ĉ`, and the *alias* sum `Σ'_{d ≠ 0} (χ_ℓ ⋆ W₁)(z + ℓ•d)` is one of its two error
terms: it is small because `W₁ = W(1−ω)` is supported in `ball 0 R` with `2R ≤ ℓ`, so the
`d`-th translation `z + ℓ•d` can only meet the `R`-neighbourhood of the box `ℓ•cell` when
`‖d‖ ≤ 1 + R/ℓ`, and at such a `d ≠ 0` the localisation factor `χ_ℓ` is evaluated at distance
`≥ 1/2 − R/ℓ` from the origin, where the bump is *flat*:

    `chi x ≤ C_K (1/2 − ‖x‖)^K`   for `‖x‖ ≤ 1/2`   (`Work.BoseFixB1.chi_boundary_taylor`).

Taking `K = 6` gives the stated `(R/ℓ)^6` decay, with the constant
`26·(√chiNormSq)⁻¹·C₆` times the `L¹`-mass `∫|W₁|` — exactly the shape used by the
`(D)`-slot estimate (`FINDING_chiScale_imageSum_lowKer_le.md` is the sibling statement for
the far-kernel alias sum).

Everything is proved directly: `raw` lattice bookkeeping (`tsum_eq_sum` on the finite set
`{-1,0,1}³`), the support geometry (`W1fun` sits in `ball 0 R`), the flatness of the corpus
bump at its support boundary, and translation invariance of the Lebesgue integral.
-/

namespace Work.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The support of the localisation bump `χ_ℓ = χ(·/ℓ)` -/

/-- `χ_ℓ = corpusBox.chiLam ℓ` is supported in `ball 0 (ℓ/2)`. -/
private lemma chiLam_supp {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3)
    (hx : Work.BoseK15.corpusBox.chiLam ℓ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  have hx' : Submission.BoseGases.chi (ℓ⁻¹ • x) ≠ 0 := hx
  have h1 : ‖ℓ⁻¹ • x‖ < (1 : ℝ) / 2 := by
    by_contra hc
    have hb : Submission.BoseGases.chiBase (ℓ⁻¹ • x) = 0 := by
      apply Submission.BoseGases.chiBump.zero_of_le_dist
      simpa [Submission.BoseGases.chiBump, dist_eq_norm] using le_of_not_gt hc
    exact hx' (by simp [Submission.BoseGases.chi, hb])
  have h2 : ‖ℓ⁻¹ • x‖ = ℓ⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
  rw [h2] at h1
  have : ‖x‖ < ℓ * (1 / 2) := by
    calc ‖x‖ = ℓ * (ℓ⁻¹ * ‖x‖) := by rw [mul_inv_cancel_left₀ (ne_of_gt hℓ)]
      _ < ℓ * (1 / 2) := mul_lt_mul_of_pos_left h1 hℓ
  linarith

/-! ## 2. The flatness of the corpus bump at its support boundary, in `max` form -/

/-- `chi x ≤ C (max 0 (1/2 − ‖x‖))^6` for every `x`: on `ball 0 (1/2)` this is the boundary
Taylor bound `chi_boundary_taylor 6`, and off it `chi` vanishes. -/
private lemma chi_max_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3,
    Submission.BoseGases.chi x ≤ C * (max 0 ((1 : ℝ) / 2 - ‖x‖)) ^ 6 := by
  obtain ⟨C₆, hC₆pos, hC₆⟩ := Work.BoseFixB1.chi_boundary_taylor 6
  refine ⟨C₆, le_of_lt hC₆pos, fun x => ?_⟩
  rcases le_or_gt ‖x‖ ((1 : ℝ) / 2) with h | h
  · have hmax : max 0 ((1 : ℝ) / 2 - ‖x‖) = (1 : ℝ) / 2 - ‖x‖ := max_eq_right (by linarith)
    rw [hmax]
    exact hC₆ x h
  · have hz : Submission.BoseGases.chi x = 0 := by
      have hb : Submission.BoseGases.chiBase x = 0 := by
        apply Submission.BoseGases.chiBump.zero_of_le_dist
        simpa [Submission.BoseGases.chiBump, dist_eq_norm] using h.le
      simp [Submission.BoseGases.chi, hb]
    rw [hz]
    positivity

/-! ## 3. The pointwise bound on the localisation factor at `w = z + ℓ•d − y` -/

/-- If `‖z‖ < ℓ/2` and `d ≠ 0` carries the index mass `‖latVec d‖ ≥ 1`, then for every `w` with
`z + ℓ•d − w` inside the support `ball 0 R` of `W₁` one has `χ_ℓ(w) ≤ C₆ (R/ℓ)^6`. -/
private lemma chiLam_le_pow {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) {C₆ : ℝ}
    (hC₆ : ∀ x : E3, Submission.BoseGases.chi x ≤ C₆ * (max 0 ((1 : ℝ) / 2 - ‖x‖)) ^ 6)
    (hC6nn : 0 ≤ C₆) {z : E3} (hz : ‖z‖ < ℓ / 2) {d : Fin 3 → ℤ}
    (hB : 1 ≤ ‖Work.BoseBoxFock.latVec d‖) {w : E3}
    (hy : ‖(z + ℓ • Work.BoseBoxFock.latVec d) - w‖ < R) :
    Work.BoseK15.corpusBox.chiLam ℓ w ≤ C₆ * (R / ℓ) ^ 6 := by
  set y : E3 := (z + ℓ • Work.BoseBoxFock.latVec d) - w with hydef
  have hsplit : ℓ⁻¹ • w = Work.BoseBoxFock.latVec d + ℓ⁻¹ • (z - y) := by
    rw [hydef, smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hℓ), one_smul]
    abel
  have hBnorm : ‖Work.BoseBoxFock.latVec d‖ ≤ ‖ℓ⁻¹ • w‖ + ‖ℓ⁻¹ • (z - y)‖ := by
    have h4 := norm_sub_le (ℓ⁻¹ • w) (ℓ⁻¹ • (z - y))
    have h5 : ℓ⁻¹ • w - ℓ⁻¹ • (z - y) = Work.BoseBoxFock.latVec d := by rw [hsplit]; abel
    rwa [h5] at h4
  have h2 : ‖ℓ⁻¹ • (z - y)‖ < (1 : ℝ) / 2 + R / ℓ := by
    have h4 : ‖z - y‖ < ℓ / 2 + R := by
      have h5 := norm_sub_le z y
      rw [hydef] at hy
      linarith
    have h6 : ‖ℓ⁻¹ • (z - y)‖ = ℓ⁻¹ * ‖z - y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
    have h7 : ℓ⁻¹ * (ℓ / 2 + R) = 1 / 2 + R / ℓ := by field_simp
    rw [h6]
    calc ℓ⁻¹ * ‖z - y‖ < ℓ⁻¹ * (ℓ / 2 + R) := mul_lt_mul_of_pos_left h4 (inv_pos.mpr hℓ)
      _ = 1 / 2 + R / ℓ := h7
  have h3 : (1 : ℝ) / 2 - ‖ℓ⁻¹ • w‖ < R / ℓ := by linarith
  have hRl0 : 0 ≤ R / ℓ := div_nonneg hR.le hℓ.le
  have hmax : max 0 ((1 : ℝ) / 2 - ‖ℓ⁻¹ • w‖) ≤ R / ℓ := max_le hRl0 (le_of_lt h3)
  have hmain := hC₆ (ℓ⁻¹ • w)
  have hp : (max 0 ((1 : ℝ) / 2 - ‖ℓ⁻¹ • w‖)) ^ 6 ≤ (R / ℓ) ^ 6 :=
    pow_le_pow_left₀ (le_max_left _ _) hmax 6
  have hgoal : Work.BoseK15.corpusBox.chiLam ℓ w = Submission.BoseGases.chi (ℓ⁻¹ • w) := rfl
  rw [hgoal]
  exact le_trans hmain (mul_le_mul_of_nonneg_left hp hC6nn)

/-! ## 4. The `(χ_ℓ ⋆ W₁)`-value at an interior alias slot -/

/-- For `‖z‖ < ℓ/2` and `‖latVec d‖ ≥ 1`,
`|(χ_ℓ ⋆ W₁)(z + ℓ•d)| ≤ C₆ (R/ℓ)^6 ∫|W₁|`. -/
private lemma chDconv_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (_hv : 0 ≤ v) (_hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {C₆ : ℝ} (hC₆ : ∀ x : E3, Submission.BoseGases.chi x ≤ C₆ * (max 0 ((1 : ℝ) / 2 - ‖x‖)) ^ 6)
    (hC6nn : 0 ≤ C₆) {z : E3} (hz : ‖z‖ < ℓ / 2) {d : Fin 3 → ℤ}
    (hB : 1 ≤ ‖Work.BoseBoxFock.latVec d‖) :
    ‖Work.BoseBoxFock.PCFU.chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
        (z + ℓ • Work.BoseBoxFock.latVec d)‖
      ≤ C₆ * (R / ℓ) ^ 6 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|) := by
  have hW1int : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) := by
    have := Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
    simpa [Work.BoseFixR.W1fun] using this
  have hW1abs : MeasureTheory.Integrable (fun y : E3 => |Work.BoseFixR.W1fun v h ℓ y|) := by
    have h1 := hW1int.abs
    simpa [Real.norm_eq_abs] using h1
  set U : E3 := z + ℓ • Work.BoseBoxFock.latVec d with hUdef
  have hpt : ∀ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * |Work.BoseFixR.W1fun v h ℓ (U - w)|
      ≤ (C₆ * (R / ℓ) ^ 6) * |Work.BoseFixR.W1fun v h ℓ (U - w)| := by
    intro w
    by_cases hw : Work.BoseFixR.W1fun v h ℓ (U - w) = 0
    · simp [hw]
    · have hy : ‖(z + ℓ • Work.BoseBoxFock.latVec d) - w‖ < R := by
        by_contra hc
        have hmem : U - w ∈ Function.support (Work.BoseFixR.W1fun v h ℓ) := by
          simpa [Function.mem_support] using hw
        have hspec := Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ (subset_tsupport _ hmem)
        rw [Metric.mem_ball, dist_zero_right] at hspec
        rw [hUdef] at hspec
        exact absurd hspec (not_lt.mpr (le_of_not_gt hc))
      exact mul_le_mul_of_nonneg_right (chiLam_le_pow hR hℓ hC₆ hC6nn hz hB hy) (abs_nonneg _)
  have hstep1 : (∫ w, ‖(((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ)) : ℂ)
      * ((Work.BoseFixR.W1fun v h ℓ (U - w) : ℝ) : ℂ)‖)
      = ∫ w, Work.BoseK15.corpusBox.chiLam ℓ w * |Work.BoseFixR.W1fun v h ℓ (U - w)| := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ Work.BoseK15.corpusBox.chiLam ℓ w from
      Submission.BoseGases.chi_nonneg _)]
  set F : E3 → ℝ :=
    fun y => Work.BoseK15.corpusBox.chiLam ℓ y * |Work.BoseFixR.W1fun v h ℓ (U - y)| with hFdef
  have hstep2 : (∫ y, F y)
      = ∫ y, Work.BoseK15.corpusBox.chiLam ℓ (U - y) * |Work.BoseFixR.W1fun v h ℓ y| := by
    have hA : (∫ y, F (U - y)) = ∫ y, F y := Submission.BoseGases.integral_comp_sub_left F U
    have hB : (∫ y, F (U - y))
        = ∫ y, Work.BoseK15.corpusBox.chiLam ℓ (U - y) * |Work.BoseFixR.W1fun v h ℓ y| := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      simp only [hFdef, sub_sub_self]
    exact hA.symm.trans hB
  have hptG : ∀ y : E3, Work.BoseK15.corpusBox.chiLam ℓ (U - y) * |Work.BoseFixR.W1fun v h ℓ y|
      ≤ (C₆ * (R / ℓ) ^ 6) * |Work.BoseFixR.W1fun v h ℓ y| := by
    intro y
    have h := hpt (U - y)
    rwa [sub_sub_self] at h
  have hmono : (∫ y, Work.BoseK15.corpusBox.chiLam ℓ (U - y) * |Work.BoseFixR.W1fun v h ℓ y|)
      ≤ ∫ y, (C₆ * (R / ℓ) ^ 6) * |Work.BoseFixR.W1fun v h ℓ y| := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun y =>
        mul_nonneg (Submission.BoseGases.chi_nonneg _) (abs_nonneg _)
    · exact hW1abs.const_mul _
    · exact Filter.Eventually.of_forall hptG
  rw [Work.BoseBoxFock.PCFU.chDconv]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  rw [hstep1, hstep2]
  rw [← MeasureTheory.integral_const_mul]
  exact hmono

/-! ## 5. Vanishing of the alias slot far from the box -/

/-- If `R + ℓ/2 ≤ ‖u‖`, the convolution `(χ_ℓ ⋆ W₁)(u)` vanishes: the `χ_ℓ`-factor forces
`‖w‖ < ℓ/2`, and then `‖u − w‖ > R` puts `u − w` outside the support of `W₁`. -/
private lemma chDconv_eq_zero_far {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {ℓ : ℝ} (hℓ : 0 < ℓ) (u : E3)
    (hu : R + ℓ / 2 ≤ ‖u‖) :
    Work.BoseBoxFock.PCFU.chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ)) u = 0 := by
  rw [Work.BoseBoxFock.PCFU.chDconv]
  have hzero : (fun w : E3 => (((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ)) : ℂ)
      * ((Work.BoseFixR.W1fun v h ℓ (u - w) : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
    funext w
    by_cases hw : Work.BoseK15.corpusBox.chiLam ℓ w = 0
    · have hw' : Submission.BoseGases.chi (ℓ⁻¹ • w) = 0 := hw
      simp [hw']
    · have hwn : ‖w‖ < ℓ / 2 := chiLam_supp hℓ w hw
      have hlt : R < ‖u - w‖ := by
        have h1 : ‖u‖ ≤ ‖u - w‖ + ‖w‖ := by
          have h2 := norm_add_le (u - w) w
          rwa [sub_add_cancel] at h2
        linarith
      have hW : Work.BoseFixR.W1fun v h ℓ (u - w) = 0 := by
        by_contra hc
        have hmem : u - w ∈ Function.support (Work.BoseFixR.W1fun v h ℓ) := by
          simpa [Function.mem_support] using hc
        have hball := Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ (subset_tsupport _ hmem)
        rw [Metric.mem_ball, dist_zero_right] at hball
        linarith
      have hW' : ((Work.BoseFixR.W1fun v h ℓ (u - w) : ℝ) : ℂ) = 0 := by simp [hW]
      simp [hW']
  rw [hzero]
  simp

/-! ## 6. The alias sum -/

theorem chDaliasSum_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃ℓ : ℝ⦄, 0 < ℓ → ∀ ⦃N : ℕ⦄ (z : EuclideanSpace ℝ (Fin 3)),
      R ≤ ℓ * Submission.BoseGases.chiR0 → 2 * R ≤ ℓ →
      (∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
          ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
            * Work.BoseBoxFock.PCFU.chDconv ℓ
                (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                (z + ℓ • Work.BoseBoxFock.latVec d)‖))
        ≤ C * (R / ℓ) ^ 6 * (∫ u : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h ℓ u|) := by
  obtain ⟨C₆, hC6nn, hC₆⟩ := chi_max_bound
  refine ⟨27 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * C₆, ?_, ?_⟩
  · have : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    positivity
  intro ℓ hℓ N z hRℓ h2R
  set M₀ : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hM0def
  set G : ℝ := ∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y| with hGdef
  have hGnn : 0 ≤ G := by
    rw [hGdef]
    exact MeasureTheory.integral_nonneg (fun y => abs_nonneg _)
  have hM0nn : 0 ≤ M₀ := by rw [hM0def]; positivity
  have hRl0 : 0 ≤ R / ℓ := div_nonneg hR.le hℓ.le
  have hTermnn : 0 ≤ M₀ * (C₆ * (R / ℓ) ^ 6 * G) :=
    mul_nonneg hM0nn (mul_nonneg (mul_nonneg hC6nn (pow_nonneg hRl0 6)) hGnn)
  have hRhsnn : 0 ≤ 27 * M₀ * C₆ * (R / ℓ) ^ 6 * G :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0nn) hC6nn)
      (pow_nonneg hRl0 6)) hGnn
  by_cases hz0 : Work.BoseK15.corpusBox.chiLam ℓ z = 0
  · -- the whole sum vanishes: the outer factor `χ_ℓ(z)` is zero
    have hzero : ∀ d : (Fin 3 → ℤ),
        (if d = 0 then 0 else
          ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
            * Work.BoseBoxFock.PCFU.chDconv ℓ
                (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                (z + ℓ • Work.BoseBoxFock.latVec d)‖) = 0 := by
      intro d
      by_cases hd : d = 0
      · rw [if_pos hd]
      · rw [if_neg hd]
        have hc : (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) = 0 := by
          rw [hz0]; simp
        rw [hc]; simp
    rw [tsum_eq_sum (s := (∅ : Finset (Fin 3 → ℤ))) (fun d _ => hzero d)]
    simp only [Finset.sum_empty]
    simpa using hRhsnn
  · -- the main case: `z` lies in the box and only `d ∈ {-1,0,1}³` contribute
    have hzn : ‖z‖ < ℓ / 2 := chiLam_supp hℓ z hz0
    set S : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)
      with hSdef
    have hScard : S.card = 27 := by
      rw [hSdef, Fintype.card_piFinset]
      decide
    -- the index-mass lower bound for `d ∈ S \ {0}`
    have hBmem : ∀ d ∈ S, d ≠ 0 → (1 : ℝ) ≤ ‖Work.BoseBoxFock.latVec d‖ := by
      intro d hdS hd
      have hmem : d ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1) := by
        rwa [hSdef] at hdS
      have hbnd : ∀ i, d i ∈ Finset.Icc (-1 : ℤ) 1 := Fintype.mem_piFinset.mp hmem
      obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hd (funext hc)
      have h1 : (1 : ℤ) ≤ |d i| := Int.one_le_abs hi
      have h2 : (1 : ℝ) ≤ |((d i : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast h1
      have h3 : |((d i : ℤ) : ℝ)| ≤ ‖Work.BoseBoxFock.latVec d‖ := by
        have := PiLp.norm_apply_le (Work.BoseBoxFock.latVec d) i
        simpa [Real.norm_eq_abs, Work.BoseBoxFock.latVec_apply] using this
      linarith
    -- terms outside `S` vanish
    have hout : ∀ d ∉ S,
        (if d = 0 then 0 else
          ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
            * Work.BoseBoxFock.PCFU.chDconv ℓ
                (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                (z + ℓ • Work.BoseBoxFock.latVec d)‖) = 0 := by
      intro d hdS
      by_cases hd : d = 0
      · rw [if_pos hd]
      · have hfar : 1 + R / ℓ ≤ ‖Work.BoseBoxFock.latVec d‖ := by
          have hnot : ¬ (∀ i, d i ∈ Finset.Icc (-1 : ℤ) 1) := by
            intro hcon
            exact hdS (by rw [hSdef, Fintype.mem_piFinset]; exact hcon)
          push Not at hnot
          obtain ⟨i, hi⟩ := hnot
          have h2 : (2 : ℤ) ≤ |d i| := by
            have hlt : d i < -1 ∨ 1 < d i := by
              have hni : ¬ ((-1 : ℤ) ≤ d i ∧ d i ≤ 1) := by
                rw [Finset.mem_Icc] at hi; exact hi
              omega
            rcases hlt with hl | hl
            · rw [abs_of_neg (by omega)]; omega
            · rw [abs_of_pos (by omega)]; omega
          have h2' : (2 : ℝ) ≤ |((d i : ℤ) : ℝ)| := by
            rw [← Int.cast_abs]; exact_mod_cast h2
          have h3 : |((d i : ℤ) : ℝ)| ≤ ‖Work.BoseBoxFock.latVec d‖ := by
            have := PiLp.norm_apply_le (Work.BoseBoxFock.latVec d) i
            simpa [Real.norm_eq_abs, Work.BoseBoxFock.latVec_apply] using this
          have hRl : R / ℓ ≤ 1 / 2 := by
            rw [div_le_iff₀ hℓ]; linarith
          linarith
        have hu : R + ℓ / 2 ≤ ‖z + ℓ • Work.BoseBoxFock.latVec d‖ := by
          have h1 : ℓ * ‖Work.BoseBoxFock.latVec d‖ ≤
              ‖z + ℓ • Work.BoseBoxFock.latVec d‖ + ‖z‖ := by
            have h4 := norm_add_le (z + ℓ • Work.BoseBoxFock.latVec d) (-(z))
            have h5 : (z + ℓ • Work.BoseBoxFock.latVec d) + (-z) = ℓ • Work.BoseBoxFock.latVec d := by
              abel
            rw [h5] at h4
            have h6 : ‖ℓ • Work.BoseBoxFock.latVec d‖ = ℓ * ‖Work.BoseBoxFock.latVec d‖ := by
              rw [norm_smul, Real.norm_of_nonneg hℓ.le]
            rw [h6] at h4
            simpa using h4
          have h7 : ℓ * (1 + R / ℓ) = ℓ + R := by field_simp
          have h2 : ℓ * (1 + R / ℓ) ≤ ℓ * ‖Work.BoseBoxFock.latVec d‖ :=
            mul_le_mul_of_nonneg_left hfar hℓ.le
          linarith
        have hcv : Work.BoseBoxFock.PCFU.chDconv ℓ
            (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
            (z + ℓ • Work.BoseBoxFock.latVec d) = 0 :=
          chDconv_eq_zero_far hv_supp hℓ (z + ℓ • Work.BoseBoxFock.latVec d) hu
        rw [if_neg hd, hcv]
        simp
    rw [tsum_eq_sum (s := S) hout]
    have hterm : ∀ d ∈ S,
        (if d = 0 then 0 else
          ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
            * Work.BoseBoxFock.PCFU.chDconv ℓ
                (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                (z + ℓ • Work.BoseBoxFock.latVec d)‖) ≤ M₀ * (C₆ * (R / ℓ) ^ 6 * G) := by
      intro d hdS
      by_cases hd : d = 0
      · rw [if_pos hd]
        exact hTermnn
      · have hB : (1 : ℝ) ≤ ‖Work.BoseBoxFock.latVec d‖ := hBmem d hdS hd
        have hmain : ‖Work.BoseBoxFock.PCFU.chDconv ℓ
            (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
            (z + ℓ • Work.BoseBoxFock.latVec d)‖
            ≤ C₆ * (R / ℓ) ^ 6 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|) :=
          chDconv_le hR hv hvrad hv_supp hℓ hRℓ hC₆ hC6nn hzn hB
        have hzle : |Work.BoseK15.corpusBox.chiLam ℓ z| ≤ M₀ := by
          have hs : (0 : ℝ) ≤ Real.sqrt Submission.BoseGases.chiNormSq := Real.sqrt_nonneg _
          have h1 : Work.BoseK15.corpusBox.chiLam ℓ z
              ≤ 1 / Real.sqrt Submission.BoseGases.chiNormSq := by
            rw [show Work.BoseK15.corpusBox.chiLam ℓ z
                = Submission.BoseGases.chiBase (ℓ⁻¹ • z)
                  / Real.sqrt Submission.BoseGases.chiNormSq from rfl]
            exact div_le_div_of_nonneg_right (Submission.BoseGases.chiBase_le_one _) hs
          have h2 : (1 : ℝ) / Real.sqrt Submission.BoseGases.chiNormSq = M₀ := by
            rw [hM0def, one_div]
          have h3 : 0 ≤ Work.BoseK15.corpusBox.chiLam ℓ z := Submission.BoseGases.chi_nonneg _
          rw [abs_of_nonneg h3]
          linarith
        rw [if_neg hd]
        calc ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
              * Work.BoseBoxFock.PCFU.chDconv ℓ
                  (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                  (z + ℓ • Work.BoseBoxFock.latVec d)‖
            = |Work.BoseK15.corpusBox.chiLam ℓ z| *
                ‖Work.BoseBoxFock.PCFU.chDconv ℓ
                  (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                  (z + ℓ • Work.BoseBoxFock.latVec d)‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ M₀ * (C₆ * (R / ℓ) ^ 6 * G) :=
              le_trans (mul_le_mul_of_nonneg_right hzle (norm_nonneg _))
                (mul_le_mul_of_nonneg_left (by simpa [hGdef] using hmain) hM0nn)
    calc (∑ d ∈ S, (if d = 0 then 0 else
            ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
              * Work.BoseBoxFock.PCFU.chDconv ℓ
                  (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                  (z + ℓ • Work.BoseBoxFock.latVec d)‖))
        ≤ S.card • (M₀ * (C₆ * (R / ℓ) ^ 6 * G)) := Finset.sum_le_card_nsmul _ _ _ hterm
      _ = 27 * M₀ * C₆ * (R / ℓ) ^ 6 * G := by
          rw [hScard, nsmul_eq_mul]
          ring

end Work.PCFU
