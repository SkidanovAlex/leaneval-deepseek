import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.Cross.bsCross_expand_mean
import Submission.Work.OneBodyKin.Cross.bsCross_subst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.bsMean_bsPair_eq_kernelForm`

The cross term of the projected moving-box family form,
`∫_u bsMean ℓ u ψ · bsPair ℓ F u ψ`, is the quadratic form of the *convolution kernel*
`bsKern ℓ F` (`OneBodyKin/CrossKern`):

  `∫_u bsMean ℓ u ψ · bsPair ℓ F u ψ
     = (2π)⁻³ ∫_x ∫_y bsKern ℓ F (x − y) · ψ x · ψ y`.

## The computation

`bsPair` is the moving-box window form `⟨χ_u, F(√−Δ)(χ_uψ)⟩`; in the cosine form
(`OneBodyKin/bsPair_eq_cos`), with the box mean `bsMean ℓ u ψ = ∫_{s∈acube 1} ψ(ℓ(u+s))`
(`OneBodyKin/bsMean_eq_boxMean`) and the `(p,v)`-factor
`bsLf ℓ F p v = F ‖p‖ profHat(ℓp) χ v cos⟪ℓp,v⟫` (`OneBodyKin/CrossDefs`), the left-hand side is

  `(2π)⁻³ ℓ⁶ ∫_u (∫_{s∈acube 1} ψ(ℓ(u+s))) · ∫_p ∫_v bsLf ℓ F p v · ψ(ℓ(v+u))`   (`bsCross_step0`).

Exchanging the integrals (`Cross/bsCross_expand_mean`) and substituting `x = ℓ(u+s)`,
`d = ℓ(v−s)` (`Cross/bsCross_subst`, with `(ℓ³)⁻¹·(ℓ³)⁻¹ = (ℓ⁶)⁻¹` cancelling the `ℓ⁶`) gives

  `(2π)⁻³ ∫_p ∫_{s∈acube 1} ∫_d bsLf ℓ F p (s + ℓ⁻¹d) · bsAc ψ d`,

and three exchanges (`Work.OneBodyKin.bsCross_mid`) turn the inner bracket into `bsKern ℓ F d`.
The right-hand side is brought to the same form by the substitution `y = x + d`, Fubini and the
parity of the kernel (`Work.OneBodyKin.bsCross_rhs`).
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The window `s + ℓ⁻¹d` of the cross kernel -/

/-- For `‖d‖ > (3/2)ℓ` and `s ∈ acube 1` the point `s + ℓ⁻¹d` lies outside the support of `χ`. -/
lemma chi_slab_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {d : ℝ³} (hd : ℓ * (3 / 2) < ‖d‖) {s : ℝ³}
    (hs : s ∈ acube 1) : chi (s + ℓ⁻¹ • d) = 0 := by
  apply chi_eq_zero_of_norm_gt
  have hs1 : ‖s‖ ≤ 1 := Work.BSKinetic.bs_norm_le_of_mem_acube (by norm_num) hs
  have hd1 : ‖ℓ⁻¹ • d‖ = ℓ⁻¹ * ‖d‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
  have hsub : ‖ℓ⁻¹ • d‖ - ‖s‖ ≤ ‖ℓ⁻¹ • d + s‖ := by
    have h := norm_sub_le (ℓ⁻¹ • d + s) s
    simpa using h
  have h3 : (1 / 2 : ℝ) < ℓ⁻¹ * ‖d‖ - 1 := by
    have h4 : (3 / 2 : ℝ) < ℓ⁻¹ * ‖d‖ := by
      rw [inv_mul_eq_div, lt_div_iff₀ hℓ]
      linarith
    linarith
  have h4 : ℓ⁻¹ * ‖d‖ - 1 ≤ ‖ℓ⁻¹ • d + s‖ := by
    rw [hd1] at hsub
    linarith
  calc (1 / 2 : ℝ) < ℓ⁻¹ * ‖d‖ - 1 := h3
    _ ≤ ‖ℓ⁻¹ • d + s‖ := h4
    _ = ‖s + ℓ⁻¹ • d‖ := by rw [add_comm]

/-- The `(s,d)`-factor `χ(s + ℓ⁻¹d) · bsAc ψ d` of the cross kernel is bounded by a constant on
`acube 1 ×ˢ closedBall 0 ((3/2)ℓ)` and vanishes for `‖d‖ > (3/2)ℓ`, `s ∈ acube 1`. -/
lemma abs_chi_slab_mul_le {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} {C : ℝ} (hC : ∀ x, |ψ x| ≤ C)
    {R : ℝ} (hR : ∀ x, R ≤ ‖x‖ → ψ x = 0) {s : ℝ³} (hs : s ∈ acube 1) (d : ℝ³) :
    |chi (s + ℓ⁻¹ • d) * bsAc ψ d|
      ≤ (Real.sqrt chiNormSq)⁻¹ * (C ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R)) *
        (Metric.closedBall (0 : ℝ³) (ℓ * (3 / 2))).indicator (fun _ => (1 : ℝ)) d := by
  have hA : |bsAc ψ d| ≤ C ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R) :=
    abs_bsAc_le hC hR d
  have hA0 : 0 ≤ C ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R) := by
    linarith [abs_bsAc_le hC hR (0 : ℝ³), abs_nonneg (bsAc ψ 0)]
  have hχ0 : 0 ≤ (Real.sqrt chiNormSq)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  by_cases hd : d ∈ Metric.closedBall (0 : ℝ³) (ℓ * (3 / 2))
  · rw [Set.indicator_of_mem hd, mul_one]
    calc |chi (s + ℓ⁻¹ • d) * bsAc ψ d|
        = |chi (s + ℓ⁻¹ • d)| * |bsAc ψ d| := abs_mul _ _
      _ ≤ (Real.sqrt chiNormSq)⁻¹ * (C ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R)) := by
          refine mul_le_mul ?_ hA (abs_nonneg _) hχ0
          rw [abs_of_nonneg (chi_nonneg _)]
          exact chi_le_sqrt_inv _
  · rw [Set.indicator_of_notMem hd, mul_zero, chi_slab_eq_zero hℓ ?_ hs, zero_mul, abs_zero]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hd
    exact hd

/-! ## 2. Auxiliary measurability and integrability facts -/

/-- The indicator of a closed ball of `ℝ³` is integrable. -/
lemma integrable_indicator_closedBall (R : ℝ) :
    MeasureTheory.Integrable ((Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ))) volume := by
  rw [integrable_indicator_iff measurableSet_closedBall]
  exact MeasureTheory.IntegrableOn.of_bound (isCompact_closedBall (0 : ℝ³) R).measure_lt_top
    aestronglyMeasurable_const 1 (Filter.Eventually.of_forall (fun x => by simp))

/-- The autocorrelation `bsAc ψ` is strongly measurable (it is an integral in the parameter of a
jointly continuous integrand). -/
lemma stronglyMeasurable_bsAc {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) : StronglyMeasurable (bsAc ψ) := by
  have hcont : Continuous (fun z : ℝ³ × ℝ³ => ψ z.2 * ψ (z.2 + z.1)) :=
    (hψ.comp continuous_snd).mul (hψ.comp (continuous_snd.add continuous_fst))
  show StronglyMeasurable (fun d : ℝ³ => ∫ x : ℝ³, ψ x * ψ (x + d))
  exact StronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ³))
    (f := fun d x : ℝ³ => ψ x * ψ (x + d)) hcont.stronglyMeasurable

/-- `bsKern` in terms of the `(p,v)`-factor `bsLf` of `OneBodyKin/CrossDefs`. -/
lemma bsKern_eq_bsLf (ℓ : ℝ) (F : ℝ → ℝ) (d : ℝ³) :
    bsKern ℓ F d = ∫ s in acube 1, ∫ p : ℝ³, bsLf ℓ F p (s + ℓ⁻¹ • d) := by
  rw [bsKern_def]
  refine setIntegral_congr_fun (acube_measurable 1) (fun s _ => ?_)
  apply integral_congr_ae
  filter_upwards with p
  simp only [bsLf]
  ring

/-- The cross-kernel integrand with the box indicator inserted explicitly, so that every bound
below is valid on the whole space. -/
private noncomputable def bsG3 (ℓ : ℝ) (F : ℝ → ℝ) (ψ : ℝ³ → ℝ) (p s d : ℝ³) : ℝ :=
  (acube 1).indicator (fun _ => (1 : ℝ)) s * (bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d)

private lemma bsG3_of_mem {ℓ : ℝ} {F : ℝ → ℝ} {ψ : ℝ³ → ℝ} {p s d : ℝ³} (hs : s ∈ acube 1) :
    bsG3 ℓ F ψ p s d = bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d := by
  rw [bsG3, Set.indicator_of_mem hs, one_mul]

private lemma bsG3_of_notMem {ℓ : ℝ} {F : ℝ → ℝ} {ψ : ℝ³ → ℝ} {p s d : ℝ³} (hs : s ∉ acube 1) :
    bsG3 ℓ F ψ p s d = 0 := by
  rw [bsG3, Set.indicator_of_notMem hs, zero_mul]

/-! ## 3. Step 0: the cosine form of the cross term -/

/-- The cross term in the cosine form `bsLf`: this is `bsMean_eq_boxMean` together with
`bsPair_eq_cos`, pointwise in `u`. -/
lemma bsCross_step0 {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ u : ℝ³, Work.BSKinetic.bsMean ℓ u ψ * bsPair ℓ F u ψ)
      = ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 6 *
        ∫ u : ℝ³, bsMf ℓ ψ u * (∫ p : ℝ³, ∫ v : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u))) := by
  have hpt : ∀ u : ℝ³, Work.BSKinetic.bsMean ℓ u ψ * bsPair ℓ F u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 6 *
        (bsMf ℓ ψ u * (∫ p : ℝ³, ∫ v : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u)))) := by
    intro u
    have hinner : (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
          (∫ v : ℝ³, chi v * ψ (ℓ • (v + u)) * Real.cos (inner ℝ (ℓ • p) v)))
        = ∫ p : ℝ³, ∫ v : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u)) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      simp only [bsLf]
      ring
    rw [bsMf_eq_bsMean (ℓ := ℓ) hℓ ψ u, bsPair_eq_cos hℓ hFi ψ hψ hcs u, hinner]
    ring
  calc (∫ u : ℝ³, Work.BSKinetic.bsMean ℓ u ψ * bsPair ℓ F u ψ)
      = ∫ u : ℝ³, ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 6 *
          (bsMf ℓ ψ u * (∫ p : ℝ³, ∫ v : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u)))) := by
        apply integral_congr_ae
        filter_upwards with u
        exact hpt u
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 6 *
        ∫ u : ℝ³, bsMf ℓ ψ u * (∫ p : ℝ³, ∫ v : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u))) := by
        rw [MeasureTheory.integral_const_mul]

/-! ## 4. The middle exchange -/

/-- **The middle step**: after the substitutions of `Cross/bsCross_subst` the four-fold integral
`∫_p ∫_{s∈acube1} ∫_d bsLf ℓ F p (s + ℓ⁻¹d) · bsAc ψ d` is the quadratic form
`∫_d bsKern ℓ F d · bsAc ψ d` of the cross kernel.  The box indicator is inserted explicitly
(`bsG3`) so that the kernel integrand is compactly supported; the three integrals are then freely
reordered (`integral_prod`, `integral_prod_symm`, `integral_integral_swap`), and the inner
bracket is `bsKern ℓ F d` (`bsKern_eq_bsLf`). -/
lemma bsCross_mid {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ p : ℝ³, ∫ s in acube 1, ∫ d : ℝ³, bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d)
      = ∫ d : ℝ³, bsKern ℓ F d * bsAc ψ d := by
  classical
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_of_contDiff_hasCompactSupport hψ hcs
  obtain ⟨R, hR0, hR⟩ := exists_radius_eq_zero_of_hasCompactSupport hcs
  have hAc : StronglyMeasurable (bsAc ψ) := stronglyMeasurable_bsAc hψ.continuous
  have hAcbd : ∀ d : ℝ³, |bsAc ψ d| ≤ Cψ ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R) :=
    fun d => abs_bsAc_le hCψ hR d
  set Cb : ℝ := Cψ ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R) with hCb
  have hCb0 : 0 ≤ Cb := by
    rw [hCb]; linarith [abs_bsAc_le hCψ hR (0 : ℝ³), abs_nonneg (bsAc ψ 0)]
  set K : ℝ := (∫ z : ℝ³, |chi z|) * ((Real.sqrt chiNormSq)⁻¹ * Cb) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (integral_nonneg (fun z => abs_nonneg _))
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hCb0)
  have hCint : 0 ≤ ∫ z : ℝ³, |chi z| := integral_nonneg (fun z => abs_nonneg _)
  have hsqrt0 : 0 ≤ (Real.sqrt chiNormSq)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  -- pointwise domination
  have hbound : ∀ p s d : ℝ³, ‖bsG3 ℓ F ψ p s d‖ ≤
      ((‖F ‖p‖‖ * K) * (acube 1).indicator (fun _ => (1 : ℝ)) s) *
        (Metric.closedBall (0 : ℝ³) (ℓ * (3 / 2))).indicator (fun _ => (1 : ℝ)) d := by
    intro p s d
    by_cases hs : s ∈ acube 1
    · by_cases hd : d ∈ Metric.closedBall (0 : ℝ³) (ℓ * (3 / 2))
      · rw [bsG3_of_mem hs, Set.indicator_of_mem hs, Set.indicator_of_mem hd, mul_one, mul_one]
        have hL : |bsLf ℓ F p (s + ℓ⁻¹ • d)| ≤
            ‖F ‖p‖‖ * ((∫ z : ℝ³, |chi z|) * (Real.sqrt chiNormSq)⁻¹) := by
          calc |bsLf ℓ F p (s + ℓ⁻¹ • d)|
              ≤ (∫ z : ℝ³, |chi z|) * |F ‖p‖| * |chi (s + ℓ⁻¹ • d)| := abs_bsLf_le _ _ _ _
            _ ≤ (∫ z : ℝ³, |chi z|) * |F ‖p‖| * (Real.sqrt chiNormSq)⁻¹ := by
                refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCint (abs_nonneg _))
                rw [abs_of_nonneg (chi_nonneg _)]
                exact chi_le_sqrt_inv _
            _ = ‖F ‖p‖‖ * ((∫ z : ℝ³, |chi z|) * (Real.sqrt chiNormSq)⁻¹) := by
                rw [Real.norm_eq_abs]; ring
        calc ‖bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d‖
            = |bsLf ℓ F p (s + ℓ⁻¹ • d)| * |bsAc ψ d| := by rw [Real.norm_eq_abs, abs_mul]
          _ ≤ (‖F ‖p‖‖ * ((∫ z : ℝ³, |chi z|) * (Real.sqrt chiNormSq)⁻¹)) * Cb :=
              mul_le_mul hL (hAcbd d) (abs_nonneg _)
                (mul_nonneg (norm_nonneg _) (mul_nonneg hCint hsqrt0))
          _ = ‖F ‖p‖‖ * K := by rw [hK]; ring
      · rw [bsG3_of_mem hs, Set.indicator_of_mem hs, Set.indicator_of_notMem hd, mul_one, mul_zero]
        have hd' : ℓ * (3 / 2) < ‖d‖ := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hd
          exact hd
        have hz : bsLf ℓ F p (s + ℓ⁻¹ • d) = 0 := by
          rw [bsLf, chi_slab_eq_zero hℓ hd' hs, mul_zero, zero_mul]
        rw [hz, zero_mul, norm_zero]
    · rw [bsG3_of_notMem hs, Set.indicator_of_notMem hs, mul_zero, zero_mul, norm_zero]
  -- integrability of the components of the dominator
  have hAint : MeasureTheory.Integrable (fun p : ℝ³ => ‖F ‖p‖‖ * K) volume := hFi.norm.mul_const K
  have hBint : MeasureTheory.Integrable ((acube 1).indicator (fun _ => (1 : ℝ))) volume :=
    integrable_indicator_acube_one
  have hDint : MeasureTheory.Integrable ((Metric.closedBall (0 : ℝ³) (ℓ * (3 / 2))).indicator (fun _ => (1 : ℝ))) volume :=
    integrable_indicator_closedBall _
  have hBmeas : Measurable ((acube 1).indicator (fun _ => (1 : ℝ)) : ℝ³ → ℝ) :=
    Measurable.indicator measurable_const (acube_measurable 1)
  -- continuity of the `(p,s,d)`-part of the integrand
  have hcontG : Continuous (fun w : (ℝ³ × ℝ³) × ℝ³ =>
      profHat (ℓ • w.1.1) * chi (w.1.2 + ℓ⁻¹ • w.2) *
        Real.cos (inner ℝ (ℓ • w.1.1) (w.1.2 + ℓ⁻¹ • w.2))) := by
    have h1 : Continuous (fun w : (ℝ³ × ℝ³) × ℝ³ => (ℓ • w.1.1 : ℝ³)) := continuous_fst.fst.const_smul ℓ
    have h2 : Continuous (fun w : (ℝ³ × ℝ³) × ℝ³ => (w.1.2 + ℓ⁻¹ • w.2 : ℝ³)) :=
      continuous_fst.snd.add (continuous_snd.const_smul ℓ⁻¹)
    have h3 : Continuous (fun w : (ℝ³ × ℝ³) × ℝ³ => inner ℝ (ℓ • w.1.1) (w.1.2 + ℓ⁻¹ • w.2)) :=
      Continuous.inner h1 h2
    exact ((continuous_profHat.comp h1).mul (chi_continuous.comp h2)).mul (Real.continuous_cos.comp h3)
  -- joint integrability on `((p,s),d)`
  have hH : MeasureTheory.Integrable (fun w : (ℝ³ × ℝ³) × ℝ³ => bsG3 ℓ F ψ w.1.1 w.1.2 w.2)
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod (volume : Measure ℝ³)) := by
    have hdom : MeasureTheory.Integrable (fun w : (ℝ³ × ℝ³) × ℝ³ =>
        ((‖F ‖w.1.1‖‖ * K) * (acube 1).indicator (fun _ => (1 : ℝ)) w.1.2) *
          (Metric.closedBall (0 : ℝ³) (ℓ * (3 / 2))).indicator (fun _ => (1 : ℝ)) w.2)
        (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod (volume : Measure ℝ³)) :=
      (hAint.mul_prod hBint).mul_prod hDint
    refine hdom.mono' ?_ (Filter.Eventually.of_forall (fun w => hbound w.1.1 w.1.2 w.2))
    have hfac : (fun w : (ℝ³ × ℝ³) × ℝ³ => bsG3 ℓ F ψ w.1.1 w.1.2 w.2)
        = fun w : (ℝ³ × ℝ³) × ℝ³ => (acube 1).indicator (fun _ => (1 : ℝ)) w.1.2 *
            (F ‖w.1.1‖ * (profHat (ℓ • w.1.1) * chi (w.1.2 + ℓ⁻¹ • w.2) *
              Real.cos (inner ℝ (ℓ • w.1.1) (w.1.2 + ℓ⁻¹ • w.2))) * bsAc ψ w.2) := by
      funext w
      rw [bsG3]
      simp only [bsLf]
      ring
    rw [hfac]
    have hF : AEStronglyMeasurable (fun w : (ℝ³ × ℝ³) × ℝ³ => F ‖w.1.1‖)
        (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod (volume : Measure ℝ³)) :=
      ((hFi.aemeasurable.comp_fst (ν := (volume : Measure ℝ³))).comp_fst).aestronglyMeasurable
    have hAc' : AEStronglyMeasurable (fun w : (ℝ³ × ℝ³) × ℝ³ => bsAc ψ w.2)
        (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod (volume : Measure ℝ³)) :=
      (hAc.comp_measurable continuous_snd.measurable).aestronglyMeasurable
    refine AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_ ?_)
    · exact (hBmeas.comp continuous_fst.snd.measurable).aestronglyMeasurable
    · exact hF.mul hcontG.aestronglyMeasurable
    · exact hAc'
  -- the `(p,s)`-marginal (free from the joint integrability)
  have hPSmarg : MeasureTheory.Integrable (fun z : ℝ³ × ℝ³ => ∫ d : ℝ³, bsG3 ℓ F ψ z.1 z.2 d)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    MeasureTheory.Integrable.integral_prod_left hH
  -- the `(p,s)`-slices at fixed `d`
  have hslice : ∀ d : ℝ³, MeasureTheory.Integrable (fun z : ℝ³ × ℝ³ => bsG3 ℓ F ψ z.1 z.2 d)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    intro d
    have hd1 : MeasureTheory.Integrable (fun p : ℝ³ => ‖F ‖p‖‖ *
        (K * (Metric.closedBall (0 : ℝ³) (ℓ * (3 / 2))).indicator (fun _ => (1 : ℝ)) d)) volume :=
      hFi.norm.mul_const _
    refine (hd1.mul_prod hBint).mono' ?_ ?_
    · have hfac : (fun z : ℝ³ × ℝ³ => bsG3 ℓ F ψ z.1 z.2 d)
          = fun z : ℝ³ × ℝ³ => (acube 1).indicator (fun _ => (1 : ℝ)) z.2 *
              ((F ‖z.1‖ * (profHat (ℓ • z.1) * chi (z.2 + ℓ⁻¹ • d) *
                Real.cos (inner ℝ (ℓ • z.1) (z.2 + ℓ⁻¹ • d)))) * bsAc ψ d) := by
        funext z
        rw [bsG3]
        simp only [bsLf]
        ring
      rw [hfac]
      have hF : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => F ‖z.1‖)
          ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
        (hFi.aemeasurable.comp_fst (ν := (volume : Measure ℝ³))).aestronglyMeasurable
      have h3 : Continuous (fun z : ℝ³ × ℝ³ => profHat (ℓ • z.1) * chi (z.2 + ℓ⁻¹ • d) *
            Real.cos (inner ℝ (ℓ • z.1) (z.2 + ℓ⁻¹ • d))) := by
        have h1 : Continuous (fun z : ℝ³ × ℝ³ => (ℓ • z.1 : ℝ³)) := continuous_fst.const_smul ℓ
        have h2 : Continuous (fun z : ℝ³ × ℝ³ => (z.2 + ℓ⁻¹ • d : ℝ³)) :=
          continuous_snd.add continuous_const
        have h4 : Continuous (fun z : ℝ³ × ℝ³ => inner ℝ (ℓ • z.1) (z.2 + ℓ⁻¹ • d)) :=
          Continuous.inner h1 h2
        exact ((continuous_profHat.comp h1).mul (chi_continuous.comp h2)).mul (Real.continuous_cos.comp h4)
      refine AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_ ?_)
      · exact (hBmeas.comp continuous_snd.measurable).aestronglyMeasurable
      · exact hF.mul h3.aestronglyMeasurable
      · exact aestronglyMeasurable_const
    · filter_upwards with z
      calc ‖bsG3 ℓ F ψ z.1 z.2 d‖
          ≤ ((‖F ‖z.1‖‖ * K) * (acube 1).indicator (fun _ => (1 : ℝ)) z.2) *
              (Metric.closedBall (0 : ℝ³) (ℓ * (3 / 2))).indicator (fun _ => (1 : ℝ)) d :=
            hbound z.1 z.2 d
        _ = ‖F ‖z.1‖‖ * (K * (Metric.closedBall (0 : ℝ³) (ℓ * (3 / 2))).indicator (fun _ => (1 : ℝ)) d) *
              (acube 1).indicator (fun _ => (1 : ℝ)) z.2 := by ring
  -- the chain of exchanges
  have hstep1 : (∫ p : ℝ³, ∫ s in acube 1, ∫ d : ℝ³, bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d)
      = ∫ p : ℝ³, ∫ s : ℝ³, ∫ d : ℝ³, bsG3 ℓ F ψ p s d := by
    apply integral_congr_ae
    filter_upwards with p
    rw [← integral_indicator (acube_measurable 1)]
    apply integral_congr_ae
    filter_upwards with s
    by_cases hs : s ∈ acube 1
    · rw [Set.indicator_of_mem hs]
      apply integral_congr_ae
      filter_upwards with d
      rw [bsG3_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      rw [show (∫ d : ℝ³, bsG3 ℓ F ψ p s d) = 0 from by
        rw [show (fun d : ℝ³ => bsG3 ℓ F ψ p s d) = fun _ => (0 : ℝ) from by
          funext d; exact bsG3_of_notMem hs]
        simp]
  have hstep2 : (∫ p : ℝ³, ∫ s : ℝ³, ∫ d : ℝ³, bsG3 ℓ F ψ p s d)
      = ∫ w : (ℝ³ × ℝ³) × ℝ³, bsG3 ℓ F ψ w.1.1 w.1.2 w.2 :=
    (MeasureTheory.integral_prod (fun z : ℝ³ × ℝ³ => ∫ d : ℝ³, bsG3 ℓ F ψ z.1 z.2 d)
        hPSmarg).symm.trans
      (MeasureTheory.integral_prod (fun w : (ℝ³ × ℝ³) × ℝ³ => bsG3 ℓ F ψ w.1.1 w.1.2 w.2)
        hH).symm
  have hstep3 : (∫ w : (ℝ³ × ℝ³) × ℝ³, bsG3 ℓ F ψ w.1.1 w.1.2 w.2)
      = ∫ d : ℝ³, ∫ z : ℝ³ × ℝ³, bsG3 ℓ F ψ z.1 z.2 d :=
    MeasureTheory.integral_prod_symm (fun w : (ℝ³ × ℝ³) × ℝ³ => bsG3 ℓ F ψ w.1.1 w.1.2 w.2) hH
  have hstep4 : (∫ d : ℝ³, ∫ z : ℝ³ × ℝ³, bsG3 ℓ F ψ z.1 z.2 d)
      = ∫ d : ℝ³, ∫ s : ℝ³, ∫ p : ℝ³, bsG3 ℓ F ψ p s d := by
    apply integral_congr_ae
    filter_upwards with d
    exact (MeasureTheory.integral_prod (fun z : ℝ³ × ℝ³ => bsG3 ℓ F ψ z.1 z.2 d) (hslice d)).trans
      (MeasureTheory.integral_integral_swap (f := fun p s : ℝ³ => bsG3 ℓ F ψ p s d) (hslice d))
  have hstep5 : (∫ d : ℝ³, ∫ s : ℝ³, ∫ p : ℝ³, bsG3 ℓ F ψ p s d)
      = ∫ d : ℝ³, ∫ s in acube 1, ∫ p : ℝ³, bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d := by
    apply integral_congr_ae
    filter_upwards with d
    rw [← integral_indicator (acube_measurable 1)]
    apply integral_congr_ae
    filter_upwards with s
    by_cases hs : s ∈ acube 1
    · rw [Set.indicator_of_mem hs]
      apply integral_congr_ae
      filter_upwards with p
      rw [bsG3_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      rw [show (∫ p : ℝ³, bsG3 ℓ F ψ p s d) = 0 from by
        rw [show (fun p : ℝ³ => bsG3 ℓ F ψ p s d) = fun _ => (0 : ℝ) from by
          funext p; exact bsG3_of_notMem hs]
        simp]
  have hstep6 : (∫ d : ℝ³, ∫ s in acube 1, ∫ p : ℝ³, bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d)
      = ∫ d : ℝ³, bsKern ℓ F d * bsAc ψ d := by
    apply integral_congr_ae
    filter_upwards with d
    simp only [MeasureTheory.integral_mul_const]
    rw [bsKern_eq_bsLf]
  exact hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans (hstep5.trans hstep6))))

/-! ## 5. The right-hand side -/

/-- The right-hand side `∫_x ∫_y bsKern ℓ F (x−y) ψ x ψ y` in the autocorrelation form
`∫_d bsKern ℓ F d · bsAc ψ d`: substitute `y = x + d`, exchange, and use the parity of the
kernel. -/
lemma bsCross_rhs {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ x : ℝ³, ∫ y : ℝ³, bsKern ℓ F (x - y) * ψ x * ψ y)
      = ∫ d : ℝ³, bsKern ℓ F d * bsAc ψ d := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_of_contDiff_hasCompactSupport hψ hcs
  obtain ⟨R, hR0, hR⟩ := exists_radius_eq_zero_of_hasCompactSupport hcs
  have hKern : MeasureTheory.Integrable (bsKern ℓ F) := integrable_bsKern hℓ hFi
  have hψc : Continuous ψ := hψ.continuous
  have hstep1 : (∫ x : ℝ³, ∫ y : ℝ³, bsKern ℓ F (x - y) * ψ x * ψ y)
      = ∫ x : ℝ³, ∫ d : ℝ³, bsKern ℓ F (-d) * ψ x * ψ (x + d) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [← MeasureTheory.integral_add_right_eq_self
      (f := fun y : ℝ³ => bsKern ℓ F (x - y) * ψ x * ψ y) x]
    apply integral_congr_ae
    filter_upwards with d
    have h1 : x - (d + x) = -d := by abel
    rw [h1, add_comm d x]
  have hjoint : MeasureTheory.Integrable
      (Function.uncurry (fun x d : ℝ³ => bsKern ℓ F (-d) * ψ x * ψ (x + d)))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    have h2 : MeasureTheory.Integrable (fun x : ℝ³ =>
        Cψ ^ 2 * (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) x) volume :=
      (integrable_indicator_closedBall R).const_mul _
    refine (h2.mul_prod hKern.norm).mono' ?_ (Filter.Eventually.of_forall (fun z => ?_))
    · have h1 : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => bsKern ℓ F (-z.2))
          ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
        refine (AEMeasurable.comp_snd (ν := (volume : Measure ℝ³)) hKern.aemeasurable).aestronglyMeasurable.congr ?_
        filter_upwards with z
        rw [bsKern_even]
      have h3 : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => ψ z.1)
          ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
        (hψc.comp continuous_fst).aestronglyMeasurable
      have h4 : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => ψ (z.1 + z.2))
          ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
        (hψc.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
      exact (h1.mul h3).mul h4
    · have hz0 : Function.uncurry (fun x d : ℝ³ => bsKern ℓ F (-d) * ψ x * ψ (x + d)) z
          = bsKern ℓ F (-z.2) * ψ z.1 * ψ (z.1 + z.2) := rfl
      show ‖bsKern ℓ F (-z.2) * ψ z.1 * ψ (z.1 + z.2)‖ ≤
          Cψ ^ 2 * (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) z.1 * ‖bsKern ℓ F z.2‖
      rw [Real.norm_eq_abs]
      by_cases hz : z.1 ∈ Metric.closedBall (0 : ℝ³) R
      · rw [Set.indicator_of_mem hz, mul_one]
        have hker : |bsKern ℓ F (-z.2)| ≤ ‖bsKern ℓ F z.2‖ := by
          rw [bsKern_even, Real.norm_eq_abs]
        have hprod : |bsKern ℓ F (-z.2) * ψ z.1 * ψ (z.1 + z.2)| ≤ ‖bsKern ℓ F z.2‖ * Cψ ^ 2 := by
          rw [abs_mul, abs_mul]
          calc |bsKern ℓ F (-z.2)| * |ψ z.1| * |ψ (z.1 + z.2)|
              ≤ ‖bsKern ℓ F z.2‖ * Cψ * Cψ := by
                refine mul_le_mul (mul_le_mul hker (hCψ z.1) (abs_nonneg _) (norm_nonneg _))
                  (hCψ _) (abs_nonneg _) (by positivity)
            _ = ‖bsKern ℓ F z.2‖ * Cψ ^ 2 := by ring
        calc |bsKern ℓ F (-z.2) * ψ z.1 * ψ (z.1 + z.2)| ≤ ‖bsKern ℓ F z.2‖ * Cψ ^ 2 := hprod
          _ = Cψ ^ 2 * ‖bsKern ℓ F z.2‖ := by ring
      · rw [Set.indicator_of_notMem hz, mul_zero]
        have hz' : R ≤ ‖z.1‖ := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hz
          exact le_of_lt hz
        rw [hR z.1 hz']
        simp
  have hstep2 : (∫ x : ℝ³, ∫ d : ℝ³, bsKern ℓ F (-d) * ψ x * ψ (x + d))
      = ∫ d : ℝ³, ∫ x : ℝ³, bsKern ℓ F (-d) * ψ x * ψ (x + d) :=
    MeasureTheory.integral_integral_swap
      (f := fun x d : ℝ³ => bsKern ℓ F (-d) * ψ x * ψ (x + d)) hjoint
  have hstep3 : ∀ d : ℝ³, (∫ x : ℝ³, bsKern ℓ F (-d) * ψ x * ψ (x + d))
      = bsKern ℓ F d * bsAc ψ d := by
    intro d
    rw [bsKern_even ℓ F d, bsAc]
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  refine hstep1.trans (hstep2.trans ?_)
  apply integral_congr_ae
  filter_upwards with d
  exact hstep3 d

/-! ## 6. Assembly -/

theorem bsMean_bsPair_eq_kernelForm {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsMean ℓ u ψ * Work.OneBodyKin.bsPair ℓ F u ψ)
      = ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.bsKern ℓ F (x - y) * ψ x * ψ y := by
  have h1 : (∫ u : ℝ³, bsMf ℓ ψ u * (∫ p : ℝ³, ∫ v : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u))))
      = ∫ p : ℝ³, ∫ v : ℝ³, ∫ s in acube 1, ∫ u : ℝ³,
          bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)) :=
    Cross.bsCross_expand_mean hℓ hFi hψ hcs
  have h2 : (∫ p : ℝ³, ∫ v : ℝ³, ∫ s in acube 1, ∫ u : ℝ³,
          bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
      = (ℓ ^ 6)⁻¹ * ∫ p : ℝ³, ∫ s in acube 1, ∫ d : ℝ³,
          bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d :=
    Cross.bsCross_subst hℓ hψ hcs
  have h4 := bsCross_rhs hℓ hFi hψ hcs
  have h6 : ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 6 * ((ℓ ^ 6)⁻¹ *
      ∫ p : ℝ³, ∫ s in acube 1, ∫ d : ℝ³, bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ d : ℝ³, bsKern ℓ F d * bsAc ψ d) := by
    rw [bsCross_mid hℓ hFi hψ hcs]
    field_simp
  rw [bsCross_step0 hℓ hFi hψ hcs, h1, h2, h6, ← h4]

end Work.OneBodyKin
