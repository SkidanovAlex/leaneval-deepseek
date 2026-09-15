import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.MeasureTheory.Integral.exists_approximate_identity_complex

open MeasureTheory Metric Filter Function
open scoped Topology ENNReal Convolution

namespace Commons.MeasureTheory.Integral

noncomputable section

/-- The basic smooth bump function on `Fin d → ℂ` supported in the closed unit ball. -/
private def bump (d : ℕ) : ContDiffBump (0 : Fin d → ℂ) :=
  { rIn := 1 / 2, rOut := 1, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

/-- The bump as a plain function. -/
private def phi (d : ℕ) : (Fin d → ℂ) → ℝ := bump d

/-- Normalization constant: the total mass of `phi`. -/
private def A (d : ℕ) : ℝ := ∫ s : Fin d → ℂ, phi d s

/-- The scaling factor `n + 1`. -/
private def b (n : ℕ) : ℝ := (n : ℝ) + 1

private lemma b_pos (n : ℕ) : 0 < b n := by unfold b; positivity

private lemma b_nonneg (n : ℕ) : 0 ≤ b n := (b_pos n).le

private lemma b_ne_zero (n : ℕ) : b n ≠ 0 := (b_pos n).ne'

private lemma phi_nonneg (d : ℕ) (s : Fin d → ℂ) : 0 ≤ phi d s := (bump d).nonneg

private lemma phi_le_one (d : ℕ) (s : Fin d → ℂ) : phi d s ≤ 1 := (bump d).le_one

private lemma phi_contDiff (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (phi d) := (bump d).contDiff

private lemma phi_hasCompactSupport (d : ℕ) : HasCompactSupport (phi d) := (bump d).hasCompactSupport

private lemma phi_zero (d : ℕ) : phi d 0 = 1 :=
  (bump d).one_of_mem_closedBall (mem_closedBall_self (bump d).rIn_pos.le)

private lemma phi_support_subset (d : ℕ) : Function.support (phi d) ⊆ Metric.closedBall 0 1 := by
  intro s hs
  rw [Function.mem_support] at hs
  have hs' : s ∈ Function.support (bump d) := hs
  rw [(bump d).support_eq] at hs'
  exact Metric.ball_subset_closedBall hs'

private lemma phi_integrable (d : ℕ) : Integrable (phi d) volume :=
  (phi_contDiff d).continuous.integrable_of_hasCompactSupport (phi_hasCompactSupport d)

private lemma A_pos (d : ℕ) : 0 < A d := by
  rw [A]
  exact integral_pos_of_integrable_nonneg_nonzero (phi_contDiff d).continuous (phi_integrable d)
    (fun s => phi_nonneg d s) (x := 0) (by rw [phi_zero d]; norm_num)

/-- The approximate identity sequence. -/
private def cK (d : ℕ) (n : ℕ) : (Fin d → ℂ) → ℝ :=
  fun s => (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d * phi d (b n • s)

private lemma cK_nonneg (d n : ℕ) (s : Fin d → ℂ) : 0 ≤ cK d n s := by
  simp only [cK]
  exact mul_nonneg (div_nonneg (pow_nonneg (b_nonneg n) _) (A_pos d).le) (phi_nonneg d _)

private lemma cK_le (d n : ℕ) (s : Fin d → ℂ) : cK d n s ≤ (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d := by
  simp only [cK]
  have h : 0 ≤ (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d := div_nonneg (pow_nonneg (b_nonneg n) _) (A_pos d).le
  calc (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d * phi d (b n • s) ≤ (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d * 1 :=
        mul_le_mul_of_nonneg_left (phi_le_one d _) h
    _ = (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d := mul_one _

private lemma cK_contDiff (d n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cK d n) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun s : Fin d → ℂ => (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d * phi d (b n • s))
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun s : Fin d → ℂ => b n • s) :=
    (contDiff_const (c := b n) (n := (⊤ : ℕ∞))).smul contDiff_id
  have hphi : ContDiff ℝ (⊤ : ℕ∞) (fun s : Fin d → ℂ => phi d (b n • s)) :=
    (phi_contDiff d).comp hscale
  have h2 := hphi.const_smul ((b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d)
  simpa only [smul_eq_mul] using h2

private lemma cK_support_subset (d n : ℕ) :
    Function.support (cK d n) ⊆ Metric.closedBall 0 (1 / (n + 1)) := by
  intro s hs
  rw [Function.mem_support] at hs
  have hphi : phi d (b n • s) ≠ 0 := by
    intro hc
    apply hs
    change (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d * phi d (b n • s) = 0
    rw [hc, mul_zero]
  have hsupp := phi_support_subset d (Function.mem_support.mpr hphi)
  rw [Metric.mem_closedBall, dist_zero_right] at hsupp ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (b_pos n)] at hsupp
  have hb : (1 : ℝ) / (n + 1) = (b n)⁻¹ := by simp only [b, one_div]
  have key : ‖s‖ ≤ (b n)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (b_pos n)]
    simpa [mul_comm] using hsupp
  rwa [hb]

private lemma cK_hasCompactSupport (d n : ℕ) : HasCompactSupport (cK d n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℂ) (1 / (n + 1))) ?_
  intro s hs
  by_contra h
  exact hs (cK_support_subset d n (Function.mem_support.mpr h))

private lemma integral_comp_smul_phi (d n : ℕ) :
    ∫ s : Fin d → ℂ, phi d (b n • s) = ((b n) ^ (Module.finrank ℝ (Fin d → ℂ)))⁻¹ * A d := by
  rw [Measure.integral_comp_smul_of_nonneg (μ := volume) (f := phi d) (R := b n)
    (hR := b_nonneg n), smul_eq_mul, A]

private lemma cK_integral (d n : ℕ) : ∫ s, cK d n s = 1 := by
  simp only [cK]
  rw [MeasureTheory.integral_const_mul, integral_comp_smul_phi]
  have hA : A d ≠ 0 := (A_pos d).ne'
  have hb : b n ≠ 0 := b_ne_zero n
  field_simp

/-- Pointwise bound: if `K` is nonnegative, bounded by `C`, supported in the closed ball of
radius `r`, and `g` is locally integrable, then the convolution integral `∫ t, K (z - t) • g t`
is at most `C` times the integral of `‖g‖` over the ball of radius `r` around `z`. -/
private lemma norm_integral_smul_lsmul_le {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (K : (Fin d → ℂ) → ℝ) (g : (Fin d → ℂ) → F)
    (z : Fin d → ℂ) {C r : ℝ}
    (hK0 : ∀ s, 0 ≤ K s) (hKb : ∀ s, K s ≤ C)
    (hKs : ∀ s, K s ≠ 0 → s ∈ Metric.closedBall 0 r)
    (hg : LocallyIntegrable g (volume : Measure (Fin d → ℂ))) :
    ‖∫ t, K (z - t) • g t‖ ≤ C * ∫ t in Metric.closedBall z r, ‖g t‖ := by
  have hmem : ∀ t : Fin d → ℂ, (z - t ∈ Metric.closedBall 0 r) ↔ (t ∈ Metric.closedBall z r) := by
    intro t
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_sub_rev t z]
  have hint : Integrable (fun t : Fin d → ℂ =>
      C * (Metric.closedBall z r).indicator (fun t => ‖g t‖) t) volume := by
    have hgi : IntegrableOn (fun t : Fin d → ℂ => ‖g t‖) (Metric.closedBall z r) volume :=
      (hg.integrableOn_isCompact (isCompact_closedBall z r)).norm
    have h1 : Integrable ((Metric.closedBall z r).indicator (fun t : Fin d → ℂ => ‖g t‖)) volume :=
      (integrable_indicator_iff measurableSet_closedBall).2 hgi
    exact h1.const_mul C
  calc ‖∫ t, K (z - t) • g t‖
      ≤ ∫ t, ‖K (z - t) • g t‖ := norm_integral_le_integral_norm _
    _ = ∫ t, K (z - t) * ‖g t‖ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [norm_smul, Real.norm_of_nonneg (hK0 (z - t))]
    _ ≤ ∫ t, C * (Metric.closedBall z r).indicator (fun t => ‖g t‖) t := by
        apply integral_mono_of_nonneg
        · filter_upwards with t
          exact mul_nonneg (hK0 (z - t)) (norm_nonneg _)
        · exact hint
        · filter_upwards with t
          by_cases ht : t ∈ Metric.closedBall z r
          · rw [Set.indicator_of_mem ht]
            exact mul_le_mul_of_nonneg_right (hKb (z - t)) (norm_nonneg _)
          · have hzt : z - t ∉ Metric.closedBall 0 r := fun hc => ht ((hmem t).mp hc)
            have hz0 : K (z - t) = 0 := by
              by_contra h; exact hzt (hKs (z - t) h)
            rw [Set.indicator_of_notMem ht, mul_zero, hz0, zero_mul]
    _ = C * ∫ t in Metric.closedBall z r, ‖g t‖ := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_indicator measurableSet_closedBall]

/-- Almost everywhere convergence of the approximate identity `cK`: for every locally integrable
`g`, the convolution `∫ s, cK d n s • g (z - s)` tends to `g z` for almost every `z`. -/
private lemma tendsto_integral_cK (d : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (g : (Fin d → ℂ) → F) (hg : LocallyIntegrable g volume) :
    ∀ᵐ z ∂(volume : Measure (Fin d → ℂ)),
      Tendsto (fun n : ℕ => ∫ s, cK d n s • g (z - s)) atTop (nhds (g z)) := by
  have hLD := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := (volume : Measure (Fin d → ℂ))) hg 0
  filter_upwards [hLD] with z hz
  have havg : Tendsto (fun n : ℕ => ⨍ y in Metric.closedBall z (1 / ((n : ℝ) + 1)),
      ‖g y - g z‖) atTop (nhds 0) := by
    have hδlim : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ),
        Eventually.of_forall (fun n => by simp only [Set.mem_Ioi]; positivity)⟩
    have hxmem : ∀ᶠ n : ℕ in atTop,
        z ∈ Metric.closedBall ((fun _ : ℕ => z) n) (0 * ((1 : ℝ) / ((n : ℝ) + 1))) := by simp
    exact hz (fun _ : ℕ => z) (fun n => (1 : ℝ) / ((n : ℝ) + 1)) hδlim hxmem
  have hgsub : LocallyIntegrable (fun t : Fin d → ℂ => g t - g z) volume :=
    hg.sub (locallyIntegrable_const (g z))
  have hbound : ∀ n : ℕ,
      ‖(∫ s, cK d n s • g (z - s)) - g z‖ ≤
        ((volume : Measure (Fin d → ℂ)).real (Metric.ball 0 1) / A d) *
          ⨍ y in Metric.closedBall z (1 / ((n : ℝ) + 1)), ‖g y - g z‖ := by
    intro n
    have hI1 : Integrable (fun t : Fin d → ℂ => cK d n (z - t) • g t) volume := by
      have hprod : Integrable (fun s : Fin d → ℂ => cK d n s • g (z - s)) volume := by
        have hgiOn : IntegrableOn (fun s : Fin d → ℂ => g (z - s))
            (Metric.closedBall 0 (1 / ((n : ℝ) + 1))) volume := by
          have h1 : IntegrableOn g (Metric.closedBall z (1 / ((n : ℝ) + 1))) volume :=
            hg.integrableOn_isCompact (isCompact_closedBall z _)
          have hpre : (fun t : Fin d → ℂ => z - t) ⁻¹'
              Metric.closedBall z (1 / ((n : ℝ) + 1)) =
              Metric.closedBall 0 (1 / ((n : ℝ) + 1)) := by
            ext s
            simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero]
            rw [show z - s - z = -s by abel, norm_neg]
          have h2 := (Measure.measurePreserving_sub_left volume z).integrableOn_comp_preimage
            (MeasurableEquiv.subLeft z).measurableEmbedding (f := g)
            (s := Metric.closedBall z (1 / ((n : ℝ) + 1)))
          rw [hpre] at h2
          exact h2.mpr h1
        have hKc : ContinuousOn (cK d n) (Metric.closedBall 0 (1 / ((n : ℝ) + 1))) :=
          (cK_contDiff d n).continuous.continuousOn
        have hprodOn : IntegrableOn (fun s : Fin d → ℂ => cK d n s • g (z - s))
            (Metric.closedBall 0 (1 / ((n : ℝ) + 1))) volume :=
          IntegrableOn.continuousOn_smul_of_subset hKc hgiOn (isCompact_closedBall 0 _)
            measurableSet_closedBall (le_refl _)
        exact hprodOn.integrable_of_forall_notMem_eq_zero (fun s hs => by
          have hz0 : cK d n s = 0 := by
            by_contra h
            exact hs (cK_support_subset d n (Function.mem_support.mpr h))
          rw [hz0, zero_smul])
      have h := hprod.comp_sub_left z
      simpa only [Function.comp_apply, sub_sub_cancel] using h
    have hI2 : Integrable (fun t : Fin d → ℂ => cK d n (z - t) • g z) volume := by
      have hKi : Integrable (cK d n) volume :=
        (cK_contDiff d n).continuous.integrable_of_hasCompactSupport (cK_hasCompactSupport d n)
      exact (hKi.comp_sub_left z).smul_const (g z)
    have hgz : (∫ t, cK d n (z - t) • g z) = g z := by
      rw [integral_smul_const, integral_sub_left_eq_self (cK d n) volume z, cK_integral d n,
        one_smul]
    have hswap : (∫ s, cK d n s • g (z - s)) = ∫ t, cK d n (z - t) • g t := by
      rw [← convolution_lsmul (μ := volume) (f := cK d n) (g := g) (x := z),
        convolution_lsmul_swap]
    have hlin : (∫ t, cK d n (z - t) • g t) - g z =
        ∫ t, cK d n (z - t) • (g t - g z) := by
      have e1 : (∫ t, cK d n (z - t) • g t) - g z =
          (∫ t, cK d n (z - t) • g t) - ∫ t, cK d n (z - t) • g z := by rw [hgz]
      rw [e1, ← integral_sub hI1 hI2]
      apply integral_congr_ae
      filter_upwards with t
      rw [smul_sub]
    have hbnd : ‖(∫ t, cK d n (z - t) • g t) - g z‖ ≤
        (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d *
          ∫ t in Metric.closedBall z (1 / ((n : ℝ) + 1)), ‖g t - g z‖ := by
      rw [hlin]
      exact norm_integral_smul_lsmul_le (cK d n) (fun t => g t - g z) z
        (cK_nonneg d n) (cK_le d n)
        (fun s hs => cK_support_subset d n (Function.mem_support.mpr hs)) hgsub
    have hvol : (volume : Measure (Fin d → ℂ)).real (Metric.closedBall z (1 / ((n : ℝ) + 1))) =
        (1 / ((n : ℝ) + 1)) ^ (Module.finrank ℝ (Fin d → ℂ)) *
          (volume : Measure (Fin d → ℂ)).real (Metric.ball 0 1) :=
      MeasureTheory.Measure.addHaar_real_closedBall volume z (by positivity)
    have hbr : b n * (1 / ((n : ℝ) + 1)) = 1 := by
      simp only [b]; field_simp
    have hp : (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) *
        (1 / ((n : ℝ) + 1)) ^ (Module.finrank ℝ (Fin d → ℂ)) = 1 := by
      rw [← mul_pow, hbr, one_pow]
    have hVpos : (0 : ℝ) < (volume : Measure (Fin d → ℂ)).real (Metric.ball 0 1) := by
      rw [Measure.real_def]
      exact ENNReal.toReal_pos (measure_ball_pos volume (0 : Fin d → ℂ) one_pos).ne'
        (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
          (isCompact_closedBall (0 : Fin d → ℂ) 1).measure_lt_top).ne
    have hne : (volume : Measure (Fin d → ℂ)).real (Metric.closedBall z (1 / ((n : ℝ) + 1))) ≠ 0 := by
      rw [hvol]
      exact mul_ne_zero (pow_ne_zero _ (by positivity)) hVpos.ne'
    have hAvg : (∫ y in Metric.closedBall z (1 / ((n : ℝ) + 1)), ‖g y - g z‖) =
        (volume : Measure (Fin d → ℂ)).real (Metric.closedBall z (1 / ((n : ℝ) + 1))) *
          ⨍ y in Metric.closedBall z (1 / ((n : ℝ) + 1)), ‖g y - g z‖ := by
      rw [MeasureTheory.setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [hswap]
    have hCvol : (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d *
        (volume : Measure (Fin d → ℂ)).real (Metric.closedBall z (1 / ((n : ℝ) + 1))) =
        (volume : Measure (Fin d → ℂ)).real (Metric.ball 0 1) / A d := by
      rw [hvol, div_mul_eq_mul_div, ← mul_assoc, hp, one_mul]
    calc ‖(∫ t, cK d n (z - t) • g t) - g z‖
        ≤ (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d *
            ∫ t in Metric.closedBall z (1 / ((n : ℝ) + 1)), ‖g t - g z‖ := hbnd
      _ = (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d *
            ((volume : Measure (Fin d → ℂ)).real (Metric.closedBall z (1 / ((n : ℝ) + 1))) *
              ⨍ y in Metric.closedBall z (1 / ((n : ℝ) + 1)), ‖g y - g z‖) := by rw [hAvg]
      _ = (b n) ^ (Module.finrank ℝ (Fin d → ℂ)) / A d *
            (volume : Measure (Fin d → ℂ)).real (Metric.closedBall z (1 / ((n : ℝ) + 1))) *
              ⨍ y in Metric.closedBall z (1 / ((n : ℝ) + 1)), ‖g y - g z‖ := by ring
      _ = ((volume : Measure (Fin d → ℂ)).real (Metric.ball 0 1) / A d) *
              ⨍ y in Metric.closedBall z (1 / ((n : ℝ) + 1)), ‖g y - g z‖ := by rw [hCvol]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
    (Eventually.of_forall hbound) ?_
  have h2 := havg.const_mul ((volume : Measure (Fin d → ℂ)).real (Metric.ball 0 1) / A d)
  simpa using h2

theorem exists_approximate_identity_complex_ae (d : ℕ) :
    ∃ K : ℕ → (Fin d → ℂ) → ℝ,
      (∀ (n : ℕ) (s : Fin d → ℂ), 0 ≤ K n s) ∧
      (∀ n : ℕ, ∫ s : (Fin d → ℂ), K n s = 1) ∧
      (∀ n : ℕ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (K n)) ∧
      (∀ n : ℕ, HasCompactSupport (K n)) ∧
      (∀ n : ℕ, Function.support (K n) ⊆ Metric.closedBall 0 (1 / (n + 1))) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        (g : (Fin d → ℂ) → E),
        MeasureTheory.LocallyIntegrable g MeasureTheory.volume →
        ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)),
          Filter.Tendsto (fun n : ℕ => ∫ s : (Fin d → ℂ), K n s • g (z - s))
            Filter.atTop (nhds (g z))) := by
  refine ⟨cK d, fun n s => cK_nonneg d n s, fun n => cK_integral d n, fun n => ?_,
    fun n => cK_hasCompactSupport d n, fun n => cK_support_subset d n, ?_⟩
  · exact cK_contDiff d n
  · intro E _ _ _ g hg
    exact tendsto_integral_cK d g hg


end

end Commons.MeasureTheory.Integral