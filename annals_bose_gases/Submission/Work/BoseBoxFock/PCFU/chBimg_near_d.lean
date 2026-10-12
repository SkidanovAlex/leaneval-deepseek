import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBogFS.integrable_integral_integral_mul_sub
import Submission.Work.BoseBoxFock.PCFU.chBslotAux
import Submission.Work.BoseBoxFock.PCFU.uvKernel_moment_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.PCFU.chBimg_near_d`

The "near-`d`" lattice image estimate for the `(B)`-slot: with `χ = chiLam ℓ` the box window,
`K = uvKernel fu Λ` the UV-smoothing kernel, `W = W1fun v h ℓ` the smoothed weight and
`v₀ = ℓ • latVec d` (`d ≠ 0`), the flatness hypothesis
`χ z * χ w ≤ Cf (ρ/ℓ)^4` on the aliasing region `‖z - w + v₀‖ ≤ ρ` yields

`χ z * ∫ w, χ w * |uvSmear fu Λ W (z - w + v₀)| ≤ Cf ℓ⁻⁴ (∫ a, (R+‖a‖)^4 ‖K a‖) (∫ x, |W x|)`.

The mechanism ("conditional Mayer bound"): write `uvSmear fu Λ W` as the convolution
`y ↦ ∫ a, K a W (y + a)`, insert the flatness bound *after* the product `χ z χ w` has been
produced (so that the two window factors are consumed together), and integrate.  All the
integrability is supplied by the rapid decay of `uvKernel fu Λ`.
-/

/-! ## Elementary helpers -/

/-- `(ρ/ℓ)^4 = ℓ^(-4) ρ^4`. -/
lemma div_pow_four_eq (ℓ ρ : ℝ) : (ρ / ℓ) ^ 4 = ℓ ^ (-(4 : ℤ)) * ρ ^ 4 := by
  have h : ℓ ^ (-(4 : ℤ)) = (ℓ ^ 4)⁻¹ := zpow_neg ℓ (4 : ℤ)
  rw [h, div_pow, div_eq_inv_mul]

/-- The cancellation `t^4 * t^(-4) = 1` for `t > 0`. -/
lemma pow_four_mul_zpow_neg_four {t : ℝ} (ht : 0 < t) : t ^ 4 * t ^ (-(4 : ℤ)) = 1 := by
  rw [← zpow_natCast t 4, ← zpow_add₀ ht.ne']
  norm_num

/-- The cancellation `t^4 * t^(-8) = t^(-4)` for `t > 0`. -/
lemma pow_four_mul_zpow_neg_eight {t : ℝ} (ht : 0 < t) :
    t ^ 4 * t ^ (-(8 : ℤ)) = t ^ (-(4 : ℤ)) := by
  rw [← zpow_natCast t 4, ← zpow_add₀ ht.ne']
  norm_num

/-- **The convolved form of `uvSmear`**: `uvSmear fu Λ W y = ∫ a, K a * W (y + a)`. -/
lemma uvSmear_eq_integral (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) (W : E3 → ℝ) (y : E3) :
    Work.BoseBoxFock.uvSmear fu Λ W y
      = ∫ a : E3, Work.BoseBoxFock.uvKernel fu Λ a * W (y + a) := by
  rw [Work.BoseBoxFock.uvSmear]
  rw [← MeasureTheory.integral_add_left_eq_self
        (fun t : E3 => Work.BoseBoxFock.uvKernel fu Λ (y - t) * W t) y]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with a
  have h : y - (y + a) = -a := by abel
  rw [h, Work.BoseBoxFock.uvKernel_even]

/-! ## The core estimate -/

/-- **Core estimate.**  For a nonnegative window `χ`, a weight `W` supported in `ball 0 R`, a
kernel `K`, and a family `S` dominated by the convolution with `K`, the flatness hypothesis on
the aliasing region of the window pair gives the lattice-image bound. -/
theorem near_d_core {v0 : E3} {K W χ : E3 → ℝ} {S : E3 → ℝ} {R ℓ Cf : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hCf : 0 ≤ Cf)
    (hχnn : ∀ x : E3, 0 ≤ χ x)
    (hWsupp : ∀ x : E3, W x ≠ 0 → ‖x‖ < R)
    (hWint : Integrable W)
    (hMaj : ∀ c : E3, Integrable (fun a : E3 => (R + ‖a‖) ^ 4 * ‖K a‖ * |W (c + a)|))
    (hKint : Integrable (fun a : E3 => (R + ‖a‖) ^ 4 * ‖K a‖))
    (hflat : ∀ (ρ : ℝ), 0 ≤ ρ → ∀ z w : E3,
        ‖z - w + v0‖ ≤ ρ → χ z * χ w ≤ Cf * (ρ / ℓ) ^ 4)
    (hSabs : ∀ y : E3, |S y| ≤ ∫ a : E3, ‖K a‖ * |W (y + a)|)
    (z : E3) :
    χ z * (∫ w : E3, χ w * |S (z - w + v0)|)
      ≤ Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖K a‖)
          * (∫ x : E3, |W x|) := by
  -- the reflected and translated weight, and the convolution form of the majorant
  have hH : Integrable (fun u : E3 => |W (z + v0 - u)|) :=
    hWint.abs.comp_sub_left (z + v0)
  have hconv := Work.BoseBogFS.integrable_integral_integral_mul_sub hKint hH
  have hint : Integrable (fun w : E3 =>
      (Cf * ℓ ^ (-(4 : ℤ))) * ∫ a : E3, (R + ‖a‖) ^ 4 * ‖K a‖ * |W (z + v0 - (w - a))|) :=
    hconv.1.const_mul _
  -- the pointwise bound
  have hpoint : ∀ w : E3, χ z * (χ w * |S (z - w + v0)|)
      ≤ (Cf * ℓ ^ (-(4 : ℤ))) *
          ∫ a : E3, (R + ‖a‖) ^ 4 * ‖K a‖ * |W (z + v0 - (w - a))| := by
    intro w
    have hptA : ∀ a : E3, χ z * χ w * (‖K a‖ * |W ((z - w + v0) + a)|)
        ≤ (Cf * ℓ ^ (-(4 : ℤ))) * ((R + ‖a‖) ^ 4 * ‖K a‖ * |W ((z - w + v0) + a)|) := by
      intro a
      by_cases hW0 : W ((z - w + v0) + a) = 0
      · rw [hW0, abs_zero]
        simp
      · have hlt : ‖(z - w + v0) + a‖ < R := hWsupp _ hW0
        have hle : ‖z - w + v0‖ ≤ R + ‖a‖ := by
          have h2 : ((z - w + v0) + a) - a = z - w + v0 := by abel
          calc ‖z - w + v0‖ = ‖((z - w + v0) + a) - a‖ := by rw [h2]
            _ ≤ ‖(z - w + v0) + a‖ + ‖a‖ := norm_sub_le _ _
            _ ≤ R + ‖a‖ := by linarith
        have hρ : 0 ≤ R + ‖a‖ := by positivity
        have hfl := hflat (R + ‖a‖) hρ z w hle
        calc χ z * χ w * (‖K a‖ * |W ((z - w + v0) + a)|)
            ≤ (Cf * ((R + ‖a‖) / ℓ) ^ 4) * (‖K a‖ * |W ((z - w + v0) + a)|) :=
              mul_le_mul_of_nonneg_right hfl (by positivity)
          _ = (Cf * ℓ ^ (-(4 : ℤ))) * ((R + ‖a‖) ^ 4 * ‖K a‖ * |W ((z - w + v0) + a)|) := by
              rw [div_pow_four_eq ℓ (R + ‖a‖)]
              ring
    have hInt_eq : (∫ a : E3,
          (Cf * ℓ ^ (-(4 : ℤ))) * ((R + ‖a‖) ^ 4 * ‖K a‖ * |W ((z - w + v0) + a)|))
        = (Cf * ℓ ^ (-(4 : ℤ))) *
            ∫ a : E3, (R + ‖a‖) ^ 4 * ‖K a‖ * |W (z + v0 - (w - a))| := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with a
      rw [show (z - w + v0) + a = z + v0 - (w - a) by abel]
    calc χ z * (χ w * |S (z - w + v0)|)
        = χ z * χ w * |S (z - w + v0)| := by rw [mul_assoc]
      _ ≤ χ z * χ w * ∫ a : E3, ‖K a‖ * |W ((z - w + v0) + a)| :=
          mul_le_mul_of_nonneg_left (hSabs (z - w + v0))
            (mul_nonneg (hχnn z) (hχnn w))
      _ = ∫ a : E3, χ z * χ w * (‖K a‖ * |W ((z - w + v0) + a)|) := by
          rw [← MeasureTheory.integral_const_mul]
      _ ≤ ∫ a : E3,
            (Cf * ℓ ^ (-(4 : ℤ))) * ((R + ‖a‖) ^ 4 * ‖K a‖ * |W ((z - w + v0) + a)|) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun a =>
              mul_nonneg (mul_nonneg (hχnn z) (hχnn w)) (by positivity))
            ((hMaj (z - w + v0)).const_mul _)
            (Filter.Eventually.of_forall hptA)
      _ = (Cf * ℓ ^ (-(4 : ℤ))) *
            ∫ a : E3, (R + ‖a‖) ^ 4 * ‖K a‖ * |W (z + v0 - (w - a))| := hInt_eq
  -- the value of the convolution integral
  have hval : (∫ w : E3, ∫ a : E3, (R + ‖a‖) ^ 4 * ‖K a‖ * |W (z + v0 - (w - a))|)
      = (∫ a : E3, (R + ‖a‖) ^ 4 * ‖K a‖) * (∫ x : E3, |W x|) := by
    rw [hconv.2]
    congr 1
    exact MeasureTheory.integral_sub_left_eq_self (fun x : E3 => |W x|) (volume : Measure E3)
      (z + v0)
  calc χ z * (∫ w : E3, χ w * |S (z - w + v0)|)
      = ∫ w : E3, χ z * (χ w * |S (z - w + v0)|) :=
        (MeasureTheory.integral_const_mul (χ z)
          (fun w : E3 => χ w * |S (z - w + v0)|)).symm
    _ ≤ ∫ w : E3, (Cf * ℓ ^ (-(4 : ℤ))) *
          ∫ a : E3, (R + ‖a‖) ^ 4 * ‖K a‖ * |W (z + v0 - (w - a))| :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun w =>
            mul_nonneg (hχnn z) (mul_nonneg (hχnn w) (abs_nonneg _)))
          hint
          (Filter.Eventually.of_forall hpoint)
    _ = Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖K a‖)
          * (∫ x : E3, |W x|) := by
        rw [MeasureTheory.integral_const_mul, hval]
        ring

/-! ## The target -/

theorem chBimg_near_d {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {R ℓ Λ Cf Cd : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hΛ : 1 ≤ Λ)
    (hCf : 0 ≤ Cf) (hCd : 0 ≤ Cd)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hdec : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
    (hflat : ∀ (ρ : ℝ), 0 ≤ ρ → ∀ (d : Fin 3 → ℤ), d ≠ 0 → ∀ z w : EuclideanSpace ℝ (Fin 3),
        ‖z - w + ℓ • Work.BoseBoxFock.latVec d‖ ≤ ρ →
          Work.BoseK15.corpusBox.chiLam ℓ z * Work.BoseK15.corpusBox.chiLam ℓ w ≤ Cf * (ρ / ℓ) ^ 4)
    {d : Fin 3 → ℤ} (hd : d ≠ 0) (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseK15.corpusBox.chiLam ℓ z *
        (∫ w : EuclideanSpace ℝ (Fin 3), Work.BoseK15.corpusBox.chiLam ℓ w *
          |Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ)
            (z - w + ℓ • Work.BoseBoxFock.latVec d)|)
      ≤ Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : EuclideanSpace ℝ (Fin 3),
            (R + ‖a‖) ^ 4 * ‖Work.BoseBoxFock.uvKernel fu Λ a‖)
          * (∫ x : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h ℓ x|) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  -- integrability of the weight
  have hWint : Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hWabsint : Integrable (fun x : E3 => |Work.BoseFixR.W1fun v h ℓ x|) := hWint.abs
  -- support of the weight
  have hWsupp : ∀ x : E3, Work.BoseFixR.W1fun v h ℓ x ≠ 0 → ‖x‖ < R := by
    intro x hx
    have h1 : x ∈ Function.support v :=
      Work.BoseFixR.support_W1fun_subset h ℓ (Function.mem_support.mpr hx)
    have h2 : x ∈ Metric.ball (0 : E3) R := hv_supp (subset_tsupport v h1)
    rwa [Metric.mem_ball, dist_zero_right] at h2
  -- decay of the UV kernel
  obtain ⟨C₈, hC₈nn, hC₈⟩ := Work.BoseBoxFock.uvKernel_rapidDecay fu hΛpos 8
  obtain ⟨C₄, hC₄nn, hC₄⟩ := Work.BoseBoxFock.uvKernel_rapidDecay fu hΛpos 4
  have hC₈' : ∀ a : E3, ‖Work.BoseBoxFock.uvKernel fu Λ a‖
      ≤ C₈ * (1 + ‖a‖) ^ (-(8 : ℤ)) := fun a => hC₈ a
  have hC₄' : ∀ a : E3, ‖Work.BoseBoxFock.uvKernel fu Λ a‖
      ≤ C₄ * (1 + ‖a‖) ^ (-(4 : ℤ)) := fun a => hC₄ a
  -- the weight `(R + ‖a‖)^4` versus `(1 + ‖a‖)^4`
  have hweight : ∀ a : E3, (R + ‖a‖) ^ 4 ≤ (max R 1) ^ 4 * (1 + ‖a‖) ^ 4 := by
    intro a
    have hle2 : (1 : ℝ) ≤ max R 1 := le_max_right R 1
    have hle3 : ‖a‖ ≤ max R 1 * ‖a‖ := by
      calc ‖a‖ = 1 * ‖a‖ := (one_mul _).symm
        _ ≤ max R 1 * ‖a‖ := mul_le_mul_of_nonneg_right hle2 (norm_nonneg a)
    have hle : R + ‖a‖ ≤ max R 1 * (1 + ‖a‖) := by
      nlinarith [norm_nonneg a, le_max_left R 1, hle3]
    calc (R + ‖a‖) ^ 4 ≤ (max R 1 * (1 + ‖a‖)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hle 4
      _ = (max R 1) ^ 4 * (1 + ‖a‖) ^ 4 := mul_pow _ _ _
  -- the uniform sup bound on `(R + ‖a‖)^4 ‖K a‖`
  have hsup : ∀ a : E3, (R + ‖a‖) ^ 4 * ‖Work.BoseBoxFock.uvKernel fu Λ a‖
      ≤ C₄ * (max R 1) ^ 4 := by
    intro a
    calc (R + ‖a‖) ^ 4 * ‖Work.BoseBoxFock.uvKernel fu Λ a‖
        ≤ ((max R 1) ^ 4 * (1 + ‖a‖) ^ 4) * (C₄ * (1 + ‖a‖) ^ (-(4 : ℤ))) :=
          mul_le_mul (hweight a) (hC₄' a) (norm_nonneg _) (by positivity)
      _ = C₄ * (max R 1) ^ 4 := by
          rw [show ((max R 1) ^ 4 * (1 + ‖a‖) ^ 4) * (C₄ * (1 + ‖a‖) ^ (-(4 : ℤ)))
                = C₄ * (max R 1) ^ 4 * ((1 + ‖a‖) ^ 4 * (1 + ‖a‖) ^ (-(4 : ℤ))) by ring,
              pow_four_mul_zpow_neg_four (by positivity : (0 : ℝ) < 1 + ‖a‖), mul_one]
  -- integrability of `(R + ‖a‖)^4 ‖K a‖`
  have hone : Integrable (fun a : E3 => (1 + ‖a‖) ^ (-(4 : ℤ))) :=
    Work.BoseBoxFock.integrable_one_add_norm_zpow 4 (by norm_num)
  have hKsmooth : Continuous (fun a : E3 => (R + ‖a‖) ^ 4 * ‖Work.BoseBoxFock.uvKernel fu Λ a‖) :=
    ((continuous_const.add continuous_norm).pow 4).mul
      (Work.BoseBoxFock.uvKernel_continuous fu hΛpos).norm
  have hKint : Integrable (fun a : E3 => (R + ‖a‖) ^ 4 * ‖Work.BoseBoxFock.uvKernel fu Λ a‖) := by
    have hbase : Integrable (fun a : E3 => (C₈ * (max R 1) ^ 4) * (1 + ‖a‖) ^ (-(4 : ℤ))) :=
      hone.const_mul _
    refine hbase.mono' hKsmooth.aestronglyMeasurable ?_
    filter_upwards with a
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (R + ‖a‖) ^ 4 * ‖Work.BoseBoxFock.uvKernel fu Λ a‖
        ≤ ((max R 1) ^ 4 * (1 + ‖a‖) ^ 4) * (C₈ * (1 + ‖a‖) ^ (-(8 : ℤ))) :=
          mul_le_mul (hweight a) (hC₈' a) (norm_nonneg _) (by positivity)
      _ = (C₈ * (max R 1) ^ 4) * (1 + ‖a‖) ^ (-(4 : ℤ)) := by
          rw [show ((max R 1) ^ 4 * (1 + ‖a‖) ^ 4) * (C₈ * (1 + ‖a‖) ^ (-(8 : ℤ)))
                = C₈ * (max R 1) ^ 4 * ((1 + ‖a‖) ^ 4 * (1 + ‖a‖) ^ (-(8 : ℤ))) by ring,
              pow_four_mul_zpow_neg_eight (by positivity : (0 : ℝ) < 1 + ‖a‖), mul_assoc]
  -- integrability of the `a`-majorant for every shift
  have hmaj : ∀ c : E3, Integrable (fun a : E3 =>
      (R + ‖a‖) ^ 4 * ‖Work.BoseBoxFock.uvKernel fu Λ a‖
        * |Work.BoseFixR.W1fun v h ℓ (c + a)|) := by
    intro c
    have hbase : Integrable (fun a : E3 =>
        (C₄ * (max R 1) ^ 4) * |Work.BoseFixR.W1fun v h ℓ (c + a)|) :=
      (hWabsint.comp_add_left c).const_mul _
    refine hbase.mono' ?_ ?_
    · exact (hKsmooth.aestronglyMeasurable).mul
        (hWabsint.comp_add_left c).aestronglyMeasurable
    · filter_upwards with a
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hsup a) (abs_nonneg _)
  -- the convolution domination of `uvSmear`
  have hSabs : ∀ y : E3, |Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) y|
      ≤ ∫ a : E3, ‖Work.BoseBoxFock.uvKernel fu Λ a‖
          * |Work.BoseFixR.W1fun v h ℓ (y + a)| := by
    intro y
    calc |Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) y|
        = ‖∫ a : E3, Work.BoseBoxFock.uvKernel fu Λ a
              * Work.BoseFixR.W1fun v h ℓ (y + a)‖ := by
          rw [uvSmear_eq_integral, Real.norm_eq_abs]
      _ ≤ ∫ a : E3, ‖Work.BoseBoxFock.uvKernel fu Λ a
              * Work.BoseFixR.W1fun v h ℓ (y + a)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ a : E3, ‖Work.BoseBoxFock.uvKernel fu Λ a‖
              * |Work.BoseFixR.W1fun v h ℓ (y + a)| := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with a
          rw [norm_mul]
          rfl
  exact near_d_core (v0 := ℓ • Work.BoseBoxFock.latVec d)
    (K := Work.BoseBoxFock.uvKernel fu Λ)
    (W := Work.BoseFixR.W1fun v h ℓ)
    (χ := Work.BoseK15.corpusBox.chiLam ℓ)
    (S := fun y : E3 => Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) y)
    hR hℓ hCf (fun x => chiLam_nonneg' ℓ x) hWsupp hWint hmaj hKint
    (fun ρ hρ z' w hle => hflat ρ hρ d hd z' w hle) hSabs z

end Work.BoseBoxFock.PCFU
