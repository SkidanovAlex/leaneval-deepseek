import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A restricted convolution (Young) inequality on `ℝ³`

This file proves `Work.BoseBoxFock.FRK.conv_restricted_le`, the estimate

`∫_p 1_{R+gap ≤ ‖p‖} ‖∫_s k s · μ (p - s)‖² ≤ (∫_s 1_{gap ≤ ‖s‖} ‖k s‖)² · ∫_p ‖μ p‖²`

for `μ` supported in the ball of radius `R`.  The proof is Young's convolution
inequality `‖f * g‖₂ ≤ ‖f‖₁ ‖g‖₂` at `f = 1_{gap ≤ ‖·‖} k`, `g = μ`: because
`‖p‖ ≥ R + gap` forces `‖s‖ ≥ gap` on the support of `μ (p - ·)`, the truncation
may be inserted into the convolution without changing it.

The analytic heart is proved at the level of `ℝ≥0∞`-valued Lebesgue integrals
(`young_lintegral`), so that no integrability of `μ` is needed: Cauchy–Schwarz
(`sq_lintegral_mul_le`, a square form of Hölder) followed by Tonelli and the
translation invariance of Lebesgue measure.  The Bochner integral of the target
is then compared with the Lebesgue integral of the (nonnegative) integrand.
-/

namespace Work.BoseBoxFock.FRK

open MeasureTheory
open scoped ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `√x * √x = x` for `x : ℝ≥0∞`, with the square root written as the rpow `x ^ (1/2)`. -/
lemma rpow_half_mul_self (x : ℝ≥0∞) : x ^ ((1:ℝ)/2) * x ^ ((1:ℝ)/2) = x := by
  rw [← pow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy–Schwarz for the Lebesgue integral, in square (non-`rpow`) form. -/
lemma sq_lintegral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ x, a x * b x ∂μ) ^ 2 ≤ (∫⁻ x, a x ^ 2 ∂μ) * (∫⁻ x, b x ^ 2 ∂μ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq ha hb
  simp only [Pi.mul_apply] at h
  have hsq : (∫⁻ x, a x * b x ∂μ) ^ 2 ≤
      ((∫⁻ x, a x ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2) * (∫⁻ x, b x ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2)) ^ 2 :=
    pow_le_pow_left' h 2
  refine hsq.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_mul, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- `v (p - ·)` is a.e.-measurable when `v` is. -/
lemma aemeasurable_comp_sub {v : E3 → ℝ≥0∞} (hv : AEMeasurable v volume) (p : E3) :
    AEMeasurable (fun s => v (p - s)) volume := by
  have hmp : Measure.map (fun t : E3 => p - t) (volume : Measure E3) = volume :=
    (Measure.measurePreserving_sub_left (volume : Measure E3) p).map_eq
  have hv' : AEMeasurable v (Measure.map (fun s : E3 => p - s) volume) := by
    rw [hmp]; exact hv
  simpa [Function.comp_def] using
    AEMeasurable.comp_measurable hv' (show Measurable (fun s : E3 => p - s) from by fun_prop)

/-- `v (· - s)` is a.e.-measurable when `v` is. -/
lemma aemeasurable_comp_sub' {v : E3 → ℝ≥0∞} (hv : AEMeasurable v volume) (s : E3) :
    AEMeasurable (fun p => v (p - s)) volume := by
  have hmp : Measure.map (fun t : E3 => t + (-s)) (volume : Measure E3) = volume :=
    (measurePreserving_add_right (volume : Measure E3) (-s)).map_eq
  have hv' : AEMeasurable v (Measure.map (fun t : E3 => t + (-s)) volume) := by
    rw [hmp]; exact hv
  simpa [Function.comp_def, sub_eq_add_neg] using
    AEMeasurable.comp_measurable hv' (show Measurable (fun t : E3 => t + (-s)) from by fun_prop)

/-- `(x, y) ↦ v (x - y)` is a.e.-measurable on the product when `v` is. -/
lemma prod_aemeasurable {v : E3 → ℝ≥0∞} (hv : AEMeasurable v volume) :
    AEMeasurable (fun z : E3 × E3 => v (z.1 - z.2)) (volume.prod volume) := by
  have hq : Measure.QuasiMeasurePreserving (fun z : E3 × E3 => z.1 - z.2)
      ((volume : Measure E3).prod volume) volume :=
    quasiMeasurePreserving_sub volume volume
  simpa [Function.comp_def] using AEMeasurable.comp_quasiMeasurePreserving hv hq

/-- **Young's convolution inequality**, Lebesgue-integral (`ℝ≥0∞`) form on `ℝ³`:
the `L²` norm of the convolution of `u` and `v` is bounded by `(∫ u)² · ∫ v²`. -/
theorem young_lintegral {u v : E3 → ℝ≥0∞} (hu : AEMeasurable u volume)
    (hv : AEMeasurable v volume) :
    ∫⁻ p, (∫⁻ s, u s * v (p - s) ∂volume) ^ 2 ∂volume ≤
      (∫⁻ s, u s ∂volume) ^ 2 * ∫⁻ x, v x ^ 2 ∂volume := by
  have key : ∀ p, (∫⁻ s, u s * v (p - s) ∂volume) ^ 2 ≤
      (∫⁻ s, u s ∂volume) * (∫⁻ s, u s * (v (p - s)) ^ 2 ∂volume) := by
    intro p
    have ha : AEMeasurable (fun s => (u s) ^ ((1:ℝ)/2)) volume := by fun_prop
    have hva : AEMeasurable (fun s => v (p - s)) volume := aemeasurable_comp_sub hv p
    have hb : AEMeasurable (fun s => (u s) ^ ((1:ℝ)/2) * v (p - s)) volume := ha.mul hva
    have h1 := sq_lintegral_mul_le ha hb
    have e1 : (∫⁻ x, (u x) ^ ((1:ℝ)/2) * ((u x) ^ ((1:ℝ)/2) * v (p - x)) ∂volume)
        = (∫⁻ x, u x * v (p - x) ∂volume) := by
      apply lintegral_congr; intro x; rw [← mul_assoc, rpow_half_mul_self]
    have e2 : (∫⁻ x, ((u x) ^ ((1:ℝ)/2)) ^ 2 ∂volume) = ∫⁻ s, u s ∂volume := by
      apply lintegral_congr; intro x; rw [pow_two, rpow_half_mul_self]
    have e3 : (∫⁻ x, ((u x) ^ ((1:ℝ)/2) * v (p - x)) ^ 2 ∂volume)
        = (∫⁻ x, u x * (v (p - x)) ^ 2 ∂volume) := by
      apply lintegral_congr; intro x; rw [mul_pow, pow_two, rpow_half_mul_self]
    rw [e1, e2, e3] at h1
    exact h1
  have huncurry : AEMeasurable (Function.uncurry (fun p s => u s * (v (p - s)) ^ 2))
      ((volume : Measure E3).prod volume) := by
    have h : Function.uncurry (fun p s => u s * (v (p - s)) ^ 2)
        = fun z : E3 × E3 => u z.2 * (v (z.1 - z.2)) ^ 2 := rfl
    rw [h]
    exact (hu.comp_snd).mul ((prod_aemeasurable hv).pow_const 2)
  have hswap : (∫⁻ p, (∫⁻ s, u s * (v (p - s)) ^ 2 ∂volume) ∂volume)
      = ∫⁻ s, ∫⁻ p, u s * (v (p - s)) ^ 2 ∂volume ∂volume := by
    rw [lintegral_lintegral_swap (f := fun p s => u s * (v (p - s)) ^ 2) huncurry]
  have hstep1 : (∫⁻ p, (∫⁻ s, u s ∂volume) * (∫⁻ s, u s * (v (p - s)) ^ 2 ∂volume) ∂volume)
      = (∫⁻ s, u s ∂volume) * ∫⁻ p, (∫⁻ s, u s * (v (p - s)) ^ 2 ∂volume) ∂volume := by
    rw [lintegral_const_mul'']
    exact huncurry.lintegral_prod_right
  have hconst : (∫⁻ s, ∫⁻ p, u s * (v (p - s)) ^ 2 ∂volume ∂volume)
      = ∫⁻ s, u s * (∫⁻ p, (v (p - s)) ^ 2 ∂volume) ∂volume := by
    apply lintegral_congr; intro s
    rw [lintegral_const_mul'']
    exact (aemeasurable_comp_sub' hv s).pow_const 2
  have htrans : (∫⁻ s, u s * (∫⁻ p, (v (p - s)) ^ 2 ∂volume) ∂volume)
      = ∫⁻ s, u s * (∫⁻ x, (v x) ^ 2 ∂volume) ∂volume := by
    apply lintegral_congr; intro s
    congr 1
    rw [← lintegral_add_left_eq_self (fun x : E3 => (v x) ^ 2) (-s)]
    apply lintegral_congr; intro x
    congr 1
    rw [sub_eq_add_neg, add_comm]
  calc ∫⁻ p, (∫⁻ s, u s * v (p - s) ∂volume) ^ 2 ∂volume
      ≤ ∫⁻ p, (∫⁻ s, u s ∂volume) * (∫⁻ s, u s * (v (p - s)) ^ 2 ∂volume) ∂volume :=
        lintegral_mono key
    _ = (∫⁻ s, u s ∂volume) * ∫⁻ p, (∫⁻ s, u s * (v (p - s)) ^ 2 ∂volume) ∂volume := hstep1
    _ = (∫⁻ s, u s ∂volume) * (∫⁻ s, ∫⁻ p, u s * (v (p - s)) ^ 2 ∂volume ∂volume) := by
          rw [hswap]
    _ = (∫⁻ s, u s ∂volume) * (∫⁻ s, u s * (∫⁻ p, (v (p - s)) ^ 2 ∂volume) ∂volume) := by
          rw [hconst]
    _ = (∫⁻ s, u s ∂volume) * (∫⁻ s, u s * (∫⁻ x, (v x) ^ 2 ∂volume) ∂volume) := by
          rw [htrans]
    _ = (∫⁻ s, u s ∂volume) ^ 2 * ∫⁻ x, v x ^ 2 ∂volume := by
          rw [lintegral_mul_const'' _ (by fun_prop), ← mul_assoc, ← pow_two]

theorem conv_restricted_le {k μ : EuclideanSpace ℝ (Fin 3) → ℂ} {R gap : ℝ} (hgap : 0 ≤ gap)
    (hk : MeasureTheory.Integrable k)
    (hμ2 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖μ p‖ ^ 2))
    (hsupp : ∀ p : EuclideanSpace ℝ (Fin 3), μ p ≠ 0 → ‖p‖ ≤ R) :
    MeasureTheory.integral MeasureTheory.volume
        (fun p : EuclideanSpace ℝ (Fin 3) =>
          (if R + gap ≤ ‖p‖ then (1 : ℝ) else 0) *
            ‖MeasureTheory.integral MeasureTheory.volume
              (fun s : EuclideanSpace ℝ (Fin 3) => k s * μ (p - s))‖ ^ 2)
      ≤ (MeasureTheory.integral MeasureTheory.volume
            (fun s : EuclideanSpace ℝ (Fin 3) => (if gap ≤ ‖s‖ then (1 : ℝ) else 0) * ‖k s‖)) ^ 2
        * MeasureTheory.integral MeasureTheory.volume
            (fun p : EuclideanSpace ℝ (Fin 3) => ‖μ p‖ ^ 2) := by
  set f : E3 → ℂ := fun s : E3 => (if gap ≤ ‖s‖ then (1 : ℂ) else 0) * k s with hf_def
  set F : E3 → ℝ := fun s : E3 => (if gap ≤ ‖s‖ then (1 : ℝ) else 0) * ‖k s‖ with hF_def
  set G : E3 → ℝ := fun x : E3 => ‖μ x‖ with hG_def
  set L : E3 → ℝ := fun p : E3 =>
      (if R + gap ≤ ‖p‖ then (1 : ℝ) else 0) * ‖∫ s, k s * μ (p - s)‖ ^ 2 with hL_def
  have hF_nn : ∀ s, 0 ≤ F s := by
    intro s; simp only [hF_def]; split_ifs <;> positivity
  have hG_nn : ∀ x, 0 ≤ G x := fun x => norm_nonneg (μ x)
  have hL_nn : ∀ p, 0 ≤ L p := by
    intro p; simp only [hL_def]; split_ifs <;> positivity
  have hf_norm : ∀ s, ‖f s‖ = F s := by
    intro s
    rw [hf_def, hF_def, norm_mul]
    congr 1
    split_ifs <;> simp
  have hFG : ∀ s x : E3, ‖f s * μ x‖ = F s * G x := by
    intro s x
    rw [norm_mul, hf_norm s]
  have hind : Measurable (fun s : E3 => (if gap ≤ ‖s‖ then (1 : ℂ) else 0)) :=
    Measurable.ite (isClosed_le continuous_const continuous_norm).measurableSet
      measurable_const measurable_const
  have hf_aesm : AEStronglyMeasurable f volume := by
    rw [hf_def]
    exact hind.aestronglyMeasurable.mul hk.aestronglyMeasurable
  have hf_int : Integrable f volume := by
    refine Integrable.mono' (g := fun s => ‖k s‖) hk.norm hf_aesm ?_
    filter_upwards with s
    rw [hf_norm s, hF_def]
    exact mul_le_of_le_one_left (norm_nonneg _) (by split_ifs <;> norm_num)
  have hF_int : Integrable F volume :=
    hf_int.norm.congr (Filter.Eventually.of_forall hf_norm)
  have hG2_int : Integrable (fun x => G x ^ 2) volume :=
    hμ2.congr (Filter.Eventually.of_forall fun x => rfl)
  have hF_aemeas : AEMeasurable F volume :=
    (hf_aesm.norm.aemeasurable).congr (Filter.Eventually.of_forall hf_norm)
  have hG_aemeas : AEMeasurable G volume := by
    have hsq : AEMeasurable (fun p : E3 => ‖μ p‖ ^ 2) volume :=
      hμ2.aestronglyMeasurable.aemeasurable
    have hsqrt : AEMeasurable (fun p : E3 => Real.sqrt (‖μ p‖ ^ 2)) volume :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hsq
    refine hsqrt.congr (Filter.Eventually.of_forall fun p => ?_)
    simpa only [Function.comp_apply, hG_def] using Real.sqrt_sq (norm_nonneg (μ p))
  have hF_meas : AEMeasurable (fun s => ENNReal.ofReal (F s)) volume := hF_aemeas.ennreal_ofReal
  have hG_meas : AEMeasurable (fun x => ENNReal.ofReal (G x)) volume := hG_aemeas.ennreal_ofReal
  have hkey : ∀ p : E3, R + gap ≤ ‖p‖ → (∫ s, k s * μ (p - s)) = (∫ s, f s * μ (p - s)) := by
    intro p hp
    apply integral_congr_ae
    filter_upwards with s
    by_cases hμ : μ (p - s) = 0
    · simp [hμ]
    · have h1 : ‖p - s‖ ≤ R := hsupp (p - s) hμ
      have h2 : gap ≤ ‖s‖ := by
        have h3 : ‖p‖ ≤ ‖s‖ + ‖p - s‖ := by
          calc ‖p‖ = ‖s + (p - s)‖ := by rw [add_sub_cancel]
            _ ≤ ‖s‖ + ‖p - s‖ := norm_add_le _ _
        linarith
      rw [hf_def]
      simp only [if_pos h2, one_mul]
  have hpt : ∀ p : E3, ENNReal.ofReal (L p) ≤
      (∫⁻ s, ENNReal.ofReal (F s) * ENNReal.ofReal (G (p - s))) ^ 2 := by
    intro p
    by_cases hp : R + gap ≤ ‖p‖
    · have hLp : L p = ‖∫ s, k s * μ (p - s)‖ ^ 2 := by
        rw [hL_def]; simp only [if_pos hp, one_mul]
      rw [hLp, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      refine pow_le_pow_left' ?_ 2
      rw [hkey p hp]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      apply lintegral_mono; intro s
      simp only []
      rw [← ofReal_norm, hFG s (p - s), ENNReal.ofReal_mul (hF_nn s)]
    · have hLp : L p = 0 := by
        rw [hL_def]; simp only [if_neg hp, zero_mul]
      rw [hLp, ENNReal.ofReal_zero]
      positivity
  have hA_lint : (∫⁻ s, ENNReal.ofReal (F s)) = ENNReal.ofReal (∫ s, F s) :=
    (ofReal_integral_eq_lintegral_ofReal hF_int (Filter.Eventually.of_forall hF_nn)).symm
  have hB_lint : (∫⁻ x, (ENNReal.ofReal (G x)) ^ 2) = ENNReal.ofReal (∫ x, G x ^ 2) := by
    have h1 : (∫⁻ x, (ENNReal.ofReal (G x)) ^ 2) = ∫⁻ x, ENNReal.ofReal (G x ^ 2) := by
      apply lintegral_congr; intro x
      exact (ENNReal.ofReal_pow (hG_nn x) 2).symm
    rw [h1]
    exact (ofReal_integral_eq_lintegral_ofReal hG2_int
      (Filter.Eventually.of_forall fun x => sq_nonneg (G x))).symm
  have hB_nn : 0 ≤ ∫ x, G x ^ 2 := integral_nonneg (fun x => sq_nonneg (G x))
  have hL_lint : (∫⁻ p, ENNReal.ofReal (L p)) ≤
      ENNReal.ofReal ((∫ s, F s) ^ 2 * ∫ x, G x ^ 2) := by
    have h1 := (lintegral_mono hpt).trans (young_lintegral hF_meas hG_meas)
    have h2 : (∫⁻ p, ENNReal.ofReal (L p)) ≤
        (ENNReal.ofReal (∫ s, F s)) ^ 2 * ENNReal.ofReal (∫ x, G x ^ 2) := by
      rwa [hA_lint, hB_lint] at h1
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (integral_nonneg hF_nn)]
    exact h2
  by_cases hLint : Integrable L volume
  · have h2 : ∫ p, L p ≤ (∫ s, F s) ^ 2 * ∫ x, G x ^ 2 := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hL_nn) hLint.aestronglyMeasurable]
      refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hL_lint).trans_eq ?_
      exact ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hB_nn)
    simpa only [hG_def] using h2
  · rw [integral_undef hLint]
    simpa only [hG_def] using mul_nonneg (sq_nonneg (∫ s, F s)) hB_nn

end Work.BoseBoxFock.FRK
