import Mathlib
import Submission.Work.NN.Core.bmPot_holder_C0a
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_sub_le_sum_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDzKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.bmKernel_decay_le
import Submission.Work.CR.Flat.Cauchy.bmCz.hasFDerivAt_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_le_sum_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_sub_le_sum_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.czAux

noncomputable section
open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

open Work.CR.Flat
open Work.CR.Flat.Cauchy

lemma measurable_bmKernel_aux {n : ℕ} (k : Fin n) : Measurable (bmKernel k) := by
  have h1 : Measurable fun y : Fin n → ℂ => starRingEnd ℂ (y k) :=
    Complex.continuous_conj.measurable.comp (continuous_apply k).measurable
  have h2 : Measurable fun y : Fin n → ℂ => ((eucNorm y : ℝ) : ℂ) ^ (2 * n) :=
    (Complex.continuous_ofReal.measurable.comp continuous_eucNorm.measurable).pow_const _
  rw [show bmKernel k = fun y : Fin n → ℂ => starRingEnd ℂ (y k) / ((eucNorm y : ℝ) : ℂ) ^ (2 * n)
    from rfl]
  exact h1.div h2

lemma div_eucNorm_pow_eq_aux {n : ℕ} {y : Fin n → ℂ} (hy : 0 < eucNorm y) (c : ℝ) :
    c / (eucNorm y) ^ (2 * n) = c * (eucNorm y) ^ (-(2 * (n : ℝ))) := by
  rw [show (eucNorm y) ^ (2 * n) = (eucNorm y) ^ (2 * (n : ℝ)) by
    rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]]
  rw [Real.rpow_neg hy.le, div_eq_mul_inv]

lemma div_eucNorm_pow_succ_eq_aux {n : ℕ} {y : Fin n → ℂ} (hy : 0 < eucNorm y) (c : ℝ) :
    c / (eucNorm y) ^ (2 * n + 1) = c * (eucNorm y) ^ (-(2 * (n : ℝ) + 1)) := by
  rw [show (eucNorm y) ^ (2 * n + 1) = (eucNorm y) ^ (2 * (n : ℝ) + 1) by
    rw [show (2 * (n : ℝ) + 1) = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]]
  rw [Real.rpow_neg hy.le, div_eq_mul_inv]

lemma norm_fderiv_bmKernel_le_aux {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : Fin n) (y : Fin n → ℂ), y ≠ 0 →
      ‖fderiv ℝ (bmKernel k) y‖ ≤ C * (eucNorm y) ^ (-(2 * (n : ℝ))) := by
  obtain ⟨Cdec, hCdecpos, hdec_dz, hdec_dbar⟩ := (bmCz.bmKernel_decay_le hn).2.2
  refine ⟨2 * ((n : ℝ) * (2 * Cdec)), by positivity, fun k y hy => ?_⟩
  have hy' : 0 < eucNorm y := eucNorm_pos hy
  set E : ℝ := (eucNorm y) ^ (-(2 * (n : ℝ))) with hE
  have hcd : ∀ l : Fin n, ‖Work.CR.Flat.dCoord l (bmKernel k) y‖ ≤ Cdec * E ∧
      ‖Work.CR.Flat.dbarCoord l (bmKernel k) y‖ ≤ Cdec * E := by
    intro l
    constructor
    · rw [bmCz.dCoord_bmKernel hy, ← div_eucNorm_pow_eq_aux hy' Cdec]; exact hdec_dz l k y hy
    · rw [bmCz.dbarCoord_bmKernel hy, ← div_eucNorm_pow_eq_aux hy' Cdec]; exact hdec_dbar l k y hy
  have hsum : ∑ l : Fin n, (‖Work.CR.Flat.dCoord l (bmKernel k) y‖
        + ‖Work.CR.Flat.dbarCoord l (bmKernel k) y‖) ≤ (n : ℝ) * (2 * (Cdec * E)) := by
    calc ∑ l : Fin n, (‖Work.CR.Flat.dCoord l (bmKernel k) y‖
          + ‖Work.CR.Flat.dbarCoord l (bmKernel k) y‖)
        ≤ ∑ _l : Fin n, (2 * (Cdec * E)) :=
          Finset.sum_le_sum fun l _ => by linarith [(hcd l).1, (hcd l).2]
      _ = (n : ℝ) * (2 * (Cdec * E)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ‖fderiv ℝ (bmKernel k) y‖ ≤ 2 * ∑ l : Fin n, (‖Work.CR.Flat.dCoord l (bmKernel k) y‖
        + ‖Work.CR.Flat.dbarCoord l (bmKernel k) y‖) :=
        bmCz.norm_fderiv_le_sum_wirtinger (bmKernel k) y
    _ ≤ 2 * ((n : ℝ) * (2 * (Cdec * E))) := by linarith
    _ = (2 * ((n : ℝ) * (2 * Cdec))) * E := by ring

lemma norm_fderiv_bmKernel_sub_le_aux {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : Fin n) (x h : Fin n → ℂ),
      2 * eucNorm h ≤ eucNorm x →
      ‖fderiv ℝ (bmKernel k) (x - h) - fderiv ℝ (bmKernel k) x‖
        ≤ C * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by
  obtain ⟨Cz, hCzpos, hCz⟩ := bmCz.norm_bmDzKernel_sub_le hn
  obtain ⟨Cb, hCbpos, hCb⟩ := bmCz.norm_bmDbarKernel_sub_le hn
  set C : ℝ := max Cz Cb with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le hCzpos (le_max_left _ _)
  have hCzC : Cz ≤ C := le_max_left _ _
  have hCbC : Cb ≤ C := le_max_right _ _
  refine ⟨2 * ((n : ℝ) * (2 * C)), by positivity, fun k x h hxh => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · have hh : h = 0 := by
      have h1 : eucNorm h = 0 := by
        simp only [eucNorm_zero] at hxh
        linarith [eucNorm_nonneg h]
      exact eucNorm_eq_zero.mp h1
    subst hh
    simp
  · have hx' : 0 < eucNorm x := eucNorm_pos hx0
    have hxh' : x - h ≠ 0 := by
      intro hcon
      have hxeh : x = h := sub_eq_zero.mp hcon
      have h1 : eucNorm h = 0 := by
        have h2 := hxh
        rw [hxeh] at h2
        linarith [eucNorm_nonneg h]
      have hxe : eucNorm x = 0 := by rw [hxeh]; exact h1
      exact hx0 (eucNorm_eq_zero.mp hxe)
    have hAnn : 0 ≤ (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) :=
      Real.rpow_nonneg (eucNorm_nonneg x) _
    have hhnn : 0 ≤ eucNorm h := eucNorm_nonneg h
    have hcd : ∀ l : Fin n,
        (‖Work.CR.Flat.dCoord l (bmKernel k) (x - h) - Work.CR.Flat.dCoord l (bmKernel k) x‖
            ≤ C * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1))) ∧
        (‖Work.CR.Flat.dbarCoord l (bmKernel k) (x - h) - Work.CR.Flat.dbarCoord l (bmKernel k) x‖
            ≤ C * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1))) := by
      intro l
      constructor
      · rw [bmCz.dCoord_bmKernel hxh', bmCz.dCoord_bmKernel hx0]
        exact le_trans (hCz l k x h hxh)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCzC hhnn) hAnn)
      · rw [bmCz.dbarCoord_bmKernel hxh', bmCz.dbarCoord_bmKernel hx0]
        have h3 := hCb l k x h hxh
        rw [div_eucNorm_pow_succ_eq_aux hx' (Cb * eucNorm h)] at h3
        exact le_trans h3
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbC hhnn) hAnn)
    have hsum : ∑ l : Fin n,
        (‖Work.CR.Flat.dCoord l (bmKernel k) (x - h) - Work.CR.Flat.dCoord l (bmKernel k) x‖
          + ‖Work.CR.Flat.dbarCoord l (bmKernel k) (x - h)
              - Work.CR.Flat.dbarCoord l (bmKernel k) x‖)
        ≤ (n : ℝ) * (2 * (C * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)))) := by
      calc ∑ l : Fin n, (‖Work.CR.Flat.dCoord l (bmKernel k) (x - h)
              - Work.CR.Flat.dCoord l (bmKernel k) x‖
            + ‖Work.CR.Flat.dbarCoord l (bmKernel k) (x - h)
                - Work.CR.Flat.dbarCoord l (bmKernel k) x‖)
          ≤ ∑ _l : Fin n, (2 * (C * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)))) :=
            Finset.sum_le_sum fun l _ => by linarith [(hcd l).1, (hcd l).2]
        _ = (n : ℝ) * (2 * (C * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ‖fderiv ℝ (bmKernel k) (x - h) - fderiv ℝ (bmKernel k) x‖
        ≤ 2 * ∑ l : Fin n, (‖Work.CR.Flat.dCoord l (bmKernel k) (x - h)
              - Work.CR.Flat.dCoord l (bmKernel k) x‖
            + ‖Work.CR.Flat.dbarCoord l (bmKernel k) (x - h)
                - Work.CR.Flat.dbarCoord l (bmKernel k) x‖) :=
          bmCz.norm_fderiv_sub_le_sum_wirtinger (bmKernel k) (x - h) x
      _ ≤ 2 * ((n : ℝ) * (2 * (C * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1))))) := by
          linarith
      _ = 2 * ((n : ℝ) * (2 * C)) * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by ring


/-! ## The candidate derivative of the shifted-kernel integral -/

/-- The candidate derivative of `x ↦ ∫ a, bmKernel k (a - x) * F a` at `z`: the integral of the
derivative of the integrand in `x`, namely the composition of multiplication by `F a` with
`- d(bmKernel k)(a - z)`. -/
private noncomputable def kernShiftDeriv {n : ℕ} (k : Fin n) (F : (Fin n → ℂ) → ℂ)
    (z a : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ (F a)).comp
    ((fderiv ℝ (bmKernel k) (a - z)).comp (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))))

private lemma measurable_kernShiftDeriv {n : ℕ} (k : Fin n) {F : (Fin n → ℂ) → ℂ}
    (hF : Measurable F) (z : Fin n → ℂ) : Measurable (fun a => kernShiftDeriv k F z a) := by
  unfold kernShiftDeriv
  fun_prop


/-! ## The far-field estimate -/

private lemma norm_neg_one_clm_le_aux {n : ℕ} :
    ‖-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))‖ ≤ 1 := by
  rw [norm_neg]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  simp

private lemma norm_pi_single_aux {n : ℕ} (i : Fin n) (c : ℂ) :
    ‖(Pi.single i c : Fin n → ℂ)‖ = ‖c‖ := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg c)]
    intro j
    by_cases h : j = i
    · subst h; simp
    · rw [Pi.single_eq_of_ne h]; simp
  · have h1 := norm_le_pi_norm (Pi.single i c : Fin n → ℂ) i
    rwa [Pi.single_eq_same] at h1

private lemma norm_dCoord_le_fderiv_aux {n : ℕ} (i : Fin n) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) : ‖Work.CR.Flat.dCoord i u z‖ ≤ ‖fderiv ℝ u z‖ := by
  have h1 : ‖(fderiv ℝ u z) (Pi.single i (1 : ℂ))‖ ≤ ‖fderiv ℝ u z‖ := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u z) (Pi.single i (1 : ℂ))
    rw [norm_pi_single_aux, norm_one, mul_one] at h
    exact h
  have h2 : ‖Complex.I * (fderiv ℝ u z) (Pi.single i Complex.I)‖ ≤ ‖fderiv ℝ u z‖ := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u z) (Pi.single i Complex.I)
    rw [norm_pi_single_aux, Complex.norm_I, mul_one] at h
    calc ‖Complex.I * (fderiv ℝ u z) (Pi.single i Complex.I)‖
        = ‖(fderiv ℝ u z) (Pi.single i Complex.I)‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖fderiv ℝ u z‖ := h
  rw [Work.CR.Flat.dCoord]
  calc ‖(1 / 2 : ℂ) * ((fderiv ℝ u z) (Pi.single i 1)
        - Complex.I * (fderiv ℝ u z) (Pi.single i Complex.I))‖
      = (1 / 2 : ℝ) * ‖(fderiv ℝ u z) (Pi.single i 1)
          - Complex.I * (fderiv ℝ u z) (Pi.single i Complex.I)‖ := by
        rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
    _ ≤ (1 / 2 : ℝ) * (‖(fderiv ℝ u z) (Pi.single i 1)‖
          + ‖Complex.I * (fderiv ℝ u z) (Pi.single i Complex.I)‖) := by
        refine mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (‖fderiv ℝ u z‖ + ‖fderiv ℝ u z‖) := by linarith
    _ = ‖fderiv ℝ u z‖ := by ring

private lemma norm_bmKernel_le_one_aux {n : ℕ} (hn : 0 < n) (k : Fin n) {y : Fin n → ℂ}
    (hy : 1 ≤ eucNorm y) : ‖bmKernel k y‖ ≤ 1 := by
  have hypos : 0 < eucNorm y := by linarith
  rw [norm_bmKernel]
  have h2 : ‖y k‖ ≤ eucNorm y := bmCz.norm_apply_le_eucNorm' y k
  have h3 : eucNorm y ≤ (eucNorm y) ^ (2 * n) := by
    have hn1 : (1 : ℕ) ≤ 2 * n := by omega
    calc eucNorm y = (eucNorm y) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (eucNorm y) ^ (2 * n) := pow_le_pow_right₀ hy hn1
  calc ‖y k‖ / eucNorm y ^ (2 * n) ≤ eucNorm y / eucNorm y ^ (2 * n) :=
        div_le_div_of_nonneg_right h2 (by positivity)
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h3

private lemma norm_kernShiftDeriv_le_aux {n : ℕ} (k : Fin n) (F : (Fin n → ℂ) → ℂ)
    (z a : Fin n → ℂ) :
    ‖kernShiftDeriv k F z a‖ ≤ ‖F a‖ * ‖fderiv ℝ (bmKernel k) (a - z)‖ := by
  rw [kernShiftDeriv]
  calc ‖(ContinuousLinearMap.mul ℝ ℂ (F a)).comp
        ((fderiv ℝ (bmKernel k) (a - z)).comp (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))))‖
      ≤ ‖ContinuousLinearMap.mul ℝ ℂ (F a)‖
          * ‖(fderiv ℝ (bmKernel k) (a - z)).comp (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖F a‖ * (‖fderiv ℝ (bmKernel k) (a - z)‖
          * ‖-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))‖) :=
        mul_le_mul (ContinuousLinearMap.opNorm_mul_apply_le (𝕜 := ℝ) (R := ℂ) (F a))
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖F a‖ * (‖fderiv ℝ (bmKernel k) (a - z)‖ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left norm_neg_one_clm_le_aux
          (norm_nonneg _)) (norm_nonneg _)
    _ = ‖F a‖ * ‖fderiv ℝ (bmKernel k) (a - z)‖ := by rw [mul_one]

private lemma norm_kernShiftDeriv_sub_le_aux {n : ℕ} (k : Fin n) (F : (Fin n → ℂ) → ℂ)
    (z z' a : Fin n → ℂ) :
    ‖kernShiftDeriv k F z a - kernShiftDeriv k F z' a‖
      ≤ ‖F a‖ * ‖fderiv ℝ (bmKernel k) (a - z) - fderiv ℝ (bmKernel k) (a - z')‖ := by
  have heq : kernShiftDeriv k F z a - kernShiftDeriv k F z' a
      = (ContinuousLinearMap.mul ℝ ℂ (F a)).comp
          (((fderiv ℝ (bmKernel k) (a - z))
            - (fderiv ℝ (bmKernel k) (a - z'))).comp
              (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))) := by
    rw [kernShiftDeriv, kernShiftDeriv]
    ext v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    rw [map_sub]
  rw [heq]
  calc ‖(ContinuousLinearMap.mul ℝ ℂ (F a)).comp
        (((fderiv ℝ (bmKernel k) (a - z)) - (fderiv ℝ (bmKernel k) (a - z'))).comp
          (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))))‖
      ≤ ‖ContinuousLinearMap.mul ℝ ℂ (F a)‖
          * ‖((fderiv ℝ (bmKernel k) (a - z)) - (fderiv ℝ (bmKernel k) (a - z'))).comp
              (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖F a‖ * (‖(fderiv ℝ (bmKernel k) (a - z)) - (fderiv ℝ (bmKernel k) (a - z'))‖
          * ‖-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))‖) :=
        mul_le_mul (ContinuousLinearMap.opNorm_mul_apply_le (𝕜 := ℝ) (R := ℂ) (F a))
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖F a‖ * (‖fderiv ℝ (bmKernel k) (a - z) - fderiv ℝ (bmKernel k) (a - z')‖ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left norm_neg_one_clm_le_aux
          (norm_nonneg _)) (norm_nonneg _)
    _ = ‖F a‖ * ‖fderiv ℝ (bmKernel k) (a - z) - fderiv ℝ (bmKernel k) (a - z')‖ := by
        rw [mul_one]

private lemma integrable_eucBall_indicator_aux {n : ℕ} (r : ℝ) (c : ℝ) :
    Integrable (fun a : Fin n → ℂ => (eucBall (n := n) r).indicator (fun _ => c) a) volume := by
  rw [integrable_indicator_iff (measurableSet_eucBall r)]
  refine integrableOn_const (C := c) ?_
  exact ne_of_lt (lt_of_le_of_lt (measure_mono eucBall_subset_eucClosedBall)
    (isCompact_eucClosedBall r).measure_lt_top)

variable {n : ℕ}

/-- **Far-field differentiability.**  For `x` in the far region, the integral
`x ↦ ∫ a, bmKernel k (a - x) * F a` is differentiable with derivative the integral of
`kernShiftDeriv k F x`. -/
private lemma hasFDerivAt_kernelIntegral_aux (hn : 0 < n) {R S : ℝ} (hR : 0 ≤ R)
    (hSR : R + 2 ≤ S) {F : (Fin n → ℂ) → ℂ} (hFmeas : Measurable F)
    (hFsupp : ∀ z, R ≤ ‖z‖ → F z = 0) {A : ℝ} (hA : 0 ≤ A) (hFb : ∀ z, ‖F z‖ ≤ A)
    {z : Fin n → ℂ} (hz : S ≤ ‖z‖) (k : Fin n) :
    HasFDerivAt (fun x => ∫ a, bmKernel k (a - x) * F a) (∫ a, kernShiftDeriv k F z a) z := by
  obtain ⟨Cker, hCkerpos, hCker⟩ := norm_fderiv_bmKernel_le_aux hn
  set rB : ℝ := Real.sqrt n * (R + 1) with hrBdef
  set s : Set (Fin n → ℂ) := Metric.closedBall z 1 with hsdef
  have hsnhds : s ∈ nhds z := Metric.closedBall_mem_nhds z one_pos
  have hzge : ∀ x ∈ s, S - 1 ≤ ‖x‖ := by
    intro x hx
    have h1 : ‖z - x‖ ≤ 1 := by
      have h := Metric.mem_closedBall.mp hx
      simpa [dist_eq_norm, norm_sub_rev] using h
    have h2 : ‖z‖ ≤ ‖x‖ + ‖z - x‖ := by
      have h3 := norm_add_le x (z - x)
      rwa [add_sub_cancel] at h3
    linarith
  have hfar : ∀ a x, F a ≠ 0 → x ∈ s → 1 ≤ eucNorm (a - x) := by
    intro a x ha hx
    have haR : ‖a‖ < R := not_le.mp fun hc => ha (hFsupp a hc)
    have hxS : S - 1 ≤ ‖x‖ := hzge x hx
    have h1 : ‖x‖ - ‖a‖ ≤ ‖a - x‖ := by
      have h2 := abs_norm_sub_norm_le x a
      have h3 : ‖x‖ - ‖a‖ ≤ |‖x‖ - ‖a‖| := le_abs_self _
      have h4 : ‖x - a‖ = ‖a - x‖ := norm_sub_rev x a
      linarith [h2, h3, h4]
    calc (1 : ℝ) ≤ ‖x‖ - ‖a‖ := by linarith
      _ ≤ ‖a - x‖ := h1
      _ ≤ eucNorm (a - x) := pi_norm_le_eucNorm _
  have hsupp_mem : ∀ a, F a ≠ 0 → a ∈ eucBall (n := n) rB := by
    intro a ha
    have haR : ‖a‖ < R := not_le.mp fun hc => ha (hFsupp a hc)
    rw [mem_eucBall, hrBdef]
    have h1 : eucNorm a ≤ Real.sqrt n * ‖a‖ := bmCz.eucNorm_le_sqrt_mul_norm a
    have h2 : Real.sqrt n * ‖a‖ < Real.sqrt n * (R + 1) :=
      mul_lt_mul_of_pos_left (by linarith) (Real.sqrt_pos.mpr (by exact_mod_cast hn))
    linarith
  set bound : (Fin n → ℂ) → ℝ := fun a =>
    (1 + Cker) * (A * (eucBall (n := n) rB).indicator (fun _ => (1 : ℝ)) a) with hbounddef
  have hbound_int : Integrable bound volume := by
    rw [hbounddef]
    exact ((integrable_eucBall_indicator_aux rB (1:ℝ)).const_mul A).const_mul (1 + Cker)
  have hbound_nn : ∀ a, 0 ≤ bound a := by
    intro a
    rw [hbounddef]
    exact mul_nonneg (by positivity) (mul_nonneg hA (Set.indicator_nonneg (fun _ _ => zero_le_one) a))
  have hCker1 : 0 ≤ 1 + Cker := by linarith
  have hbnd : ∀ᵐ a ∂volume, ∀ x ∈ s, ‖kernShiftDeriv k F x a‖ ≤ bound a := by
    refine Filter.Eventually.of_forall fun a x hx => ?_
    show ‖kernShiftDeriv k F x a‖ ≤ (1 + Cker) * (A * (eucBall (n := n) rB).indicator (fun _ => (1:ℝ)) a)
    by_cases ha : F a = 0
    · rw [show kernShiftDeriv k F x a = 0 from by rw [kernShiftDeriv, ha]; simp, norm_zero]
      exact hbound_nn a
    · have hmem : a ∈ eucBall (n := n) rB := hsupp_mem a ha
      rw [Set.indicator_of_mem hmem, mul_one]
      have hd : 1 ≤ eucNorm (a - x) := hfar a x ha hx
      have hne : a - x ≠ 0 := by
        intro h0
        have h1 : eucNorm (a - x) = 0 := by rw [h0, eucNorm_zero]
        linarith
      have h2 : ‖fderiv ℝ (bmKernel k) (a - x)‖ ≤ Cker * (eucNorm (a - x)) ^ (-(2 * (n : ℝ))) :=
        hCker k (a - x) hne
      have h3 : (eucNorm (a - x)) ^ (-(2 * (n : ℝ))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hd (by push_cast; linarith)
      have h4 : Cker * (eucNorm (a - x)) ^ (-(2 * (n : ℝ))) ≤ Cker := by
        simpa using mul_le_mul_of_nonneg_left h3 hCkerpos.le
      calc ‖kernShiftDeriv k F x a‖
          ≤ ‖F a‖ * ‖fderiv ℝ (bmKernel k) (a - x)‖ := norm_kernShiftDeriv_le_aux k F x a
        _ ≤ A * (Cker * (eucNorm (a - x)) ^ (-(2 * (n : ℝ)))) :=
            mul_le_mul (hFb a) h2 (norm_nonneg _) hA
        _ ≤ A * Cker := mul_le_mul_of_nonneg_left h4 hA
        _ ≤ (1 + Cker) * A := by nlinarith [hA, hCkerpos]
  have hint : Integrable (fun a => bmKernel k (a - z) * F a) volume := by
    refine Integrable.mono' hbound_int ?_ ?_
    · exact (((measurable_bmKernel_aux k).comp
        (measurable_id.sub measurable_const)).mul hFmeas).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun a => ?_
      by_cases ha : F a = 0
      · rw [ha, mul_zero, norm_zero]
        exact hbound_nn a
      · have hmem : a ∈ eucBall (n := n) rB := hsupp_mem a ha
        have hd : 1 ≤ eucNorm (a - z) := hfar a z ha (Metric.mem_closedBall_self zero_le_one)
        have h2 : ‖bmKernel k (a - z)‖ ≤ 1 := norm_bmKernel_le_one_aux hn k hd
        have h3 : bound a = (1 + Cker) * A := by
          show (1 + Cker) * (A * (eucBall (n := n) rB).indicator (fun _ => (1:ℝ)) a) = (1+Cker) * A
          rw [Set.indicator_of_mem hmem, mul_one]
        rw [h3]
        calc ‖bmKernel k (a - z) * F a‖ = ‖bmKernel k (a - z)‖ * ‖F a‖ := norm_mul _ _
          _ ≤ 1 * A := mul_le_mul h2 (hFb a) (norm_nonneg _) zero_le_one
          _ ≤ (1 + Cker) * A := by nlinarith [hA, hCkerpos]
  have hF'_meas : AEStronglyMeasurable (fun a => kernShiftDeriv k F z a) volume :=
    (measurable_kernShiftDeriv k hFmeas z).aestronglyMeasurable
  have hdiff : ∀ᵐ a ∂volume, ∀ x ∈ s,
      HasFDerivAt (fun x => bmKernel k (a - x) * F a) (kernShiftDeriv k F x a) x := by
    refine Filter.Eventually.of_forall fun a x hx => ?_
    by_cases ha : F a = 0
    · have hfun : (fun x : Fin n → ℂ => bmKernel k (a - x) * F a) = fun _ => 0 := by
        funext y; rw [ha, mul_zero]
      have hd : kernShiftDeriv k F x a = 0 := by
        rw [kernShiftDeriv, ha]; simp
      rw [hfun, hd]
      exact hasFDerivAt_const (c := (0 : ℂ)) x
    · have hne : a - x ≠ 0 := by
        intro h0
        have h1 : eucNorm (a - x) = 0 := by rw [h0, eucNorm_zero]
        linarith [hfar a x ha hx]
      have hshift : HasFDerivAt (fun y : Fin n → ℂ => a - y)
          (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))) x :=
        (hasFDerivAt_id (𝕜 := ℝ) x).const_sub a
      have hb := bmCz.hasFDerivAt_bmKernel k hne
      have hk : HasFDerivAt (fun y : Fin n → ℂ => bmKernel k (a - y))
          ((fderiv ℝ (bmKernel k) (a - x)).comp (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))) x := by
        have h2 : HasFDerivAt (fun y : Fin n → ℂ => bmKernel k (a - y))
            ((bmCz.bmKernelFDeriv k (a - x)).comp (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))) x :=
          hb.comp x hshift
        rw [← hb.fderiv] at h2
        exact h2
      have hmul := hk.mul_const (F a)
      have heq : (F a) • ((fderiv ℝ (bmKernel k) (a - x)).comp
            (-(1 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))) = kernShiftDeriv k F x a := by
        rw [kernShiftDeriv]
        ext v
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
          ContinuousLinearMap.mul_apply']
      rwa [heq] at hmul
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F := fun x a => bmKernel k (a - x) * F a)
    (F' := fun x a => kernShiftDeriv k F x a)
    (x₀ := z) (bound := bound) (s := s)
    hsnhds (Filter.Eventually.of_forall fun x => (((measurable_bmKernel_aux k).comp
      (measurable_id.sub measurable_const)).mul hFmeas).aestronglyMeasurable)
    hint hF'_meas hbnd hbound_int hdiff


private lemma one_le_sqrt_aux {n : ℕ} (hn : 0 < n) : 1 ≤ Real.sqrt n := by
  have h2 : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have h3 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [Real.sqrt_nonneg n]

private lemma mem_eucBall_of_support_aux {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 ≤ R)
    {F : (Fin n → ℂ) → ℂ} (hsupp : ∀ z, R ≤ ‖z‖ → F z = 0) {a : Fin n → ℂ} (ha : F a ≠ 0) :
    a ∈ eucBall (n := n) (Real.sqrt n * (R + 1)) := by
  rw [mem_eucBall]
  have haR : ‖a‖ < R := not_le.mp fun hc => ha (hsupp a hc)
  have h1 : eucNorm a ≤ Real.sqrt n * ‖a‖ := bmCz.eucNorm_le_sqrt_mul_norm a
  have h2 : Real.sqrt n * ‖a‖ < Real.sqrt n * (R + 1) :=
    mul_lt_mul_of_pos_left (by linarith) (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  linarith

private lemma one_le_eucNorm_sub_of_support_aux {n : ℕ} {R S : ℝ} (hSR : R + 2 ≤ S)
    {F : (Fin n → ℂ) → ℂ} (hsupp : ∀ z, R ≤ ‖z‖ → F z = 0) {a x : Fin n → ℂ}
    (ha : F a ≠ 0) (hx : S - 1 ≤ ‖x‖) : 1 ≤ eucNorm (a - x) := by
  have haR : ‖a‖ < R := not_le.mp fun hc => ha (hsupp a hc)
  have h1 : ‖x‖ - ‖a‖ ≤ ‖a - x‖ := by
    have h2 := abs_norm_sub_norm_le x a
    have h3 : ‖x‖ - ‖a‖ ≤ |‖x‖ - ‖a‖| := le_abs_self _
    have h4 : ‖x - a‖ = ‖a - x‖ := norm_sub_rev x a
    linarith [h2, h3, h4]
  calc (1 : ℝ) ≤ ‖x‖ - ‖a‖ := by linarith
    _ ≤ ‖a - x‖ := h1
    _ ≤ eucNorm (a - x) := pi_norm_le_eucNorm _

private lemma norm_dCoord_sub_le_fderiv_sub_aux {n : ℕ} (i : Fin n) (u : (Fin n → ℂ) → ℂ)
    (z z' : Fin n → ℂ) :
    ‖Work.CR.Flat.dCoord i u z - Work.CR.Flat.dCoord i u z'‖
      ≤ ‖fderiv ℝ u z - fderiv ℝ u z'‖ := by
  have h1 : ‖(fderiv ℝ u z - fderiv ℝ u z') (Pi.single i (1 : ℂ))‖
      ≤ ‖fderiv ℝ u z - fderiv ℝ u z'‖ := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u z - fderiv ℝ u z') (Pi.single i (1:ℂ))
    rw [norm_pi_single_aux, norm_one, mul_one] at h
    exact h
  have h2 : ‖Complex.I * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i Complex.I))‖
      ≤ ‖fderiv ℝ u z - fderiv ℝ u z'‖ := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u z - fderiv ℝ u z') (Pi.single i Complex.I)
    rw [norm_pi_single_aux, Complex.norm_I, mul_one] at h
    calc ‖Complex.I * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i Complex.I))‖
        = ‖(fderiv ℝ u z - fderiv ℝ u z') (Pi.single i Complex.I)‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖fderiv ℝ u z - fderiv ℝ u z'‖ := h
  have heq : Work.CR.Flat.dCoord i u z - Work.CR.Flat.dCoord i u z'
      = (1 / 2 : ℂ) * (((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i 1))
          - Complex.I * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i Complex.I))) := by
    rw [Work.CR.Flat.dCoord, Work.CR.Flat.dCoord]
    simp only [sub_apply]
    ring
  rw [heq]
  calc ‖(1 / 2 : ℂ) * (((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i 1))
        - Complex.I * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i Complex.I)))‖
      = (1 / 2 : ℝ) * ‖((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i 1))
          - Complex.I * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i Complex.I))‖ := by
        rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
    _ ≤ (1 / 2 : ℝ) * (‖((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i 1))‖
          + ‖Complex.I * ((fderiv ℝ u z - fderiv ℝ u z') (Pi.single i Complex.I))‖) := by
        refine mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (‖fderiv ℝ u z - fderiv ℝ u z'‖
          + ‖fderiv ℝ u z - fderiv ℝ u z'‖) := by linarith
    _ = ‖fderiv ℝ u z - fderiv ℝ u z'‖ := by ring

/-- **Far-field bound.**  For uniformly bounded measurable data supported in the ball `‖z‖ ≤ R`,
the `(1,0)`-derivative of the Bochner–Martinelli potential is bounded and `α`-Hölder in the far
region `‖z‖ ≥ 4(√n (R+1)) + 4`; the constants only involve `n`, `R` and `α`. -/
private lemma far_bound_aux {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ) (A : Fin n → ℝ),
      (∀ j, 0 ≤ A j) → (∀ j, Measurable (F j)) →
      (∀ j z, R ≤ ‖z‖ → F j z = 0) → (∀ j z, ‖F j z‖ ≤ A j) →
      ∀ i : Fin n,
        (∀ z : Fin n → ℂ, 4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z‖ →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z‖
            ≤ C * ∑ j, A j) ∧
        (∀ z z' : Fin n → ℂ, 4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z‖ →
          4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z'‖ →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
            ≤ C * ‖z - z'‖ ^ α * ∑ j, A j) := by
  obtain ⟨Cker, hCkerpos, hCker⟩ := norm_fderiv_bmKernel_le_aux hn
  obtain ⟨Cdif, hCdifpos, hCdif⟩ := norm_fderiv_bmKernel_sub_le_aux hn
  have hsqrt1 : 1 ≤ Real.sqrt n := one_le_sqrt_aux hn
  have hsqrtnn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  set S : ℝ := 4 * (Real.sqrt n * (R + 1)) + 4 with hSdef
  have hSR2 : R + 2 ≤ S := by
    rw [hSdef]
    have h2 : R ≤ Real.sqrt n * (R + 1) := by
      calc R ≤ 1 * (R + 1) := by linarith
        _ ≤ Real.sqrt n * (R + 1) := mul_le_mul_of_nonneg_right hsqrt1 (by linarith)
    linarith
  set S' : ℝ := Real.sqrt n * (R + 1) with hS'def
  set V : ℝ := (volume (eucBall (n := n) S')).toReal with hVdef
  have hVnn : 0 ≤ V := ENNReal.toReal_nonneg
  set Cs : ℝ := Cker * V with hCsdef
  set Ch : ℝ := Cdif * V with hChdef
  have hCsnn : 0 ≤ Cs := by rw [hCsdef]; exact mul_nonneg hCkerpos.le hVnn
  have hChnn : 0 ≤ Ch := by
    rw [hChdef]; exact mul_nonneg hCdifpos.le hVnn
  set Cfin : ℝ := 2 * Cs + Ch * (Real.sqrt n + 1) + 1 with hCfindef
  have hCs_le : Cs ≤ Cfin := by
    rw [hCfindef]; nlinarith [hCsnn, hChnn, hsqrtnn]
  have hCh_le : Ch * (Real.sqrt n) ≤ Cfin := by
    rw [hCfindef]; nlinarith [hCsnn, hChnn, hsqrtnn]
  have h2Cs_le : 2 * Cs ≤ Cfin := by rw [hCfindef]; nlinarith [hCsnn, hChnn, hsqrtnn]
  refine ⟨Cfin, by rw [hCfindef]; linarith, ?_⟩
  intro F A hA hFmeas hsupp hFbnd i
  have hsumA : 0 ≤ ∑ j, A j := Finset.sum_nonneg fun j _ => hA j
  have hCfin0 : 0 ≤ Cfin := by rw [hCfindef]; linarith
  have hbm : Work.CR.Flat.Cauchy.bmPotential F
      = fun z => ∑ k, ∫ a, bmKernel k (a - z) * F k a := by
    funext z; rfl
  have hfd : ∀ z, S ≤ ‖z‖ →
      fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential F) z
        = ∑ k, ∫ a, kernShiftDeriv k (F k) z a := by
    intro z hz
    have h1 : HasFDerivAt (Work.CR.Flat.Cauchy.bmPotential F)
        (∑ k, ∫ a, kernShiftDeriv k (F k) z a) z := by
      have hsum := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (x := z)
        fun k _ => hasFDerivAt_kernelIntegral_aux hn hR hSR2 (hFmeas k) (hsupp k) (hA k)
          (hFbnd k) hz k
      have hfun : (∑ i, fun x : Fin n → ℂ => ∫ a, bmKernel i (a - x) * F i a)
          = Work.CR.Flat.Cauchy.bmPotential F := by
        funext y
        rw [Finset.sum_apply]
        rfl
      rw [hfun] at hsum
      exact hsum
    exact h1.fderiv
  have hderiv_bound : ∀ k (z : Fin n → ℂ), S ≤ ‖z‖ → ∀ a,
      ‖kernShiftDeriv k (F k) z a‖
        ≤ Cker * (A k * (eucBall (n := n) S').indicator (fun _ => (1 : ℝ)) a) := by
    intro k z hz a
    by_cases ha : F k a = 0
    · rw [show kernShiftDeriv k (F k) z a = 0 from by rw [kernShiftDeriv, ha]; simp, norm_zero]
      exact mul_nonneg hCkerpos.le (mul_nonneg (hA k)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) a))
    · have hmem : a ∈ eucBall (n := n) S' := mem_eucBall_of_support_aux hn hR (hsupp k) ha
      rw [Set.indicator_of_mem hmem, mul_one]
      have hd : 1 ≤ eucNorm (a - z) :=
        one_le_eucNorm_sub_of_support_aux hSR2 (hsupp k) ha (by linarith)
      have hne : a - z ≠ 0 := by
        intro h0; rw [h0, eucNorm_zero] at hd; linarith
      have h2 : ‖fderiv ℝ (bmKernel k) (a - z)‖ ≤ Cker * (eucNorm (a - z)) ^ (-(2 * (n : ℝ))) :=
        hCker k (a - z) hne
      have h3 : (eucNorm (a - z)) ^ (-(2 * (n : ℝ))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hd (by push_cast; linarith)
      have h4 : Cker * (eucNorm (a - z)) ^ (-(2 * (n : ℝ))) ≤ Cker := by
        simpa using mul_le_mul_of_nonneg_left h3 hCkerpos.le
      calc ‖kernShiftDeriv k (F k) z a‖
          ≤ ‖F k a‖ * ‖fderiv ℝ (bmKernel k) (a - z)‖ :=
            norm_kernShiftDeriv_le_aux k (F k) z a
        _ ≤ A k * (Cker * (eucNorm (a - z)) ^ (-(2 * (n : ℝ)))) :=
            mul_le_mul (hFbnd k a) h2 (norm_nonneg _) (hA k)
        _ ≤ A k * Cker := mul_le_mul_of_nonneg_left h4 (hA k)
        _ = Cker * A k := by ring
  have hkern_int : ∀ k (z : Fin n → ℂ), S ≤ ‖z‖ →
      Integrable (fun a => kernShiftDeriv k (F k) z a) volume := by
    intro k z hz
    refine Integrable.mono' (g := fun a => Cker * (A k *
        (eucBall (n := n) S').indicator (fun _ => (1 : ℝ)) a)) ?_ ?_ ?_
    · exact ((integrable_eucBall_indicator_aux S' (1:ℝ)).const_mul (A k)).const_mul Cker
    · exact (measurable_kernShiftDeriv k (hFmeas k) z).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun a => hderiv_bound k z hz a
  have hIntInd : ∫ a : Fin n → ℂ, (eucBall (n := n) S').indicator (fun _ => (1 : ℝ)) a = V := by
    show ∫ a : Fin n → ℂ, (eucBall (n := n) S').indicator (fun _ => (1 : ℝ)) a
      = (volume (eucBall (n := n) S')).toReal
    exact MeasureTheory.integral_indicator_one (measurableSet_eucBall S')
  have hsup : ∀ z, S ≤ ‖z‖ →
      ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z‖ ≤ Cs * ∑ j, A j := by
    intro z hz
    have hL := hfd z hz
    have hk : ∀ k : Fin n, ‖∫ a, kernShiftDeriv k (F k) z a‖ ≤ Cker * (A k * V) := by
      intro k
      have hgint : Integrable (fun a => Cker * (A k *
          (eucBall (n := n) S').indicator (fun _ => (1 : ℝ)) a)) volume :=
        ((integrable_eucBall_indicator_aux S' (1:ℝ)).const_mul (A k)).const_mul Cker
      refine le_trans (MeasureTheory.norm_integral_le_of_norm_le hgint
        (Filter.Eventually.of_forall fun a => hderiv_bound k z hz a)) ?_
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hIntInd]
    calc ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z‖
        ≤ ‖fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential F) z‖ :=
          norm_dCoord_le_fderiv_aux i _ z
      _ = ‖∑ k, ∫ a, kernShiftDeriv k (F k) z a‖ := by rw [hL]
      _ ≤ ∑ k, ‖∫ a, kernShiftDeriv k (F k) z a‖ := norm_sum_le _ _
      _ ≤ ∑ k, Cker * (A k * V) := Finset.sum_le_sum fun k _ => hk k
      _ = Cker * V * ∑ k, A k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = Cs * ∑ k, A k := by rw [hCsdef]
  have hhol : ∀ z z', S ≤ ‖z‖ → S ≤ ‖z'‖ →
      ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
        - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
        ≤ Cfin * ‖z - z'‖ ^ α * ∑ j, A j := by
    intro z z' hz hz'
    have hL := hfd z hz
    have hL' := hfd z' hz'
    have hred : ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
        - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
        ≤ ‖∑ k, ((∫ a, kernShiftDeriv k (F k) z a) - (∫ a, kernShiftDeriv k (F k) z' a))‖ := by
      refine le_trans (norm_dCoord_sub_le_fderiv_sub_aux i _ z z') ?_
      rw [hL, hL', Finset.sum_sub_distrib]
    by_cases hclose : ‖z - z'‖ ≤ 1
    · have hznn : 0 ≤ ‖z - z'‖ := norm_nonneg _
      have hαle : ‖z - z'‖ ≤ ‖z - z'‖ ^ α := by
        rcases eq_or_lt_of_le hznn with h0 | hpos
        · rw [← h0]
          exact Real.rpow_nonneg (le_refl (0:ℝ)) α
        · simpa using Real.rpow_le_rpow_of_exponent_ge hpos hclose hα1.le
      have heuc_le : eucNorm (z - z') ≤ Real.sqrt n * ‖z - z'‖ := bmCz.eucNorm_le_sqrt_mul_norm _
      have hkey : ∀ k : Fin n,
          ‖(∫ a, kernShiftDeriv k (F k) z a) - (∫ a, kernShiftDeriv k (F k) z' a)‖
            ≤ Cdif * eucNorm (z - z') * (A k * V) := by
        intro k
        rw [← MeasureTheory.integral_sub (hkern_int k z hz) (hkern_int k z' hz')]
        have hgint : Integrable (fun a => Cdif * eucNorm (z - z') * (A k *
            (eucBall (n := n) S').indicator (fun _ => (1 : ℝ)) a)) volume :=
          (((integrable_eucBall_indicator_aux S' (1:ℝ))).const_mul (A k)).const_mul
            (Cdif * eucNorm (z - z'))
        refine le_trans (MeasureTheory.norm_integral_le_of_norm_le hgint
          (Filter.Eventually.of_forall fun a => ?_)) ?_
        · by_cases ha : F k a = 0
          · rw [show kernShiftDeriv k (F k) z a = 0 from by rw [kernShiftDeriv, ha]; simp,
              show kernShiftDeriv k (F k) z' a = 0 from by rw [kernShiftDeriv, ha]; simp,
              sub_zero, norm_zero]
            exact mul_nonneg (mul_nonneg hCdifpos.le (eucNorm_nonneg _))
              (mul_nonneg (hA k) (Set.indicator_nonneg (fun _ _ => zero_le_one) a))
          · have hmem : a ∈ eucBall (n := n) S' := mem_eucBall_of_support_aux hn hR (hsupp k) ha
            rw [Set.indicator_of_mem hmem, mul_one]
            have hd : 1 ≤ eucNorm (a - z) :=
              one_le_eucNorm_sub_of_support_aux hSR2 (hsupp k) ha (by linarith)
            have hdz : 2 * eucNorm (z' - z) ≤ eucNorm (a - z) := by
              have h1 : eucNorm (z' - z) ≤ Real.sqrt n * ‖z' - z‖ :=
                bmCz.eucNorm_le_sqrt_mul_norm _
              have h2 : ‖z' - z‖ ≤ 1 := by rw [norm_sub_rev]; exact hclose
              have h3 : Real.sqrt n * ‖z' - z‖ ≤ Real.sqrt n :=
                by simpa using mul_le_mul_of_nonneg_left h2 hsqrtnn
              have haR : ‖a‖ < R := not_le.mp fun hc => ha (hsupp k a hc)
              have hSR' : 2 * Real.sqrt n ≤ S - R := by
                rw [hSdef, hS'def]
                have h12 : 0 ≤ R * (4 * Real.sqrt n - 1) :=
                  mul_nonneg hR (by linarith)
                nlinarith [h12, hsqrt1, hsqrtnn]
              have h8 : ‖z‖ - ‖a‖ ≤ ‖a - z‖ := by
                have h9 := abs_norm_sub_norm_le z a
                have h10 : ‖z‖ - ‖a‖ ≤ |‖z‖ - ‖a‖| := le_abs_self _
                have h11 : ‖z - a‖ = ‖a - z‖ := norm_sub_rev z a
                linarith [h9, h10, h11]
              have h9 : 2 * Real.sqrt n ≤ ‖a - z‖ := by
                have hRz : R ≤ ‖z‖ := le_trans (by linarith [hSR2]) hz
                linarith
              have h10 : 2 * Real.sqrt n ≤ eucNorm (a - z) := le_trans h9 (pi_norm_le_eucNorm _)
              linarith
            have hne : a - z ≠ 0 := by
              intro h0; rw [h0, eucNorm_zero] at hd; linarith
            have h3 := hCdif k (a - z) (z' - z) hdz
            rw [show (a - z) - (z' - z) = a - z' by ring, norm_sub_rev] at h3
            have h4 : (eucNorm (a - z)) ^ (-(2 * (n : ℝ) + 1)) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos hd (by push_cast; linarith)
            calc ‖kernShiftDeriv k (F k) z a - kernShiftDeriv k (F k) z' a‖
                ≤ ‖F k a‖ * ‖fderiv ℝ (bmKernel k) (a - z) - fderiv ℝ (bmKernel k) (a - z')‖ :=
                  norm_kernShiftDeriv_sub_le_aux k (F k) z z' a
              _ ≤ ‖F k a‖ * (Cdif * eucNorm (z' - z)
                    * (eucNorm (a - z)) ^ (-(2 * (n : ℝ) + 1))) :=
                  mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
              _ ≤ A k * (Cdif * eucNorm (z - z') * 1) := by
                  refine mul_le_mul (hFbnd k a) ?_
                    (mul_nonneg (mul_nonneg hCdifpos.le (eucNorm_nonneg _))
                      (Real.rpow_nonneg (eucNorm_nonneg _) _)) (hA k)
                  calc Cdif * eucNorm (z' - z) * (eucNorm (a - z)) ^ (-(2 * (n : ℝ) + 1))
                      ≤ Cdif * eucNorm (z' - z) * 1 :=
                        mul_le_mul_of_nonneg_left h4 (mul_nonneg hCdifpos.le (eucNorm_nonneg _))
                    _ = Cdif * eucNorm (z - z') * 1 := by
                        rw [show z' - z = -(z - z') by ring, eucNorm_neg]
              _ = Cdif * eucNorm (z - z') * A k := by ring
        · have hI2 : ∫ a : Fin n → ℂ, Cdif * eucNorm (z - z') * (A k *
              (eucBall (n := n) S').indicator (fun _ => (1 : ℝ)) a)
              = Cdif * eucNorm (z - z') * (A k * V) := by
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hIntInd]
          exact le_of_eq hI2
      calc ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
          ≤ ‖∑ k, ((∫ a, kernShiftDeriv k (F k) z a)
              - (∫ a, kernShiftDeriv k (F k) z' a))‖ := hred
        _ ≤ ∑ k, ‖(∫ a, kernShiftDeriv k (F k) z a)
              - (∫ a, kernShiftDeriv k (F k) z' a)‖ := norm_sum_le _ _
        _ ≤ ∑ k, Cdif * eucNorm (z - z') * (A k * V) := Finset.sum_le_sum fun k _ => hkey k
        _ = Cdif * eucNorm (z - z') * V * ∑ k, A k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ = Ch * eucNorm (z - z') * ∑ k, A k := by rw [hChdef]; ring
        _ ≤ Cfin * ‖z - z'‖ ^ α * ∑ k, A k := by
            have h1 : Ch * eucNorm (z - z') * ∑ k, A k
                ≤ Ch * (Real.sqrt n * ‖z - z'‖) * ∑ k, A k :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heuc_le hChnn) hsumA
            have h2 : Ch * (Real.sqrt n * ‖z - z'‖) * ∑ k, A k
                ≤ Ch * (Real.sqrt n * ‖z - z'‖ ^ α) * ∑ k, A k :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hαle hsqrtnn) hChnn) hsumA
            have h3 : Ch * (Real.sqrt n * ‖z - z'‖ ^ α) * ∑ k, A k
                ≤ Cfin * ‖z - z'‖ ^ α * ∑ k, A k := by
              have h5 : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg hznn α
              calc Ch * (Real.sqrt n * ‖z - z'‖ ^ α) * ∑ k, A k
                  = (Ch * Real.sqrt n) * ‖z - z'‖ ^ α * ∑ k, A k := by ring
                _ ≤ Cfin * ‖z - z'‖ ^ α * ∑ k, A k := by
                    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCh_le h5) hsumA
            linarith
    · have hznn : 0 ≤ ‖z - z'‖ := norm_nonneg _
      have h1 : 1 ≤ ‖z - z'‖ := le_of_lt (not_le.mp hclose)
      have hα1' : 1 ≤ ‖z - z'‖ ^ α := Real.one_le_rpow h1 hα0.le
      calc ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
          ≤ ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z‖
            + ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖ := norm_sub_le _ _
        _ ≤ Cs * ∑ j, A j + Cs * ∑ j, A j := add_le_add (hsup z hz) (hsup z' hz')
        _ = 2 * Cs * ∑ j, A j := by ring
        _ ≤ Cfin * ‖z - z'‖ ^ α * ∑ j, A j := by
            have h4 : 2 * Cs * ∑ j, A j ≤ Cfin * ∑ j, A j :=
              mul_le_mul_of_nonneg_right h2Cs_le hsumA
            calc 2 * Cs * ∑ j, A j ≤ Cfin * ∑ j, A j := h4
              _ ≤ Cfin * (‖z - z'‖ ^ α * ∑ j, A j) := by
                  refine mul_le_mul_of_nonneg_left ?_ hCfin0
                  simpa using mul_le_mul_of_nonneg_right hα1' hsumA
              _ = Cfin * ‖z - z'‖ ^ α * ∑ j, A j := by ring
  exact ⟨fun z hz => le_trans (hsup z hz) (mul_le_mul_of_nonneg_right hCs_le hsumA),
    fun z z' hz hz' => hhol z z' hz hz'⟩


private lemma continuous_of_holder_aux {n : ℕ} {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    {g : (Fin n → ℂ) → ℂ} (hg : ∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) :
    Continuous g := by
  have hH : HolderWith (Real.toNNReal K) (Real.toNNReal α) g := by
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    refine le_trans (ENNReal.ofReal_le_ofReal (hg x y)) ?_
    rw [ENNReal.ofReal_mul hK, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα.le]
    rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal K hK, Real.coe_toNNReal α hα.le]
  exact hH.continuous (by rw [Real.toNNReal_pos]; exact hα)

/-- **Near-field bound** (from the `C^{1,α}` Schauder estimate for Hölder data). -/
private lemma near_bound_aux {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j z, R ≤ ‖z‖ → F j z = 0) →
      (∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) →
      ∀ i : Fin n,
        Work.CR.Flat.holderNorm 0 α
            (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z)
            (Work.CR.Flat.polydisc 0 (fun _ => 4 * (Real.sqrt n * (R + 1)) + 5))
          ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ := by
  set T : ℝ := 4 * (Real.sqrt n * (R + 1)) + 5 with hTdef
  obtain ⟨C₀, hC₀pos, hC₀⟩ := bmPot_holder_C0a (n := n) hn (c := (0 : Fin n → ℂ))
    (r := fun _ => 2 * T) hα0 hα1 (fun _ => by rw [hTdef]; positivity)
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro F hsupp hfin i
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 (fun _ => T) with hPdef
  set Sge : ℝ≥0∞ := ∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ with hSgedef
  have hSgtop : Sge ≠ ⊤ := by
    rw [hSgedef]
    exact ne_of_lt (WithTop.sum_lt_top.mpr fun j _ => hfin j)
  set Sg : ℝ := Sge.toReal with hSgdef
  have hSgnn : 0 ≤ Sg := ENNReal.toReal_nonneg
  have hSge : ENNReal.ofReal Sg = Sge := ENNReal.ofReal_toReal hSgtop
  have hsqrt1 : 1 ≤ Real.sqrt n := one_le_sqrt_aux hn
  have hsupp' : ∀ j z, (∃ i, (fun _ : Fin n => 2 * T) i / 2 ≤ ‖z i - (0 : Fin n → ℂ) i‖) →
      F j z = 0 := by
    intro j z h
    obtain ⟨k, hk⟩ := h
    refine hsupp j z ?_
    have hk' : T ≤ ‖z k‖ := by simpa using hk
    have h1 : ‖z k‖ ≤ ‖z‖ := norm_le_pi_norm z k
    have h2 : R ≤ T := by
      rw [hTdef]
      have h5 : R + 1 ≤ Real.sqrt n * (R + 1) := by
        calc R + 1 = 1 * (R + 1) := by ring
          _ ≤ Real.sqrt n * (R + 1) := mul_le_mul_of_nonneg_right hsqrt1 (by linarith)
      nlinarith [h5, hR]
    exact le_trans h2 (le_trans hk' h1)
  have hmain := hC₀ F hsupp' (fun j => ne_of_lt (hfin j))
  have hfun : (fun z => Work.CR.Flat.Cauchy.bmPot F z) = Work.CR.Flat.Cauchy.bmPotential F := by
    funext z; exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot F z).symm
  rw [hfun] at hmain
  rw [show (fun j : Fin n => 2 * T / 2) = (fun _ : Fin n => T) from by funext j; ring] at hmain
  have hmain' : Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P
      ≤ ENNReal.ofReal (C₀ * Sg) := by
    rw [hPdef]
    rw [← hSgedef] at hmain
    rw [← hSge, ← ENNReal.ofReal_mul hC₀pos.le] at hmain
    exact hmain
  set M : ℝ≥0∞ := ENNReal.ofReal (C₀ * Sg) with hMdef
  have hsplit := Work.NN.Core.holderNorm_one_eq α (Work.CR.Flat.Cauchy.bmPotential F) P
  have hiter1 : Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential F) P ≤ M := by
    calc Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential F) P
        ≤ Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential F) P
          + Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P :=
          le_add_of_nonneg_right zero_le
      _ ≤ (Work.CR.Flat.iterDerivNorm 0 (Work.CR.Flat.Cauchy.bmPotential F) P
            + Work.CR.Flat.holderSeminorm 0 α (Work.CR.Flat.Cauchy.bmPotential F) P)
          + (Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential F) P
            + Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P) :=
          le_add_of_nonneg_left zero_le
      _ = Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P := hsplit.symm
      _ ≤ M := by rw [hMdef]; exact hmain'
  have hsem1 : Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P ≤ M := by
    calc Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P
        ≤ Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential F) P
          + Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P :=
          le_add_of_nonneg_left zero_le
      _ ≤ (Work.CR.Flat.iterDerivNorm 0 (Work.CR.Flat.Cauchy.bmPotential F) P
            + Work.CR.Flat.holderSeminorm 0 α (Work.CR.Flat.Cauchy.bmPotential F) P)
          + (Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential F) P
            + Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P) :=
          le_add_of_nonneg_left zero_le
      _ = Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P := hsplit.symm
      _ ≤ M := by rw [hMdef]; exact hmain'
  have hPopen : IsOpen P := by rw [hPdef]; exact isOpen_polydisc 0 _
  have hiter0 : Work.CR.Flat.iterDerivNorm 0
      (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z) P ≤ M := by
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun z hz => ?_
    rw [norm_iteratedFDerivWithin_zero]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (le_trans (Work.CR.Flat.le_iterDerivNorm 1 _ P hz) hiter1)
    rw [norm_iteratedFDerivWithin_one (Work.CR.Flat.Cauchy.bmPotential F)
        (hPopen.uniqueDiffWithinAt hz),
      fderivWithin_of_isOpen hPopen hz]
    exact norm_dCoord_le_fderiv_aux i _ z
  have hsem0 : Work.CR.Flat.holderSeminorm 0 α
      (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z) P ≤ M := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub]
    have h1 : ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) x
        - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) y‖
        ≤ ‖iteratedFDerivWithin ℝ 1 (Work.CR.Flat.Cauchy.bmPotential F) P x
            - iteratedFDerivWithin ℝ 1 (Work.CR.Flat.Cauchy.bmPotential F) P y‖ := by
      refine le_trans (norm_dCoord_sub_le_fderiv_sub_aux i _ x y) ?_
      rw [← fderivWithin_of_isOpen hPopen hx, ← fderivWithin_of_isOpen hPopen hy]
      exact Work.NN.Core.norm_fderivWithin_sub_le_iteratedFDerivWithin_one
        (Work.CR.Flat.Cauchy.bmPotential F) P x y (hPopen.uniqueDiffWithinAt hx)
        (hPopen.uniqueDiffWithinAt hy)
    have hden : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    calc ENNReal.ofReal (‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) x
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal (‖iteratedFDerivWithin ℝ 1 (Work.CR.Flat.Cauchy.bmPotential F) P x
            - iteratedFDerivWithin ℝ 1 (Work.CR.Flat.Cauchy.bmPotential F) P y‖ / ‖x - y‖ ^ α) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h1 hden.le)
      _ ≤ Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential F) P :=
          Work.CR.Flat.le_holderSeminorm 1 α _ P hx hy hxy
      _ ≤ M := hsem1
  rw [Work.NN.Core.holderNorm_zero_eq]
  have hArith : M + M = ENNReal.ofReal (2 * C₀) * Sge := by
    rw [hMdef, ← ENNReal.ofReal_add (mul_nonneg hC₀pos.le hSgnn)
        (mul_nonneg hC₀pos.le hSgnn),
      ← hSge, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * C₀)]
    congr 1
    ring
  calc Work.CR.Flat.iterDerivNorm 0
        (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z) P
      + Work.CR.Flat.holderSeminorm 0 α
        (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z) P
      ≤ M + M := add_le_add hiter0 hsem0
    _ = ENNReal.ofReal (2 * C₀) * Sge := hArith
    _ = ENNReal.ofReal (2 * C₀) * ∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ := by
        rw [hSgedef]


private lemma mem_polydisc_of_norm_le_aux {n : ℕ} {S T : ℝ} (hST : S < T) {z : Fin n → ℂ}
    (hz : ‖z‖ ≤ S) : z ∈ Work.CR.Flat.polydisc 0 (fun _ : Fin n => T) := by
  rw [Work.CR.Flat.mem_polydisc]
  intro j
  have h1 : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
  simpa using lt_of_le_of_lt (le_trans h1 hz) hST

private lemma exists_segment_point_aux {n : ℕ} {S : ℝ} {x y : Fin n → ℂ}
    (hx : ‖x‖ ≤ S) (hy : S < ‖y‖) :
    ∃ x₀ : Fin n → ℂ, ‖x₀‖ = S ∧ ‖x - x₀‖ ≤ ‖x - y‖ ∧ ‖x₀ - y‖ ≤ ‖x - y‖ := by
  have hcont : Continuous fun t : ℝ => ‖x + t • (y - x)‖ := by fun_prop
  have h0 : ‖x + (0 : ℝ) • (y - x)‖ ≤ S := by simpa using hx
  have h1 : S ≤ ‖x + (1 : ℝ) • (y - x)‖ := by simpa using le_of_lt hy
  obtain ⟨t, ht, htS⟩ := (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hcont.continuousOn) ⟨h0, h1⟩
  refine ⟨x + t • (y - x), htS, ?_, ?_⟩
  · rw [show x - (x + t • (y - x)) = -(t • (y - x)) by abel, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖y - x‖ ≤ 1 * ‖y - x‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = ‖x - y‖ := by
          rw [one_mul]
          exact (norm_sub_rev x y).symm
  · rw [show (x + t • (y - x)) - y = (1 - t) • (x - y) by module, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ht.2])]
    calc (1 - t) * ‖x - y‖ ≤ 1 * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (by linarith [ht.1]) (norm_nonneg _)
      _ = ‖x - y‖ := by rw [one_mul]

theorem czB_holderNorm_bound_holder {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) →
      (∀ j, HasCompactSupport (F j)) →
      (∀ j z, R ≤ ‖z‖ → F j z = 0) →
      ∀ i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
          (Work.CR.Flat.Cauchy.bmPotential F) z) Set.univ
          ≤ ENNReal.ofReal C * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α (F j) Set.univ := by
  obtain ⟨Cnear, hCnear0, hnear⟩ := near_bound_aux hn hα0 hα1 hR
  obtain ⟨Cfar, hCfar0, hfar⟩ := far_bound_aux hn hα0 hα1 hR
  set S : ℝ := 4 * (Real.sqrt n * (R + 1)) + 4 with hSdef
  set T : ℝ := 4 * (Real.sqrt n * (R + 1)) + 5 with hTdef
  have hST : S < T := by rw [hSdef, hTdef]; linarith
  have hCnn : 0 ≤ max Cnear Cfar + (Cnear + Cfar) := by
    have h1 : 0 ≤ max Cnear Cfar := le_trans hCnear0 (le_max_left _ _)
    linarith
  refine ⟨max Cnear Cfar + (Cnear + Cfar), hCnn, ?_⟩
  intro F hfin _hcs hsupp i
  set A : Fin n → ℝ := fun j => (Work.CR.Flat.iterDerivNorm 0 (F j) Set.univ).toReal with hAdef
  set K : Fin n → ℝ := fun j => (Work.CR.Flat.holderSeminorm 0 α (F j) Set.univ).toReal with hKdef
  have hAnn : ∀ j, 0 ≤ A j := fun j => ENNReal.toReal_nonneg
  have hKnn : ∀ j, 0 ≤ K j := fun j => ENNReal.toReal_nonneg
  have hAfin : ∀ j, Work.CR.Flat.iterDerivNorm 0 (F j) Set.univ < ⊤ := fun j =>
    lt_of_le_of_lt (Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α (F j) Set.univ (le_refl 0)) (hfin j)
  have hKfin : ∀ j, Work.CR.Flat.holderSeminorm 0 α (F j) Set.univ < ⊤ := fun j =>
    lt_of_le_of_lt (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α (F j) Set.univ (le_refl 0)) (hfin j)
  have hAe : ∀ j, ENNReal.ofReal (A j) = Work.CR.Flat.iterDerivNorm 0 (F j) Set.univ :=
    fun j => ENNReal.ofReal_toReal (ne_of_lt (hAfin j))
  have hKe : ∀ j, ENNReal.ofReal (K j) = Work.CR.Flat.holderSeminorm 0 α (F j) Set.univ :=
    fun j => ENNReal.ofReal_toReal (ne_of_lt (hKfin j))
  have hb : ∀ j z, ‖F j z‖ ≤ A j := by
    intro j z
    have h1 : ENNReal.ofReal ‖F j z‖ ≤ Work.CR.Flat.iterDerivNorm 0 (F j) Set.univ := by
      rw [← norm_iteratedFDerivWithin_zero (𝕜 := ℝ) (f := F j) (s := Set.univ) (x := z)]
      exact Work.CR.Flat.le_iterDerivNorm 0 (F j) Set.univ (Set.mem_univ z)
    rw [← hAe j] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (hAnn j)).mp h1
  have hh : ∀ j x y, ‖F j x - F j y‖ ≤ K j * ‖x - y‖ ^ α := by
    intro j x y
    rcases eq_or_ne x y with rfl | hxy
    · simp [Real.zero_rpow (ne_of_gt hα0)]
    · have h1 : ENNReal.ofReal (‖F j x - F j y‖ / ‖x - y‖ ^ α)
          ≤ Work.CR.Flat.holderSeminorm 0 α (F j) Set.univ := by
        simpa [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub (F j) Set.univ x y] using
          Work.CR.Flat.le_holderSeminorm 0 α (F j) Set.univ (Set.mem_univ x) (Set.mem_univ y) hxy
      rw [← hKe j] at h1
      have h2 : ‖F j x - F j y‖ / ‖x - y‖ ^ α ≤ K j :=
        (ENNReal.ofReal_le_ofReal_iff (hKnn j)).mp h1
      calc ‖F j x - F j y‖ = (‖F j x - F j y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α := by
            rw [div_mul_cancel₀]
            exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α).ne'
        _ ≤ K j * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) α)
  have hmeas : ∀ j, Measurable (F j) :=
    fun j => (continuous_of_holder_aux hα0 (hKnn j) (hh j)).measurable
  set Sge : ℝ≥0∞ := ∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ with hSgedef
  have hSgtop : Sge < ⊤ := by
    rw [hSgedef]
    exact WithTop.sum_lt_top.mpr fun j _ => hfin j
  set Sg : ℝ := Sge.toReal with hSgdef
  have hSgnn : 0 ≤ Sg := ENNReal.toReal_nonneg
  have hSge : ENNReal.ofReal Sg = Sge := ENNReal.ofReal_toReal (ne_of_lt hSgtop)
  have hNj : ∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ = ENNReal.ofReal (A j + K j) := by
    intro j
    rw [Work.NN.Core.holderNorm_zero_eq, ← hAe j, ← hKe j,
      ← ENNReal.ofReal_add (hAnn j) (hKnn j)]
  have hSge_eq : Sge = ENNReal.ofReal (∑ j, (A j + K j)) := by
    rw [hSgedef, Finset.sum_congr rfl (fun j _ => hNj j),
      ← ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hAnn j) (hKnn j))]
  have hSgval : Sg = ∑ j, (A j + K j) := by
    rw [hSgdef, hSge_eq,
      ENNReal.toReal_ofReal (Finset.sum_nonneg fun j _ => add_nonneg (hAnn j) (hKnn j))]
  have hsumA : ∑ j, A j ≤ Sg := by
    rw [hSgval]
    exact Finset.sum_le_sum fun j _ => le_add_of_nonneg_right (hKnn j)
  set g : (Fin n → ℂ) → ℂ :=
    fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z with hgdef
  -- ### the near-field bound in real form
  have hnear' : ∀ z, ‖z‖ ≤ S → ‖g z‖ ≤ Cnear * Sg := by
    intro z hz
    have hzP : z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => T) :=
      mem_polydisc_of_norm_le_aux hST hz
    have hb0 := hnear F hsupp hfin i
    have hb1 : Work.CR.Flat.holderNorm 0 α g (Work.CR.Flat.polydisc 0 (fun _ => T))
        ≤ ENNReal.ofReal (Cnear * Sg) := by
      rw [hgdef]
      rw [← hSgedef] at hb0
      rw [← hSge, ← ENNReal.ofReal_mul hCnear0] at hb0
      exact hb0
    have h1 : ENNReal.ofReal ‖g z‖ ≤ ENNReal.ofReal (Cnear * Sg) :=
      le_trans (Work.CR.Flat.norm_apply_le_holderNorm 0 α g _ hzP) hb1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCnear0 hSgnn)).mp h1
  have hnear_hol : ∀ x y, x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => T) →
      y ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => T) → x ≠ y →
      ‖g x - g y‖ ≤ Cnear * ‖x - y‖ ^ α * Sg := by
    intro x y hx hy hxy
    have hb0 := hnear F hsupp hfin i
    have hb1 : Work.CR.Flat.holderNorm 0 α g (Work.CR.Flat.polydisc 0 (fun _ => T))
        ≤ ENNReal.ofReal (Cnear * Sg) := by
      rw [hgdef]
      rw [← hSgedef] at hb0
      rw [← hSge, ← ENNReal.ofReal_mul hCnear0] at hb0
      exact hb0
    have h1 : ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) ≤ ENNReal.ofReal (Cnear * Sg) := by
      refine le_trans ?_ (le_trans (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α g _ (le_refl 0)) hb1)
      simpa [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub g _ x y] using
        Work.CR.Flat.le_holderSeminorm 0 α g _ hx hy hxy
    have h2 : ‖g x - g y‖ / ‖x - y‖ ^ α ≤ Cnear * Sg :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCnear0 hSgnn)).mp h1
    have hden : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rw [div_le_iff₀ hden] at h2
    calc ‖g x - g y‖ ≤ (Cnear * Sg) * ‖x - y‖ ^ α := h2
      _ = Cnear * ‖x - y‖ ^ α * Sg := by ring
  -- ### the far-field bound in real form
  have hfar_sup : ∀ z, S ≤ ‖z‖ → ‖g z‖ ≤ Cfar * Sg := by
    intro z hz
    have h := (hfar F A hAnn hmeas hsupp hb i).1 z hz
    refine le_trans h (mul_le_mul_of_nonneg_left hsumA hCfar0)
  have hfar_hol : ∀ x y, S ≤ ‖x‖ → S ≤ ‖y‖ → ‖g x - g y‖ ≤ Cfar * ‖x - y‖ ^ α * Sg := by
    intro x y hx hy
    have h := (hfar F A hAnn hmeas hsupp hb i).2 x y hx hy
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left hsumA
      (mul_nonneg hCfar0 (Real.rpow_nonneg (norm_nonneg _) α))
  -- ### global bounds
  have hglob_sup : ∀ z, ‖g z‖ ≤ max Cnear Cfar * Sg := by
    intro z
    by_cases hz : ‖z‖ ≤ S
    · exact le_trans (hnear' z hz) (mul_le_mul_of_nonneg_right (le_max_left _ _) hSgnn)
    · exact le_trans (hfar_sup z (le_of_lt (not_le.mp hz)))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hSgnn)
  have hglob_hol : ∀ x y, x ≠ y → ‖g x - g y‖ ≤ (Cnear + Cfar) * ‖x - y‖ ^ α * Sg := by
    intro x y hxy
    have hxP : ∀ {w : Fin n → ℂ}, ‖w‖ ≤ S →
        w ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => T) :=
      fun hw => mem_polydisc_of_norm_le_aux hST hw
    by_cases hx : ‖x‖ ≤ S
    · by_cases hy : ‖y‖ ≤ S
      · -- both near
        have h := hnear_hol x y (hxP hx) (hxP hy) hxy
        refine le_trans h ?_
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
          (Real.rpow_nonneg (norm_nonneg _) α)) hSgnn
        linarith
      · -- x near, y far
        obtain ⟨x₀, hx₀S, hd1, hd2⟩ := exists_segment_point_aux hx (not_le.mp hy)
        have hx₀P : x₀ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => T) :=
          hxP (le_of_eq hx₀S)
        have htri : ‖g x - g y‖ ≤ ‖g x - g x₀‖ + ‖g x₀ - g y‖ := by
          have h := norm_add_le (g x - g x₀) (g x₀ - g y)
          rwa [show (g x - g x₀) + (g x₀ - g y) = g x - g y by abel] at h
        have h1 : ‖g x - g x₀‖ ≤ Cnear * ‖x - x₀‖ ^ α * Sg := by
          rcases eq_or_ne x x₀ with hxx | hxx
          · subst hxx; simp [Real.zero_rpow (ne_of_gt hα0)]
          · exact hnear_hol x x₀ (hxP hx) hx₀P hxx
        have h2 : ‖g x₀ - g y‖ ≤ Cfar * ‖x₀ - y‖ ^ α * Sg :=
          hfar_hol x₀ y (le_of_eq hx₀S.symm) (le_of_lt (not_le.mp hy))
        have hd1' : ‖x - x₀‖ ^ α ≤ ‖x - y‖ ^ α :=
          Real.rpow_le_rpow (norm_nonneg _) hd1 hα0.le
        have hd2' : ‖x₀ - y‖ ^ α ≤ ‖x - y‖ ^ α :=
          Real.rpow_le_rpow (norm_nonneg _) hd2 hα0.le
        calc ‖g x - g y‖ ≤ ‖g x - g x₀‖ + ‖g x₀ - g y‖ := htri
          _ ≤ Cnear * ‖x - x₀‖ ^ α * Sg + Cfar * ‖x₀ - y‖ ^ α * Sg := add_le_add h1 h2
          _ ≤ Cnear * ‖x - y‖ ^ α * Sg + Cfar * ‖x - y‖ ^ α * Sg := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd1' hCnear0) hSgnn
              · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2' hCfar0) hSgnn
          _ = (Cnear + Cfar) * ‖x - y‖ ^ α * Sg := by ring
    · -- x far
      by_cases hy : ‖y‖ ≤ S
      · -- y near, x far: symmetric
        obtain ⟨x₀, hx₀S, hd1, hd2⟩ := exists_segment_point_aux hy (not_le.mp hx)
        have hx₀P : x₀ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => T) :=
          hxP (le_of_eq hx₀S)
        have htri : ‖g x - g y‖ ≤ ‖g x - g x₀‖ + ‖g x₀ - g y‖ := by
          have h := norm_add_le (g x - g x₀) (g x₀ - g y)
          rwa [show (g x - g x₀) + (g x₀ - g y) = g x - g y by abel] at h
        have h1 : ‖g y - g x₀‖ ≤ Cnear * ‖y - x₀‖ ^ α * Sg := by
          rcases eq_or_ne y x₀ with hyy | hyy
          · subst hyy; simp [Real.zero_rpow (ne_of_gt hα0)]
          · exact hnear_hol y x₀ (hxP hy) hx₀P hyy
        have h2 : ‖g x₀ - g x‖ ≤ Cfar * ‖x₀ - x‖ ^ α * Sg :=
          hfar_hol x₀ x (le_of_eq hx₀S.symm) (le_of_lt (not_le.mp hx))
        have hd1' : ‖y - x₀‖ ^ α ≤ ‖y - x‖ ^ α :=
          Real.rpow_le_rpow (norm_nonneg _) hd1 hα0.le
        have hd1'' : ‖y - x₀‖ ^ α ≤ ‖x - y‖ ^ α := by
          rw [← norm_sub_rev y x]
          exact hd1'
        have hd2' : ‖x₀ - x‖ ^ α ≤ ‖y - x‖ ^ α :=
          Real.rpow_le_rpow (norm_nonneg _) hd2 hα0.le
        have hd2'' : ‖x₀ - x‖ ^ α ≤ ‖x - y‖ ^ α := by
          rw [← norm_sub_rev y x]
          exact hd2'
        calc ‖g x - g y‖ ≤ ‖g x - g x₀‖ + ‖g x₀ - g y‖ := htri
          _ = ‖g x₀ - g x‖ + ‖g y - g x₀‖ := by
              rw [norm_sub_rev (g x) (g x₀), norm_sub_rev (g x₀) (g y)]
          _ ≤ Cfar * ‖x₀ - x‖ ^ α * Sg + Cnear * ‖y - x₀‖ ^ α * Sg := add_le_add h2 h1
          _ ≤ Cfar * ‖x - y‖ ^ α * Sg + Cnear * ‖x - y‖ ^ α * Sg := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2'' hCfar0) hSgnn
              · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd1'' hCnear0) hSgnn
          _ = (Cnear + Cfar) * ‖x - y‖ ^ α * Sg := by ring
      · exact le_trans (hfar_hol x y (le_of_lt (not_le.mp hx)) (le_of_lt (not_le.mp hy)))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg
            (norm_nonneg _) α)) hSgnn)
  -- ### assembly
  have hiter : Work.CR.Flat.iterDerivNorm 0 g Set.univ
      ≤ ENNReal.ofReal (max Cnear Cfar * Sg) := by
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun z _ => ?_
    rw [norm_iteratedFDerivWithin_zero]
    exact ENNReal.ofReal_le_ofReal (hglob_sup z)
  have hsem : Work.CR.Flat.holderSeminorm 0 α g Set.univ
      ≤ ENNReal.ofReal ((Cnear + Cfar) * Sg) := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    rw [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub]
    have hden : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rw [show (‖g x - g y‖ / ‖x - y‖ ^ α) = (‖g x - g y‖ / ‖x - y‖ ^ α) from rfl]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hden]
    calc ‖g x - g y‖ ≤ (Cnear + Cfar) * ‖x - y‖ ^ α * Sg := hglob_hol x y hxy
      _ = ((Cnear + Cfar) * Sg) * ‖x - y‖ ^ α := by ring
  have hgoal : ENNReal.ofReal (max Cnear Cfar * Sg) + ENNReal.ofReal ((Cnear + Cfar) * Sg)
      = ENNReal.ofReal (max Cnear Cfar + (Cnear + Cfar)) * Sge := by
    rw [← ENNReal.ofReal_add (mul_nonneg (le_trans hCnear0 (le_max_left _ _)) hSgnn)
        (mul_nonneg (add_nonneg hCnear0 hCfar0) hSgnn),
      ← hSge, ← ENNReal.ofReal_mul hCnn]
    congr 1
    ring
  rw [Work.NN.Core.holderNorm_zero_eq]
  calc Work.CR.Flat.iterDerivNorm 0 g Set.univ + Work.CR.Flat.holderSeminorm 0 α g Set.univ
      ≤ ENNReal.ofReal (max Cnear Cfar * Sg) + ENNReal.ofReal ((Cnear + Cfar) * Sg) :=
        add_le_add hiter hsem
    _ = ENNReal.ofReal (max Cnear Cfar + (Cnear + Cfar)) * Sge := hgoal
    _ = ENNReal.ofReal (max Cnear Cfar + (Cnear + Cfar))
        * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α (F j) Set.univ := by rw [hSgedef]

end Work.NN.Core

