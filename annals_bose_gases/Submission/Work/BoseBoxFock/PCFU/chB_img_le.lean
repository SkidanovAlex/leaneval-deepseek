import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.chBimg_J_le
import Submission.Work.BoseBoxFock.PCFU.chBimg_far_tail
import Submission.Work.BoseBoxFock.PCFU.chBimg_near_d
import Submission.Work.BoseBoxFock.PCFU.chiLam_mul_le_of_alias
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

set_option autoImplicit false

/-! ## 0. `chiLam` regularity -/

lemma continuous_chiLam (ℓ : ℝ) : Continuous (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w) := by
  have hfun : (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w)
      = fun w => Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • w) := by
    funext w
    simp only [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]
  rw [hfun]
  exact Submission.BoseGases.chi_contDiff.continuous.comp (continuous_const_smul _)

lemma integrable_chiLam (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w) := by
  refine (continuous_chiLam ℓ).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall (0 : E3) (ℓ / 2))
    (isCompact_closedBall _ _) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push_neg at h
  exact hz (chiLam_eq_zero_of_half_lt hℓ h)

lemma chiLam_nonzero_le_half {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3}
    (hz : Work.BoseK15.corpusBox.chiLam ℓ z ≠ 0) : ‖z‖ ≤ ℓ / 2 := by
  by_contra h
  push_neg at h
  exact hz (chiLam_eq_zero_of_half_lt hℓ h)

/-! ## 1. zpow monotonicity helpers -/

lemma zpow_neg_five_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-(5 : ℤ)) ≤ a ^ (-(5 : ℤ)) := by
  rw [zpow_neg, zpow_neg]
  exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le ha hab) 5) (pow_pos ha 5)).mpr
    (pow_le_pow_left₀ ha.le hab 5)

lemma zpow_neg_five_le_one {a : ℝ} (ha : 1 ≤ a) : a ^ (-(5 : ℤ)) ≤ 1 := by
  rw [zpow_neg]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ ha)

/-! ## 2. lattice-norm facts -/

lemma sq_norm_latVec_le_three_sq (d : Fin 3 → ℤ) :
    ‖latVec d‖ ^ 2 ≤ 3 * ‖d‖ ^ 2 := by
  have hK : ‖d‖ = ((K d : ℕ) : ℝ) := Work.BoseBoxFock.NormEqKcast d
  have hnSq : (nSq d : ℝ) = ∑ i, ((d i).natAbs : ℝ) ^ 2 := by
    simp only [nSq, Nat.cast_sum, Nat.cast_pow]
  have hle : (nSq d : ℝ) ≤ 3 * ((K d : ℕ) : ℝ) ^ 2 := by
    rw [hnSq]
    calc ∑ i, ((d i).natAbs : ℝ) ^ 2 ≤ ∑ _i : Fin 3, ((K d : ℕ) : ℝ) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have h1 : (d i).natAbs ≤ K d := Work.BoseBoxFock.K_spec d i
          have h2 : (((d i).natAbs : ℕ) : ℝ) ≤ ((K d : ℕ) : ℝ) := by exact_mod_cast h1
          exact pow_le_pow_left₀ (by positivity) h2 2
      _ = 3 * ((K d : ℕ) : ℝ) ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
  rw [Work.BoseBoxFock.latVec_norm_sq, hK]
  exact hle

lemma norm_le_norm_latVec (d : Fin 3 → ℤ) : ‖d‖ ≤ ‖latVec d‖ := by
  rw [Work.BoseBoxFock.NormEqKcast d]
  exact Work.BoseBoxFock.K_le_norm_latVec d

lemma abs_le_three_of_mem_smLab {d : Fin 3 → ℤ} (hd : d ∈ smLab) (i : Fin 3) : |d i| ≤ 3 := by
  simp only [smLab, Finset.mem_image, Finset.mem_univ, true_and] at hd
  obtain ⟨c, rfl⟩ := hd
  have h1 : (((c i : ℕ)) : ℤ) ≤ 6 := by
    have := (c i).isLt
    omega
  have h2 : (0 : ℤ) ≤ (((c i : ℕ)) : ℤ) := Int.natCast_nonneg _
  show |(((c i : ℕ)) : ℤ) - 3| ≤ 3
  rw [abs_le]
  constructor <;> omega

lemma zero_mem_smLab : (0 : Fin 3 → ℤ) ∈ smLab :=
  mem_smLab (fun i => by simp)

/-- Substitution `a ↦ c - a` in a product integrand. -/
lemma integral_sub_left_mul (g h : E3 → ℝ) (c : E3) :
    (∫ a : E3, g (c - a) * h a) = ∫ b : E3, g b * h (c - b) := by
  rw [show (fun a : E3 => g (c - a) * h a)
      = (fun a : E3 => (fun b : E3 => g b * h (c - b)) (c - a)) from
        funext fun a => by
          show g (c - a) * h a = g (c - a) * h (c - (c - a))
          rw [sub_sub_cancel]]
  exact Submission.BoseGases.integral_comp_sub_left (fun b : E3 => g b * h (c - b)) c

/-! ## 3. the pointwise bound on the smoothed weight -/

lemma uvSmear_W1_abs_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fu : Work.BoseBoxFix.LowCut}
    {R ℓ Λ Cd : ℝ} (hΛ : 0 < Λ) (hCd : 0 ≤ Cd)
    (hdec : ∀ z : E3, ‖uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
    (hR : 0 < R) (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (y : E3) :
    |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) y|
      ≤ Cd * Λ ^ 3 * (1 + Λ * max 0 (‖y‖ - R)) ^ (-(5 : ℤ))
          * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := by
  have hWsupp : tsupport (Work.BoseFixR.W1fun v h ℓ) ⊆ Metric.ball (0 : E3) R :=
    Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ
  have hsub : |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) y|
      ≤ ∫ a : E3, ‖uvKernel fu Λ a‖ * |Work.BoseFixR.W1fun v h ℓ (y - a)| := by
    have h1 : |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) y|
        = |∫ a : E3, uvKernel fu Λ (y - a) * Work.BoseFixR.W1fun v h ℓ a| := rfl
    rw [h1]
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    rw [show (fun a : E3 => |uvKernel fu Λ (y - a) * Work.BoseFixR.W1fun v h ℓ a|)
        = (fun a : E3 => |uvKernel fu Λ (y - a)| * |Work.BoseFixR.W1fun v h ℓ a|)
        from funext fun a => abs_mul _ _]
    rw [integral_sub_left_mul (fun b : E3 => |uvKernel fu Λ b|)
      (fun b : E3 => |Work.BoseFixR.W1fun v h ℓ b|) y]
    apply integral_congr_ae
    filter_upwards with b
    rw [Real.norm_eq_abs]
  have hpt : ∀ a : E3, ‖uvKernel fu Λ a‖ * |Work.BoseFixR.W1fun v h ℓ (y - a)|
      ≤ (Cd * Λ ^ 3 * (1 + Λ * max 0 (‖y‖ - R)) ^ (-(5 : ℤ))) * |Work.BoseFixR.W1fun v h ℓ (y - a)| := by
    intro a
    by_cases hWa : Work.BoseFixR.W1fun v h ℓ (y - a) = 0
    · rw [hWa, abs_zero, mul_zero, mul_zero]
    · have hmem : y - a ∈ Metric.ball (0 : E3) R :=
        hWsupp (subset_tsupport _ (Function.mem_support.mpr hWa))
      rw [Metric.mem_ball, dist_zero_right] at hmem
      have hna : max 0 (‖y‖ - R) ≤ ‖a‖ := by
        have h3 : ‖y‖ ≤ ‖y - a‖ + ‖a‖ := by
          have := norm_add_le (y - a) a
          rwa [sub_add_cancel] at this
        exact max_le (norm_nonneg a) (by linarith)
      have hdec_a : ‖uvKernel fu Λ a‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖a‖) ^ (-(5 : ℤ)) := hdec a
      have hkey : (1 + Λ * ‖a‖) ^ (-(5 : ℤ)) ≤ (1 + Λ * max 0 (‖y‖ - R)) ^ (-(5 : ℤ)) := by
        refine zpow_neg_five_le ?_ ?_
        · have : (0 : ℝ) ≤ Λ * max 0 (‖y‖ - R) := by positivity
          linarith
        · have := mul_le_mul_of_nonneg_left hna hΛ.le
          linarith
      calc ‖uvKernel fu Λ a‖ * |Work.BoseFixR.W1fun v h ℓ (y - a)|
          ≤ (Cd * Λ ^ 3 * (1 + Λ * ‖a‖) ^ (-(5 : ℤ))) * |Work.BoseFixR.W1fun v h ℓ (y - a)| :=
            mul_le_mul_of_nonneg_right hdec_a (abs_nonneg _)
        _ ≤ (Cd * Λ ^ 3 * (1 + Λ * max 0 (‖y‖ - R)) ^ (-(5 : ℤ)))
              * |Work.BoseFixR.W1fun v h ℓ (y - a)| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by positivity))
              (abs_nonneg _)
  have hWabs : Integrable (fun a : E3 => |Work.BoseFixR.W1fun v h ℓ (y - a)|) := by
    have hWint : Integrable (Work.BoseFixR.W1fun v h ℓ) := by
      have hw := Submission.BoseGases.wScaled_g0_integrable (v := v) (R := R) (ℓ := ℓ)
        hR hv_supp h hℓ hRℓ
      simpa [Work.BoseFixR.W1fun] using hw
    have h1 : Integrable (fun x : E3 => |Work.BoseFixR.W1fun v h ℓ x|) := hWint.abs
    have h2 := (h1.comp_neg).comp_sub_right y
    refine h2.congr (Filter.Eventually.of_forall fun a => ?_)
    show |Work.BoseFixR.W1fun v h ℓ (-(a - y))| = |Work.BoseFixR.W1fun v h ℓ (y - a)|
    rw [neg_sub]
  refine hsub.trans ?_
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => by positivity) ?_
    (Filter.Eventually.of_forall fun a => hpt a)).trans ?_
  · exact hWabs.const_mul _
  · have heq : (∫ a : E3, |Work.BoseFixR.W1fun v h ℓ (y - a)|)
        = ∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x| :=
      Submission.BoseGases.integral_comp_sub_left (fun x : E3 => |Work.BoseFixR.W1fun v h ℓ x|) y
    rw [integral_const_mul, heq]

/-- For `a ≤ c * b` (all positive): `b^{-5} ≤ c^5 a^{-5}`. -/
lemma zpow_neg_five_le_of_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ≤ c * b) : b ^ (-(5 : ℤ)) ≤ c ^ 5 * a ^ (-(5 : ℤ)) := by
  have h1 : b⁻¹ ≤ c * a⁻¹ := by
    rw [inv_eq_one_div, show c * a⁻¹ = c / a by rw [div_eq_mul_inv]]
    rw [div_le_div_iff₀ hb ha]
    simpa using h
  have h2 : (b⁻¹) ^ 5 ≤ (c * a⁻¹) ^ 5 := pow_le_pow_left₀ (by positivity) h1 5
  rw [zpow_neg, zpow_neg]
  calc (b ^ 5)⁻¹ = (b⁻¹) ^ 5 := by rw [inv_pow]
    _ ≤ (c * a⁻¹) ^ 5 := h2
    _ = c ^ 5 * (a ^ 5)⁻¹ := by rw [mul_pow, inv_pow]

lemma uvSmear_W1_abs_le_crude {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fu : Work.BoseBoxFix.LowCut}
    {R ℓ Λ Cd : ℝ} (hΛ : 0 < Λ) (hCd : 0 ≤ Cd)
    (hdec : ∀ z : E3, ‖uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
    (hR : 0 < R) (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (y : E3) :
    |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) y|
      ≤ Cd * Λ ^ 3 * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := by
  refine (uvSmear_W1_abs_le hΛ hCd hdec hR hℓ hRℓ hv_supp y).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun x => abs_nonneg _)
  have hge : (1 : ℝ) ≤ 1 + Λ * max 0 (‖y‖ - R) := by
    have h0 : (0 : ℝ) ≤ Λ * max 0 (‖y‖ - R) := by positivity
    linarith
  refine (mul_le_mul_of_nonneg_left (zpow_neg_five_le_one hge) (by positivity)).trans ?_
  rw [mul_one]

lemma tsum_norm_images_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fu : Work.BoseBoxFix.LowCut}
    {R ℓ Λ Cd Bfar : ℝ} (hR : 0 < R) (hRℓ : 2 * R ≤ ℓ)
    (hχ : R ≤ ℓ * Submission.BoseGases.chiR0) (hℓ : 0 < ℓ) (hΛ : 1 ≤ Λ)
    (hCd : 0 ≤ Cd) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hdec : ∀ z : E3, ‖uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
    {x : E3} (hx : ‖x‖ ≤ ℓ)
    (hfar : (∑' d : Fin 3 → ℤ, if d ∈ smLab then 0
        else |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d)|) ≤ Bfar) :
    ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
        else ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d) : ℝ) : ℂ))‖
      ≤ (∑ d ∈ smLab.filter (fun d => d ≠ 0),
          |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d)|) + Bfar := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hmass : (0 : ℝ) ≤ ∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y| :=
    integral_nonneg fun y => abs_nonneg _
  have hpt : ∀ y : E3, |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) y|
      ≤ Cd * Λ ^ 3 * (1 + Λ * max 0 (‖y‖ - R)) ^ (-(5 : ℤ))
          * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) :=
    fun y => uvSmear_W1_abs_le hΛpos hCd hdec hR hℓ hχ hv_supp y
  have hptCrude : ∀ y : E3, |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) y|
      ≤ Cd * Λ ^ 3 * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) :=
    fun y => uvSmear_W1_abs_le_crude hΛpos hCd hdec hR hℓ hχ hv_supp y
  set Cl : ℝ := Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|) with hCldef
  have hCl0 : 0 ≤ Cl := by rw [hCldef]; positivity
  set Kdec : ℝ := 6 ^ 5 * (1 + Real.sqrt 3) ^ 5 * (Λ * ℓ) ^ (-(5 : ℤ)) with hKdecdef
  have hKdec0 : 0 ≤ Kdec := by rw [hKdecdef]; positivity
  have hsumLat : Summable (fun d : Fin 3 → ℤ => (1 + ‖latVec d‖) ^ (-(4 : ℤ))) := by
    have h := Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv (N := 4) (le_refl 4)
    simpa [zpow_neg, zpow_natCast] using h
  have hsumMaj : Summable (fun d : Fin 3 → ℤ =>
      (if d ∈ smLab then (1 : ℝ) else 0) * Cl
        + Kdec * Cl * (1 + ‖latVec d‖) ^ (-(4 : ℤ))) := by
    refine Summable.add ?_ ?_
    · refine summable_of_hasFiniteSupport ?_
      show (Function.support (fun d : Fin 3 → ℤ => (if d ∈ smLab then (1 : ℝ) else 0) * Cl)).Finite
      refine Set.Finite.subset smLab.finite_toSet ?_
      intro d hd
      by_contra hnot
      exact (Function.mem_support.mp hd) (by
        by_cases hmem : d ∈ smLab
        · exact absurd hmem hnot
        · rw [if_neg hmem, zero_mul])
    · exact hsumLat.mul_left (Kdec * Cl)
  set m : (Fin 3 → ℤ) → ℝ :=
    fun d => if d = 0 then 0 else |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d)|
    with hmdef
  have hmle : ∀ d : Fin 3 → ℤ,
      m d ≤ (if d ∈ smLab then (1 : ℝ) else 0) * Cl
            + Kdec * Cl * (1 + ‖latVec d‖) ^ (-(4 : ℤ)) := by
    intro d
    simp only [hmdef]
    by_cases hs : d ∈ smLab
    · have h1 : (if d = 0 then (0 : ℝ)
            else |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d)|) ≤ Cl := by
        by_cases hd0 : d = 0
        · rw [if_pos hd0]; exact hCl0
        · rw [if_neg hd0]; exact hptCrude _
      rw [if_pos hs]
      have h2 : (0 : ℝ) ≤ Kdec * Cl * (1 + ‖latVec d‖) ^ (-(4 : ℤ)) :=
        mul_nonneg (mul_nonneg hKdec0 hCl0) (zpow_nonneg (by positivity) _)
      linarith
    · have hd0 : d ≠ 0 := fun hcon => hs (hcon ▸ zero_mem_smLab)
      rw [if_neg hs, if_neg hd0, zero_mul, zero_add]
      have hdge : 4 ≤ ‖latVec d‖ := norm_latVec_ge_of_notMem_smLab hs
      have hsq : ‖latVec d‖ ^ 2 ≤ 3 * ‖d‖ ^ 2 := sq_norm_latVec_le_three_sq d
      have hdle : (9 / 4 : ℝ) ≤ ‖d‖ := by
        have h16 : (16 : ℝ) ≤ 3 * ‖d‖ ^ 2 := by
          nlinarith [hdge, norm_nonneg (latVec d), hsq]
        nlinarith [norm_nonneg d]
      have hbound : ℓ * ‖d‖ / 3 ≤ max 0 (‖x + ℓ • latVec d‖ - R) := by
        have h1 : ‖x + ℓ • latVec d‖ ≥ ℓ * ‖d‖ - ‖x‖ := by
          have h2 : ‖ℓ • latVec d‖ ≤ ‖x + ℓ • latVec d‖ + ‖x‖ := by
            have hh := norm_add_le (x + ℓ • latVec d) (-x)
            have h2 : x + ℓ • latVec d + -x = ℓ • latVec d := by abel
            rw [h2, norm_neg] at hh
            exact hh
          have h3 : ‖ℓ • latVec d‖ = ℓ * ‖latVec d‖ := by
            rw [norm_smul, Real.norm_of_nonneg hℓ.le]
          have h4 : ‖d‖ ≤ ‖latVec d‖ := norm_le_norm_latVec d
          have h5 : ℓ * ‖d‖ ≤ ℓ * ‖latVec d‖ := mul_le_mul_of_nonneg_left h4 hℓ.le
          linarith
        have h6 : ℓ * ‖d‖ / 3 ≤ ‖x + ℓ • latVec d‖ - R := by
          have h7 : R ≤ ℓ / 2 := by linarith
          nlinarith
        exact le_max_of_le_right h6
      have hkey : (1 + Λ * max 0 (‖x + ℓ • latVec d‖ - R)) ^ (-(5 : ℤ))
          ≤ Kdec * (1 + ‖latVec d‖) ^ (-(4 : ℤ)) := by
        have hdle' : (1 : ℝ) ≤ ‖d‖ := by linarith [hdle]
        have hpos1 : (0 : ℝ) < Λ * ℓ * (1 + ‖d‖) / 6 := by positivity
        have hle1 : Λ * ℓ * (1 + ‖d‖) / 6 ≤ 1 + Λ * max 0 (‖x + ℓ • latVec d‖ - R) := by
          have h8 : Λ * (ℓ * ‖d‖ / 3) ≤ Λ * max 0 (‖x + ℓ • latVec d‖ - R) :=
            mul_le_mul_of_nonneg_left hbound hΛpos.le
          have h9 : Λ * ℓ * (1 + ‖d‖) / 6 ≤ Λ * (ℓ * ‖d‖ / 3) := by
            nlinarith [hdle', mul_nonneg hΛpos.le hℓ.le, norm_nonneg d]
          linarith
        have hstep1 : (1 + Λ * max 0 (‖x + ℓ • latVec d‖ - R)) ^ (-(5 : ℤ))
            ≤ (Λ * ℓ * (1 + ‖d‖) / 6) ^ (-(5 : ℤ)) := zpow_neg_five_le hpos1 hle1
        have hstep2 : (Λ * ℓ * (1 + ‖d‖) / 6) ^ (-(5 : ℤ))
            = 6 ^ 5 * (Λ * ℓ) ^ (-(5 : ℤ)) * (1 + ‖d‖) ^ (-(5 : ℤ)) := by
          simp only [zpow_neg]
          field_simp
        have hstep3 : (1 + ‖d‖) ^ (-(5 : ℤ))
            ≤ (1 + Real.sqrt 3) ^ 5 * (1 + ‖latVec d‖) ^ (-(4 : ℤ)) := by
          have hsqr : ‖latVec d‖ ≤ Real.sqrt 3 * ‖d‖ := by
            have h2 : ‖latVec d‖ ≤ Real.sqrt (3 * ‖d‖ ^ 2) := by
              rw [← Real.sqrt_sq (norm_nonneg (latVec d))]
              exact Real.sqrt_le_sqrt hsq
            have h3 : Real.sqrt (3 * ‖d‖ ^ 2) = Real.sqrt 3 * ‖d‖ := by
              rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_sq (norm_nonneg d)]
            rwa [h3] at h2
          have h1 : 1 + ‖latVec d‖ ≤ (1 + Real.sqrt 3) * (1 + ‖d‖) := by
            nlinarith [hsqr, norm_nonneg d, norm_nonneg (latVec d), Real.sqrt_nonneg 3,
              norm_le_norm_latVec d]
          have h5 := zpow_neg_five_le_of_le (a := 1 + ‖latVec d‖) (b := 1 + ‖d‖)
            (c := 1 + Real.sqrt 3) (by positivity) (by positivity) (by positivity) h1
          have hbase : (0 : ℝ) < 1 + ‖latVec d‖ := by positivity
          refine h5.trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [zpow_neg, zpow_neg]
          exact (inv_le_inv₀ (pow_pos hbase 5) (pow_pos hbase 4)).mpr
            (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + ‖latVec d‖) (by norm_num : 4 ≤ 5))
        calc (1 + Λ * max 0 (‖x + ℓ • latVec d‖ - R)) ^ (-(5 : ℤ))
            ≤ (Λ * ℓ * (1 + ‖d‖) / 6) ^ (-(5 : ℤ)) := hstep1
          _ = 6 ^ 5 * (Λ * ℓ) ^ (-(5 : ℤ)) * (1 + ‖d‖) ^ (-(5 : ℤ)) := hstep2
          _ ≤ 6 ^ 5 * (Λ * ℓ) ^ (-(5 : ℤ))
                * ((1 + Real.sqrt 3) ^ 5 * (1 + ‖latVec d‖) ^ (-(4 : ℤ))) :=
              mul_le_mul_of_nonneg_left hstep3 (by positivity)
          _ = Kdec * (1 + ‖latVec d‖) ^ (-(4 : ℤ)) := by rw [hKdecdef]; ring
      calc |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d)|
          ≤ Cd * Λ ^ 3 * (1 + Λ * max 0 (‖x + ℓ • latVec d‖ - R)) ^ (-(5 : ℤ))
              * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := hpt _
        _ ≤ Cd * Λ ^ 3 * (Kdec * (1 + ‖latVec d‖) ^ (-(4 : ℤ)))
              * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by positivity)) hmass
        _ = Kdec * Cl * (1 + ‖latVec d‖) ^ (-(4 : ℤ)) := by rw [hCldef]; ring
  have hsumm : Summable m :=
    Summable.of_nonneg_of_le (fun d => by simp only [hmdef]; split <;> positivity) hmle hsumMaj
  have hnorm_pt : ∀ d : Fin 3 → ℤ, m d
      = ‖(if d = 0 then 0
        else ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d) : ℝ) : ℂ))‖ := by
    intro d
    simp only [hmdef]
    by_cases hd0 : d = 0
    · rw [if_pos hd0, if_pos hd0, norm_zero]
    · rw [if_neg hd0, if_neg hd0, Complex.norm_def, Complex.normSq_ofReal, ← sq,
        Real.sqrt_sq_eq_abs]
  have hsumm_norm : Summable (fun d : Fin 3 → ℤ => ‖(if d = 0 then 0
        else ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d) : ℝ) : ℂ))‖) :=
    hsumm.congr hnorm_pt
  have hnorm : (∑' d : Fin 3 → ℤ, ‖(if d = 0 then 0
        else ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d) : ℝ) : ℂ))‖)
      = ∑' d : Fin 3 → ℤ, m d := tsum_congr (fun d => (hnorm_pt d).symm)
  refine (norm_tsum_le_tsum_norm hsumm_norm).trans ?_
  rw [hnorm]
  have hsum1 : Summable (fun d : Fin 3 → ℤ => if d ∈ smLab then m d else 0) := by
    refine summable_of_hasFiniteSupport ?_
    show (Function.support (fun d : Fin 3 → ℤ => if d ∈ smLab then m d else 0)).Finite
    refine Set.Finite.subset smLab.finite_toSet ?_
    intro d hd
    by_contra hnot
    exact (Function.mem_support.mp hd) (by
      by_cases hmem : d ∈ smLab
      · exact absurd hmem hnot
      · rw [if_neg hmem])
  have hsum2 : Summable (fun d : Fin 3 → ℤ => if d ∈ smLab then 0 else m d) := by
    refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hsumm
    · by_cases hs : d ∈ smLab
      · rw [if_pos hs]
      · rw [if_neg hs]; simp only [hmdef]; split <;> positivity
    · by_cases hs : d ∈ smLab
      · rw [if_pos hs]; simp only [hmdef]; split <;> positivity
      · rw [if_neg hs]
  have hsplit : (∑' d : Fin 3 → ℤ, m d)
      = (∑' d : Fin 3 → ℤ, (if d ∈ smLab then m d else 0))
        + (∑' d : Fin 3 → ℤ, (if d ∈ smLab then 0 else m d)) := by
    rw [← Summable.tsum_add hsum1 hsum2]
    refine tsum_congr (fun d => ?_)
    by_cases hs : d ∈ smLab <;> simp [hs]
  rw [hsplit]
  have hfirst : (∑' d : Fin 3 → ℤ, (if d ∈ smLab then m d else 0))
      ≤ ∑ d ∈ smLab.filter (fun d => d ≠ 0),
          |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d)| := by
    rw [tsum_eq_sum (s := smLab.filter (fun d => d ≠ 0)) ?_]
    · refine Finset.sum_le_sum (fun dd hdd => ?_)
      rw [Finset.mem_filter] at hdd
      obtain ⟨hds, hd0⟩ := hdd
      rw [if_pos hds]
      simp only [hmdef]
      rw [if_neg hd0]
    · intro dd hdd
      rw [Finset.mem_filter] at hdd
      push_neg at hdd
      by_cases hs : dd ∈ smLab
      · rw [if_pos hs]
        simp only [hmdef]
        rw [if_pos (hdd hs)]
      · rw [if_neg hs]
  have hsecond : (∑' d : Fin 3 → ℤ, (if d ∈ smLab then 0 else m d)) ≤ Bfar := by
    refine le_trans (le_of_eq ?_) hfar
    refine tsum_congr (fun d => ?_)
    by_cases hs : d ∈ smLab
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      simp only [hmdef]
      rw [if_neg (by intro hcon; subst hcon; exact hs zero_mem_smLab)]
  linarith

/-- The assembly, with the four analytic inputs as hypotheses. -/
theorem chB_img_le_of_inputs {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fu : Work.BoseBoxFix.LowCut}
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (C1 : ∀ (N : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ ρ : ℝ}, 0 < ℓ → 0 ≤ ρ →
      ∀ {d : Fin 3 → ℤ}, d ≠ 0 → ∀ z w : E3,
        ‖z - w + ℓ • latVec d‖ ≤ ρ →
          Work.BoseK15.corpusBox.chiLam ℓ z * Work.BoseK15.corpusBox.chiLam ℓ w
            ≤ C * (ρ / ℓ) ^ (2 * N))
    (C2 : ∀ {Λ ℓ R' Bm : ℝ}, 0 < ℓ → 1 ≤ Λ → 0 < R' → ∀ {ψ : E3 → ℝ},
      Integrable (fun a : E3 => ‖ψ a‖ * (1 + Λ * ‖a‖) ^ 4) →
      (∫ a : E3, ‖ψ a‖ * (1 + Λ * ‖a‖) ^ 4 ≤ Bm) →
      ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R' + ‖a‖) ^ 4 * ‖ψ a‖)
        ≤ 16 * Bm * ((R' / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))))
    (C3 : ∀ {R' ℓ Λ Cd : ℝ}, 0 < R' → 0 < ℓ → 2 * R' ≤ ℓ → 1 ≤ Λ → 0 ≤ Cd →
      tsupport v ⊆ Metric.ball (0 : E3) R' →
      (∀ z : E3, ‖uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ))) →
      ∀ {x : E3}, ‖x‖ ≤ ℓ →
      (∑' d : Fin 3 → ℤ, if d ∈ smLab then 0
          else |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (x + ℓ • latVec d)|)
        ≤ 4 ^ 5 * 227 * Cd * (Λ * ℓ) ^ (-(2 : ℤ)) * ℓ ^ (-(3 : ℤ))
            * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|))
    (C4 : ∀ {R' ℓ Λ Cf Cd : ℝ}, 0 < R' → 0 < ℓ → R' ≤ ℓ * Submission.BoseGases.chiR0 → 1 ≤ Λ →
      0 ≤ Cf → 0 ≤ Cd → tsupport v ⊆ Metric.ball (0 : E3) R' →
      (∀ z : E3, ‖uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ))) →
      (∀ (ρ : ℝ), 0 ≤ ρ → ∀ (d : Fin 3 → ℤ), d ≠ 0 → ∀ z w : E3,
        ‖z - w + ℓ • latVec d‖ ≤ ρ →
          Work.BoseK15.corpusBox.chiLam ℓ z * Work.BoseK15.corpusBox.chiLam ℓ w ≤ Cf * (ρ / ℓ) ^ 4) →
      ∀ {d : Fin 3 → ℤ}, d ≠ 0 → ∀ z : E3,
      Work.BoseK15.corpusBox.chiLam ℓ z *
          (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w *
            |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)|)
        ≤ Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R' + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
            * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)) :
    ∀ (Bm : ℝ), 0 ≤ Bm →
      (∀ (Λ : ℝ), 1 ≤ Λ → ∫ a : E3, ‖uvKernel fu Λ a‖ * (1 + Λ * ‖a‖) ^ 4 ≤ Bm) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ : ℝ) (_hℓ : 0 < ℓ) (_hRℓ : 2 * R ≤ ℓ)
        (_hchi : R ≤ ℓ * Submission.BoseGases.chiR0) (Λ : ℝ) (_hΛ : 1 ≤ Λ)
        (_hΛℓ : 1 ≤ Λ * ℓ) (z : E3),
        (Work.BoseK15.corpusBox.chiLam ℓ z) *
          (∫ w : E3, (Work.BoseK15.corpusBox.chiLam ℓ w) *
            ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0 else
                ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ)
                  (z - w + ℓ • latVec d) : ℝ) : ℂ))‖)
        ≤ K * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) *
            ((Λ * ℓ)⁻¹ + (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) := by
  intro Bm hBm hmom
  obtain ⟨Cd, hCd0, hdec⟩ := uvKernel_decay fu 5
  obtain ⟨Cf, hCf0, hflat0⟩ := C1 2
  set ch : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hchdef
  have hch0 : 0 ≤ ch := by rw [hchdef]; positivity
  set Chv : ℝ := max 1 (Work.BoseB4.BoxData.hatChi Work.BoseK15.corpusBox 0) with hChvdef
  have hChv0 : 0 ≤ Chv := by rw [hChvdef]; exact le_trans zero_le_one (le_max_left _ _)
  have hK0 : 0 ≤ 343 * Cf * 16 * Bm + ch * 4 ^ 5 * 227 * Cd * Chv := by positivity
  refine ⟨343 * Cf * 16 * Bm + ch * 4 ^ 5 * 227 * Cd * Chv, hK0, ?_⟩
  intro ℓ hℓ hRℓ2 hchi Λ hΛ hΛℓ z
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hΛℓpos : 0 < Λ * ℓ := mul_pos hΛpos hℓ
  have hΛℓ1 : (1 : ℝ) ≤ Λ * ℓ := hΛℓ
  have hflat : ∀ (ρ : ℝ), 0 ≤ ρ → ∀ (d : Fin 3 → ℤ), d ≠ 0 → ∀ z w : E3,
      ‖z - w + ℓ • latVec d‖ ≤ ρ →
        Work.BoseK15.corpusBox.chiLam ℓ z * Work.BoseK15.corpusBox.chiLam ℓ w
          ≤ Cf * (ρ / ℓ) ^ 4 := by
    intro ρ hρ d hd z w hzw
    simpa using hflat0 (ℓ := ℓ) hℓ hρ (d := d) hd z w hzw
  have hWint : Integrable (Work.BoseFixR.W1fun v h ℓ) := by
    have hw := Submission.BoseGases.wScaled_g0_integrable (v := v) (R := R) (ℓ := ℓ)
      hR hv_supp h hℓ hchi
    simpa [Work.BoseFixR.W1fun] using hw
  have hmass : 0 ≤ ∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x| :=
    integral_nonneg fun x => abs_nonneg _
  have hψi : Integrable (fun a : E3 => ‖uvKernel fu Λ a‖ * (1 + Λ * ‖a‖) ^ 4) := by
    obtain ⟨Cd9, hCd90, hdec9⟩ := uvKernel_decay fu 9
    have hmaj : Integrable (fun a : E3 => (Cd9 * Λ ^ 3) * (1 + ‖a‖) ^ (-(5 : ℤ))) :=
      (Work.BoseBoxFock.integrable_one_add_norm_zpow 5 (by norm_num)).const_mul _
    refine Integrable.mono' hmaj ?_ ?_
    · exact (((uvKernel_continuous fu hΛpos).norm).mul
        (by fun_prop : Continuous fun a : E3 => (1 + Λ * ‖a‖) ^ 4)).aestronglyMeasurable
    · filter_upwards with a
      rw [Real.norm_of_nonneg (by positivity)]
      have h9 := hdec9 Λ hΛpos a
      have hb : (0 : ℝ) < 1 + Λ * ‖a‖ := by positivity
      calc ‖uvKernel fu Λ a‖ * (1 + Λ * ‖a‖) ^ 4
          ≤ (Cd9 * Λ ^ 3 * (1 + Λ * ‖a‖) ^ (-(9 : ℤ))) * (1 + Λ * ‖a‖) ^ 4 :=
            mul_le_mul_of_nonneg_right h9 (by positivity)
        _ = Cd9 * Λ ^ 3 * ((1 + Λ * ‖a‖) ^ (-(9 : ℤ)) * (1 + Λ * ‖a‖) ^ 4) := by ring
        _ = Cd9 * Λ ^ 3 * (1 + Λ * ‖a‖) ^ (-(5 : ℤ)) := by
            rw [← zpow_natCast (1 + Λ * ‖a‖) 4, ← zpow_add₀ hb.ne']
            norm_num
        _ ≤ Cd9 * Λ ^ 3 * (1 + ‖a‖) ^ (-(5 : ℤ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact zpow_neg_five_le (by positivity) (by nlinarith [norm_nonneg a, hΛ])
        _ = (Cd9 * Λ ^ 3) * (1 + ‖a‖) ^ (-(5 : ℤ)) := by ring
  have hdec' : ∀ z : E3, ‖uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)) :=
    fun z => hdec Λ hΛpos z
  have hJ := C2 (Λ := Λ) (ℓ := ℓ) (R' := R) (Bm := Bm) hℓ hΛ hR hψi (hmom Λ hΛ)
  by_cases hz : Work.BoseK15.corpusBox.chiLam ℓ z = 0
  · rw [hz, zero_mul]
    exact mul_nonneg (mul_nonneg hK0 hmass) (by positivity)
  · have hzle : ‖z‖ ≤ ℓ / 2 := chiLam_nonzero_le_half hℓ hz
    have hzpos : 0 ≤ Work.BoseK15.corpusBox.chiLam ℓ z := chiLam_nonneg' ℓ z
    set Mfar : ℝ := 4 ^ 5 * 227 * Cd * (Λ * ℓ) ^ (-(2 : ℤ)) * ℓ ^ (-(3 : ℤ))
      * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|) with hMfardef
    have hMfar0 : 0 ≤ Mfar := by rw [hMfardef]; positivity
    set Sn : E3 → ℝ := fun w => ∑ d ∈ smLab.filter (fun d => d ≠ 0),
      |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)| with hSndef
    have hcard : ((smLab.filter (fun d => d ≠ 0)).card : ℝ) ≤ 343 := by
      have h1 : (smLab.filter (fun d => d ≠ 0)).card ≤ smLab.card := Finset.card_filter_le _ _
      exact_mod_cast le_trans h1 smLab_card
    have hSn_nonneg : ∀ w : E3, 0 ≤ Sn w := by
      intro w; rw [hSndef]; exact Finset.sum_nonneg fun d _ => abs_nonneg _
    have hpt : ∀ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w *
        ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
          else ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d) : ℝ) : ℂ))‖
        ≤ Work.BoseK15.corpusBox.chiLam ℓ w * Sn w + Work.BoseK15.corpusBox.chiLam ℓ w * Mfar := by
      intro w
      rw [hSndef]
      by_cases hw : Work.BoseK15.corpusBox.chiLam ℓ w = 0
      · rw [hw, zero_mul, zero_mul, zero_mul, zero_add]
      · have hwle : ‖w‖ ≤ ℓ / 2 := chiLam_nonzero_le_half hℓ hw
        have hzw : ‖z - w‖ ≤ ℓ := by
          have h1 : ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
          linarith
        have hfar := C3 (R' := R) (ℓ := ℓ) (Λ := Λ) (Cd := Cd)
          hR hℓ hRℓ2 hΛ hCd0 hv_supp hdec' hzw
        have hsplit := tsum_norm_images_le (v := v) (h := h) (fu := fu) (R := R) (ℓ := ℓ)
          (Λ := Λ) (Cd := Cd) (Bfar := Mfar) hR hRℓ2 hchi hℓ hΛ hCd0 hv_supp hdec' hzw
          (by rw [hMfardef]; exact hfar)
        have hwpos : 0 ≤ Work.BoseK15.corpusBox.chiLam ℓ w := chiLam_nonneg' ℓ w
        calc Work.BoseK15.corpusBox.chiLam ℓ w *
              ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
                else ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d) : ℝ) : ℂ))‖
            ≤ Work.BoseK15.corpusBox.chiLam ℓ w * (Sn w + Mfar) := by
              rw [hSndef]; exact mul_le_mul_of_nonneg_left hsplit hwpos
          _ = Work.BoseK15.corpusBox.chiLam ℓ w * Sn w + Work.BoseK15.corpusBox.chiLam ℓ w * Mfar := by
              ring
    have hSn_int : Integrable (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w * Sn w) := by
      refine Integrable.mono' ((integrable_chiLam ℓ hℓ).const_mul
        (343 * (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|)))) ?_ ?_
      · have hmeas : Measurable (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w * Sn w) := by
          refine (continuous_chiLam ℓ).measurable.mul ?_
          rw [hSndef]
          refine Finset.measurable_sum _ (fun d _ => ?_)
          exact (((uvSmear_continuous fu hΛpos hWint).comp
            (by fun_prop : Continuous fun w : E3 => z - w + ℓ • latVec d)).abs).measurable
        exact hmeas.aestronglyMeasurable
      · filter_upwards with w
        rw [Real.norm_of_nonneg (mul_nonneg (chiLam_nonneg' ℓ w) (hSn_nonneg w))]
        rw [hSndef]
        have hbound : (∑ d ∈ smLab.filter (fun d => d ≠ 0),
              |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)|)
            ≤ 343 * (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|)) := by
          calc ∑ d ∈ smLab.filter (fun d => d ≠ 0),
              |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)|
            ≤ ∑ _d ∈ smLab.filter (fun d => d ≠ 0),
              (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|)) :=
              Finset.sum_le_sum (fun d _ => uvSmear_W1_abs_le_crude hΛpos hCd0 hdec' hR hℓ hchi hv_supp _)
          _ = ((smLab.filter (fun d => d ≠ 0)).card : ℝ)
                * (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 343 * (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|)) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
        calc Work.BoseK15.corpusBox.chiLam ℓ w * (∑ d ∈ smLab.filter (fun d => d ≠ 0),
              |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)|)
            ≤ Work.BoseK15.corpusBox.chiLam ℓ w
                * (343 * (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|))) :=
              mul_le_mul_of_nonneg_left hbound (chiLam_nonneg' ℓ w)
          _ = 343 * (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|))
                * Work.BoseK15.corpusBox.chiLam ℓ w := by ring
    have hMfar_int : Integrable (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w * Mfar) :=
      (integrable_chiLam ℓ hℓ).mul_const Mfar
    have hIntZa : Integrable (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ z *
        (Work.BoseK15.corpusBox.chiLam ℓ w * Sn w)) := hSn_int.const_mul _
    have hIntZb : Integrable (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ z *
        (Work.BoseK15.corpusBox.chiLam ℓ w * Mfar)) := hMfar_int.const_mul _
    have hIntZ : Integrable (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ z *
        (Work.BoseK15.corpusBox.chiLam ℓ w * Sn w + Work.BoseK15.corpusBox.chiLam ℓ w * Mfar)) :=
      (hIntZa.add hIntZb).congr (Filter.Eventually.of_forall fun w => by
        simp only [Pi.add_apply]; ring)
    have hmain : Work.BoseK15.corpusBox.chiLam ℓ z *
        (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w *
          ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
            else ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d) : ℝ) : ℂ))‖)
        ≤ ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ z *
            (Work.BoseK15.corpusBox.chiLam ℓ w * Sn w + Work.BoseK15.corpusBox.chiLam ℓ w * Mfar) := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
        mul_nonneg hzpos (mul_nonneg (chiLam_nonneg' ℓ w) (norm_nonneg _))) hIntZ
        (Filter.Eventually.of_forall fun w => ?_)
      exact mul_le_mul_of_nonneg_left (hpt w) hzpos
    have hsplitI : (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ z *
          (Work.BoseK15.corpusBox.chiLam ℓ w * Sn w + Work.BoseK15.corpusBox.chiLam ℓ w * Mfar))
        = Work.BoseK15.corpusBox.chiLam ℓ z * (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Sn w)
          + Work.BoseK15.corpusBox.chiLam ℓ z * (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Mfar) := by
      have hpt : ∀ w : E3, Work.BoseK15.corpusBox.chiLam ℓ z *
            (Work.BoseK15.corpusBox.chiLam ℓ w * Sn w + Work.BoseK15.corpusBox.chiLam ℓ w * Mfar)
          = Work.BoseK15.corpusBox.chiLam ℓ z * (Work.BoseK15.corpusBox.chiLam ℓ w * Sn w)
            + Work.BoseK15.corpusBox.chiLam ℓ z * (Work.BoseK15.corpusBox.chiLam ℓ w * Mfar) :=
        fun w => by ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      rw [integral_add hIntZa hIntZb, integral_const_mul, integral_const_mul]
    have hnearSum : Work.BoseK15.corpusBox.chiLam ℓ z *
        (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Sn w)
        ≤ 343 * (Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
            * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)) := by
      have hℓ4 : (0 : ℝ) ≤ ℓ ^ (-(4 : ℤ)) := zpow_nonneg hℓ.le _
      have hJnn : (0 : ℝ) ≤ ∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖ :=
        integral_nonneg fun a => by positivity
      have hcst : (0 : ℝ) ≤ Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
          * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) :=
        mul_nonneg (mul_nonneg (mul_nonneg hCf0 hℓ4) hJnn) hmass
      have hexch : (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Sn w)
          = ∑ d ∈ smLab.filter (fun d => d ≠ 0),
              ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w *
                |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)| := by
        rw [hSndef]
        rw [show (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w *
              (∑ d ∈ smLab.filter (fun d => d ≠ 0),
                |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)|))
            = fun w : E3 => ∑ d ∈ smLab.filter (fun d => d ≠ 0),
                Work.BoseK15.corpusBox.chiLam ℓ w *
                  |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)| from
              funext fun w => Finset.mul_sum _ _ _]
        rw [integral_finsetSum _ (fun d _ => ?_)]
        refine Integrable.mono' ((integrable_chiLam ℓ hℓ).const_mul
          (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|))) ?_ ?_
        · exact (((continuous_chiLam ℓ).mul (((uvSmear_continuous fu hΛpos hWint).comp
            (by fun_prop : Continuous fun w : E3 => z - w + ℓ • latVec d)).abs)).aestronglyMeasurable)
        · filter_upwards with w
          rw [Real.norm_of_nonneg (mul_nonneg (chiLam_nonneg' ℓ w) (abs_nonneg _))]
          calc Work.BoseK15.corpusBox.chiLam ℓ w *
                |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)|
              ≤ Work.BoseK15.corpusBox.chiLam ℓ w
                  * (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|)) :=
                mul_le_mul_of_nonneg_left
                  (uvSmear_W1_abs_le_crude hΛpos hCd0 hdec' hR hℓ hchi hv_supp _) (chiLam_nonneg' ℓ w)
            _ = (Cd * Λ ^ 3 * (∫ y : E3, |Work.BoseFixR.W1fun v h ℓ y|))
                  * Work.BoseK15.corpusBox.chiLam ℓ w := by ring
      rw [hexch, Finset.mul_sum]
      have h1 : (∑ d ∈ smLab.filter (fun d => d ≠ 0),
            Work.BoseK15.corpusBox.chiLam ℓ z *
              (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w *
                |uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d)|))
          ≤ ∑ _d ∈ smLab.filter (fun d => d ≠ 0),
              (Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
                * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)) :=
        Finset.sum_le_sum (fun d hd => by
          rw [Finset.mem_filter] at hd
          exact C4 (R' := R) (ℓ := ℓ) (Λ := Λ) (Cf := Cf) (Cd := Cd)
            hR hℓ hchi hΛ hCf0 hCd0 hv_supp hdec' hflat hd.2 z)
      refine h1.trans ?_
      calc ∑ _d ∈ smLab.filter (fun d => d ≠ 0),
            (Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
              * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|))
            = ((smLab.filter (fun d => d ≠ 0)).card : ℝ)
              * (Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
                * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 343 * (Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
                * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)) :=
              mul_le_mul_of_nonneg_right hcard hcst
    have hfarInt : Work.BoseK15.corpusBox.chiLam ℓ z *
        (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Mfar)
        ≤ ch * Mfar * ℓ ^ 3 * Chv := by
      have hχz : Work.BoseK15.corpusBox.chiLam ℓ z ≤ ch := chiLam_le_chiSupAbs ℓ z
      have hhat : Work.BoseB4.BoxData.hatChi Work.BoseK15.corpusBox 0 ≤ Chv := by
        rw [hChvdef]; exact le_max_right _ _
      have hhat0 : 0 ≤ Work.BoseB4.BoxData.hatChi Work.BoseK15.corpusBox 0 := by
        have h := integral_chiLam_eq ℓ hℓ
        have h2 : 0 ≤ ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w :=
          integral_nonneg fun w => chiLam_nonneg' ℓ w
        rw [h] at h2
        exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < ℓ ^ 3)).mp h2
      have h1 : Work.BoseK15.corpusBox.chiLam ℓ z *
          (ℓ ^ 3 * Work.BoseB4.BoxData.hatChi Work.BoseK15.corpusBox 0 * Mfar)
          ≤ ch * (ℓ ^ 3 * Work.BoseB4.BoxData.hatChi Work.BoseK15.corpusBox 0 * Mfar) :=
        mul_le_mul_of_nonneg_right hχz (by positivity)
      have h2 : ℓ ^ 3 * Work.BoseB4.BoxData.hatChi Work.BoseK15.corpusBox 0 * Mfar
          ≤ ℓ ^ 3 * Chv * Mfar := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhat (by positivity)) hMfar0
      rw [integral_mul_const, integral_chiLam_eq ℓ hℓ]
      refine h1.trans ?_
      refine (mul_le_mul_of_nonneg_left h2 hch0).trans_eq ?_
      ring
    have hP2 : (Λ * ℓ) ^ (-(2 : ℤ)) = ((Λ * ℓ) ^ 2)⁻¹ := by
      rw [zpow_neg]
      norm_num
    have hJ' : ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
        ≤ 16 * Bm * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) := by
      refine hJ.trans ?_
      have hP : (Λ * ℓ) ^ (-(4 : ℤ)) ≤ ((Λ * ℓ) ^ 2)⁻¹ := by
        rw [← hP2]
        rw [zpow_neg, zpow_neg]
        exact (inv_le_inv₀ (pow_pos hΛℓpos 4) (pow_pos hΛℓpos 2)).mpr
          (pow_le_pow_right₀ hΛℓ1 (by norm_num : 2 ≤ 4))
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hP) (by positivity)
    have hnear' : 343 * (Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
          * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|))
        ≤ 343 * (Cf * (16 * Bm * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)))
          * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := by
      rw [show (343 : ℝ) * (Cf * ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖)
            * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|))
          = 343 * Cf * (ℓ ^ (-(4 : ℤ)) * (∫ a : E3, (R + ‖a‖) ^ 4 * ‖uvKernel fu Λ a‖))
            * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) from by ring]
      rw [show (343 : ℝ) * (Cf * (16 * Bm * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)))
            * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)
          = 343 * Cf * (16 * Bm * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹))
            * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) from by ring]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ' (by positivity)) hmass
    have hfar' : ch * Mfar * ℓ ^ 3 * Chv
        ≤ ch * (4 ^ 5 * 227 * Cd) * Chv * ((Λ * ℓ) ^ 2)⁻¹
          * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := by
      have heq : ch * Mfar * ℓ ^ 3 * Chv
          = ch * (4 ^ 5 * 227 * Cd) * Chv * ((Λ * ℓ) ^ 2)⁻¹
            * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := by
        rw [hMfardef, hP2]
        simp only [zpow_neg]
        field_simp
      rw [heq]
    have htotal : Work.BoseK15.corpusBox.chiLam ℓ z *
        (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w *
          ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
            else ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d) : ℝ) : ℂ))‖)
        ≤ (343 * Cf * 16 * Bm + ch * 4 ^ 5 * 227 * Cd * Chv)
          * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)
          * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) := by
      have hbase : Work.BoseK15.corpusBox.chiLam ℓ z *
            (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Sn w)
          + Work.BoseK15.corpusBox.chiLam ℓ z * (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Mfar)
          ≤ (343 * Cf * 16 * Bm + ch * (4 ^ 5 * 227 * Cd) * Chv)
            * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)
            * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := by
        have hR4 : (0 : ℝ) ≤ (R / ℓ) ^ 4 := by positivity
        have hstep : ch * (4 ^ 5 * 227 * Cd) * Chv * ((Λ * ℓ) ^ 2)⁻¹
              * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)
            ≤ ch * (4 ^ 5 * 227 * Cd) * Chv * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)
              * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := by
          refine mul_le_mul_of_nonneg_right ?_ hmass
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
        calc Work.BoseK15.corpusBox.chiLam ℓ z *
              (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Sn w)
            + Work.BoseK15.corpusBox.chiLam ℓ z * (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Mfar)
            ≤ 343 * (Cf * (16 * Bm * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)))
                * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)
              + ch * (4 ^ 5 * 227 * Cd) * Chv * ((Λ * ℓ) ^ 2)⁻¹
                * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) :=
              add_le_add (hnearSum.trans hnear') (hfarInt.trans hfar')
          _ ≤ 343 * (Cf * (16 * Bm * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)))
                * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)
              + ch * (4 ^ 5 * 227 * Cd) * Chv * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)
                * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) :=
              add_le_add le_rfl hstep
          _ = (343 * Cf * 16 * Bm + ch * (4 ^ 5 * 227 * Cd) * Chv)
                * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)
                * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := by ring
      calc Work.BoseK15.corpusBox.chiLam ℓ z *
            (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w *
              ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0
                else ((uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w + ℓ • latVec d) : ℝ) : ℂ))‖)
          ≤ ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ z *
              (Work.BoseK15.corpusBox.chiLam ℓ w * Sn w + Work.BoseK15.corpusBox.chiLam ℓ w * Mfar) :=
            hmain
        _ = Work.BoseK15.corpusBox.chiLam ℓ z * (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Sn w)
              + Work.BoseK15.corpusBox.chiLam ℓ z
                * (∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w * Mfar) := hsplitI
        _ ≤ (343 * Cf * 16 * Bm + ch * (4 ^ 5 * 227 * Cd) * Chv)
              * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)
              * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) := hbase
        _ = (343 * Cf * 16 * Bm + ch * 4 ^ 5 * 227 * Cd * Chv)
              * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)
              * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) := by ring
    refine htotal.trans ?_
    have hlast : (343 * Cf * 16 * Bm + ch * 4 ^ 5 * 227 * Cd * Chv)
          * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)
          * ((R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹)
        ≤ (343 * Cf * 16 * Bm + ch * 4 ^ 5 * 227 * Cd * Chv)
          * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)
          * ((Λ * ℓ)⁻¹ + (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) := by
      have h1 : (0 : ℝ) ≤ (Λ * ℓ)⁻¹ := inv_nonneg.mpr hΛℓpos.le
      have h2 : (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹
          ≤ (Λ * ℓ)⁻¹ + (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹ := by linarith
      exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 hmass)
    exact hlast


/-! ## The target statement, with the four analytic inputs instantiated. -/

theorem chB_img_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {fu : Work.BoseBoxFix.LowCut} {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∀ (Bm : ℝ), 0 ≤ Bm →
      (∀ (Λ : ℝ), 1 ≤ Λ → ∫ a : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.uvKernel fu Λ a‖
          * (1 + Λ * ‖a‖) ^ 4 ≤ Bm) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ : ℝ) (_hℓ : 0 < ℓ) (_hRℓ : 2 * R ≤ ℓ)
        (_hchi : R ≤ ℓ * Submission.BoseGases.chiR0) (Λ : ℝ) (_hΛ : 1 ≤ Λ)
        (_hΛℓ : 1 ≤ Λ * ℓ) (z : EuclideanSpace ℝ (Fin 3)),
        (Work.BoseK15.corpusBox.chiLam ℓ z) *
          (∫ w : EuclideanSpace ℝ (Fin 3), (Work.BoseK15.corpusBox.chiLam ℓ w) *
            ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0 else
                ((Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ)
                  (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖)
        ≤ K * (∫ x : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h ℓ x|) *
            ((Λ * ℓ)⁻¹ + (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) := by
  exact chB_img_le_of_inputs (v := v) (h := h) (fu := fu) (R := R) hR hv_supp
    chiLam_mul_le_of_alias chBimg_J_le chBimg_far_tail chBimg_near_d

end Work.BoseBoxFock.PCFU
