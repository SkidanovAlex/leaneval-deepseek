import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadGreenSupport

/-- `t ^ a * t ^ b = t ^ (a + b)` for `t > 0`. -/
private lemma rpowMul {t : ℝ} (ht : 0 < t) (a b : ℝ) : t ^ a * t ^ b = t ^ (a + b) :=
  (Real.rpow_add ht a b).symm

/-- `t ^ a / t ^ n = t ^ (a - n)` for `t > 0` and a natural exponent `n`. -/
private lemma rpowDivNat {t : ℝ} (ht : 0 < t) (a : ℝ) (n : ℕ) : t ^ a / t ^ n = t ^ (a - n) := by
  rw [show t ^ n = t ^ ((n : ℕ) : ℝ) from (Real.rpow_natCast t n).symm, div_eq_mul_inv,
    ← Real.rpow_neg ht.le ((n : ℕ) : ℝ), rpowMul ht a (-((n : ℕ) : ℝ)), ← sub_eq_add_neg]

/-- `1 / t = t ^ (-1)`. -/
private lemma one_div_eq_rpow (t : ℝ) : 1 / t = t ^ (-1 : ℝ) := by
  rw [one_div, ← Real.rpow_neg_one]

/-- `t ^ (-1) * t ^ (-r - 1) = t ^ (-r - 2)`. -/
private lemma rpow_neg_one_mul {t : ℝ} (ht : 0 < t) (r : ℝ) :
    t ^ (-1 : ℝ) * t ^ (-r - 1) = t ^ (-r - 2) := by
  rw [rpowMul ht (-1) (-r - 1), show (-1 : ℝ) + (-r - 1) = -r - 2 by ring]

/-- `t ^ n / (1 + t ^ (n + 1)) ≤ 1 / t` for `t > 0`. -/
private lemma pow_div_one_add_pow_le {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ n / (1 + t ^ (n + 1)) ≤ 1 / t := by
  have hpos : (0 : ℝ) < 1 + t ^ (n + 1) := by
    have := pow_nonneg ht.le (n + 1); linarith
  rw [div_le_div_iff₀ hpos ht, one_mul, (pow_succ t n).symm]
  linarith

theorem ibp_upper {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hc : ContDiffOn ℝ 2 c (Set.Ioi 0))
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1)))
    {z : ℝ} (hz : 0 < z) :
    ∫ t in Set.Ioi z,
        (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t)
          * t ^ (-(2 * (m : ℝ) / α) - 1)
      = -α * z ^ (1 - 2 * (m : ℝ) / α) * deriv c z
        - (2 * (m : ℝ) + 5) * z ^ (-(2 * (m : ℝ) / α)) * c z
        + (2 * (m : ℝ) + 5) * (2 * (m : ℝ) / α)
            * ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1) := by
  set r : ℝ := 2 * (m : ℝ) / α with hr
  have hrr : 2 * (m : ℝ) = α * r := by
    calc 2 * (m : ℝ) = (2 * (m : ℝ) / α) * α := (div_mul_cancel₀ _ (ne_of_gt hα)).symm
      _ = r * α := by rw [hr]
      _ = α * r := by ring
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) hα.le
  have hm5 : (0 : ℝ) ≤ 2 * (m : ℝ) + 5 := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  -- ### bounds for `c` and its derivatives
  have hc0 : ∀ t : ℝ, 0 < t → |c t| ≤ A / (1 + t) := by
    intro t ht
    simpa only [iteratedDeriv_zero, Nat.zero_add, pow_one] using
      hb 0 (by norm_num : (0 : ℕ) ≤ 2) t ht
  have hc1 : ∀ t : ℝ, 0 < t → |deriv c t| ≤ A / (1 + t ^ 2) := by
    intro t ht
    simpa only [iteratedDeriv_one, Nat.reduceAdd] using hb 1 (by norm_num : (1 : ℕ) ≤ 2) t ht
  have hc2 : ∀ t : ℝ, 0 < t → |iteratedDeriv 2 c t| ≤ A / (1 + t ^ 3) := by
    intro t ht
    simpa only [Nat.reduceAdd] using hb 2 (by norm_num : (2 : ℕ) ≤ 2) t ht
  -- ### the second derivative, continuity and differentiability statements
  have hfun2 : (fun t : ℝ => iteratedDeriv 2 c t) = deriv (deriv c) := by
    funext t
    have h2 : (2 : ℕ) = 1 + 1 := by norm_num
    rw [h2, iteratedDeriv_succ, iteratedDeriv_one]
  have hcd : ContinuousOn (deriv c) (Set.Ioi (0 : ℝ)) :=
    hc.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hcdd : ContinuousOn (deriv (deriv c)) (Set.Ioi (0 : ℝ)) :=
    ((hc.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioi
      (m := 0) (by norm_num)).continuousOn
  have hcont2 : ContinuousOn (fun t : ℝ => iteratedDeriv 2 c t) (Set.Ioi (0 : ℝ)) := by
    rw [hfun2]; exact hcdd
  have hderiv_c : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t := by
    intro t ht
    have hc1' : ContDiffOn ℝ 1 c (Set.Ioi (0 : ℝ)) := hc.of_le (by norm_num)
    have hdiff : DifferentiableAt ℝ c t :=
      ((contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).1 hc1').1.differentiableAt
        (Ioi_mem_nhds ht)
    exact hdiff.hasDerivAt
  have hderiv_d : ∀ t : ℝ, 0 < t → HasDerivAt (deriv c) (iteratedDeriv 2 c t) t := by
    intro t ht
    have hd1 : ContDiffOn ℝ 1 (deriv c) (Set.Ioi (0 : ℝ)) :=
      hc.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
    have hdiff : DifferentiableAt ℝ (deriv c) t :=
      ((contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).1 hd1).1.differentiableAt
        (Ioi_mem_nhds ht)
    have hpt : iteratedDeriv 2 c t = deriv (deriv c) t := by
      have h := congrFun hfun2 t
      simpa using h
    rw [hpt]
    exact hdiff.hasDerivAt
  -- ### the antiderivative and the two integrands
  let G : ℝ → ℝ := fun s => α * (s ^ (1 - r) * deriv c s) + (2 * (m : ℝ) + 5) * (s ^ (-r) * c s)
  let I : ℝ → ℝ :=
    fun s => (α * s ^ 2 * iteratedDeriv 2 c s + (5 + α) * s * deriv c s) * s ^ (-r - 1)
  let J : ℝ → ℝ := fun s => c s * s ^ (-r - 1)
  let Kc : ℝ := (2 * (m : ℝ) + 5) * r
  -- ### continuity of `I`, `J` on the tail
  have hsub : Set.Ioi z ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hz.le
  have hcontJ : ContinuousOn J (Set.Ioi z) := by
    have h4 : ContinuousOn (fun t : ℝ => t ^ (-r - 1)) (Set.Ioi z) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))
    have h5 : ContinuousOn c (Set.Ioi z) := hc.continuousOn.mono hsub
    exact h5.mul h4
  have hcontI : ContinuousOn I (Set.Ioi z) := by
    have h1 : ContinuousOn (fun t : ℝ => iteratedDeriv 2 c t) (Set.Ioi z) := hcont2.mono hsub
    have h2 : ContinuousOn (deriv c) (Set.Ioi z) := hcd.mono hsub
    have h3 : ContinuousOn (fun t : ℝ => t ^ (-r - 1)) (Set.Ioi z) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))
    have h4a : ContinuousOn (fun t : ℝ => α * t ^ 2) (Set.Ioi z) :=
      continuousOn_const.mul (continuousOn_id.pow 2)
    have h4b : ContinuousOn (fun t : ℝ => (5 + α) * t) (Set.Ioi z) :=
      continuousOn_const.mul continuousOn_id
    have h4 : ContinuousOn
        (fun t : ℝ => α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) (Set.Ioi z) :=
      (h4a.mul h1).add (h4b.mul h2)
    exact h4.mul h3
  -- ### integrability of `J`
  have hIntJ : IntegrableOn J (Set.Ioi z) := by
    rw [MeasureTheory.IntegrableOn]
    refine Integrable.mono' (g := fun t : ℝ => A * t ^ (-r - 2)) ?_ ?_ ?_
    · exact ((integrableOn_Ioi_rpow_iff hz).2 (by linarith)).const_mul A
    · exact hcontJ.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans hz ht
      have hAdiv : A / (1 + t) ≤ A / t := div_le_div_of_nonneg_left hA ht0 (by linarith)
      have hAeq : A / t * t ^ (-r - 1) = A * t ^ (-r - 2) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one t, mul_assoc, rpow_neg_one_mul ht0 r]
      rw [Real.norm_eq_abs]
      dsimp only [J]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc |c t| * t ^ (-r - 1)
          ≤ (A / t) * t ^ (-r - 1) :=
            mul_le_mul_of_nonneg_right (le_trans (hc0 t ht0) hAdiv)
              (Real.rpow_nonneg ht0.le _)
        _ = A * t ^ (-r - 2) := hAeq
  -- ### integrability of `I`
  have hIntI : IntegrableOn I (Set.Ioi z) := by
    rw [MeasureTheory.IntegrableOn]
    refine Integrable.mono' (g := fun t : ℝ => (2 * α + 5) * A * t ^ (-r - 2)) ?_ ?_ ?_
    · exact ((integrableOn_Ioi_rpow_iff hz).2 (by linarith)).const_mul ((2 * α + 5) * A)
    · exact hcontI.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans hz ht
      have hp : t ^ (-1 : ℝ) * t ^ (-r - 1) = t ^ (-r - 2) := rpow_neg_one_mul ht0 r
      have hI1 : |α * t ^ 2 * iteratedDeriv 2 c t| * t ^ (-r - 1) ≤ α * A * t ^ (-r - 2) := by
        have habs : |α * t ^ 2 * iteratedDeriv 2 c t| = α * t ^ 2 * |iteratedDeriv 2 c t| := by
          simp only [abs_mul, abs_of_nonneg hα.le, abs_of_nonneg (pow_nonneg ht0.le 2)]
        rw [habs]
        have hdiv : t ^ 2 / (1 + t ^ 3) ≤ 1 / t := pow_div_one_add_pow_le ht0 2
        have hstep : α * t ^ 2 * (A / (1 + t ^ 3)) ≤ α * A * t ^ (-1 : ℝ) := by
          have he : α * t ^ 2 * (A / (1 + t ^ 3)) = α * A * (t ^ 2 / (1 + t ^ 3)) := by ring
          have he2 : α * A * (1 / t) = α * A * t ^ (-1 : ℝ) := by rw [one_div_eq_rpow]
          rw [he, ← he2]
          exact mul_le_mul_of_nonneg_left hdiv (mul_nonneg hα.le hA)
        have hle : α * t ^ 2 * |iteratedDeriv 2 c t| ≤ α * t ^ 2 * (A / (1 + t ^ 3)) :=
          mul_le_mul_of_nonneg_left (hc2 t ht0) (mul_nonneg hα.le (pow_nonneg ht0.le 2))
        calc α * t ^ 2 * |iteratedDeriv 2 c t| * t ^ (-r - 1)
            ≤ (α * t ^ 2 * (A / (1 + t ^ 3))) * t ^ (-r - 1) :=
              mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg ht0.le _)
          _ ≤ (α * A * t ^ (-1 : ℝ)) * t ^ (-r - 1) :=
              mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg ht0.le _)
          _ = α * A * t ^ (-r - 2) := by rw [mul_assoc, hp]
      have hI2 : |(5 + α) * t * deriv c t| * t ^ (-r - 1) ≤ (5 + α) * A * t ^ (-r - 2) := by
        have h5α : (0 : ℝ) ≤ 5 + α := by linarith
        have habs : |(5 + α) * t * deriv c t| = (5 + α) * t * |deriv c t| := by
          simp only [abs_mul, abs_of_nonneg h5α, abs_of_nonneg ht0.le]
        rw [habs]
        have hdiv : t / (1 + t ^ 2) ≤ 1 / t := by
          simpa only [pow_one] using pow_div_one_add_pow_le ht0 1
        have hstep : (5 + α) * t * (A / (1 + t ^ 2)) ≤ (5 + α) * A * t ^ (-1 : ℝ) := by
          have he : (5 + α) * t * (A / (1 + t ^ 2)) = (5 + α) * A * (t / (1 + t ^ 2)) := by ring
          have he2 : (5 + α) * A * (1 / t) = (5 + α) * A * t ^ (-1 : ℝ) := by rw [one_div_eq_rpow]
          rw [he, ← he2]
          exact mul_le_mul_of_nonneg_left hdiv (mul_nonneg h5α hA)
        have hle : (5 + α) * t * |deriv c t| ≤ (5 + α) * t * (A / (1 + t ^ 2)) :=
          mul_le_mul_of_nonneg_left (hc1 t ht0) (mul_nonneg h5α ht0.le)
        calc (5 + α) * t * |deriv c t| * t ^ (-r - 1)
            ≤ ((5 + α) * t * (A / (1 + t ^ 2))) * t ^ (-r - 1) :=
              mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg ht0.le _)
          _ ≤ ((5 + α) * A * t ^ (-1 : ℝ)) * t ^ (-r - 1) :=
              mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg ht0.le _)
          _ = (5 + α) * A * t ^ (-r - 2) := by rw [mul_assoc, hp]
      rw [Real.norm_eq_abs]
      dsimp only [I]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc |α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t| * t ^ (-r - 1)
          ≤ (|α * t ^ 2 * iteratedDeriv 2 c t| + |(5 + α) * t * deriv c t|) * t ^ (-r - 1) :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.rpow_nonneg ht0.le _)
        _ = |α * t ^ 2 * iteratedDeriv 2 c t| * t ^ (-r - 1)
              + |(5 + α) * t * deriv c t| * t ^ (-r - 1) := by ring
        _ ≤ α * A * t ^ (-r - 2) + (5 + α) * A * t ^ (-r - 2) := add_le_add hI1 hI2
        _ = (2 * α + 5) * A * t ^ (-r - 2) := by ring
  have hIntKJ : IntegrableOn (fun t : ℝ => I t - Kc * J t) (Set.Ioi z) :=
    hIntI.sub (hIntJ.const_mul Kc)
  -- ### the derivative of `G`
  have hderivG : ∀ t : ℝ, 0 < t → HasDerivAt G (I t - Kc * J t) t := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht
    have hpow1 : HasDerivAt (fun s : ℝ => s ^ (1 - r)) ((1 - r) * t ^ (1 - r - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl htne)
    have hpow2 : HasDerivAt (fun s : ℝ => s ^ (-r)) ((-r) * t ^ (-r - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl htne)
    have h1 : HasDerivAt (fun s : ℝ => α * (s ^ (1 - r) * deriv c s))
        (α * ((1 - r) * t ^ (1 - r - 1) * deriv c t + t ^ (1 - r) * iteratedDeriv 2 c t))
        t :=
      (hpow1.mul (hderiv_d t ht)).const_mul α
    have h2 : HasDerivAt (fun s : ℝ => (2 * (m : ℝ) + 5) * (s ^ (-r) * c s))
        ((2 * (m : ℝ) + 5) * ((-r) * t ^ (-r - 1) * c t + t ^ (-r) * deriv c t)) t :=
      (hpow2.mul (hderiv_c t ht)).const_mul (2 * (m : ℝ) + 5)
    have hkey : α * ((1 - r) * t ^ (1 - r - 1) * deriv c t + t ^ (1 - r) * iteratedDeriv 2 c t)
        + (2 * (m : ℝ) + 5) * ((-r) * t ^ (-r - 1) * c t + t ^ (-r) * deriv c t)
        = I t - Kc * J t := by
      have hw1 : t ^ (1 - r - 1) = t * t ^ (-r - 1) := by
        rw [show 1 - r - 1 = 1 + (-r - 1) by ring, Real.rpow_add ht 1 (-r - 1),
          Real.rpow_one]
      have hw2 : t ^ (1 - r) = t ^ 2 * t ^ (-r - 1) := by
        rw [show 1 - r = 2 + (-r - 1) by ring, Real.rpow_add ht 2 (-r - 1)]
        rw [Real.rpow_ofNat]
      have hw3 : t ^ (-r) = t * t ^ (-r - 1) := by
        calc t ^ (-r) = t ^ (1 + (-r - 1)) := congrArg (fun p : ℝ => t ^ p) (by ring)
          _ = t ^ 1 * t ^ (-r - 1) := Real.rpow_add ht 1 (-r - 1)
          _ = t * t ^ (-r - 1) := by simp only [Real.rpow_one]
      dsimp only [I, J, Kc]
      rw [hw1, hw2, hw3]
      rw [hrr]
      ring
    exact (h1.add h2).congr_deriv hkey
  -- ### the limit of `G` at infinity
  have hlim : Tendsto G atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero'
      (g := fun t : ℝ => (α * A + (2 * (m : ℝ) + 5) * A) * t ^ (-1 : ℝ))
      (Eventually.of_forall fun t => norm_nonneg (G t)) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht1
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
      have h1 : t ^ (1 - r) * (A / (1 + t ^ 2)) ≤ A * t ^ (-r - 1) := by
        have hdiv : t ^ (1 - r) / (1 + t ^ 2) ≤ t ^ (1 - r) / t ^ 2 :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le _) (pow_pos ht0 2) (by linarith)
        have he : t ^ (1 - r) / t ^ 2 = t ^ (-r - 1) := by
          rw [rpowDivNat ht0 (1 - r) 2,
            show (1 - r) - ((2 : ℕ) : ℝ) = -r - 1 by push_cast; ring]
        have hmul : t ^ (1 - r) * (A / (1 + t ^ 2)) = A * (t ^ (1 - r) / (1 + t ^ 2)) := by ring
        rw [hmul]
        calc A * (t ^ (1 - r) / (1 + t ^ 2)) ≤ A * (t ^ (1 - r) / t ^ 2) :=
              mul_le_mul_of_nonneg_left hdiv hA
          _ = A * t ^ (-r - 1) := by rw [he]
      have h2 : t ^ (-r) * (A / (1 + t)) ≤ A * t ^ (-r - 1) := by
        have hdiv : t ^ (-r) / (1 + t) ≤ t ^ (-r) / t ^ 1 := by
          simpa only [pow_one] using
            div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le _) ht0 (by linarith)
        have he : t ^ (-r) / t ^ 1 = t ^ (-r - 1) := by
          rw [rpowDivNat ht0 (-r) 1,
            show (-r) - ((1 : ℕ) : ℝ) = -r - 1 by push_cast; ring]
        have hmul : t ^ (-r) * (A / (1 + t)) = A * (t ^ (-r) / (1 + t)) := by ring
        rw [hmul]
        calc A * (t ^ (-r) / (1 + t)) ≤ A * (t ^ (-r) / t ^ 1) :=
              mul_le_mul_of_nonneg_left hdiv hA
          _ = A * t ^ (-r - 1) := by rw [he]
      have hA1 : |α * (t ^ (1 - r) * deriv c t)| = α * (t ^ (1 - r) * |deriv c t|) := by
        simp only [abs_mul, abs_of_nonneg hα.le, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hA2 : |(2 * (m : ℝ) + 5) * (t ^ (-r) * c t)|
          = (2 * (m : ℝ) + 5) * (t ^ (-r) * |c t|) := by
        simp only [abs_mul, abs_of_nonneg hm5, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hG : ‖G t‖ ≤ α * (t ^ (1 - r) * |deriv c t|)
          + (2 * (m : ℝ) + 5) * (t ^ (-r) * |c t|) := by
        rw [Real.norm_eq_abs]
        dsimp only [G]
        calc |α * (t ^ (1 - r) * deriv c t) + (2 * (m : ℝ) + 5) * (t ^ (-r) * c t)|
            ≤ |α * (t ^ (1 - r) * deriv c t)|
              + |(2 * (m : ℝ) + 5) * (t ^ (-r) * c t)| := abs_add_le _ _
          _ = α * (t ^ (1 - r) * |deriv c t|) + (2 * (m : ℝ) + 5) * (t ^ (-r) * |c t|) := by
              rw [hA1, hA2]
      calc ‖G t‖
          ≤ α * (t ^ (1 - r) * |deriv c t|) + (2 * (m : ℝ) + 5) * (t ^ (-r) * |c t|) := hG
        _ ≤ α * (t ^ (1 - r) * (A / (1 + t ^ 2)))
              + (2 * (m : ℝ) + 5) * (t ^ (-r) * (A / (1 + t))) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hc1 t ht0) (Real.rpow_nonneg ht0.le _)) hα.le
            · exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hc0 t ht0) (Real.rpow_nonneg ht0.le _)) hm5
        _ ≤ α * (A * t ^ (-r - 1)) + (2 * (m : ℝ) + 5) * (A * t ^ (-r - 1)) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left h1 hα.le
            · exact mul_le_mul_of_nonneg_left h2 hm5
        _ = (α + (2 * (m : ℝ) + 5)) * A * t ^ (-r - 1) := by ring
        _ ≤ (α + (2 * (m : ℝ) + 5)) * A * t ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith))
              (mul_nonneg (by linarith) hA)
        _ = (α * A + (2 * (m : ℝ) + 5) * A) * t ^ (-1 : ℝ) := by ring
    · have hfun : (fun t : ℝ => (α * A + (2 * (m : ℝ) + 5) * A) * t ^ (-1 : ℝ))
          = fun t : ℝ => (α * A + (2 * (m : ℝ) + 5) * A) * t⁻¹ := by
        funext t
        rw [Real.rpow_neg_one]
      rw [hfun]
      simpa using tendsto_inv_atTop_zero.const_mul (α * A + (2 * (m : ℝ) + 5) * A)
  -- ### the fundamental theorem of calculus on `(z, ∞)`
  have hftc : ∫ t in Set.Ioi z, (I t - Kc * J t) = 0 - G z :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (a := z) (f := G) (f' := fun t => I t - Kc * J t)
      (fun t ht => hderivG t (lt_of_lt_of_le hz ht)) hIntKJ hlim
  have hsplit : (∫ t in Set.Ioi z, (I t - Kc * J t))
      = (∫ t in Set.Ioi z, I t) - Kc * (∫ t in Set.Ioi z, J t) := by
    have h1 : (∫ t in Set.Ioi z, (I t - Kc * J t))
        = (∫ t in Set.Ioi z, I t) - (∫ t in Set.Ioi z, Kc * J t) := by
      simpa only [smul_eq_mul] using integral_sub hIntI (hIntJ.const_mul Kc)
    have h2 : (∫ t in Set.Ioi z, Kc * J t) = Kc * (∫ t in Set.Ioi z, J t) :=
      integral_const_mul Kc J
    rw [h1, h2]
  have hmain : (∫ t in Set.Ioi z, I t) = -G z + Kc * (∫ t in Set.Ioi z, J t) := by
    linarith [hftc, hsplit]
  have hfinal : (∫ t in Set.Ioi z, I t)
      = -α * z ^ (1 - r) * deriv c z - (2 * (m : ℝ) + 5) * z ^ (-r) * c z
        + (2 * (m : ℝ) + 5) * r * ∫ t in Set.Ioi z, c t * t ^ (-r - 1) := by
    rw [hmain]
    dsimp only [G, Kc, J]
    ring
  have hgoal_eq : (∫ t in Set.Ioi z, I t)
      = ∫ t in Set.Ioi z,
          (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (-r - 1) := rfl
  rw [← hgoal_eq]
  exact hfinal

end Work.FTS.PhiStar.RadGreenSupport
