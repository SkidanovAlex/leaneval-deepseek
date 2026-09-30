import Mathlib
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.dyadic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The weighted frequency integral of `dirP` is dominated by the sup-bound `S`

For a bounded coefficient sequence `a` (so `‖dirP a X t‖ ≤ Σ_{n ∈ [X,3X]} 1/n`) and a scale
`R > 0`, the hypothesis that every `T ≥ R` satisfies
`(R/T) * ∫_{-(2T)}^{2T} ‖dirP a X t‖² ≤ S` controls the weighted integral
`∫_ℝ ‖dirP a X t‖² * (min 1 (8R/(1+|t|)))²`.

The weight is at most `1` on `|t| ≤ 8R`, and at most `(8R)²/t²` off it, so the integral splits
into the inner piece `∫_{-8R}^{8R} ‖dirP‖² ≤ 4 S` (hypothesis with `T = 4R`) and the dyadic
tail `∫_{8R < |t|} ‖dirP‖² · (8R)²/t² ≤ 2 · (8 S)` (`dyadicTail_le`, using `S' = 8S` and
`R' = 8R`).  Total `≤ 20 S ≤ 100 S`.
-/

namespace Work.BMF

open MeasureTheory Set Filter
open scoped BigOperators

/-- The Dirichlet polynomial `dirP a X t = Σ_{n ∈ [X,3X]} a n · n^{-(1+it)}` is continuous in
`t`. -/
private lemma continuous_dirP' (a : ℕ → ℂ) (X : ℝ) : Continuous (fun t : ℝ => dirP a X t) := by
  unfold dirP
  apply continuous_finsetSum
  intro n _
  have hf : Continuous (fun t : ℝ => -(1 + Complex.I * (t : ℂ))) := by fun_prop
  exact continuous_const.mul (hf.const_cpow (Or.inr (fun t => by
    intro h; have := congrArg Complex.re h; simp at this)))

/-- Pointwise size of the Dirichlet polynomial `dirP` against the harmonic sum over its range. -/
private lemma dirP_norm_le_sum' (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X t : ℝ) (hX : 1 ≤ X) :
    ‖dirP a X t‖ ≤ ∑ n ∈ natIcc X (3*X), (1:ℝ)/(n:ℝ) := by
  unfold dirP
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn1 : 1 ≤ n := one_le_of_mem_natIccD hX hn
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1]
  have hre : (-(1 + Complex.I*(t:ℂ))).re = -1 := by simp
  rw [hre, Real.rpow_neg_one]
  calc ‖a n‖ * (n:ℝ)⁻¹ ≤ 1 * (n:ℝ)⁻¹ := mul_le_mul_of_nonneg_right (ha n) (by positivity)
    _ = (1:ℝ)/(n:ℝ) := by rw [one_mul, one_div]

theorem dirP_weighted_integral_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X R S : ℝ)
    (hX : 1 ≤ X) (hR : 0 < R) (hS : 0 ≤ S)
    (hsup : ∀ T : ℝ, R ≤ T → R/T * (∫ t in (-(2*T))..(2*T), ‖dirP a X t‖^2) ≤ S) :
    (∫ t : ℝ, ‖dirP a X t‖^2 * (min 1 ((8*R)/(1+|t|)))^2) ≤ 100 * S := by
  have hcontD : Continuous (fun t : ℝ => dirP a X t) := continuous_dirP' a X
  have hnormD : ∀ t : ℝ, ‖dirP a X t‖ ≤ ∑ n ∈ natIcc X (3*X), (1:ℝ)/(n:ℝ) :=
    fun t => dirP_norm_le_sum' a ha X t hX
  set B : ℝ := ∑ n ∈ natIcc X (3*X), (1:ℝ)/(n:ℝ) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; exact Finset.sum_nonneg (fun n _ => by positivity)
  set R' : ℝ := 8*R with hR'def
  set F : ℝ → ℝ := fun t => ‖dirP a X t‖^2 with hFdef
  set W : ℝ → ℝ := fun t => (min 1 (R'/(1+|t|)))^2 with hWdef
  change (∫ t : ℝ, F t * W t) ≤ 100 * S
  have hR'pos : 0 < R' := by rw [hR'def]; positivity
  have hRR' : R ≤ R' := by rw [hR'def]; linarith [hR]
  have hS8 : 0 ≤ 8*S := by linarith [hS]
  have hFnn : ∀ t, 0 ≤ F t := fun t => by rw [hFdef]; positivity
  have hFcont : Continuous F := by rw [hFdef]; exact (hcontD.norm).pow 2
  have hFmeas : Measurable F := hFcont.measurable
  have hFbd : ∀ t, F t ≤ B^2 := by
    intro t
    rw [hFdef]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    rw [hBdef]
    exact hnormD t
  have hsup' : ∀ T : ℝ, R' ≤ T → R'/T * (∫ t in (-(2*T))..(2*T), F t) ≤ 8*S := by
    intro T hT
    have hTR : R ≤ T := le_trans hRR' hT
    have h := hsup T hTR
    have heq : R'/T = 8 * (R/T) := by rw [hR'def]; ring
    rw [heq, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have htail : ∫ t in {t : ℝ | R' < |t|}, F t * (R'^2/t^2) ≤ 2*(8*S) :=
    dyadicTail_le F hFnn hFmeas (B^2) hFbd R' (8*S) hR'pos hS8 hsup'
  have hW_nn : ∀ t, 0 ≤ W t := fun t => by rw [hWdef]; exact sq_nonneg _
  have hW_le_one : ∀ t, W t ≤ 1 := by
    intro t
    rw [hWdef]
    refine pow_le_one₀ ?_ ?_
    · exact le_min (by norm_num) (by positivity)
    · exact min_le_left _ _
  have hW_le_tail : ∀ t, R' < |t| → W t ≤ R'^2/t^2 := by
    intro t ht
    have htpos : 0 < |t| := lt_trans hR'pos ht
    have h1 : min 1 (R'/(1+|t|)) ≤ R'/|t| := by
      calc min 1 (R'/(1+|t|)) ≤ R'/(1+|t|) := min_le_right _ _
        _ ≤ R'/|t| := by
              apply div_le_div_of_nonneg_left (by positivity) htpos
              linarith
    have h2 : 0 ≤ min 1 (R'/(1+|t|)) := le_min (by norm_num) (by positivity)
    rw [hWdef, show R'^2/t^2 = (R'/|t|)^2 by rw [div_pow, sq_abs]]
    exact pow_le_pow_left₀ h2 h1 2
  have hinner : ∫ t in Set.Icc (-R') R', F t ≤ 4*S := by
    have h := hsup (4*R) (by linarith [hR])
    have h2T : 2*(4*R) = R' := by rw [hR'def]; ring
    rw [h2T] at h
    have hc : R/(4*R) = 1/4 := by field_simp
    rw [hc] at h
    have hI : ∫ t in (-R')..R', F t = ∫ t in Set.Icc (-R') R', F t := by
      rw [intervalIntegral.integral_of_le (show -R' ≤ R' by linarith [hR'pos])]
      exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
    rw [hI] at h
    linarith
  have hIntF : IntegrableOn F (Set.Icc (-R') R') volume := by
    refine IntegrableOn.of_bound measure_Icc_lt_top (hFmeas.aestronglyMeasurable.restrict) (B^2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x)]
    exact hFbd x
  have hIntT : IntegrableOn (fun t => F t * (R'^2/t^2)) {t : ℝ | R' < |t|} volume :=
    tail_integrable F hFnn hFmeas (B^2) hFbd R' hR'pos
  have hmeasT : MeasurableSet {t : ℝ | R' < |t|} :=
    measurableSet_lt measurable_const measurable_id.abs
  have hIntMaj : Integrable (fun t => (Set.Icc (-R') R').indicator F t +
      ({t : ℝ | R' < |t|}).indicator (fun t => F t * (R'^2/t^2)) t) :=
    (hIntF.integrable_indicator measurableSet_Icc).add (hIntT.integrable_indicator hmeasT)
  have hA : ∀ t, t ∈ Set.Icc (-R') R' ↔ |t| ≤ R' := fun t => by rw [Set.mem_Icc, abs_le]
  have hpt : ∀ t, F t * W t ≤ (Set.Icc (-R') R').indicator F t +
      ({t : ℝ | R' < |t|}).indicator (fun t => F t * (R'^2/t^2)) t := by
    intro t
    by_cases h : |t| ≤ R'
    · have hnot : t ∉ {t : ℝ | R' < |t|} := by simp [h]
      rw [Set.indicator_of_mem ((hA t).mpr h), Set.indicator_of_notMem hnot, add_zero]
      exact mul_le_of_le_one_right (hFnn t) (hW_le_one t)
    · have hnot : t ∉ Set.Icc (-R') R' := fun hm => h ((hA t).mp hm)
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem (s := {t : ℝ | R' < |t|}) (lt_of_not_ge h), zero_add]
      exact mul_le_mul_of_nonneg_left (hW_le_tail t (lt_of_not_ge h)) (hFnn t)
  have hle1 : (∫ t : ℝ, F t * W t) ≤ ∫ t : ℝ, ((Set.Icc (-R') R').indicator F t +
      ({t : ℝ | R' < |t|}).indicator (fun t => F t * (R'^2/t^2)) t) :=
    MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun t => mul_nonneg (hFnn t) (hW_nn t))
      hIntMaj (Eventually.of_forall hpt)
  have hsplit : (∫ t : ℝ, ((Set.Icc (-R') R').indicator F t +
      ({t : ℝ | R' < |t|}).indicator (fun t => F t * (R'^2/t^2)) t))
      = (∫ t in Set.Icc (-R') R', F t) + ∫ t in {t : ℝ | R' < |t|}, F t * (R'^2/t^2) := by
    rw [MeasureTheory.integral_add (hIntF.integrable_indicator measurableSet_Icc)
      (hIntT.integrable_indicator hmeasT)]
    rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.integral_indicator hmeasT]
  calc (∫ t : ℝ, F t * W t) ≤ _ := hle1
    _ = (∫ t in Set.Icc (-R') R', F t) + ∫ t in {t : ℝ | R' < |t|}, F t * (R'^2/t^2) := hsplit
    _ ≤ 4*S + 2*(8*S) := add_le_add hinner htail
    _ ≤ 100*S := by linarith [hS]

end Work.BMF
