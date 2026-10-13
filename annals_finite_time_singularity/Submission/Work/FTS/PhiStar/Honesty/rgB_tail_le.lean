/-
# The tail bound for the growing branch of the radial Green function

`Work.FTS.PhiStar.Honesty.rgB_tail_le` bounds the `(δ,∞)`-integral of `t ↦ |c t| t^{-p-1}`
(the integrand of `Work.FTS.EllExist.rgB` with `p = rgP α m ≥ 8`) by

  `(∫_{(0,1)} c²/x⁴)/2 + (∫_{(1,∞)} c²)/2 + δ^{-(2p+1)} + 1`.

The route (everything is elementary; the content is the AM–GM split):

* `rgB_int_Ioi` (proved in `rgB_int_Ioi.lean`) gives `IntegrableOn` of the integrand on all of
  `(δ,∞)` from the two `L¹`-hypotheses and the a.e. strong measurability of `|c|`.  This is what
  makes the *split* of the tail integral legitimate: `setIntegral_union` needs `IntegrableOn` on
  each piece;
* split `(δ,∞) = (δ,1] ∪ (1,∞)` (disjoint measurable pieces) with `setIntegral_union`;
* on `(1,∞)` use `rgB_tail_far_le` (`Submission/.../rgB_tail_far_le.lean`): AM–GM
  `|c t|·t^{-p-1} ≤ c(t)²/2 + t^{-2p-2}/2` and `∫_1^∞ t^{-2p-2} = 1/(2p+1) ≤ 1`;
* on `(δ,1]` the integrand is dominated by `c(t)²/(2t⁴) + t^{2-2p}/2` (AM–GM with
  `a = |c t|/t²`, `b = t^{1-p}`, using `t^{-p-1} = t^{-2}·t^{1-p}`); the first piece is
  comparable with `∫_{(0,1)} c²/x⁴` because `(δ,1] ⊆ (0,1)` up to a null set, and the second is
  `≤ δ^{-(2p+1)}` since `∫_δ^1 t^{2-2p} = (δ^{-(2p-3)} - 1)/(2p-3) ≤ δ^{-(2p-3)} ≤ δ^{-(2p+1)}`
  for `p ≥ 2` and `δ ≤ 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Honesty.rgB_int_Ioi
import Submission.Work.FTS.PhiStar.Honesty.rgB_tail_far_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-! ## The near piece `(δ,1]` -/

/-- **Power integral on `(δ,1]`.**  For `p ≥ 2` and `0 < δ ≤ 1`,
`∫_δ^1 t^{2-2p} ≤ 2 δ^{-(2p+1)}`.  (The exact value of the integral is
`(δ^{-(2p-3)} - 1)/(2p-3) ≤ δ^{-(2p-3)} = δ^{-(2p+1)}·δ⁴ ≤ δ^{-(2p+1)}`.) -/
private lemma rgBtail_rpow_Ioc_two_le {p δ : ℝ} (hp : 2 ≤ p) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ t in Set.Ioc δ 1, t ^ (2 - 2 * p)) ≤ 2 * δ ^ (-(2 * p + 1)) := by
  rw [← intervalIntegral.integral_of_le hδ1]
  have hr : (2 - 2 * p) ≠ -1 := by intro h; linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc δ 1 := by
    rw [Set.uIcc_of_le hδ1]
    simp only [Set.mem_Icc, not_and, not_le]
    intro _
    linarith
  rw [integral_rpow (Or.inr ⟨hr, h0⟩)]
  have e : 2 - 2 * p + 1 = 3 - 2 * p := by ring
  rw [e, Real.one_rpow]
  rw [show δ ^ (3 - 2 * p) = δ ^ (-(2 * p - 3)) by congr 1; ring]
  have h3 : (1 - δ ^ (-(2 * p - 3))) / (3 - 2 * p)
      = (δ ^ (-(2 * p - 3)) - 1) / (2 * p - 3) := by
    rw [show 3 - 2 * p = -(2 * p - 3) by ring, div_neg, ← neg_div]
    congr 1
    ring
  rw [h3]
  have hm3 : (1 : ℝ) ≤ 2 * p - 3 := by linarith
  have hd1 : 1 ≤ δ ^ (-(2 * p - 3)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge (x := δ) (y := 0) (z := -(2 * p - 3)) hδ hδ1
      (show -(2 * p - 3) ≤ 0 by linarith)
    simpa using h
  have hstep : (δ ^ (-(2 * p - 3)) - 1) / (2 * p - 3) ≤ δ ^ (-(2 * p - 3)) / (2 * p - 3) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    linarith
  have hstep2 : δ ^ (-(2 * p - 3)) / (2 * p - 3) ≤ δ ^ (-(2 * p - 3)) :=
    div_le_self (Real.rpow_pos_of_pos hδ _).le hm3
  have hd2 : δ ^ (-(2 * p - 3)) ≤ δ ^ (-(2 * p + 1)) :=
    Real.rpow_le_rpow_of_exponent_ge (x := δ) (y := -(2 * p - 3)) (z := -(2 * p + 1)) hδ hδ1
      (by linarith)
  linarith

/-- The `c²/x⁴`-integral over `(δ,1]` is dominated by the one over `(0,1)`. -/
private lemma rgBtail_Ioc_sq_div_le {c : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    (∫ t in Set.Ioc δ 1, (c t) ^ 2 / t ^ 4) ≤ ∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4 := by
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_mono_set hnear ?_ ?_
  · filter_upwards with x
    positivity
  · filter_upwards with x hx
    exact ⟨by linarith [hx.1], hx.2⟩

/-- **The near piece `(δ,1]`.**  For `p ≥ 2`, `0 < δ ≤ 1` and `(c t)²/t⁴ ∈ L¹(0,1)`,

  `∫_δ^1 ‖c t·t^{-p-1}‖ ≤ (1/2)∫_0^1 c²/x⁴ + δ^{-(2p+1)}`. -/
private lemma rgBtail_near_le {c : ℝ → ℝ} {p δ : ℝ} (hp : 2 ≤ p) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    ∫ t in Set.Ioc δ 1, ‖c t * t ^ (-p - 1)‖
      ≤ (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2 + δ ^ (-(2 * p + 1)) := by
  -- AM–GM pointwise on `(δ,1]`
  have ham : ∀ t ∈ Set.Ioc δ 1, ‖c t * t ^ (-p - 1)‖
      ≤ (c t) ^ 2 / t ^ 4 / 2 + t ^ (2 - 2 * p) / 2 := by
    intro t ht
    obtain ⟨htδ, _ht1⟩ := ht
    have ht0 : 0 < t := lt_trans hδ htδ
    have hsplit : t ^ (-p - 1) = t ^ (-2 : ℝ) * t ^ (1 - p) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have h1 : t ^ (-2 : ℝ) = 1 / t ^ 2 := by
      rw [Real.rpow_neg ht0.le, Real.rpow_two, one_div]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    rw [hsplit, h1]
    have h2 : |c t| * (1 / t ^ 2 * t ^ (1 - p)) = (|c t| / t ^ 2) * t ^ (1 - p) := by ring
    rw [h2]
    have hA : (|c t| / t ^ 2) ^ 2 = (c t) ^ 2 / t ^ 4 := by
      rw [div_pow, sq_abs]; ring_nf
    have hB : (t ^ (1 - p)) ^ 2 = t ^ (2 - 2 * p) := by
      rw [sq, ← Real.rpow_add ht0]; congr 1; ring
    nlinarith [sq_nonneg (|c t| / t ^ 2 - t ^ (1 - p)), hA, hB]
  -- integrability of both pieces of the majorant
  have hnearIoc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioc δ 1) :=
    (hnear.mono_set (fun x hx => ⟨by linarith [hx.1], hx.2⟩)).congr_set_ae
      ((MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)).trans
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm)
  have hrpowIoc : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (2 - 2 * p)) (Set.Ioc δ 1) := by
    refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro t ht
    exact (Real.continuousAt_rpow_const t _
      (Or.inl (ne_of_gt (lt_of_lt_of_le hδ ht.1)))).continuousWithinAt
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => (c t) ^ 2 / t ^ 4 / 2 + t ^ (2 - 2 * p) / 2) (Set.Ioc δ 1) :=
    (hnearIoc.div_const 2).add (hrpowIoc.div_const 2)
  have hmono : ∫ t in Set.Ioc δ 1, ‖c t * t ^ (-p - 1)‖
      ≤ ∫ t in Set.Ioc δ 1, ((c t) ^ 2 / t ^ 4 / 2 + t ^ (2 - 2 * p) / 2) :=
    MeasureTheory.setIntegral_mono_of_nonneg (fun t _ => norm_nonneg _) ham hmaj
  have hval : ∫ t in Set.Ioc δ 1, ((c t) ^ 2 / t ^ 4 / 2 + t ^ (2 - 2 * p) / 2)
      = (∫ t in Set.Ioc δ 1, (c t) ^ 2 / t ^ 4) / 2
        + (∫ t in Set.Ioc δ 1, t ^ (2 - 2 * p)) / 2 := by
    rw [MeasureTheory.integral_add (hnearIoc.div_const 2) (hrpowIoc.div_const 2),
      MeasureTheory.integral_div, MeasureTheory.integral_div]
  rw [hval] at hmono
  have h3 : (∫ t in Set.Ioc δ 1, (c t) ^ 2 / t ^ 4) / 2
      ≤ (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2 :=
    div_le_div_of_nonneg_right (rgBtail_Ioc_sq_div_le hδ hnear) (by norm_num)
  have h4 : (∫ t in Set.Ioc δ 1, t ^ (2 - 2 * p)) / 2 ≤ δ ^ (-(2 * p + 1)) := by
    have hh := rgBtail_rpow_Ioc_two_le hp hδ hδ1
    linarith
  linarith

/-! ## The tail bound -/

theorem rgB_tail_le {c : ℝ → ℝ} {p δ : ℝ} (hp : 2 ≤ p) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |c t|)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∫ t in Set.Ioi δ, ‖c t * t ^ (-p - 1)‖
      ≤ (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
        + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
        + δ ^ (-(2 * p + 1)) + 1 := by
  have hp1 : 1 ≤ p := by linarith
  -- the integrand is integrable on the whole tail `(δ,∞)`
  have hInt : MeasureTheory.IntegrableOn (fun t : ℝ => ‖c t * t ^ (-p - 1)‖) (Set.Ioi δ) :=
    rgB_int_Ioi hp1 hδ hmeas hnear hfar
  -- the tail splits as `(δ,1] ∪ (1,∞)`
  have hU : Set.Ioc δ 1 ∪ Set.Ioi 1 = Set.Ioi δ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  have hIntU : MeasureTheory.IntegrableOn (fun t : ℝ => ‖c t * t ^ (-p - 1)‖)
      (Set.Ioc δ 1 ∪ Set.Ioi 1) := hInt.mono_set (by rw [hU])
  have hIntA : MeasureTheory.IntegrableOn (fun t : ℝ => ‖c t * t ^ (-p - 1)‖) (Set.Ioc δ 1) :=
    hIntU.mono_set Set.subset_union_left
  have hIntB : MeasureTheory.IntegrableOn (fun t : ℝ => ‖c t * t ^ (-p - 1)‖) (Set.Ioi 1) :=
    hIntU.mono_set Set.subset_union_right
  have hdisj : Disjoint (Set.Ioc δ 1) (Set.Ioi 1) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2)
  rw [← hU, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIntA hIntB]
  -- the two region estimates
  have hN := rgBtail_near_le (c := c) (p := p) (δ := δ) hp hδ hδ1 hnear
  have hF := rgB_tail_far_le (c := c) (p := p) hp hfar
  linarith

end Work.FTS.PhiStar.Honesty
