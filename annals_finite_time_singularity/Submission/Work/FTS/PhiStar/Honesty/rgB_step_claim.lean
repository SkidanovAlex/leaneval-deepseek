/-
# `Work.FTS.PhiStar.Honesty.rgB_step_claim`

The claimed bounds on the tail primitive
`rgB α m c z = ∫ t in Ioi z, c t * t^{-p-1}` (`p = rgP α m`, `rgB` of
`Submission/Work/FTS/EllExist/RadGreenDefs.lean`), under the hypotheses

* `hvy : |c t| ≤ ε t^{3/2}` for `0 < t ≤ δ` (the "vanishing" bound near `0`),
* `hnear : (c t)²/t⁴ ∈ L¹(0,1)`,
* `hfar : (c t)² ∈ L¹(1,∞)`.

For every `z > 0` with `2 z ≤ δ` there is a number `cB` with

`|cB| ≤ ε z^{3/2-p}/(p - 3/2) + ∫_{(0,1)} c²/x⁴ / 2 + ∫_{1}^∞ c² / 2
        + δ^{-(2p+1)} + 1`

which is a `h ↦ h · ε z^{1/2-p}`-Lipschitz model for `rgB · (z + h)` for small `h > 0`.

The mathematics is elementary: split `(z,∞)` into `(z,δ]`, `(δ,1]`, `(1,∞)`; on the first piece
`hvy` gives `ε ∫_z^δ t^{1/2-p} ≤ ε z^{3/2-p}/(p-3/2)`; on the second and third pieces AM–GM
(`2|ab| ≤ a² + b²`) with `a = c t/t²`, `b = t^{1-p}` (resp. `a = c t`, `b = t^{-p-1}`) plus the
power integrals `∫_δ^1 t^{2-2p} ≤ 2δ^{-(2p+1)}` and `∫_1^∞ t^{-2p-2} = 1/(2p+1)` give the
stated constants.

The subtle point is that `c` is *not* assumed measurable, so the Bochner integrals in `rgB` are
junk (`= 0`) whenever the integrand fails to be a.e. strongly measurable.  The proof therefore
splits on `IntegrableOn (rgF2 α m c) (Ioi z)`:

* if it holds, `cB := rgB α m c z` and both claims are the honest estimates above
  (`rgBstep_value_of_integrableOn` and `rgBstep_step_of_integrableOn`);
* if it fails, the strong-measurability set `{h > 0 : AEStronglyMeasurable (rgF2 ) (Ioi (z+h))}`
  (an up-set) cannot contain arbitrarily small `h`: if it did, then
  `AEStronglyMeasurable (rgF2) (Ioi (z + 1/(n+1)))` for all `n`, hence (countable union
  `⋃_n (z + 1/(n+1), ∞) = (z,∞)`) on `Ioi z`, which combined with the domination by the two
  L¹ functions and `hvy` yields `IntegrableOn (rgF2) (Ioi z)`, a contradiction.  So there is
  `h₀ > 0` with `¬ IntegrableOn (rgF2) (Ioi (z+h))` for every `0 < h ≤ h₀`, whence
  `rgB α m c (z+h) = 0` on that range and the conclusion holds with `cB = 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.rgBstep_integrableOn_Ioi_of_aestronglyMeasurable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty

/-- The half-lines with thresholds `1/(n+1)` exhaust `(z,∞)`. -/
private lemma rgBstep_iUnion_Ioi_eq (z : ℝ) :
    (⋃ n : ℕ, Set.Ioi (z + 1 / ((n : ℝ) + 1))) = Set.Ioi z := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioi]
  constructor
  · rintro ⟨n, hn⟩
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < x - z by linarith)
    exact ⟨n, by linarith⟩

/-- The right-hand side of the value bound is nonnegative (so the degenerate case in which the
Bochner integral of `rgF2` is `0` is trivial). -/
private lemma rgBstep_rhs_nonneg {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hδ : 0 < δ) (hε : 0 ≤ ε)
    {z : ℝ} (hz : 0 < z) :
    0 ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m) / (Work.FTS.EllExist.rgP α m - 3 / 2)
          + (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
          + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
          + δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) + 1 := by
  have hp8 : 8 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_ge hα hα4 hm
  have h1 : 0 ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m)
      / (Work.FTS.EllExist.rgP α m - 3 / 2) := by
    have hz' : 0 ≤ z ^ (3 / 2 - Work.FTS.EllExist.rgP α m) := Real.rpow_nonneg hz.le _
    have hd : 0 < Work.FTS.EllExist.rgP α m - 3 / 2 := by linarith
    positivity
  have h2 : 0 ≤ (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) :=
    MeasureTheory.integral_nonneg (fun x => by positivity)
  have h3 : 0 ≤ (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) :=
    MeasureTheory.integral_nonneg (fun x => by positivity)
  have h4 : 0 < δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) := Real.rpow_pos_of_pos hδ _
  linarith

/-- **Power integral on `(z,δ]`.**  For `p > 3/2` and `0 < z ≤ δ`,
`∫_z^δ t^{1/2-p} ≤ z^{3/2-p}/(p-3/2)`. -/
private lemma rgBstep_rpow_Ioc_le {p z δ : ℝ} (hp : 3 / 2 < p) (hz : 0 < z) (hzδ : z ≤ δ) :
    (∫ t in Set.Ioc z δ, t ^ ((1 : ℝ) / 2 - p)) ≤ z ^ ((3 : ℝ) / 2 - p) / (p - 3 / 2) := by
  rw [← intervalIntegral.integral_of_le hzδ]
  have hr : ((1 : ℝ) / 2 - p) ≠ -1 := by intro h; linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc z δ := by
    rw [Set.uIcc_of_le hzδ]
    simp only [Set.mem_Icc, not_and, not_le]
    intro _
    linarith
  rw [integral_rpow (Or.inr ⟨hr, h0⟩)]
  have e : (1 : ℝ) / 2 - p + 1 = (3 : ℝ) / 2 - p := by ring
  rw [e]
  have key : (δ ^ ((3 : ℝ) / 2 - p) - z ^ ((3 : ℝ) / 2 - p)) / ((3 : ℝ) / 2 - p)
      = (z ^ ((3 : ℝ) / 2 - p) - δ ^ ((3 : ℝ) / 2 - p)) / (p - 3 / 2) := by
    rw [show p - 3 / 2 = -((3 : ℝ) / 2 - p) by ring, div_neg, ← neg_div]
    congr 1
    ring
  rw [key]
  have hδ0 : 0 ≤ δ ^ ((3 : ℝ) / 2 - p) := Real.rpow_nonneg (le_trans hz.le hzδ) _
  have hpos : 0 < p - 3 / 2 := by linarith
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- **Power integral on `(δ,1]`.**  For `p ≥ 2` and `0 < δ ≤ 1`,
`∫_δ^1 t^{2-2p} ≤ 2δ^{-(2p+1)}`. -/
private lemma rgBstep_rpow_Ioc_two_le {p δ : ℝ} (hp : 2 ≤ p) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
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
  have hd2 : δ ^ (-(2 * p - 3)) ≤ δ ^ (-(2 * p + 1)) :=
    Real.rpow_le_rpow_of_exponent_ge (x := δ) (y := -(2 * p - 3)) (z := -(2 * p + 1)) hδ hδ1
      (by linarith)
  have hstep : (δ ^ (-(2 * p - 3)) - 1) / (2 * p - 3) ≤ δ ^ (-(2 * p - 3)) / (2 * p - 3) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    linarith
  have hstep2 : δ ^ (-(2 * p - 3)) / (2 * p - 3) ≤ δ ^ (-(2 * p - 3)) :=
    div_le_self (Real.rpow_pos_of_pos hδ _).le hm3
  linarith

/-- **Power integral on `(1,∞)`.**  For `p > 0`, `∫_1^∞ t^{-2p-2} = 1/(2p+1)`. -/
private lemma rgBstep_rpow_Ioi_one {p : ℝ} (hp : 0 < p) :
    (∫ t in Set.Ioi (1 : ℝ), t ^ (-2 * p - 2)) = 1 / (2 * p + 1) := by
  rw [integral_Ioi_rpow_of_lt (show -2 * p - 2 < -1 by linarith) one_pos]
  have e : -2 * p - 2 + 1 = -(2 * p + 1) := by ring
  rw [e, Real.one_rpow, neg_div, div_neg, neg_neg]

/-- The `c²/x⁴`-integral over `(δ,1]` is dominated by the one over `(0,1)`. -/
private lemma rgBstep_Ioc_sq_div_le {c : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    (∫ t in Set.Ioc δ 1, (c t) ^ 2 / t ^ 4) ≤ ∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4 := by
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_mono_set hnear ?_ ?_
  · filter_upwards with x
    positivity
  · filter_upwards with x hx
    exact ⟨by linarith [hx.1], hx.2⟩

/-- **The value bound, assuming the integrand is integrable on `(z,∞)`.** -/
private lemma rgBstep_value_of_integrableOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → 2 * z ≤ δ →
      MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi z) →
      |Work.FTS.EllExist.rgB α m c z|
        ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m) / (Work.FTS.EllExist.rgP α m - 3 / 2)
          + (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
          + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
          + δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) + 1 := by
  have hp32 : (3 : ℝ) / 2 < Work.FTS.EllExist.rgP α m := by
    have := Work.FTS.EllExist.rgP_ge hα hα4 hm; linarith
  have hp2 : (2 : ℝ) ≤ Work.FTS.EllExist.rgP α m := by
    have := Work.FTS.EllExist.rgP_ge hα hα4 hm; linarith
  have hp1 : 0 < Work.FTS.EllExist.rgP α m := by
    have := Work.FTS.EllExist.rgP_ge hα hα4 hm; linarith
  intro z hz h2z hInt
  have hzδ : z ≤ δ := by linarith
  have hz1 : z ≤ 1 := by linarith
  -- pointwise AM–GM bounds on the two ranges
  have ham_near : ∀ t ∈ Set.Ioc δ 1, |Work.FTS.EllExist.rgF2 α m c t|
      ≤ (c t) ^ 2 / t ^ 4 / 2 + t ^ (2 - 2 * Work.FTS.EllExist.rgP α m) / 2 := by
    intro t ht
    obtain ⟨htδ, _ht1⟩ := ht
    have ht0 : 0 < t := lt_of_lt_of_le hδ htδ.le
    have hpw : Work.FTS.EllExist.rgF2 α m c t
        = c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1) := rfl
    rw [hpw, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    have hsplit : t ^ (-(Work.FTS.EllExist.rgP α m) - 1)
        = t ^ (-2 : ℝ) * t ^ (1 - Work.FTS.EllExist.rgP α m) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have h1 : t ^ (-2 : ℝ) = 1 / t ^ 2 := by
      rw [Real.rpow_neg ht0.le, Real.rpow_two, one_div]
    rw [hsplit, h1]
    have h2 : |c t| * (1 / t ^ 2 * t ^ (1 - Work.FTS.EllExist.rgP α m))
        = (|c t| / t ^ 2) * t ^ (1 - Work.FTS.EllExist.rgP α m) := by ring
    rw [h2]
    have hA : (|c t| / t ^ 2) ^ 2 = (c t) ^ 2 / t ^ 4 := by
      rw [div_pow, sq_abs]; ring_nf
    have hB : (t ^ (1 - Work.FTS.EllExist.rgP α m)) ^ 2
        = t ^ (2 - 2 * Work.FTS.EllExist.rgP α m) := by
      rw [sq, ← Real.rpow_add ht0]; congr 1; ring
    nlinarith [sq_nonneg (|c t| / t ^ 2 - t ^ (1 - Work.FTS.EllExist.rgP α m)), hA, hB]
  have ham_far : ∀ t ∈ Set.Ioi 1, |Work.FTS.EllExist.rgF2 α m c t|
      ≤ (c t) ^ 2 / 2 + t ^ (-2 * Work.FTS.EllExist.rgP α m - 2) / 2 := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    have hpw : Work.FTS.EllExist.rgF2 α m c t
        = c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1) := rfl
    rw [hpw, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    have hB : (t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) ^ 2
        = t ^ (-2 * Work.FTS.EllExist.rgP α m - 2) := by
      rw [sq, ← Real.rpow_add ht0]; congr 1; ring
    nlinarith [sq_nonneg (|c t| - t ^ (-(Work.FTS.EllExist.rgP α m) - 1)), hB, sq_abs (c t)]
  -- `hvy` on `(z,δ]`
  have hvybd : ∀ t ∈ Set.Ioc z δ, |Work.FTS.EllExist.rgF2 α m c t|
      ≤ ε * t ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) := by
    intro t ht
    obtain ⟨hzt, htδ⟩ := ht
    have ht0 : 0 < t := lt_trans hz hzt
    obtain ⟨hc, hpow, hval⟩ : |c t| ≤ ε * t ^ ((3 : ℝ) / 2) ∧
        (0 : ℝ) < t ^ (-(Work.FTS.EllExist.rgP α m) - 1) ∧
        ε * t ^ ((3 : ℝ) / 2) * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)
          = ε * t ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) :=
      ⟨hvy t ht0 htδ, Real.rpow_pos_of_pos ht0 _,
        by rw [mul_assoc, ← Real.rpow_add ht0]; congr 2; ring⟩
    calc |Work.FTS.EllExist.rgF2 α m c t|
        = |c t| * t ^ (-(Work.FTS.EllExist.rgP α m) - 1) := by
          simp only [Work.FTS.EllExist.rgF2, abs_mul, abs_of_pos hpow]
      _ ≤ ε * t ^ ((3 : ℝ) / 2) * t ^ (-(Work.FTS.EllExist.rgP α m) - 1) :=
          mul_le_mul_of_nonneg_right hc hpow.le
      _ = ε * t ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) := hval
  -- integrability of the absolute values
  have hAδ : MeasureTheory.IntegrableOn (fun t => |Work.FTS.EllExist.rgF2 α m c t|)
      (Set.Ioc z δ) := (hInt.mono_set (fun x hx => hx.1)).integrable.abs
  have hAδ1 : MeasureTheory.IntegrableOn (fun t => |Work.FTS.EllExist.rgF2 α m c t|)
      (Set.Ioc δ 1) :=
    (hInt.mono_set (fun x hx => lt_of_le_of_lt hzδ hx.1)).integrable.abs
  have hA1 : MeasureTheory.IntegrableOn (fun t => |Work.FTS.EllExist.rgF2 α m c t|)
      (Set.Ioc z 1) := (hInt.mono_set (fun x hx => hx.1)).integrable.abs
  have hA3 : MeasureTheory.IntegrableOn (fun t => |Work.FTS.EllExist.rgF2 α m c t|)
      (Set.Ioi 1) := (hInt.mono_set (fun x hx => lt_of_le_of_lt hz1 hx)).integrable.abs
  -- the split of `(z,∞)` into `(z,δ]`, `(δ,1]`, `(1,∞)`
  have hsplit1 : (∫ t in Set.Ioi z, |Work.FTS.EllExist.rgF2 α m c t|)
      = (∫ t in Set.Ioc z 1, |Work.FTS.EllExist.rgF2 α m c t|)
        + (∫ t in Set.Ioi 1, |Work.FTS.EllExist.rgF2 α m c t|) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hz1]
    exact MeasureTheory.setIntegral_union (s := Set.Ioc z 1) (t := Set.Ioi 1)
      (Set.disjoint_left.mpr (fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2)) measurableSet_Ioi hA1 hA3
  have hsplit2 : (∫ t in Set.Ioc z 1, |Work.FTS.EllExist.rgF2 α m c t|)
      = (∫ t in Set.Ioc z δ, |Work.FTS.EllExist.rgF2 α m c t|)
        + (∫ t in Set.Ioc δ 1, |Work.FTS.EllExist.rgF2 α m c t|) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hzδ hδ1]
    exact MeasureTheory.setIntegral_union (s := Set.Ioc z δ) (t := Set.Ioc δ 1)
      (Set.disjoint_left.mpr (fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1)) measurableSet_Ioc hAδ hAδ1
  -- integrability of the dominating functions
  have hnearIoc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioc δ 1) :=
    (hnear.mono_set (fun x hx => ⟨by linarith [hx.1], hx.2⟩)).congr_set_ae
      ((MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)).trans
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm)
  have hrpowIoc : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (2 - 2 * Work.FTS.EllExist.rgP α m)) (Set.Ioc δ 1) := by
    refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro t ht
    exact (Real.continuousAt_rpow_const t _
      (Or.inl (ne_of_gt (lt_of_lt_of_le hδ ht.1)))).continuousWithinAt
  have hrpowIoc2 : MeasureTheory.IntegrableOn
      (fun t : ℝ => ε * t ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)) (Set.Ioc z δ) := by
    refine (ContinuousOn.integrableOn_compact isCompact_Icc
      (ContinuousOn.mul continuousOn_const ?_)).mono_set Set.Ioc_subset_Icc_self
    intro t ht
    exact (Real.continuousAt_rpow_const t _
      (Or.inl (ne_of_gt (lt_of_lt_of_le hz ht.1)))).continuousWithinAt
  have hfar_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => (c t) ^ 2 / 2 + t ^ (-2 * Work.FTS.EllExist.rgP α m - 2) / 2) (Set.Ioi 1) :=
    (hfar.div_const 2).add
      ((integrableOn_Ioi_rpow_of_lt (show -2 * Work.FTS.EllExist.rgP α m - 2 < -1 by linarith)
        one_pos).div_const 2)
  have hnear_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => (c t) ^ 2 / t ^ 4 / 2 + t ^ (2 - 2 * Work.FTS.EllExist.rgP α m) / 2)
      (Set.Ioc δ 1) := (hnearIoc.div_const 2).add (hrpowIoc.div_const 2)
  -- the three estimates
  have hP1 : (∫ t in Set.Ioc z δ, |Work.FTS.EllExist.rgF2 α m c t|)
      ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m) / (Work.FTS.EllExist.rgP α m - 3 / 2) := by
    have h1 : (∫ t in Set.Ioc z δ, |Work.FTS.EllExist.rgF2 α m c t|)
        ≤ ∫ t in Set.Ioc z δ, (ε * t ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)) :=
      MeasureTheory.setIntegral_mono_on hAδ hrpowIoc2 measurableSet_Ioc hvybd
    have h2 : (∫ t in Set.Ioc z δ, (ε * t ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)))
        = ε * ∫ t in Set.Ioc z δ, t ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) :=
      MeasureTheory.integral_const_mul _ _
    rw [h2] at h1
    refine h1.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (rgBstep_rpow_Ioc_le hp32 hz hzδ) hε
  have hP2 : (∫ t in Set.Ioc δ 1, |Work.FTS.EllExist.rgF2 α m c t|)
      ≤ (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
        + δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) := by
    have h1 : (∫ t in Set.Ioc δ 1, |Work.FTS.EllExist.rgF2 α m c t|)
        ≤ ∫ t in Set.Ioc δ 1,
            ((c t) ^ 2 / t ^ 4 / 2 + t ^ (2 - 2 * Work.FTS.EllExist.rgP α m) / 2) :=
      MeasureTheory.setIntegral_mono_on hAδ1 hnear_int measurableSet_Ioc ham_near
    have h2 : (∫ t in Set.Ioc δ 1,
          ((c t) ^ 2 / t ^ 4 / 2 + t ^ (2 - 2 * Work.FTS.EllExist.rgP α m) / 2))
        = (∫ t in Set.Ioc δ 1, (c t) ^ 2 / t ^ 4) / 2
          + (∫ t in Set.Ioc δ 1, t ^ (2 - 2 * Work.FTS.EllExist.rgP α m)) / 2 := by
      rw [MeasureTheory.integral_add (hnearIoc.div_const 2) (hrpowIoc.div_const 2),
        MeasureTheory.integral_div, MeasureTheory.integral_div]
    rw [h2] at h1
    have h3 : (∫ t in Set.Ioc δ 1, (c t) ^ 2 / t ^ 4) / 2
        ≤ (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2 :=
      div_le_div_of_nonneg_right (rgBstep_Ioc_sq_div_le hδ hnear) (by norm_num)
    have h4 : (∫ t in Set.Ioc δ 1, t ^ (2 - 2 * Work.FTS.EllExist.rgP α m)) / 2
        ≤ δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) := by
      have hh := rgBstep_rpow_Ioc_two_le hp2 hδ hδ1
      linarith
    linarith
  have hP3 : (∫ t in Set.Ioi 1, |Work.FTS.EllExist.rgF2 α m c t|)
      ≤ (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2 + 1 := by
    have h1 : (∫ t in Set.Ioi 1, |Work.FTS.EllExist.rgF2 α m c t|)
        ≤ ∫ t in Set.Ioi 1, ((c t) ^ 2 / 2 + t ^ (-2 * Work.FTS.EllExist.rgP α m - 2) / 2) :=
      MeasureTheory.setIntegral_mono_on hA3 hfar_int measurableSet_Ioi ham_far
    have h2 : (∫ t in Set.Ioi 1, ((c t) ^ 2 / 2 + t ^ (-2 * Work.FTS.EllExist.rgP α m - 2) / 2))
        = (∫ t in Set.Ioi 1, (c t) ^ 2) / 2
          + (∫ t in Set.Ioi 1, t ^ (-2 * Work.FTS.EllExist.rgP α m - 2)) / 2 := by
      rw [MeasureTheory.integral_add (hfar.div_const 2)
          ((integrableOn_Ioi_rpow_of_lt (show -2 * Work.FTS.EllExist.rgP α m - 2 < -1 by linarith)
            one_pos).div_const 2), MeasureTheory.integral_div, MeasureTheory.integral_div]
    rw [h2] at h1
    have h4 : (∫ t in Set.Ioi (1 : ℝ), t ^ (-2 * Work.FTS.EllExist.rgP α m - 2)) / 2 ≤ 1 := by
      have hh := rgBstep_rpow_Ioi_one hp1
      rw [hh]
      have h3 : 1 / (2 * Work.FTS.EllExist.rgP α m + 1) ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < 2 * Work.FTS.EllExist.rgP α m + 1)]
        linarith
      have h5 : 1 / (2 * Work.FTS.EllExist.rgP α m + 1) / 2
          ≤ 1 / (2 * Work.FTS.EllExist.rgP α m + 1) :=
        div_le_self (by positivity) (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    linarith
  have habs : |∫ t in Set.Ioi z, Work.FTS.EllExist.rgF2 α m c t|
      ≤ ∫ t in Set.Ioi z, |Work.FTS.EllExist.rgF2 α m c t| :=
    MeasureTheory.abs_integral_le_integral_abs
  have hrb : Work.FTS.EllExist.rgB α m c z
      = ∫ t in Set.Ioi z, Work.FTS.EllExist.rgF2 α m c t := rfl
  rw [hrb]
  linarith

/-- **The Lipschitz step of `rgB` on the `hvy`-range.**  If `rgF2` is integrable on `(z,∞)` then
`rgB · (z+h) - rgB · z = -∫_z^{z+h} rgF2` is bounded by `h · ε z^{1/2-p}`, because `|rgF2|` is
dominated there by the decreasing function `ε t^{1/2-p} ≤ ε z^{1/2-p}`. -/
private lemma rgBstep_step_of_integrableOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2)) :
    ∀ z : ℝ, 0 < z → 2 * z ≤ δ →
      MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi z) →
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
        |Work.FTS.EllExist.rgB α m c (z + h) - Work.FTS.EllExist.rgB α m c z|
          ≤ h * (ε * z ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)) := by
  have hp8 : 8 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_ge hα hα4 hm
  intro z hz h2z hInt
  have hz0 : (0 : ℝ) < δ - z := by linarith
  refine ⟨δ - z, hz0, ?_⟩
  intro h hh hhle
  have hzδ : z + h ≤ δ := by linarith
  have hzle : z ≤ z + h := by linarith
  -- pointwise bound on `(z, z+h]`
  have hpp : ∀ x ∈ Set.Ioc z (z + h),
      |Work.FTS.EllExist.rgF2 α m c x| ≤ ε * z ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 < x := lt_trans hz hx1
    have hxδ : x ≤ δ := le_trans hx2 hzδ
    have h1 : |c x| ≤ ε * x ^ ((3 : ℝ) / 2) := hvy x hx0 hxδ
    have h2 : (0 : ℝ) < x ^ (-(Work.FTS.EllExist.rgP α m) - 1) := Real.rpow_pos_of_pos hx0 _
    have h4 : ε * x ^ ((3 : ℝ) / 2) * x ^ (-(Work.FTS.EllExist.rgP α m) - 1)
        = ε * x ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      congr 2
      ring
    have h5 : x ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)
        ≤ z ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) := by
      have hinv : x⁻¹ ≤ z⁻¹ := (inv_le_inv₀ hx0 hz).mpr hx1.le
      have e1 : (x⁻¹) ^ (-((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m))
          = x ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) := by
        rw [Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le, neg_neg]
      have e2 : (z⁻¹) ^ (-((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m))
          = z ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) := by
        rw [Real.inv_rpow hz.le, ← Real.rpow_neg hz.le, neg_neg]
      calc x ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)
          = (x⁻¹) ^ (-((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)) := e1.symm
        _ ≤ (z⁻¹) ^ (-((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)) :=
            Real.rpow_le_rpow (inv_nonneg.mpr hx0.le) hinv (by linarith)
        _ = z ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) := e2
    calc |Work.FTS.EllExist.rgF2 α m c x|
        = |c x| * x ^ (-(Work.FTS.EllExist.rgP α m) - 1) := by
          simp only [Work.FTS.EllExist.rgF2, abs_mul, abs_of_pos h2]
      _ ≤ ε * x ^ ((3 : ℝ) / 2) * x ^ (-(Work.FTS.EllExist.rgP α m) - 1) :=
          mul_le_mul_of_nonneg_right h1 h2.le
      _ = ε * x ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) := h4
      _ ≤ ε * z ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m) :=
          mul_le_mul_of_nonneg_left h5 hε
  have hIocSub : Set.Ioc z (z + h) ⊆ Set.Ioi z := fun s hs => hs.1
  have hIntSub : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c)
      (Set.Ioc z (z + h)) := hInt.mono_set hIocSub
  -- `rgB (z+h) - rgB z = -∫_z^{z+h} rgF2`
  have hdiff : Work.FTS.EllExist.rgB α m c (z + h) - Work.FTS.EllExist.rgB α m c z
      = -(∫ t in Set.Ioc z (z + h), Work.FTS.EllExist.rgF2 α m c t) := by
    have hsdiff := MeasureTheory.setIntegral_sdiff₀ (s := Set.Ioi z) (t := Set.Ioi (z + h))
      (f := Work.FTS.EllExist.rgF2 α m c)
      measurableSet_Ioi.nullMeasurableSet hInt (Set.Ioi_subset_Ioi hzle)
    have hset : Set.Ioi z \ Set.Ioi (z + h) = Set.Ioc z (z + h) := by
      ext s
      simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, not_lt.mp h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, not_lt.mpr h2⟩
    rw [hset] at hsdiff
    simp only [Work.FTS.EllExist.rgB]
    linarith
  rw [hdiff, abs_neg]
  calc |∫ t in Set.Ioc z (z + h), Work.FTS.EllExist.rgF2 α m c t|
      ≤ ∫ t in Set.Ioc z (z + h), |Work.FTS.EllExist.rgF2 α m c t| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _ in Set.Ioc z (z + h),
          (ε * z ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)) := by
        refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun x hx => hpp x hx)
        · exact hIntSub.integrable.abs
        · exact MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; simp)
    _ = h * (ε * z ^ ((1 : ℝ) / 2 - Work.FTS.EllExist.rgP α m)) := by
        rw [← intervalIntegral.integral_of_le hzle, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

theorem rgB_step_claim {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → 2 * z ≤ δ →
      ∃ cB : ℝ,
        |cB| ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m) / (Work.FTS.EllExist.rgP α m - 3 / 2)
          + (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
          + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
          + δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) + 1
        ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
            |Work.FTS.EllExist.rgB α m c (z + h) - cB|
              ≤ h * (ε * z ^ (1 / 2 - Work.FTS.EllExist.rgP α m)) := by
  intro z hz h2z
  by_cases hInt : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi z)
  · -- honest case: `cB := rgB α m c z`
    exact ⟨Work.FTS.EllExist.rgB α m c z,
      rgBstep_value_of_integrableOn hα hα4 hm hδ hδ1 hε hvy hnear hfar z hz h2z hInt,
      rgBstep_step_of_integrableOn hα hα4 hm hε hvy z hz h2z hInt⟩
  · -- degenerate case: the integrand is nowhere (a.e.) strongly measurable near `z`, `cB := 0`
    have hb : ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ¬ MeasureTheory.AEStronglyMeasurable (Work.FTS.EllExist.rgF2 α m c)
            (MeasureTheory.volume.restrict (Set.Ioi (z + h))) := by
      by_contra hcon
      push_neg at hcon
      have hgood : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (Work.FTS.EllExist.rgF2 α m c)
          (MeasureTheory.volume.restrict (Set.Ioi (z + 1 / ((n : ℝ) + 1)))) := by
        intro n
        obtain ⟨h, hh, hhle, hsm⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
        exact hsm.mono_measure
          (MeasureTheory.Measure.restrict_mono (Set.Ioi_subset_Ioi (by linarith)) le_rfl)
      have hcov : MeasureTheory.AEStronglyMeasurable (Work.FTS.EllExist.rgF2 α m c)
          (MeasureTheory.volume.restrict (Set.Ioi z)) := by
        have h := MeasureTheory.AEStronglyMeasurable.iUnion hgood
        rwa [rgBstep_iUnion_Ioi_eq z] at h
      exact hInt (rgBstep_integrableOn_Ioi_of_aestronglyMeasurable hα hα4 hm hδ hδ1 hε hvy
        hnear hfar z hz hcov)
    obtain ⟨h₀, hh₀, hb⟩ := hb
    refine ⟨0, ?_, h₀, hh₀, ?_⟩
    · rw [abs_zero]
      exact rgBstep_rhs_nonneg hα hα4 hm hδ hε hz
    · intro h hh hhle
      have hz' : ¬ MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c)
          (Set.Ioi (z + h)) := fun hI => hb h hh hhle hI.aestronglyMeasurable
      have hzero : Work.FTS.EllExist.rgB α m c (z + h) = 0 := by
        simp only [Work.FTS.EllExist.rgB]
        exact MeasureTheory.integral_undef hz'
      rw [hzero, zero_sub, abs_neg, abs_zero]
      positivity

end Work.FTS.PhiStar.Honesty
