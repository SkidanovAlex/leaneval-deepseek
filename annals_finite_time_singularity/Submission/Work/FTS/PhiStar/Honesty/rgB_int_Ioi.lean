/-
# Integrability of `c t · t^{-p-1}` on a halfline `Ioi δ`, `δ > 0`

The weight `t^{-p-1}` has exponent `≤ -2` (since `p ≥ 1`), so it is *more* singular at `0` than
`t^{-2}`; nevertheless, on `Ioi δ` with `δ > 0` the origin is excluded, and the two hypotheses

* `hnear : ∫_{(0,1)} (c t)²/t⁴ < ∞` and
* `hfar : ∫_{(1,∞)} (c t)² < ∞`

control `c` on the two pieces of `Ioi δ ⊆ (δ, 1] ∪ (1, ∞)`:

* on `(δ, 1]` the weight is bounded by `δ^{-p-1}` and
  `|c x| ≤ x²·|c x|/x² ≤ ((c x)²/x⁴ + 1)/2`, so the integrand is dominated by a multiple of
  `(c x)²/x⁴ + 1`, integrable on the finite interval `(δ, 1)`;
* on `(1, ∞)` AM–GM (`2|ab| ≤ a² + b²`) gives
  `|c x|·x^{-p-1} ≤ ((c x)² + x^{-2p-2})/2`, and `x^{-2p-2}` is integrable there because
  `-2p-2 < -1`.

No measurability or continuity of `c` is used beyond the a.e. strong measurability of `|c|`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * (|a| * |b|) ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  rw [abs_mul]
  linarith [h, sq_abs a, sq_abs b]

/-- AM–GM in the form used below: `|y| ≤ (y² + 1)/2`. -/
private lemma abs_le_sq_add_one_div_two (y : ℝ) : |y| ≤ (y ^ 2 + 1) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]

/-- For `0 < δ ≤ x` the negative power `x^{-p-1}` is dominated by its value at `δ`, provided the
exponent is negative, i.e. `0 ≤ p`. -/
private lemma rpow_neg_sub_one_le {t x p : ℝ} (ht : 0 < t) (htx : t ≤ x) (hp : 0 ≤ p) :
    x ^ (-p - 1) ≤ t ^ (-p - 1) := by
  have hx : 0 < x := lt_of_lt_of_le ht htx
  rw [show -p - 1 = -(p + 1) from by ring]
  rw [Real.rpow_neg hx.le, Real.rpow_neg ht.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ht _) (Real.rpow_le_rpow ht.le htx (by linarith))

theorem rgB_int_Ioi {c : ℝ → ℝ} {p δ : ℝ} (hp : 1 ≤ p) (hδ : 0 < δ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |c t|)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => ‖c t * t ^ (-p - 1)‖) (Set.Ioi δ) := by
  have hp0 : 0 ≤ p := by linarith
  -- ### a.e. strong measurability of `|c t| * t^{-p-1}` on `Ioi δ`
  have hAesm : AEStronglyMeasurable (fun t : ℝ => |c t| * t ^ (-p - 1))
      (volume.restrict (Ioi δ)) := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => |c t|) (volume.restrict (Ioi δ)) :=
      hmeas.mono_set (fun x hx => lt_trans hδ hx)
    have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1))
        (volume.restrict (Ioi δ)) :=
      (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt (lt_trans hδ hx)))).aestronglyMeasurable measurableSet_Ioi
    exact h1.mul h2
  -- ### The part `(δ, 1]`: bounded weight, `L²` control of `c` from `hnear`
  have hA : IntegrableOn (fun x : ℝ => |c x| * x ^ (-p - 1)) (Ioc δ 1) := by
    have hIoo : Integrable (fun x : ℝ => |c x| * x ^ (-p - 1))
        (volume.restrict (Ioo δ 1)) := by
      have hmaj : Integrable
          (fun x : ℝ => δ ^ (-p - 1) * (((c x) ^ 2 / x ^ 4 + 1) / 2))
          (volume.restrict (Ioo δ 1)) := by
        have h11 : Integrable (fun x : ℝ => (c x) ^ 2 / x ^ 4)
            (volume.restrict (Ioo δ 1)) :=
          hnear.mono_set (fun x hx => ⟨lt_trans hδ hx.1, hx.2⟩)
        have h12 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo δ 1)) :=
          integrable_const 1
        exact ((h11.add h12).div_const 2).const_mul _
      refine Integrable.mono' hmaj (hAesm.mono_set (fun x hx => hx.1)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hxδ : δ < x := hx.1
      have hx1 : x ≤ 1 := hx.2.le
      have hx0 : 0 < x := lt_trans hδ hxδ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg (c x)),
        abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      have hw : x ^ (-p - 1) ≤ δ ^ (-p - 1) := rpow_neg_sub_one_le hδ hxδ.le hp0
      -- `|c x| ≤ x²·|c x|/x² ≤ ((c x)²/x⁴ + 1)/2` on `(δ,1]`
      have hcA : |c x| ≤ ((c x) ^ 2 / x ^ 4 + 1) / 2 := by
        have h1 : |c x / x ^ 2| ≤ ((c x / x ^ 2) ^ 2 + 1) / 2 := abs_le_sq_add_one_div_two _
        have h2 : (c x / x ^ 2) ^ 2 = (c x) ^ 2 / x ^ 4 := by
          rw [div_pow, show (x ^ 2) ^ 2 = x ^ 4 from by ring]
        have h3 : |c x / x ^ 2| = |c x| / x ^ 2 := by
          rw [abs_div, abs_of_nonneg (sq_nonneg x)]
        have h4 : x ^ 2 * (|c x| / x ^ 2) = |c x| := by
          field_simp
        have h5 : x ^ 2 ≤ 1 := by nlinarith [hx1, hx0]
        rw [h2] at h1
        rw [h3] at h1
        calc |c x| = x ^ 2 * (|c x| / x ^ 2) := h4.symm
          _ ≤ 1 * (|c x| / x ^ 2) := mul_le_mul_of_nonneg_right h5 (by positivity)
          _ = |c x| / x ^ 2 := one_mul _
          _ ≤ ((c x) ^ 2 / x ^ 4 + 1) / 2 := h1
      calc |c x| * x ^ (-p - 1)
          ≤ |c x| * δ ^ (-p - 1) := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
        _ = δ ^ (-p - 1) * |c x| := by ring
        _ ≤ δ ^ (-p - 1) * (((c x) ^ 2 / x ^ 4 + 1) / 2) :=
            mul_le_mul_of_nonneg_left hcA (Real.rpow_nonneg hδ.le _)
    exact MeasureTheory.IntegrableOn.congr_set_ae hIoo
      (Ioo_ae_eq_Ioc (a := δ) (b := 1)).symm
  -- ### The part `(1, ∞)`: `c ∈ L²` against the `L²` weight `x^{-p-1}`
  have hB : IntegrableOn (fun x : ℝ => |c x| * x ^ (-p - 1)) (Ioi (max δ 1)) := by
    have hδ' : 0 < max δ 1 := lt_of_lt_of_le zero_lt_one (le_max_right δ 1)
    have hmaj : Integrable (fun x : ℝ => ((c x) ^ 2 + x ^ (-(2 * p) - 2)) / 2)
        (volume.restrict (Ioi (max δ 1))) := by
      have h1 : Integrable (fun x => (c x) ^ 2) (volume.restrict (Ioi (max δ 1))) :=
        hfar.mono_set (fun x hx => lt_of_le_of_lt (le_max_right δ 1) hx)
      have h2 : Integrable (fun x => x ^ (-(2 * p) - 2)) (volume.restrict (Ioi (max δ 1))) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hδ'
      exact (h1.add h2).div_const 2
    refine Integrable.mono' hmaj (hAesm.mono_set (fun x hx => ?_)) ?_
    · exact lt_of_le_of_lt (le_max_left δ 1) hx
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_right δ 1) hx)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg (c x)),
        abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      have hb : (x ^ (-p - 1)) ^ 2 = x ^ (-(2 * p) - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        congr 1
        ring
      calc |c x| * x ^ (-p - 1)
          = |c x * x ^ (-p - 1)| := by
              rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
        _ ≤ ((c x) ^ 2 + (x ^ (-p - 1)) ^ 2) / 2 := abs_mul_le_half_sq_add_sq _ _
        _ = ((c x) ^ 2 + x ^ (-(2 * p) - 2)) / 2 := by rw [hb]
  -- ### Glue the two parts
  have hsub : Ioi δ ⊆ Ioc δ 1 ∪ Ioi (max δ 1) := by
    intro x hx
    by_cases h : x ≤ 1
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (max_lt hx (lt_of_not_ge h))
  have hU : IntegrableOn (fun x : ℝ => |c x| * x ^ (-p - 1))
      (Ioc δ 1 ∪ Ioi (max δ 1)) := hA.union hB
  have hmain : IntegrableOn (fun x : ℝ => |c x| * x ^ (-p - 1)) (Ioi δ) :=
    hU.mono_set hsub
  -- ### Rewrite the absolutised integrand as the norm of the original one
  refine hmain.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans hδ hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]

end Work.FTS.PhiStar.Honesty
