/-
# Integrability of the tail Green integrand `rgF2` away from the origin

`Work.FTS.EllExist.rgF2 α m c t = c t · t^{-p-1}` with `p = rgP α m = 2m/α ≥ 8` is the
integrand of the growing branch of the radial Green function.  Since `p ≥ 8`, the weight
`t^{-p-1}` blows up like `t^{-9}` at the origin; nevertheless `rgF2` is integrable on any
`Ioi t` with `t > 0`, because the origin is excluded and the weight decays at infinity.

The two hypotheses on `c` give exactly this:

* `hnear : ∫_{(0,1)} (c t)²/t⁴ < ∞` — on a compact subinterval `(t,1]` of `(0,1)` this controls
  the `L¹`-norm of `c`: `|c x| ≤ (|c x/x²|)·x² ≤ ((c x)²/x⁴ + 1)/2`, and the constant weight
  `x^{-p-1}` is bounded by `t^{-p-1}` there;
* `hfar : ∫_{(1,∞)} (c t)² < ∞` — at infinity `c` is `L²` and `t^{-p-1}` is `L²` (since
  `2p+2 > 1`), so AM–GM (`2|ab| ≤ a² + b²`) gives the domination
  `|c x|·x^{-p-1} ≤ ((c x)² + x^{-2p-2})/2`.

The only hypothesis really needed about `rgF2` itself is the a.e. strong measurability: it is
not assumed that `c` is measurable (a function whose square is measurable need not be), and no
smallness/continuity of `c` is used.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set
open Work.FTS.EllExist

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * (|a| * |b|) ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  rw [abs_mul]
  linarith [h, sq_abs a, sq_abs b]

/-- AM–GM in the form used below: `|y| ≤ (y² + 1)/2`. -/
private lemma abs_le_sq_add_one_div_two (y : ℝ) : |y| ≤ (y ^ 2 + 1) / 2 := by
  have h : 2 * (|y| * 1) ≤ |y| ^ 2 + 1 ^ 2 := by nlinarith [sq_nonneg (|y| - 1)]
  rw [mul_one] at h
  linarith [h, sq_abs y]

/-- For `0 < t ≤ x` the negative power `x^{-p-1}` is dominated by its value at `t`,
provided the exponent is negative, i.e. `0 ≤ p`. -/
private lemma rpow_neg_sub_one_le {t x p : ℝ} (ht : 0 < t) (htx : t ≤ x) (hp : 0 ≤ p) :
    x ^ (-p - 1) ≤ t ^ (-p - 1) := by
  have hx : 0 < x := lt_of_lt_of_le ht htx
  rw [show -p - 1 = -(p + 1) from by ring]
  rw [Real.rpow_neg hx.le, Real.rpow_neg ht.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ht _) (Real.rpow_le_rpow ht.le htx (by linarith))

theorem rgBstep_integrableOn_Ioi_of_aestronglyMeasurable {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ t : ℝ, 0 < t →
      MeasureTheory.AEStronglyMeasurable (Work.FTS.EllExist.rgF2 α m c)
        (MeasureTheory.volume.restrict (Set.Ioi t)) →
      MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi t) := by
  intro t ht hAesm
  have hp8 : 8 ≤ rgP α m := rgP_ge hα hα4 hm
  have hp0 : 0 ≤ rgP α m := by linarith
  -- the absolute value of the integrand, written with the negative power
  have hFval : ∀ x : ℝ, 0 < x → ‖rgF2 α m c x‖ = |c x| * x ^ (-(rgP α m) - 1) := by
    intro x hx
    rw [rgF2, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  -- ### The part `(t, 1]`: bounded weight, `L²` control of `c` from `hnear`
  have hA : IntegrableOn (fun x => ‖rgF2 α m c x‖) (Ioc t 1) := by
    have hIoo : Integrable (fun x => ‖rgF2 α m c x‖) (volume.restrict (Ioo t 1)) := by
      have hmaj : Integrable (fun x => t ^ (-(rgP α m) - 1) * (((c x) ^ 2 / x ^ 4 + 1) / 2))
          (volume.restrict (Ioo t 1)) := by
        have h11 : Integrable (fun x => (c x) ^ 2 / x ^ 4) (volume.restrict (Ioo t 1)) :=
          hnear.mono_set (fun x hx => ⟨lt_trans ht hx.1, hx.2⟩)
        have h12 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo t 1)) :=
          integrable_const 1
        exact ((h11.add h12).div_const 2).const_mul _
      refine Integrable.mono' hmaj (hAesm.norm.mono_set (fun x hx => hx.1)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hxt : t < x := hx.1
      have hx1 : x ≤ 1 := hx.2.le
      have hx0 : 0 < x := lt_trans ht hxt
      rw [norm_norm, hFval x hx0]
      have hw : x ^ (-(rgP α m) - 1) ≤ t ^ (-(rgP α m) - 1) :=
        rpow_neg_sub_one_le ht hxt.le hp0
      -- `|c x| ≤ x²·|c x|/x² ≤ ((c x)²/x⁴ + 1)/2` on `(t,1)`
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
      calc |c x| * x ^ (-(rgP α m) - 1)
          ≤ |c x| * t ^ (-(rgP α m) - 1) := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
        _ = t ^ (-(rgP α m) - 1) * |c x| := by ring
        _ ≤ t ^ (-(rgP α m) - 1) * (((c x) ^ 2 / x ^ 4 + 1) / 2) :=
            mul_le_mul_of_nonneg_left hcA (Real.rpow_nonneg ht.le _)
    exact MeasureTheory.IntegrableOn.congr_set_ae hIoo (Ioo_ae_eq_Ioc (a := t) (b := 1)).symm
  -- ### The part `(1, ∞)`: `c ∈ L²` against the `L²` weight `x^{-p-1}`
  have hB : IntegrableOn (fun x => ‖rgF2 α m c x‖) (Ioi (max t 1)) := by
    have ht' : 0 < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right t 1)
    have hmaj : Integrable (fun x => ((c x) ^ 2 + x ^ (-(2 * rgP α m) - 2)) / 2)
        (volume.restrict (Ioi (max t 1))) := by
      have h1 : Integrable (fun x => (c x) ^ 2) (volume.restrict (Ioi (max t 1))) :=
        hfar.mono_set (fun x hx => lt_of_le_of_lt (le_max_right t 1) hx)
      have h2 : Integrable (fun x => x ^ (-(2 * rgP α m) - 2))
          (volume.restrict (Ioi (max t 1))) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) ht'
      exact (h1.add h2).div_const 2
    refine Integrable.mono' hmaj (hAesm.norm.mono_set (fun x hx => ?_)) ?_
    · exact lt_of_le_of_lt (le_max_left t 1) hx
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := by have := lt_of_le_of_lt (le_max_right t 1) hx; linarith
      rw [norm_norm, hFval x hx0]
      have hb : (x ^ (-(rgP α m) - 1)) ^ 2 = x ^ (-(2 * rgP α m) - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        congr 1
        ring
      calc |c x| * x ^ (-(rgP α m) - 1)
          = |c x * x ^ (-(rgP α m) - 1)| := by
              rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
        _ ≤ ((c x) ^ 2 + (x ^ (-(rgP α m) - 1)) ^ 2) / 2 := abs_mul_le_half_sq_add_sq _ _
        _ = ((c x) ^ 2 + x ^ (-(2 * rgP α m) - 2)) / 2 := by rw [hb]
  -- ### Glue the two parts
  have hsub : Ioi t ⊆ Ioc t 1 ∪ Ioi (max t 1) := by
    intro x hx
    by_cases h : x ≤ 1
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (max_lt hx (lt_of_not_ge h))
  have hU : IntegrableOn (fun x => ‖rgF2 α m c x‖) (Ioc t 1 ∪ Ioi (max t 1)) := hA.union hB
  have hIoi : IntegrableOn (fun x => ‖rgF2 α m c x‖) (Ioi t) := hU.mono_set hsub
  exact (integrable_norm_iff hAesm).mp hIoi

end Work.FTS.PhiStar.Honesty
