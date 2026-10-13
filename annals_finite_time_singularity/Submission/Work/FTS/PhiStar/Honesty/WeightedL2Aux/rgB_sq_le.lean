/-
# `WeightedL2Aux.rgB_sq_le` — the weighted-`L²` bound for the growing Green branch

The growing branch of the radial Green function is

  `rgB α m d z = ∫_{Ioi z} d t · t^{-p-1} dt`,  `p = rgP α m = 2m/α ≥ 8` (`rgP_ge`, `m ≥ 1`,
`α ≤ 1/4`), and the target is the sharp Cauchy–Schwarz bound

  `(rgB α m d z)² ≤ M · z^{-2p-1}/(2p+1)`,  `M = ∫_{Ioo 0 1} d²/t⁴ + ∫_{Ioi 1} d²`.

Note that this is *exactly* the square of the `L²((z,∞),dt)` norm of `t ↦ t^{-p-1}`, which is
`∫_{Ioi z} t^{-2p-2} = z^{-2p-1}/(2p+1)`: the whole content is that the measure `d²` may be
replaced by the (larger) two-piece weight `M` of the hypotheses.

Proof, in two steps.

* `sq_Ioi_le_aux` (proved here; also requested next door as `WeightedL2Aux.sq_Ioi_le`):
  `∫_{Ioi z} d² ≤ M`, together with the integrability of `d²` on the tail `(z,∞)` (needed to
  apply Cauchy–Schwarz).  For `z ≥ 1` the tail sits inside `(1,∞)` where the hypothesis controls
  `d²`; for `0 < z < 1` it is split as `(z,1] ∪ (1,∞)`, and on `(z,1]` one has `t⁴ ≤ 1`, so
  `d² ≤ d²/t⁴` pointwise; monotonicity of the integral against `hnear` finishes.
  (`Ioc_union_Ioi_eq_Ioi`, `Ioo_ae_eq_Ioc`, `integral_Ioc_eq_integral_Ioo` do the bookkeeping;
  the single point `t = 1` is null.)

* `rgB_tail_sq_le` (general exponent `p > 3/2`): Cauchy–Schwarz for set integrals
  (`WeightedL2Aux.sq_setIntegral_mul_le`) with `f = d`, `g = t ↦ t^{-p-1}` on `(z,∞)` gives

    `(∫_{Ioi z} d t·t^{-p-1})² ≤ (∫_{Ioi z} d²) · (∫_{Ioi z} t^{-2p-2})`,

  then `∫_{Ioi z} t^{-2p-2} = z^{-2p-1}/(2p+1)` (`integral_Ioi_rpow_of_lt`) and the previous
  bound on `∫_{Ioi z} d²` conclude.

The instantiation at `p = rgP α m ≥ 8 > 3/2` is the statement below.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.WeightedL2Aux.cs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.WeightedL2Aux

open MeasureTheory Set Filter

/-- **The `L²`-mass of `d` on the tail `(z,∞)` is controlled by the two-piece weight `M`.**

For `0 < z`, an a.e.-measurable `c` with `c²/t⁴ ∈ L¹(0,1)` and `c² ∈ L¹(1,∞)`: `c²` is
integrable on `(z,∞)` and `∫_{Ioi z} c² ≤ ∫_{Ioo 0 1} c²/t⁴ + ∫_{Ioi 1} c²`.

(The same statement is being proved independently as `WeightedL2Aux.sq_Ioi_le`.) -/
private lemma sq_Ioi_le_aux {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z) (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi 1)) :
    IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi z) ∧
      (∫ t in Ioi z, (c t) ^ 2)
        ≤ (∫ t in Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4) + (∫ t in Ioi (1 : ℝ), (c t) ^ 2) := by
  have hA_nn : 0 ≤ ∫ t in Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4 :=
    integral_nonneg (fun t => by positivity)
  rcases le_or_gt 1 z with h1 | h1
  · -- `z ≥ 1`: the tail lies inside `(1,∞)`
    have hsub : Ioi z ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi h1
    have hInt : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi z) := hfar.mono_set hsub
    refine ⟨hInt, ?_⟩
    have hmono : (∫ t in Ioi z, (c t) ^ 2) ≤ ∫ t in Ioi (1 : ℝ), (c t) ^ 2 :=
      setIntegral_mono_set hfar (Eventually.of_forall (fun t => sq_nonneg (c t)))
        (Eventually.of_forall (fun t ht => hsub ht))
    linarith
  · -- `0 < z < 1`: split `(z,∞) = (z,1] ∪ (1,∞)`
    have hz1 : z ≤ 1 := h1.le
    have hnear_z : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo z 1) :=
      hnear.mono_set (fun t ht => ⟨lt_trans hz ht.1, ht.2⟩)
    -- on `(z,1]` one has `t⁴ ≤ 1`, hence `(c t)² ≤ (c t)²/t⁴`
    have hle_pt : ∀ t ∈ Ioo z 1, (c t) ^ 2 ≤ (c t) ^ 2 / t ^ 4 := by
      intro t ht
      have ht0 : 0 < t := lt_trans hz ht.1
      have ht1 : t ≤ 1 := ht.2.le
      have h4 : t ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1
      have h4pos : 0 < t ^ 4 := by positivity
      have hinv : 1 ≤ (t ^ 4)⁻¹ := (one_le_inv₀ h4pos).mpr h4
      rw [div_eq_mul_inv]
      simpa using mul_le_mul_of_nonneg_left hinv (sq_nonneg (c t))
    have hint_Ioo : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioo z 1) :=
      Integrable.mono' hnear_z ((hc.aestronglyMeasurable.restrict).pow 2) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hle_pt t ht)
    have hint_Ioc : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioc z 1) :=
      hint_Ioo.congr_set_ae (Ioo_ae_eq_Ioc (a := z) (b := 1)).symm
    have hInt : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi z) := by
      have hU := hint_Ioc.union hfar
      rwa [Ioc_union_Ioi_eq_Ioi hz1] at hU
    refine ⟨hInt, ?_⟩
    have hsplit : (∫ t in Ioi z, (c t) ^ 2)
        = (∫ t in Ioc z 1, (c t) ^ 2) + ∫ t in Ioi (1 : ℝ), (c t) ^ 2 := by
      rw [← Ioc_union_Ioi_eq_Ioi hz1]
      exact setIntegral_union (Set.disjoint_left.mpr (fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2))
        measurableSet_Ioi hint_Ioc hfar
    rw [hsplit]
    have hnear_val : (∫ t in Ioc z 1, (c t) ^ 2) ≤ ∫ t in Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4 := by
      rw [integral_Ioc_eq_integral_Ioo]
      calc (∫ t in Ioo z 1, (c t) ^ 2) ≤ ∫ t in Ioo z 1, (c t) ^ 2 / t ^ 4 :=
            setIntegral_mono_of_nonneg (fun t _ => sq_nonneg _) hle_pt hnear_z
        _ ≤ ∫ t in Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4 :=
            setIntegral_mono_set hnear (Eventually.of_forall (fun t => by positivity))
              (Eventually.of_forall (fun t ht => ⟨lt_trans hz ht.1, ht.2⟩))
    linarith

/-- **Cauchy–Schwarz tail bound for the growing-branch integrand** (general exponent
`p > 3/2`): the square of `∫_{Ioi z} c t·t^{-p-1}` is at most the `L²`-mass of `c` on `(z,∞)`
times `z^{-2p-1}/(2p+1)`. -/
theorem rgB_tail_sq_le {c : ℝ → ℝ} {p z : ℝ} (hp : 3 / 2 < p) (hz : 0 < z) (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi 1)) :
    (∫ t in Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ ((∫ t in Ioo (0:ℝ) 1, (c t) ^ 2 / t ^ 4) + (∫ t in Ioi (1:ℝ), (c t) ^ 2))
        * (z ^ (-(2 * p) - 1) / (2 * p + 1)) := by
  obtain ⟨hInt2, hle⟩ := sq_Ioi_le_aux (c := c) hz hc hnear hfar
  -- the second Cauchy–Schwarz factor: `t ↦ t^{-p-1}` is in `L²(z,∞)`
  have hpow : IntegrableOn (fun t : ℝ => (t ^ (-p - 1)) ^ 2) (Ioi z) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2 * p - 2) (by linarith) hz).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    rw [pow_two, ← Real.rpow_add ht0]
    congr 1
    ring
  have hcs := sq_setIntegral_mul_le (s := Ioi z) measurableSet_Ioi hInt2 hpow
  -- its square integral: `∫_{Ioi z} t^{-2p-2} = z^{-2p-1}/(2p+1)`
  have hval : (∫ t in Ioi z, (t ^ (-p - 1)) ^ 2) = z ^ (-(2 * p) - 1) / (2 * p + 1) := by
    have hcong : (∫ t in Ioi z, (t ^ (-p - 1)) ^ 2) = ∫ t in Ioi z, t ^ (-(2 * p) - 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : 0 < t := lt_trans hz ht
      rw [pow_two, ← Real.rpow_add ht0]
      congr 1
      ring
    rw [hcong, integral_Ioi_rpow_of_lt (a := -(2 * p) - 2) (by linarith) hz]
    rw [show -(2 * p) - 2 + 1 = -(2 * p) - 1 by ring]
    rw [show -(2 * p) - 1 = -(2 * p + 1) by ring, neg_div_neg_eq]
  have hbase : 0 ≤ z ^ (-(2 * p) - 1) / (2 * p + 1) :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by linarith)
  calc (∫ t in Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ (∫ t in Ioi z, (c t) ^ 2) * (∫ t in Ioi z, (t ^ (-p - 1)) ^ 2) := hcs
    _ = (∫ t in Ioi z, (c t) ^ 2) * (z ^ (-(2 * p) - 1) / (2 * p + 1)) := by rw [hval]
    _ ≤ ((∫ t in Ioo (0:ℝ) 1, (c t) ^ 2 / t ^ 4) + (∫ t in Ioi (1:ℝ), (c t) ^ 2))
          * (z ^ (-(2 * p) - 1) / (2 * p + 1)) := mul_le_mul_of_nonneg_right hle hbase

theorem rgB_sq_le {α : ℝ} {m : ℕ} {d : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hd : AEMeasurable d)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz : 0 < z) :
    (Work.FTS.EllExist.rgB α m d z) ^ 2
      ≤ ((∫ t in Set.Ioo (0:ℝ) 1, (d t) ^ 2 / t ^ 4)
          + (∫ t in Set.Ioi (1:ℝ), (d t) ^ 2))
        * (z ^ (-(2 * Work.FTS.EllExist.rgP α m) - 1) / (2 * Work.FTS.EllExist.rgP α m + 1)) := by
  have hp32 : (3 : ℝ) / 2 < Work.FTS.EllExist.rgP α m := by
    have h := Work.FTS.EllExist.rgP_ge hα hα4 hm
    linarith
  have h := rgB_tail_sq_le (c := d) (p := Work.FTS.EllExist.rgP α m) (z := z)
    hp32 hz hd hnear hfar
  simpa only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2] using h

end Work.FTS.PhiStar.Honesty.WeightedL2Aux
