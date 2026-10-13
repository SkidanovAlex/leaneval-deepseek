import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

open MeasureTheory Set Filter
open scoped Topology

/-- Key auxiliary step: if `F` has a limit `L` at `+∞` and `G` is integrable on `(1,∞)` with
`‖G t‖ = ‖F t‖ / t` for all sufficiently large `t`, then `L = 0`.

Indeed, if `‖L‖ ≠ 0` then `‖G t‖ ≥ ‖L‖/(2t) ≥ ‖L‖/(4R)` for `t ∈ [R, 2R]` and `R` large, so
`∫ x in Ioi R, ‖G x‖ ≥ |L| / 4` for all large `R`; but this integral tends to `0` because `G`
is integrable on `(1,∞)` (`MeasureTheory.tendsto_integral_Ioi_zero`). -/
private lemma tendsto_eq_zero_of_div_integrable {F G : ℝ → ℝ} {L : ℝ}
    (hF : Filter.Tendsto F Filter.atTop (nhds L))
    (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1))
    (hrel : ∀ᶠ t in Filter.atTop, ‖G t‖ = ‖F t‖ / t) :
    L = 0 := by
  have hev : ∀ᶠ x in Filter.atTop, ‖L‖ / 2 ≤ ‖F x‖ := by
    rcases eq_or_lt_of_le (norm_nonneg L) with h0 | h0
    · filter_upwards with x
      rw [← h0]
      simp
    · have hL := (tendsto_order.1 hF.norm).1 (‖L‖ / 2) (by linarith)
      filter_upwards [hL] with x hx using le_of_lt hx
  have hKey : ∀ᶠ R in Filter.atTop, ‖L‖ / 4 ≤ ∫ x in Set.Ioi R, ‖G x‖ := by
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (hev.and hrel)
    refine Filter.eventually_atTop.2 ⟨max T 1, fun R hR => ?_⟩
    have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
    have hRT : T ≤ R := le_trans (le_max_left _ _) hR
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    have hR2 : R ≤ 2 * R := by linarith
    have hpt : ∀ x ∈ Set.Icc R (2 * R), ‖L‖ / (4 * R) ≤ ‖G x‖ := by
      intro x hx
      have hxR : R ≤ x := hx.1
      have hx2R : x ≤ 2 * R := hx.2
      have hx0 : 0 < x := lt_of_lt_of_le one_pos (le_trans hR1 hxR)
      obtain ⟨hFb, hGx⟩ := hT x (le_trans hRT hxR)
      rw [hGx, show ‖L‖ / (4 * R) = (‖L‖ / 2) / (2 * R) by field_simp; ring]
      exact le_trans (div_le_div_of_nonneg_left (by positivity) hx0 hx2R)
        (div_le_div_of_nonneg_right hFb (le_of_lt hx0))
    have hlow : ‖L‖ / 4 ≤ ∫ x in R..(2 * R), ‖G x‖ := by
      have hconst : (∫ x in R..(2 * R), (‖L‖ / (4 * R) : ℝ)) = ‖L‖ / 4 := by
        rw [intervalIntegral.integral_const, smul_eq_mul, show (2 : ℝ) * R - R = R by ring]
        field_simp
      rw [← hconst]
      have hint : IntervalIntegrable (fun x => ‖G x‖) volume R (2 * R) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR2]
        have h1 : IntegrableOn (fun x => ‖G x‖) (Set.Ioi 1) := hG.norm
        exact h1.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hR1))
      exact intervalIntegral.integral_mono_on hR2 intervalIntegrable_const hint hpt
    have hup : (∫ x in R..(2 * R), ‖G x‖) ≤ ∫ x in Set.Ioi R, ‖G x‖ := by
      rw [intervalIntegral.integral_of_le hR2]
      refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
      · have h1 : IntegrableOn (fun x => ‖G x‖) (Set.Ioi 1) := hG.norm
        exact h1.mono_set (Set.Ioi_subset_Ioi hR1)
      · filter_upwards with x using norm_nonneg (G x)
      · filter_upwards with x hx using hx.1
    linarith
  have hAbsT : Filter.Tendsto (fun R : ℝ => ∫ x in Set.Ioi R, ‖G x‖) Filter.atTop (nhds 0) :=
    MeasureTheory.tendsto_integral_Ioi_zero (b := fun R : ℝ => R) (f := fun x : ℝ => ‖G x‖)
      tendsto_id
  have hle : ‖L‖ / 4 ≤ 0 := ge_of_tendsto hAbsT hKey
  have hz : ‖L‖ = 0 := le_antisymm (by linarith) (norm_nonneg L)
  exact norm_eq_zero.1 hz

/-- **Right-endpoint limit** (intended namespace `Work.FTS.ClassCHon.Zpz`, module
`Submission.Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_upper`).

If `c` is differentiable on `(0,∞)` and both `c t * t ^ (-p - 1)` and its `t`-weighted derivative
`t * deriv c t * t ^ (-p - 1)` are integrable on `(1,∞)`, then `t ↦ c t * t ^ (-p)` tends to `0`
at `∞`.  No hypothesis on the real exponent `p` is needed.

Route (tools available in Mathlib): `F t := c t * t ^ (-p)` satisfies
`F' t = deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))` on `(0,∞)`, which is `L¹` on `(1,∞)`
(because `deriv c t * t ^ (-p) = t * deriv c t * t ^ (-p - 1)`); moreover
`∫ x in Ioi R, F' x → 0` as `R → ∞` (`MeasureTheory.tendsto_integral_Ioi_zero`), and
`F R - F 1 = ∫ x in (1)..R, F' x = ∫ x in Ioi 1, F' x - ∫ x in Ioi R, F' x` for `1 < R`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt` plus `intervalIntegral.integral_interval_add_Ioi`),
so `F` has the finite limit `C := F 1 + ∫ x in Ioi 1, F' x` at `∞`.  Finally `C = 0`: if `C ≠ 0`
then `|c t * t ^ (-p - 1)| = |F t| / t ≥ |C| / (2 * t)` for all large `t`, contradicting `hinf`
because `∫ x in R..S, 1/x = Real.log (S / R) → ∞` as `S → ∞` (`integral_one_div_of_pos`). -/
theorem rpow_mul_tendsto_zero_upper {p : ℝ} {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioi 1))
    (hdinf : MeasureTheory.IntegrableOn (fun t => t * deriv c t * t ^ (-p - 1))
      (Set.Ioi 1)) :
    Filter.Tendsto (fun t => c t * t ^ (-p)) Filter.atTop (nhds 0) := by
  -- `t ^ (-p) = t * t ^ (-p - 1)` for `t > 0`
  have hrpow : ∀ t : ℝ, 0 < t → t ^ (-p) = t * t ^ (-p - 1) := by
    intro t ht
    have h : (1 : ℝ) + (-p - 1) = -p := by ring
    calc t ^ (-p) = t ^ ((1 : ℝ) + (-p - 1)) := by rw [h]
      _ = t ^ (1 : ℝ) * t ^ (-p - 1) := Real.rpow_add ht _ _
      _ = t * t ^ (-p - 1) := by rw [Real.rpow_one]
  -- the derivative of `F t = c t * t ^ (-p)`
  have hderiv : ∀ t ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (fun s : ℝ => c s * s ^ (-p))
        (deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))) t := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    have h2 : HasDerivAt (fun s : ℝ => s ^ (-p)) ((-p) * t ^ (-p - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht0))
    have h3 := (hcd t ht0).mul h2
    convert h3 using 1
    ring
  -- this derivative is integrable on `(1,∞)`
  have hF'int : MeasureTheory.IntegrableOn
      (fun t : ℝ => deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))) (Set.Ioi 1) := by
    have hA : MeasureTheory.IntegrableOn (fun t : ℝ => deriv c t * t ^ (-p)) (Set.Ioi 1) := by
      refine MeasureTheory.IntegrableOn.congr_fun hdinf (fun t ht => ?_) measurableSet_Ioi
      have ht0 : 0 < t := lt_trans one_pos ht
      show t * deriv c t * t ^ (-p - 1) = deriv c t * t ^ (-p)
      rw [show t * deriv c t * t ^ (-p - 1) = deriv c t * (t * t ^ (-p - 1)) by ring,
        hrpow t ht0]
    exact hA.sub (hinf.const_mul p)
  have hlim := MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 1)
    hderiv hF'int
  -- `‖c t * t ^ (-p - 1)‖ = ‖c t * t ^ (-p)‖ / t` for large `t`
  have hrel : ∀ᶠ t in Filter.atTop, ‖c t * t ^ (-p - 1)‖ = ‖c t * t ^ (-p)‖ / t := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    have hmul : t ^ (-p - 1) * t = t ^ (-p) := by
      have h := Real.rpow_add ht0 (-p - 1) (1 : ℝ)
      rw [Real.rpow_one] at h
      rw [show (-p - 1) + 1 = -p by ring] at h
      exact h.symm
    rw [eq_div_iff_mul_eq (ne_of_gt ht0), norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 (-p - 1)),
      abs_of_pos (Real.rpow_pos_of_pos ht0 (-p))]
    rw [mul_assoc, hmul]
  have hkey : Filter.atTop.limUnder (fun t : ℝ => c t * t ^ (-p)) = 0 :=
    tendsto_eq_zero_of_div_integrable hlim hinf hrel
  rw [hkey] at hlim
  exact hlim

end Work.FTS.ClassCHon.Zpz
