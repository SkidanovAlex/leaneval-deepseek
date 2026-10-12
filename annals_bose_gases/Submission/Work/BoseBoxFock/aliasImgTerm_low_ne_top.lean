import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.AliasClosedTermAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aliasImgTerm_low_ne_top`

The **low-index** (i.e. `‖m‖ ≤ 1`, `m ≠ 0`) finiteness of the individual summands of the image
series of the closed-ball aliasing chapter:

    aliasImgTerm ℓ g m = ∫⁻_u ofReal(‖𝒢(u)‖ · imgW ℓ m u) ≠ ⊤ ,   𝒢 = aliasKernel g .

In fact the argument proves the statement for **every** `m ≠ 0` (the hypothesis `‖m‖ ≤ 1` is
inherited from the requester's interface and is not needed): it is a *per-term* statement, the
`tsum`-level decay in `m` being the content of `aliasImgTerm_tail_sum_le` and of the low/far split
of `tsum_lintegral_aliasKernel_imageW_lens_closed`.

The mechanism is the interplay of the closed-ball inputs of
`Submission.Work.BoseBoxFock.AliasClosedAux` and `Submission.Work.BoseBoxFock.AliasClosedTermAux`:

* the autocorrelation `𝒢 = aliasKernel g` vanishes beyond radius `ℓ`
  (`autocorr_eq_zero_of_lt_norm_closed`), so the integral lives on `closedBall 0 ℓ`;
* on `closedBall 0 ℓ` the *lens bound* gives `‖𝒢(u)‖ ≤ C(ℓ² − ‖u‖²)^{3/2}`
  (`autocorr_lens_bound`), which in turn is `≤ C(2ℓ)^{3/2}‖u − ℓ m‖^{3/2}` as soon as
  `1 ≤ ‖latVec m‖` (`rpow_lens_le_of_one_le_norm_latVec`, and `one_le_norm_latVec` for `m ≠ 0`);
* multiplying against the Riesz weight `imgW ℓ m u = (‖u − ℓ m‖⁴)⁻¹` produces the *locally
  integrable* singular weight `‖u − ℓ m‖^{−5/2}`, whose `ℝ≥0∞`-integral over `closedBall 0 ℓ` is
  finite (`lintegral_norm_rpow_neg_five_halves_closedBall_lt_top`).

This is exactly the "vanishing at the touching image" phenomenon: at `‖latVec m‖ = 1` the point
`ℓ m` sits on the boundary of the support ball, where `‖u − ℓ m‖^{−4}` is not integrable, and the
`(ℓ² − ‖u‖²)^{3/2}` decay of the lens bound is what makes the product integrable; at
`‖latVec m‖ > 1` the point `ℓ m` lies outside the ball and the kernel vanishes near it.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The exponent identity `x^{3/2}·(x⁴)⁻¹ = x^{−5/2}` for `x ≥ 0` (both sides equal `0` at
`x = 0`).  This is what turns the lens weight `(ℓ² − ‖u‖²)^{3/2}` times the Riesz weight
`‖u − z‖⁻⁴` into the locally integrable `‖u − z‖^{-5/2}`. -/
private lemma rpow_three_halves_mul_inv_pow {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) * (x ^ 4)⁻¹ = x ^ (-(5 / 2 : ℝ)) := by
  rcases hx.lt_or_eq with h | h
  · rw [← Real.rpow_natCast x 4, ← Real.rpow_neg h.le ((4 : ℕ) : ℝ), ← Real.rpow_add h]
    congr 1
    norm_num
  · subst h
    simp

theorem aliasImgTerm_low_ne_top {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    (m : Fin 3 → ℤ) (hm0 : m ≠ 0) (hm : ‖m‖ ≤ 1) :
    Work.BoseBoxFock.aliasImgTerm ℓ g m ≠ ⊤ := by
  have _hm := hm
  change (∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)) ≠ ⊤
  obtain ⟨C, hC0, hC⟩ := autocorr_lens_bound hℓ hg hgsupp
  have hK0 : 0 ≤ C * (2 * ℓ) ^ (3 / 2 : ℝ) :=
    mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _)
  have hm1 : 1 ≤ ‖latVec m‖ := one_le_norm_latVec hm0
  -- the pointwise bound on `closedBall 0 ℓ`
  have hbound : ∀ u : E3, ‖u‖ ≤ ℓ →
      ‖aliasKernel g u‖ * imgW ℓ m u
        ≤ (C * (2 * ℓ) ^ (3 / 2 : ℝ)) * ‖u - ℓ • latVec m‖ ^ (-(5 / 2 : ℝ)) := by
    intro u hu
    have h1 : ‖aliasKernel g u‖ ≤ C * (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ) := by
      calc ‖aliasKernel g u‖ = |(autocorr g u).re| := by rw [aliasKernel, Real.norm_eq_abs]
        _ ≤ ‖autocorr g u‖ := Complex.abs_re_le_norm _
        _ ≤ C * (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ) := hC u hu
    rw [imgW_ne_zero hm0]
    have h2 : (C * (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ)) * (‖u - ℓ • latVec m‖ ^ 4)⁻¹
        ≤ ((C * (2 * ℓ) ^ (3 / 2 : ℝ)) * ‖u - ℓ • latVec m‖ ^ (3 / 2 : ℝ))
            * (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc C * (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ)
          ≤ C * ((2 * ℓ) ^ (3 / 2 : ℝ) * ‖u - ℓ • latVec m‖ ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (rpow_lens_le_of_one_le_norm_latVec hℓ hu hm1) hC0
        _ = (C * (2 * ℓ) ^ (3 / 2 : ℝ)) * ‖u - ℓ • latVec m‖ ^ (3 / 2 : ℝ) := by ring
    refine (mul_le_mul_of_nonneg_right h1 (by positivity)).trans (h2.trans ?_)
    rw [mul_assoc, rpow_three_halves_mul_inv_pow (norm_nonneg _)]
  -- the integrand vanishes off the ball of radius `ℓ`
  have hvan : ∀ u : E3, ℓ < ‖u‖ → ‖aliasKernel g u‖ * imgW ℓ m u = 0 := by
    intro u hu
    have hz : aliasKernel g u = 0 := by
      rw [aliasKernel, autocorr_eq_zero_of_lt_norm_closed hℓ hgsupp hu]
      simp
    rw [hz, norm_zero, zero_mul]
  -- the indicator domination
  have hpt : ∀ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u) ≤
      (Metric.closedBall (0 : E3) ℓ).indicator
        (fun u : E3 => ENNReal.ofReal ((C * (2 * ℓ) ^ (3 / 2 : ℝ))
          * ‖u - ℓ • latVec m‖ ^ (-(5 / 2 : ℝ)))) u := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : E3) ℓ
    · rw [Set.indicator_of_mem hu]
      refine ENNReal.ofReal_le_ofReal (hbound u ?_)
      rwa [Metric.mem_closedBall, dist_zero_right] at hu
    · rw [Set.indicator_of_notMem hu, hvan u ?_]
      · simp
      · rw [Metric.mem_closedBall, dist_zero_right, not_le] at hu
        exact hu
  have hmain : (∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u))
      ≤ ENNReal.ofReal (C * (2 * ℓ) ^ (3 / 2 : ℝ))
          * ∫⁻ u in Metric.closedBall (0 : E3) ℓ,
              ENNReal.ofReal (‖u - ℓ • latVec m‖ ^ (-(5 / 2 : ℝ))) := by
    calc (∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u))
        ≤ ∫⁻ u : E3, (Metric.closedBall (0 : E3) ℓ).indicator
            (fun u : E3 => ENNReal.ofReal ((C * (2 * ℓ) ^ (3 / 2 : ℝ))
              * ‖u - ℓ • latVec m‖ ^ (-(5 / 2 : ℝ)))) u := lintegral_mono hpt
      _ = ∫⁻ u in Metric.closedBall (0 : E3) ℓ,
            ENNReal.ofReal ((C * (2 * ℓ) ^ (3 / 2 : ℝ))
              * ‖u - ℓ • latVec m‖ ^ (-(5 / 2 : ℝ))) :=
          lintegral_indicator measurableSet_closedBall _
      _ = ENNReal.ofReal (C * (2 * ℓ) ^ (3 / 2 : ℝ))
            * ∫⁻ u in Metric.closedBall (0 : E3) ℓ,
                ENNReal.ofReal (‖u - ℓ • latVec m‖ ^ (-(5 / 2 : ℝ))) := by
          rw [lintegral_congr (fun u => ENNReal.ofReal_mul hK0)]
          exact lintegral_const_mul _ (by fun_prop)
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_of_lt (lintegral_norm_rpow_neg_five_halves_closedBall_lt_top hℓ (ℓ • latVec m))))
    hmain

end Work.BoseBoxFock
