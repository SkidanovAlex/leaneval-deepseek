import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Work.BoseBoxFock.AliasClosedAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.AliasClosedTermAux` — the vocabulary of the closed-ball image series

The `ℝ≥0∞`-summability of the image series of the closed-ball aliasing chapter

    ∑'_m ∫⁻_u ofReal(‖𝒢(u)‖ · imgW ℓ m u) ≠ ⊤ ,   𝒢 = aliasKernel g ,

is proved by splitting the lattice into the *low* indices (`‖m‖ ≤ 1`, the 27 indices whose
translate `ℓ • latVec m` can meet the ball `B(0,ℓ)`) and the *far* ones (`2 ≤ ‖m‖`).

This file supplies the two elementary inputs that both halves need:

* `aliasImgTerm` — the `m`-th summand of the series;
* `norm_le_norm_latVec` — the sup-norm dominated by the Euclidean norm of the lattice vector
  (`‖m‖ ≤ ‖latVec m‖`), which turns a bound in terms of `‖latVec m‖` into one in terms of the
  integer sup-norm, the quantity carrying the lattice decay of `lattice_sum_inv_fourth_le`;
* `lintegral_norm_rpow_neg_five_halves_closedBall_lt_top` — the *lens* finiteness input: for every
  centre `c`, `∫⁻_{u ∈ closedBall 0 ℓ} ofReal(‖u − c‖^{-5/2}) < ⊤`.  This is what makes the low
  indices finite: the lens bound `‖𝒢(u)‖ ≤ C (ℓ² − ‖u‖²)^{3/2} ≤ C(2ℓ)^{3/2}‖u − ℓm‖^{3/2}`
  turns `‖𝒢(u)‖‖u − ℓm‖^{-4}` into the integrable `C(2ℓ)^{3/2}‖u − ℓm‖^{-5/2}`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `m`-th summand of the image series of the closed-ball aliasing chapter:

    `aliasImgTerm ℓ g m = ∫⁻_u ofReal(‖aliasKernel g u‖ · imgW ℓ m u)`. -/
noncomputable def aliasImgTerm (ℓ : ℝ) (g : E3 → ℂ) (m : Fin 3 → ℤ) : ℝ≥0∞ :=
  ∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)

/-- The scalar sup-norm of an integer multi-index is dominated by the Euclidean norm of the
lattice vector `latVec m = ∑_i m_i e_i`. -/
theorem norm_le_norm_latVec (m : Fin 3 → ℤ) : ‖m‖ ≤ ‖latVec m‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [Int.norm_eq_abs]
  have hsq : (m i : ℝ) ^ 2 ≤ ∑ j, (m j : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 3 => (m j : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  calc |(m i : ℝ)| = Real.sqrt ((m i : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (m j : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖latVec m‖ := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [latVec_apply, Real.norm_eq_abs, sq_abs]

/-- **The lens finiteness.**  For every centre `c` the function `u ↦ ‖u − c‖^{-5/2}` has finite
`ℝ≥0∞`-integral over the ball `closedBall 0 ℓ`.

Proof: `z ↦ ‖z‖^{-5/2}` is integrable on a ball (`MeasureTheory.integrableOn_ball_of_norm_le_rpow`,
the exponent `5/2` being `< 3 = dim`), the translation `z ↦ z + c` is measure preserving
(`MeasurePreserving.lintegral_comp`), and on the ball `‖u‖ ≤ ℓ` the shift `z = u − c` is confined
to `‖z‖ ≤ ℓ + ‖c‖`. -/
theorem lintegral_norm_rpow_neg_five_halves_closedBall_lt_top {ℓ : ℝ} (_hℓ : 0 < ℓ) (c : E3) :
    (∫⁻ u in Metric.closedBall (0 : E3) ℓ, ENNReal.ofReal (‖u - c‖ ^ (-(5 / 2 : ℝ)))) < ⊤ := by
  have hdim : 1 ≤ Module.finrank ℝ E3 := by rw [finrank_euclideanSpace]; norm_num
  have h35 : (5 / 2 : ℝ) < (Module.finrank ℝ E3 : ℝ) := by
    rw [finrank_euclideanSpace]; norm_num
  have hrad : IntegrableOn (fun z : E3 => ‖z‖ ^ (-(5 / 2 : ℝ)))
      (Metric.ball (0 : E3) (ℓ + ‖c‖ + 1)) := by
    refine integrableOn_ball_of_norm_le_rpow (E := E3) (F := ℝ) (μ := (volume : Measure E3))
      hdim (f := fun z : E3 => ‖z‖ ^ (-(5 / 2 : ℝ))) (C := 1) (α := 5 / 2)
      (r := ℓ + ‖c‖ + 1) h35 ?_ ?_
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), one_mul]
    · exact (by fun_prop : Measurable fun z : E3 => ‖z‖ ^ (-(5 / 2 : ℝ))).aestronglyMeasurable
  have hfin : (∫⁻ z in Metric.closedBall (0 : E3) (ℓ + ‖c‖),
      ENNReal.ofReal (‖z‖ ^ (-(5 / 2 : ℝ)))) < ⊤ :=
    (hrad.mono_set (Metric.closedBall_subset_ball (by linarith [norm_nonneg c]))).setLIntegral_lt_top
  rw [← lintegral_indicator measurableSet_closedBall]
  have hmeas : Measurable (fun u : E3 =>
      (Metric.closedBall (0:E3) ℓ).indicator (fun u => ENNReal.ofReal (‖u - c‖ ^ (-(5/2:ℝ)))) u) := by
    refine Measurable.indicator ?_ measurableSet_closedBall
    exact (by fun_prop : Measurable fun u : E3 => ENNReal.ofReal (‖u - c‖ ^ (-(5/2:ℝ))))
  have hmp := measurePreserving_add_right (volume : Measure E3) c
  have hpt : ∀ z : E3,
      (Metric.closedBall (0:E3) ℓ).indicator (fun u => ENNReal.ofReal (‖u - c‖ ^ (-(5/2:ℝ)))) (z + c)
      ≤ ENNReal.ofReal (‖z‖ ^ (-(5/2:ℝ))) *
        (Metric.closedBall (0:E3) (ℓ + ‖c‖)).indicator (fun _ => (1:ENNReal)) z := by
    intro z
    by_cases hz : z + c ∈ Metric.closedBall (0:E3) ℓ
    · rw [Set.indicator_of_mem hz]
      have hzc : z + c - c = z := by abel
      rw [hzc]
      have hzR : z ∈ Metric.closedBall (0:E3) (ℓ + ‖c‖) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have h1 : ‖z + c‖ ≤ ℓ := by
          have h := hz; rw [Metric.mem_closedBall, dist_zero_right] at h; exact h
        calc ‖z‖ = ‖(z + c) - c‖ := by rw [hzc]
          _ ≤ ‖z + c‖ + ‖c‖ := norm_sub_le _ _
          _ ≤ ℓ + ‖c‖ := by linarith
      rw [Set.indicator_of_mem hzR, mul_one]
    · rw [Set.indicator_of_notMem hz]
      positivity
  refine lt_of_le_of_lt ?_ hfin
  calc ∫⁻ u : E3, (Metric.closedBall (0:E3) ℓ).indicator
        (fun u => ENNReal.ofReal (‖u - c‖ ^ (-(5/2:ℝ)))) u
      = ∫⁻ z : E3, (Metric.closedBall (0:E3) ℓ).indicator
        (fun u => ENNReal.ofReal (‖u - c‖ ^ (-(5/2:ℝ)))) (z + c) :=
        (hmp.lintegral_comp hmeas).symm
    _ ≤ ∫⁻ z : E3, ENNReal.ofReal (‖z‖ ^ (-(5/2:ℝ))) *
          (Metric.closedBall (0:E3) (ℓ + ‖c‖)).indicator (fun _ => (1:ENNReal)) z :=
        lintegral_mono hpt
    _ = ∫⁻ z : E3, (Metric.closedBall (0:E3) (ℓ + ‖c‖)).indicator
          (fun z => ENNReal.ofReal (‖z‖ ^ (-(5/2:ℝ)))) z := by
        refine lintegral_congr (fun z => ?_)
        by_cases hz : z ∈ Metric.closedBall (0:E3) (ℓ + ‖c‖)
        · rw [Set.indicator_of_mem hz, mul_one, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, mul_zero, Set.indicator_of_notMem hz]
    _ = ∫⁻ z in Metric.closedBall (0:E3) (ℓ + ‖c‖),
          ENNReal.ofReal (‖z‖ ^ (-(5/2:ℝ))) :=
        lintegral_indicator measurableSet_closedBall _

end Work.BoseBoxFock
