import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Separation.CompletelyRegular

set_option maxHeartbeats 4000000

open MeasureTheory
open scoped BigOperators

namespace Commons.MeasureTheory

/-- Nonnegativity of the logarithmic kernel `log (D / ‖x i - x j‖)` on the empirical
measure, given that all pairwise distances are at most `D` and the points are distinct. -/
lemma log_dist_ratio_nonneg {n : ℕ} (x : Fin n → ℂ) (hx : Function.Injective x) {D : ℝ}
    (hD : 0 < D) (hDiam : ∀ i j : Fin n, ‖x i - x j‖ ≤ D) (i j : Fin n) :
    0 ≤ Real.log (D / ‖x i - x j‖) := by
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Real.log_div (ne_of_gt hD) (by
      intro h
      exact hij (hx (sub_eq_zero.mp (norm_eq_zero.mp h))))]
    have hnormpos : 0 < ‖x i - x j‖ := by
      rw [norm_pos_iff]
      intro h
      exact hij (hx (sub_eq_zero.mp h))
    rw [sub_nonneg]
    exact Real.log_le_log hnormpos (hDiam i j)

/-- The real double sum of the logarithmic kernel over the empirical measure equals
`n (n-1) log D` minus twice the log of the product of the upper-triangular pairwise
distances. -/
lemma sum_log_dist_ratio_eq {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℂ) (hx : Function.Injective x)
    {D : ℝ} (hD : 0 < D) :
    (∑ i : Fin n, ∑ j : Fin n, Real.log (D / ‖x i - x j‖))
      = (n : ℝ) * ((n : ℝ) - 1) * Real.log D
          - 2 * Real.log (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖x j - x i‖) := by
  have hne : ∀ {i j : Fin n}, i ≠ j → ‖x i - x j‖ ≠ 0 := by
    intro i j hij h
    exact hij (hx (sub_eq_zero.mp (norm_eq_zero.mp h)))
  have hsymm : ∀ i j : Fin n, Real.log ‖x i - x j‖ = Real.log ‖x j - x i‖ := by
    intro i j
    rw [show x i - x j = -(x j - x i) by ring, norm_neg]
  have hIoi : ∀ i : Fin n, Finset.Ioi i = Finset.univ.filter (fun j : Fin n => i < j) :=
    fun i => by ext j; simp [Finset.mem_Ioi]
  have hIio : ∀ i : Fin n, Finset.Iio i = Finset.univ.filter (fun j : Fin n => j < i) :=
    fun i => by ext j; simp [Finset.mem_Iio]
  have herase : ∀ i : Fin n,
      (Finset.univ.erase i : Finset (Fin n)) = Finset.Iio i ∪ Finset.Ioi i := by
    intro i
    ext j
    rw [Finset.mem_erase, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi]
    simp only [Finset.mem_univ, and_true]
    exact ne_iff_lt_or_gt
  have hdisj : ∀ i : Fin n, Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    intro i
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    rw [Finset.mem_Iio] at hj1
    rw [Finset.mem_Ioi] at hj2
    exact absurd hj1 (not_lt.mpr (le_of_lt hj2))
  -- Step A: drop the diagonal, then rewrite the off-diagonal terms as a difference of logs
  have hA : (∑ i : Fin n, ∑ j : Fin n, Real.log (D / ‖x i - x j‖))
      = ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i), (Real.log D - Real.log ‖x i - x j‖) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_erase_add Finset.univ (fun j => Real.log (D / ‖x i - x j‖))
      (Finset.mem_univ i)]
    rw [show Real.log (D / ‖x i - x i‖) = 0 by simp, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.log_div (ne_of_gt hD) (hne (Finset.mem_erase.mp hj).1.symm)
  -- Step B: separate the constant part
  have hB : (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i), (Real.log D - Real.log ‖x i - x j‖))
      = ∑ i : Fin n, (((Finset.univ.erase i).card : ℝ) * Real.log D
            - ∑ j ∈ (Finset.univ.erase i), Real.log ‖x i - x j‖) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  -- Step C: evaluate the constant part
  have hcard : ∀ i : Fin n, ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hn]
    norm_num
  have hconst : (∑ i : Fin n, ((Finset.univ.erase i).card : ℝ) * Real.log D)
      = (n : ℝ) * ((n : ℝ) - 1) * Real.log D := by
    calc (∑ i : Fin n, ((Finset.univ.erase i).card : ℝ) * Real.log D)
        = ∑ i : Fin n, ((n : ℝ) - 1) * Real.log D := by
            apply Finset.sum_congr rfl; intro i _; rw [hcard i]
      _ = ((Finset.univ : Finset (Fin n)).card : ℕ) • (((n : ℝ) - 1) * Real.log D) := by
            rw [Finset.sum_const]
      _ = (n : ℝ) * ((n : ℝ) - 1) * Real.log D := by
            rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hC : (∑ i : Fin n, (((Finset.univ.erase i).card : ℝ) * Real.log D
            - ∑ j ∈ (Finset.univ.erase i), Real.log ‖x i - x j‖))
      = (n : ℝ) * ((n : ℝ) - 1) * Real.log D
          - ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i), Real.log ‖x i - x j‖ := by
    rw [Finset.sum_sub_distrib, hconst]
  -- Step D: the pairwise-distance part via symmetry
  have hD1 : (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i), Real.log ‖x i - x j‖)
      = (∑ i : Fin n, ∑ j ∈ Finset.Iio i, Real.log ‖x i - x j‖)
        + (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log ‖x i - x j‖) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [herase i, Finset.sum_union (hdisj i)]
  have hD2 : (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log ‖x i - x j‖)
      = (∑ i : Fin n, ∑ j ∈ Finset.Iio i, Real.log ‖x i - x j‖) := by
    calc (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log ‖x i - x j‖)
        = ∑ i : Fin n, ∑ j ∈ (Finset.univ.filter (fun j : Fin n => i < j)),
            Real.log ‖x i - x j‖ := by simp_rw [hIoi]
      _ = ∑ i : Fin n, ∑ j : Fin n, if i < j then Real.log ‖x i - x j‖ else 0 := by
            apply Finset.sum_congr rfl; intro i _
            rw [Finset.sum_filter]
      _ = ∑ j : Fin n, ∑ i : Fin n, if i < j then Real.log ‖x i - x j‖ else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin n, if j < i then Real.log ‖x j - x i‖ else 0 := rfl
      _ = ∑ i : Fin n, ∑ j : Fin n, if j < i then Real.log ‖x i - x j‖ else 0 := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro j _
            by_cases h : j < i
            · simp only [h, if_true]; exact hsymm j i
            · simp [h]
      _ = ∑ i : Fin n, ∑ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)),
            Real.log ‖x i - x j‖ := by
            apply Finset.sum_congr rfl; intro i _
            rw [Finset.sum_filter]
      _ = ∑ i : Fin n, ∑ j ∈ Finset.Iio i, Real.log ‖x i - x j‖ := by
            apply Finset.sum_congr rfl; intro i _
            rw [hIio i]
  have hD3 : (∑ i : Fin n, ∑ j ∈ Finset.Iio i, Real.log ‖x i - x j‖)
      = Real.log (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖x j - x i‖) := by
    rw [show (∑ i : Fin n, ∑ j ∈ Finset.Iio i, Real.log ‖x i - x j‖)
        = ∑ i : Fin n, ∑ j ∈ Finset.Iio i, Real.log ‖x j - x i‖ from by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          exact hsymm i j]
    rw [Real.log_prod (fun i _ => by
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      exact hne (ne_of_lt (Finset.mem_Iio.mp hj)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_prod (fun j hj => hne (ne_of_lt (Finset.mem_Iio.mp hj)))]
  have hDsym : (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i), Real.log ‖x i - x j‖)
      = 2 * Real.log (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖x j - x i‖) := by
    rw [hD1, hD2, ← two_mul, hD3]
  rw [hA, hB, hC, hDsym]

/-- The log-kernel empirical integral: for distinct points `x i : ℂ` of diameter at most `D > 0`,
the integral of `log (D / ‖z.1 - z.2‖)` against the product of the empirical measure
`∑ δ_{x i}` with itself equals the explicit finite expression. -/
theorem lintegral_log_kernel_empirical_sum_injective {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℂ)
    (hx : Function.Injective x) {D : ℝ} (hD : 0 < D) (hDiam : ∀ i j : Fin n, ‖x i - x j‖ ≤ D) :
    ∫⁻ z, ENNReal.ofReal (Real.log (D / ‖z.1 - z.2‖))
        ∂((∑ i : Fin n, MeasureTheory.Measure.dirac (x i)).prod
          (∑ i : Fin n, MeasureTheory.Measure.dirac (x i)))
      = ENNReal.ofReal ((n : ℝ) * ((n : ℝ) - 1) * Real.log D
          - 2 * Real.log (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖x j - x i‖)) := by
  -- rewrite the empirical product measure as a sum of Dirac masses on the pairs
  have hmeasure : (∑ i : Fin n, MeasureTheory.Measure.dirac (x i)).prod
        (∑ i : Fin n, MeasureTheory.Measure.dirac (x i))
      = MeasureTheory.Measure.sum
          (fun p : Fin n × Fin n => MeasureTheory.Measure.dirac (x p.1, x p.2)) := by
    rw [← Measure.sum_fintype (fun i : Fin n => MeasureTheory.Measure.dirac (x i))]
    rw [Measure.prod_sum]
    simp_rw [Measure.dirac_prod_dirac]
  rw [hmeasure, lintegral_sum_measure]
  simp_rw [lintegral_dirac]
  rw [tsum_fintype, Fintype.sum_prod_type]
  -- convert the sums of `ofReal`s into an `ofReal` of the sum
  have hnn : ∀ i j : Fin n, 0 ≤ Real.log (D / ‖x i - x j‖) :=
    fun i j => log_dist_ratio_nonneg x hx hD hDiam i j
  have hinner : ∀ i : Fin n,
      (∑ j : Fin n, ENNReal.ofReal (Real.log (D / ‖x i - x j‖)))
        = ENNReal.ofReal (∑ j : Fin n, Real.log (D / ‖x i - x j‖)) := by
    intro i
    exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn i j)).symm
  have hconv : (∑ i : Fin n, ∑ j : Fin n, ENNReal.ofReal (Real.log (D / ‖x i - x j‖)))
      = ENNReal.ofReal (∑ i : Fin n, ∑ j : Fin n, Real.log (D / ‖x i - x j‖)) := by
    simp_rw [hinner]
    exact (ENNReal.ofReal_sum_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))).symm
  rw [hconv, sum_log_dist_ratio_eq hn x hx hD]

end Commons.MeasureTheory