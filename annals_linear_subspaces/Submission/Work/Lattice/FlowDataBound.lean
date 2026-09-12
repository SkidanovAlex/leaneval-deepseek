import Mathlib
import Submission.Work.Lattice.LatticePolygon
import Submission.Work.Lattice.GraysonLattice
import Submission.Work.Lattice.UniformBddBelow
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Analysis.Real.prefix_average_mono

/-!
# The rank data of a lattice is bounded by the successive minima — (G) is free

The "bounded covolume subgroup" input (G) of the §3 route is **automatic**: for a full-rank
lattice `Λ ≤ ℝᵈ` with `covolume Λ = 1`,

    `rankData Λ j ≤ ∑_{i<j} log λ_{i+1}(Λ) ≤ (j/d) · log (2^{2d} / vol(B_d))`,

so the rank-`j` data is bounded by a constant depending only on `d` and `j`, **uniformly in
`t`** along a unimodular flow `Λ_t = a_t Λ₀`.  The ingredients are all on disk:

* `Submission.GraysonLattice.exists_subgroup_logCovol_le_sum_log` (exact successive-minimum
  realisers, Hadamard, `latticeCovol_span`), giving the first inequality;
* prefix averaging of the increasing sequence `i ↦ log λ_{i+1}`
  (`Commons.Analysis.Real.prefix_average_mono`) for the second;
* `Commons.Lattice.Minkowski.minkowski_second_upper` for the final bound.

Module `Submission.Work.Lattice.FlowDataBound`, namespace `Submission.FlowDataBound`.
-/

noncomputable section

open Set Module Real MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.FlowDataBound

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.LatticePolygon
open Commons.Lattice.SuccessiveMinima

/-- Prefix averaging for a monotone sequence: for `m ≤ n` and `a : ℕ → ℝ` monotone,
`∑_{i<m} a i ≤ (m/n) ∑_{i<n} a i`.  (Valid for sequences with negative values too;
proved from `Commons.Analysis.Real.prefix_average_mono`.) -/
lemma sum_range_le_mul {a : ℕ → ℝ} (hmono : Monotone a) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.range m).sum a ≤ ((m : ℝ) / (n : ℝ)) * (Finset.range n).sum a := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  have hnpos : 0 < n := lt_of_lt_of_le hm hmn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have h := Commons.Analysis.Real.prefix_average_mono a hmono hm hmn
  rw [div_le_div_iff₀ hmR hnR] at h
  have h2 : ((m : ℝ) / (n : ℝ)) * (Finset.range n).sum a =
      ((m : ℝ) * (Finset.range n).sum a) / (n : ℝ) := by ring
  rw [h2, le_div_iff₀ hnR]
  nlinarith [h]

/-- The rank-`j` Grayson data is bounded by the sum of the logarithms of the first `j`
successive minima. -/
theorem rankData_le_sum_log_successiveMinimum {d j : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛ : Module.finrank ℤ Λ = d)
    (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    rankData Λ j ≤ ∑ i : Fin j,
      Real.log (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) := by
  obtain ⟨W, hWle, hWdim, hlog⟩ :=
    GraysonLattice.exists_subgroup_logCovol_le_sum_log Λ hΛ hj1 hjd
  exact le_trans (csInf_le (UniformBddBelow.rankData_bddBelow_of_lattice Λ hΛ j hjd)
    ⟨W, hWle, hWdim, rfl⟩) hlog

/-- **The uniform data bound.**  For a full-rank lattice `Λ ≤ ℝᵈ` with `covolume Λ = 1` and
`1 ≤ j ≤ d`: `rankData Λ j ≤ (j/d)·log (2^{2d}/vol(B_d))`. -/
theorem rankData_le_of_unimodular {d j : ℕ} (hd : 1 ≤ d) (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛ : Module.finrank ℤ Λ = d)
    (hcov : ZLattice.covolume Λ = 1) (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    rankData Λ j ≤ ((j : ℝ) / (d : ℝ)) *
      Real.log ((2 : ℝ) ^ (2 * d) / ENNReal.toReal (volume (Metric.closedBall (0 : E d) 1))) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (E d) := inferInstance
  have hvolpos : 0 < ENNReal.toReal (volume (Metric.closedBall (0 : E d) 1)) :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_closedBall_pos volume 0
      (by norm_num : (0 : ℝ) < 1))) MeasureTheory.measure_closedBall_lt_top.ne
  -- the increasing extension of `i ↦ log λ_{i+1}` to all of `ℕ`
  set b : ℕ → ℝ := fun i =>
    Real.log (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (min (i + 1) d)) with hb
  have hbpos : ∀ i : ℕ, 0 < Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (min (i + 1) d) :=
    fun i => Commons.Lattice.SuccessiveMinima.positive Λ _ (le_min (by omega) hd) (by rw [hΛ]; exact min_le_right _ _)
  have hbmono : Monotone b := by
    intro i k hik
    refine Real.log_le_log (hbpos i) ?_
    exact successiveMinimum_mono Λ (by omega) (by rw [hΛ]; exact min_le_right _ _)
  have hbj : (Finset.range j).sum b = ∑ i : Fin j, Real.log
      (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : min (i.val + 1) d = i.val + 1 := by omega
    rw [this]
  have hbd : (Finset.range d).sum b = ∑ i : Fin d, Real.log
      (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : min (i.val + 1) d = i.val + 1 := by omega
    rw [this]
  -- step 1: prefix averaging
  have hstep1 : (∑ i : Fin j, Real.log
        (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1))) ≤
      ((j : ℝ) / (d : ℝ)) * (∑ i : Fin d, Real.log
        (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1))) := by
    rw [← hbj, ← hbd]
    exact sum_range_le_mul hbmono hjd
  -- step 2: Minkowski's second theorem (upper)
  have hmin2 := Commons.Lattice.Minkowski.minkowski_second_upper (d := d) (by omega) (E := E d)
    Λ hΛ
  have hprodle : (∏ i : Fin d,
        Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) ≤
      (2 : ℝ) ^ (2 * d) / ENNReal.toReal (volume (Metric.closedBall (0 : E d) 1)) := by
    rw [hcov, mul_one] at hmin2
    rw [le_div_iff₀ hvolpos]
    linarith
  have hprodpos : 0 < ∏ i : Fin d,
      Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1) :=
    Finset.prod_pos fun i _ => Commons.Lattice.SuccessiveMinima.positive Λ (i.val + 1)
      (by omega) (by rw [hΛ]; omega)
  have hstep2 : (∑ i : Fin d, Real.log
        (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1))) ≤
      Real.log ((2 : ℝ) ^ (2 * d) /
        ENNReal.toReal (volume (Metric.closedBall (0 : E d) 1))) := by
    rw [← Real.log_prod (s := Finset.univ)
      (f := fun i : Fin d => Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1))
      (fun i _ => ne_of_gt (Commons.Lattice.SuccessiveMinima.positive Λ (i.val + 1)
        (by omega) (by rw [hΛ]; omega)))]
    exact Real.log_le_log hprodpos hprodle
  have hj0 : (0 : ℝ) ≤ (j : ℝ) / (d : ℝ) := by positivity
  calc rankData Λ j
      ≤ ∑ i : Fin j, Real.log
          (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) :=
        rankData_le_sum_log_successiveMinimum Λ hΛ hj1 hjd
    _ ≤ ((j : ℝ) / (d : ℝ)) * (∑ i : Fin d, Real.log
          (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1))) := hstep1
    _ ≤ ((j : ℝ) / (d : ℝ)) * Real.log ((2 : ℝ) ^ (2 * d) /
          ENNReal.toReal (volume (Metric.closedBall (0 : E d) 1))) :=
        mul_le_mul_of_nonneg_left hstep2 hj0

end Submission.FlowDataBound
