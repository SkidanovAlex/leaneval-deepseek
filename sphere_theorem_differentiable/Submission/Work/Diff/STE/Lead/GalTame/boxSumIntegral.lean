import Mathlib
import Submission.Work.Diff.STE.B3.boxIdx_iUnion
import Submission.Work.Diff.STE.B3.boxIdx_pairwiseDisjoint
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Splitting a whole-space integral into the `2^n` unit-cube pieces of `(-1,1]^n`

The target `boxSumIntegral` says that for a continuous `h` vanishing on the closed exterior of
the ball of radius `1/2`, the integral over the unit cube `(0,1]^n` of the `2^n`-fold sum
`∑_{k ∈ {-1,0}^n} h (· + k)` equals the integral of `h` over all of `ℝ^n`.

## Route

* `integral_finsetSum` splits the sum out of the integral (each translate of `h` is continuous,
  hence integrable on the bounded cube).
* `steB3_setIntegral_comp_add_real` (change of variables `y ↦ y + k` in a set integral) turns the
  `k`-th term into the integral of `h` over the box `(0,1]^n + k = ∏ᵢ (kᵢ, kᵢ+1]`.
* `integral_biUnion_finset` adds these up over the pairwise disjoint boxes
  (`B3.boxIdx_pairwiseDisjoint`), giving the integral of `h` over their union
  `⋃_{k ∈ {-1,0}^n} ((0,1]^n + k) = (-1,1]^n` (`B3.boxIdx_iUnion`).
* Finally, since `h` vanishes off the ball of radius `1/2 ⊆ (-1,1]^n`, the integral over
  `(-1,1]^n` is the integral over the whole space
  (`setIntegral_eq_integral_of_forall_compl_eq_zero`); for this we only need that a point of
  `(-1,1]^n`'s complement has some coordinate of absolute value `≥ 1`, hence norm `≥ 1 ≥ 1/2`.
-/

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory

/-- Splitting the whole-space (`L²`) integral of a function that is supported in the open ball of
radius `1/2` into the `2^n` unit-cube pieces `(0,1]^n + k`, `k ∈ {-1,0}^n`. -/
theorem boxSumIntegral {n : ℕ} (h : (Fin n → ℝ) → ℝ) (hh : Continuous h)
    (hzero : ∀ z : Fin n → ℝ, (1 : ℝ) / 2 ≤ ‖z‖ → h z = 0) :
    ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        (∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n), h (x + Work.Diff.STE.iVec k))
      = ∫ z : Fin n → ℝ, h z := by
  classical
  -- The translate of the cube by a lattice vector is the half-open box `∏ᵢ (kᵢ, kᵢ+1]`.
  have hB : ∀ k : Fin n → ℤ,
      (fun y : Fin n → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube (ι := Fin n)
        = Set.pi Set.univ (fun i : Fin n => Set.Ioc ((k i : ℝ)) ((k i : ℝ) + 1)) := by
    intro k
    ext x
    rw [Work.Diff.STE.B3.mem_image_iVec_unitCube]
    simp
  -- `h` is compactly supported (the ball of radius `1/2`), hence integrable.
  have hsupp : Function.support h ⊆ Metric.closedBall (0 : Fin n → ℝ) (1 / 2) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    rw [not_le] at hlt
    exact (Function.mem_support.mp hz) (hzero z (le_of_lt hlt))
  have hcpt : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact (ProperSpace.isCompact_closedBall 0 (1 / 2))
      hsupp
  have hInt : Integrable h volume := hh.integrable_of_hasCompactSupport hcpt
  -- The `2 ^ n` boxes are measurable …
  have hmeas : ∀ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
      MeasurableSet ((fun y : Fin n → ℝ => y + Work.Diff.STE.iVec k) ''
        Work.Diff.STE.unitCube (ι := Fin n)) := by
    intro k _
    rw [hB k]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)
  -- … and pairwise disjoint (`B3.boxIdx_pairwiseDisjoint`).
  have hdisj := Work.Diff.STE.B3.boxIdx_pairwiseDisjoint (ι := Fin n)
  calc ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        (∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n), h (x + Work.Diff.STE.iVec k))
      = ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
          ∫ x in Work.Diff.STE.unitCube (ι := Fin n), h (x + Work.Diff.STE.iVec k) := by
        rw [integral_finsetSum]
        intro k _
        exact Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real
          (hh.comp (continuous_id.add continuous_const))
    _ = ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
          ∫ y in (fun y : Fin n → ℝ => y + Work.Diff.STE.iVec k) ''
            Work.Diff.STE.unitCube (ι := Fin n), h y := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Work.Diff.STE.B3.steB3_setIntegral_comp_add_real]
    _ = ∫ y in (⋃ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
          (fun y : Fin n → ℝ => y + Work.Diff.STE.iVec k) ''
            Work.Diff.STE.unitCube (ι := Fin n)), h y :=
        (integral_biUnion_finset (Work.Diff.STE.csqp_boxIdx (Fin n)) hmeas hdisj
          (fun k _ => hInt.integrableOn)).symm
    _ = ∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1), h y := by
        rw [Work.Diff.STE.B3.boxIdx_iUnion (ι := Fin n)]
    _ = ∫ y : Fin n → ℝ, h y := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)
        -- A point outside `(-1,1]^n` has a coordinate of absolute value `≥ 1`, hence norm `≥ 1`.
        have hzi : ∃ i : Fin n, ¬ (z i ∈ Set.Ioc (-1 : ℝ) 1) := by
          by_contra hc
          exact hz (by
            rw [Set.mem_pi]
            intro i _
            by_contra hi
            exact hc ⟨i, hi⟩)
        obtain ⟨i, hi⟩ := hzi
        rw [Set.mem_Ioc, not_and_or] at hi
        have h1i : (1 : ℝ) ≤ |z i| := by
          rcases hi with h1 | h1
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have hnorm : (1 : ℝ) ≤ ‖z‖ := by
          calc (1 : ℝ) ≤ |z i| := h1i
            _ = ‖z i‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖z‖ := norm_le_pi_norm z i
        exact hzero z (by linarith)

end Work.Diff.STE.Lead.GalTame
