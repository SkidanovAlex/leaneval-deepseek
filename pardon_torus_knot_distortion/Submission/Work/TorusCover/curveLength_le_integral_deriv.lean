import Mathlib
import Submission.Work.TorusCover.Basic

/-!
# The length of a `C¹` curve is at most the integral of the norm of its derivative

For a `C¹` curve `γ : ℝ → ℝ³` and `a ≤ b`, the total variation of `γ` over `[a,b]`
(the supremum of the lengths of inscribed polygonal lines, `curveLength γ a b`)
is at most the classical arclength `∫ a..b, ‖γ'‖`.

The proof has two ingredients.

* The fundamental theorem of calculus for `C¹` functions,
  `intervalIntegral.integral_deriv_of_contDiffOn_Icc`, together with the inequality
  between the norm of an integral and the integral of the norm
  (`intervalIntegral.norm_integral_le_integral_norm`) shows that for `x ≤ y`,
  `edist (γ y) (γ x) ≤ ENNReal.ofReal (∫ t in x..y, ‖deriv γ t‖)`
  (`curveLength_edist_le_integral_deriv`).

* The total variation is a supremum of sums of such `edist`'s over monotone
  sequences in `[a,b]`; summing the previous bound and using additivity of the
  interval integral over adjacent intervals
  (`intervalIntegral.sum_integral_adjacent_intervals`) and monotonicity of the
  integral of a nonnegative function with respect to the interval
  (`intervalIntegral.integral_mono_interval`) gives the claim
  (`curveLength_sum_le_integral_deriv`).

No regularity of `γ` beyond `C¹` is used.  Note that the hypothesis `a ≤ b` is not needed for
the proof: when `a > b` the set `Icc a b` is empty, so the left-hand side is `0`, while the
interval integral `∫ a..b` is `≤ 0` and `ENNReal.ofReal` of a nonpositive number is `0`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

namespace Work.TorusCover

noncomputable section

/-- Fundamental estimate for a `C¹` curve: the distance between the values of `γ` at `x` and
at `y` (with `x ≤ y`) is at most the integral of `‖deriv γ‖` over `[x,y]`. -/
theorem curveLength_edist_le_integral_deriv (γ : ℝ → R3)
    (hγ : ContDiff ℝ (1 : ℕ∞) γ) {x y : ℝ} (hxy : x ≤ y) :
    edist (γ y) (γ x) ≤ ENNReal.ofReal (∫ t in x..y, ‖deriv γ t‖) := by
  have hcd : ContDiffOn ℝ 1 γ (Set.Icc x y) := hγ.contDiffOn
  have hftc : ∫ t in x..y, deriv γ t = γ y - γ x :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd hxy
  have hnorm : ‖γ y - γ x‖ ≤ ∫ t in x..y, ‖deriv γ t‖ := by
    rw [← hftc]
    exact intervalIntegral.norm_integral_le_integral_norm hxy
  have hnn : 0 ≤ ∫ t in x..y, ‖deriv γ t‖ :=
    intervalIntegral.integral_nonneg hxy (fun u _ => norm_nonneg _)
  rw [edist_eq_enorm_sub, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hnn]
  exact hnorm

/-- The sum of the lengths of the chords of a partition of `[a,b]` contained in `[a,b]` is at
most `∫ a..b, ‖deriv γ‖`. -/
theorem curveLength_sum_le_integral_deriv (γ : ℝ → R3)
    (hγ : ContDiff ℝ (1 : ℕ∞) γ) {a b : ℝ}
    (n : ℕ) (u : ℕ → ℝ) (hu : Monotone u) (hus : ∀ i, u i ∈ Set.Icc a b) :
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
      ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  have hcont : Continuous (fun t : ℝ => ‖deriv γ t‖) :=
    (hγ.continuous_deriv le_rfl).norm
  calc ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
      ≤ ∑ i ∈ Finset.range n,
          ENNReal.ofReal (∫ t in u i..u (i + 1), ‖deriv γ t‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact curveLength_edist_le_integral_deriv γ hγ (hu (Nat.le_succ i))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
          ∫ t in u i..u (i + 1), ‖deriv γ t‖) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        exact fun i _ =>
          intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun x _ => norm_nonneg _)
    _ = ENNReal.ofReal (∫ t in u 0..u n, ‖deriv γ t‖) := by
        rw [intervalIntegral.sum_integral_adjacent_intervals]
        intro k _
        exact hcont.intervalIntegrable _ _
    _ ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
        apply ENNReal.ofReal_le_ofReal
        exact intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le n)) (hus n).2
          (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hcont.intervalIntegrable _ _)

theorem curveLength_le_integral_deriv (γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3)
    (hγ : ContDiff ℝ (1 : ℕ∞) γ) {a b : ℝ} (hab : a ≤ b) :
    Work.TorusCover.curveLength γ a b ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  rw [curveLength_def, eVariationOn]
  refine iSup_le fun p => ?_
  exact curveLength_sum_le_integral_deriv γ hγ p.1 p.2.1 p.2.2.1 p.2.2.2

end

end Work.TorusCover
