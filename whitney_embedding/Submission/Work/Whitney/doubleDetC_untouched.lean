import Mathlib
import Submission.Work.Whitney.DoubleDetC

/-!
# `doubleDetC` is unchanged away from the modification region

For the endgame of the strong Whitney embedding theorem one inserts a double point near a
pre-existing double point `P`, and then cancels the pair.  The cancellation needs the *relative*
sign of the two double points, computed in one chart; the pre-existing double point must therefore
keep its `doubleDetC`-value.  This file records that a modification which is the identity outside
`{y | R ≤ ‖c y‖}` does not change `doubleDetC` at points of norm `> R` in the chart `c`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

/-- `doubleDetRep` only depends on the values of the function near the two parameters. -/
theorem doubleDetRep_congr {n : ℕ}
    {g g' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n))}
    (u v : EuclideanSpace ℝ (Fin n))
    (hu : g =ᶠ[𝓝 u] g') (hv : g =ᶠ[𝓝 v] g') :
    doubleDetRep g u v = doubleDetRep g' u v := by
  rw [doubleDetRep, doubleDetRep, hu.fderiv_eq, hv.fderiv_eq]

/-- **The single-chart signed determinant is unchanged at points outside the modification region.**
If `f' = f` whenever `R ≤ ‖c y‖`, then `doubleDetC f' c p q = doubleDetC f c p q` for any two
points `p, q` of `c`'s source with `R < ‖c p‖` and `R < ‖c q‖`. -/
theorem doubleDetC_eq_of_eq_of_norm_ge {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f f' : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (R : ℝ)
    (h : ∀ y : M, R ≤ ‖c y‖ → f' y = f y)
    (p q : M) (hp : p ∈ c.source) (hq : q ∈ c.source)
    (hRp : R < ‖c p‖) (hRq : R < ‖c q‖) :
    doubleDetC f' c p q = doubleDetC f c p q := by
  refine doubleDetRep_congr _ _ ?_ ?_
  · filter_upwards [c.open_target.mem_nhds (c.map_source hp),
      isOpen_lt continuous_const continuous_norm |>.mem_nhds hRp] with u hu hnu
    have hcu : c (c.symm u) = u := c.right_inv hu
    have hnorm : R ≤ ‖c (c.symm u)‖ := by rw [hcu]; exact le_of_lt hnu
    exact h (c.symm u) hnorm
  · filter_upwards [c.open_target.mem_nhds (c.map_source hq),
      isOpen_lt continuous_const continuous_norm |>.mem_nhds hRq] with u hu hnu
    have hcu : c (c.symm u) = u := c.right_inv hu
    have hnorm : R ≤ ‖c (c.symm u)‖ := by rw [hcu]; exact le_of_lt hnu
    exact h (c.symm u) hnorm

end Work.Whitney
