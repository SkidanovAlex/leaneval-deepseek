import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Commons.Analysis.Convex.closestPoint_variational

open scoped RealInnerProductSpace
open Commons.Analysis.Convex

namespace Commons.Analysis.Convex

/-- Strong separation of a point from a convex compact set by a halfspace, in a
real inner product space.

For a convex compact nonempty set `D` and a point `y ∉ D`, there is a vector
`u` and a real `c` such that `D` lies strictly in the halfspace `{x | c < u•x}`
while `y` lies strictly on the other side (`u•y < c`).

The proof picks the point `p ∈ D` closest to `y` and uses the variational
inequality `closestPoint_variational` for the projection onto a convex set:
`⟪y - p, x - p⟫ ≤ 0` for every `x ∈ D`.  With `u = p - y` this gives
`⟪u, p⟫ ≤ ⟪u, x⟫` for all `x ∈ D`, while `⟪u, p⟫ = ⟪u, y⟫ + ‖u‖² > ⟪u, y⟫`
(because `u ≠ 0`); hence the midpoint `c` of `⟪u, y⟫` and `⟪u, p⟫` separates. -/
theorem exists_separating_halfplane
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] {D : Set V} (hDconv : Convex ℝ D) (hDcpt : IsCompact D)
    (hDne : D.Nonempty) {y : V} (hy : y ∉ D) :
    ∃ (u : V) (c : ℝ), (∀ x ∈ D, c < inner ℝ u x) ∧ inner ℝ u y < c := by
  -- Pick the closest point `p` of `D` to `y`.
  rcases hDcpt.exists_isMinOn hDne (by fun_prop : ContinuousOn (fun x : V => ‖y - x‖) D) with
    ⟨p, hpD, hpmin⟩
  let u : V := p - y
  have hmin : ∀ x ∈ D, ‖y - p‖ ≤ ‖y - x‖ := by
    intro x hx
    exact hpmin hx
  -- `u ≠ 0` because `p ∈ D` while `y ∉ D`.
  have hu_ne : u ≠ 0 := by
    intro h
    apply hy
    have : p = y := by simpa [u] using sub_eq_zero.mp h
    simpa [this] using hpD
  have hsq_pos : 0 < ‖u‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu_ne)
  -- `⟪u, p⟫ = ⟪u, y⟫ + ‖u‖²`, hence `⟪u, y⟫ < ⟪u, p⟫`.
  have hsub : inner ℝ u (p - y) = inner ℝ u p - inner ℝ u y := by
    rw [inner_sub_right]
  have hself : inner ℝ u (p - y) = ‖u‖ ^ 2 := by
    simp [u]
  have hrel : inner ℝ u p = inner ℝ u y + ‖u‖ ^ 2 := by
    rw [hsub] at hself
    linarith
  have hylt : inner ℝ u y < inner ℝ u p := by
    nlinarith
  -- Variational inequality: `⟪u, p⟫ ≤ ⟪u, x⟫` for every `x ∈ D`.
  have hvar : ∀ x ∈ D, inner ℝ u p ≤ inner ℝ u x := by
    intro x hx
    have hv := closestPoint_variational (V := V) hDconv (q := y) (p := p) hpD hmin x hx
    have hneg : inner ℝ (p - y) (x - p) = - inner ℝ (y - p) (x - p) := by
      calc
        inner ℝ (p - y) (x - p) = inner ℝ (-(y - p)) (x - p) := by rw [neg_sub]
        _ = - inner ℝ (y - p) (x - p) := by rw [inner_neg_left]
    have hnonneg : 0 ≤ inner ℝ (p - y) (x - p) := by
      rw [hneg]
      linarith
    have hsplit : inner ℝ (p - y) (x - p) = inner ℝ (p - y) x - inner ℝ (p - y) p := by
      rw [inner_sub_right]
    have hge : inner ℝ (p - y) p ≤ inner ℝ (p - y) x := by
      linarith
    simpa [u] using hge
  -- The midpoint `c` of `⟪u, y⟫` and `⟪u, p⟫` lies strictly between them.
  refine ⟨u, (inner ℝ u y + inner ℝ u p) / 2, ?_, ?_⟩
  · intro x hx
    have hxineq : inner ℝ u p ≤ inner ℝ u x := hvar x hx
    have hclt : (inner ℝ u y + inner ℝ u p) / 2 < inner ℝ u p := by
      linarith
    exact lt_of_lt_of_le hclt hxineq
  · linarith

end Commons.Analysis.Convex