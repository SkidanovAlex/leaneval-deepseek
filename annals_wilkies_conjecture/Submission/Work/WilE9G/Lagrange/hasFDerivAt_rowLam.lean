import Mathlib
import Submission.Work.WilE9G.Lagrange.DegenDiff

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
open scoped BigOperators

namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9G

/-- **The normalisation depends only on the multiplier coordinates.**
The differential of `degenLam S` at `p` is `rowLam S p`, the row
`∑_a 2 ν_a · vν_a` of the differential of `degenH`. -/
theorem hasFDerivAt_rowLam {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (p : Fin (Work.WilE9G.Lagrange.degenDim n m S.j) → ℝ) :
    HasFDerivAt (fun p' : Fin (Work.WilE9G.Lagrange.degenDim n m S.j) → ℝ =>
        Work.WilE9G.Lagrange.degenLam S p')
      (Work.WilE9G.Lagrange.rowLam S p) p := by
  -- `degenLam S p' = (∑_a (p' (νIdx a))^2) - 1`: differentiate the sum of squares, then subtract
  -- the constant `1`.
  have h1 : HasFDerivAt (fun p' : Fin (degenDim n m S.j) → ℝ =>
        ∑ a : Fin (S.j + 1), (p' (nuIdx (m := m) a)) ^ 2)
      (rowLam S p) p := by
    have hsum := HasFDerivAt.sum (u := Finset.univ)
      (A := fun a p' => (p' (nuIdx (m := m) a)) ^ 2)
      (A' := fun a : Fin (S.j + 1) =>
        (2 * p (nuIdx (m := m) a)) •
          (ContinuousLinearMap.proj (nuIdx (m := m) a) :
            (Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ))
      (fun a _ => by
        -- `p' ↦ (p' (νIdx a))^2` is `(· ^ 2)` composed with the projection onto the `a`-th
        -- multiplier coordinate; the derivative is `2 ν_a • proj`.
        have h0 := HasFDerivAt.pow
          ((ContinuousLinearMap.proj (nuIdx (m := m) a) :
            (Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)) 2
        convert h0 using 1
        · funext x; simp [ContinuousLinearMap.proj_apply]
        · simp only [ContinuousLinearMap.proj_apply]
          congr 1
          rw [nsmul_eq_mul]
          norm_num)
    have hfun : (∑ i ∈ Finset.univ, (fun p' : Fin (degenDim n m S.j) → ℝ =>
          (p' (nuIdx (m := m) i)) ^ 2))
        = fun p' : Fin (degenDim n m S.j) → ℝ =>
          ∑ a : Fin (S.j + 1), (p' (nuIdx (m := m) a)) ^ 2 := by
      funext x
      rw [Finset.sum_apply]
    have hder : (∑ i ∈ Finset.univ, (2 * p (nuIdx (m := m) i)) •
          (ContinuousLinearMap.proj (nuIdx (m := m) i) :
            (Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ))
        = rowLam S p := by
      rw [rowLam]
      simp
    rw [hfun, hder] at hsum
    exact hsum
  have h2 : (fun p' : Fin (degenDim n m S.j) → ℝ => degenLam S p')
      = (fun p' : Fin (degenDim n m S.j) → ℝ =>
          ∑ a : Fin (S.j + 1), (p' (nuIdx (m := m) a)) ^ 2)
        - (fun _ : Fin (degenDim n m S.j) → ℝ => (1 : ℝ)) := by
    funext p'
    simp [degenLam]
  rw [h2]
  simpa using h1.sub (hasFDerivAt_const (1 : ℝ) p)

end Work.WilE9G.Lagrange
