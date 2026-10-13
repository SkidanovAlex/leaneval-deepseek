/-
Copyright: work module for the Elgindi finite-time singularity project.

# The recurrence for the angular coefficients `c_{q,j}`

`Work.Elliptic.WtoW_ccoeff q j θ = A_{q,j} + B_{q,j}·X(θ)` with `X = 2cos(2·)`, and the
integer recursion
`A_{q+1,j} = (j=0 ? 0 : A_{q,j-1}) - 4B_{q,j}`, `B_{q+1,j} = (j=0 ? 0 : B_{q,j-1}) - A_{q,j}`
(`Work.Elliptic.WtoW_cA_succ`, `Work.Elliptic.WtoW_cB_succ`).

Here we prove the differential recurrence that this integer recursion encodes:

  `c_{q+1,j} = sin(2θ)·∂_θ c_{q,j} - X·c_{q,j} + (j=0 ? 0 : c_{q,j-1})`,

the differentiated form of `sin(2θ)·D_θ^q(∂_θ g) = Σ_j c_{q,j} D_θ^{j+1} g`.  The point is
that `∂_θ c_{q,j} = B_{q,j}·X' = -4B_{q,j} sin(2θ)`, so

  `sin(2θ)∂_θ c_{q,j} - X c_{q,j} = -4B_{q,j} sin²(2θ) - A_{q,j} X - B_{q,j} X²
                                  = -4B_{q,j} - A_{q,j} X`

using `4sin²(2θ) + X(θ)² = 4` (i.e. `sin²+cos²=1`), which is exactly the real form of the
integer recursion.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.WtoW_g_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- `X = ∂_θ (sin 2·) = 2cos(2·)` has derivative `-4 sin(2θ)`. -/
theorem WtoW_hasDerivAt_X (θ : ℝ) :
    HasDerivAt WtoW_X (-4 * Real.sin (2 * θ)) θ := by
  have hg : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h1 : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-Real.sin (2 * θ) * 2) θ := by
    simpa [Function.comp_def] using (Real.hasDerivAt_cos (2 * θ)).comp θ hg
  have h2 := h1.const_mul (2 : ℝ)
  convert h2 using 1
  · ext x; simp [WtoW_X]
  · ring

/-- `X' (θ) = -4 sin(2θ)`. -/
theorem WtoW_deriv_X (θ : ℝ) : deriv WtoW_X θ = -4 * Real.sin (2 * θ) :=
  (WtoW_hasDerivAt_X θ).deriv

/-- The coefficient `c_{q,j} = A_{q,j} + B_{q,j}X` has derivative `B_{q,j}·X'`. -/
theorem WtoW_hasDerivAt_ccoeff (q j : ℕ) (θ : ℝ) :
    HasDerivAt (WtoW_ccoeff q j) (WtoW_cB q j * (-4 * Real.sin (2 * θ))) θ := by
  have h : HasDerivAt
      (fun x => WtoW_cA q j + WtoW_cB q j * WtoW_X x)
      (WtoW_cB q j * (-4 * Real.sin (2 * θ))) θ :=
    ((WtoW_hasDerivAt_X θ).const_mul (WtoW_cB q j)).const_add (WtoW_cA q j)
  rw [show WtoW_ccoeff q j
      = fun x => WtoW_cA q j + WtoW_cB q j * WtoW_X x from rfl]
  exact h

/-- `∂_θ c_{q,j} = -4 B_{q,j} sin(2θ)`. -/
theorem WtoW_deriv_ccoeff (q j : ℕ) (θ : ℝ) :
    deriv (WtoW_ccoeff q j) θ = WtoW_cB q j * (-4 * Real.sin (2 * θ)) :=
  (WtoW_hasDerivAt_ccoeff q j θ).deriv

/-- The differential recurrence satisfied by the angular coefficients `c_{q,j}`. -/
theorem WtoW_g_coeff_rec (q j : ℕ) (θ : ℝ) :
    Work.Elliptic.WtoW_ccoeff (q + 1) j θ
      = Real.sin (2 * θ) * deriv (Work.Elliptic.WtoW_ccoeff q j) θ
        - Work.Elliptic.WtoW_X θ * Work.Elliptic.WtoW_ccoeff q j θ
        + (if j = 0 then 0 else Work.Elliptic.WtoW_ccoeff q (j - 1) θ) := by
  have hd := WtoW_deriv_ccoeff q j θ
  have hA := WtoW_cA_succ q j
  have hB := WtoW_cB_succ q j
  have hc : Real.sin (2 * θ) ^ 2 + Real.cos (2 * θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * θ)
  simp only [WtoW_ccoeff] at *
  rw [hA, hB, hd]
  by_cases hj : j = 0
  · subst hj
    simp only [WtoW_X, ↓reduceIte] at *
    linear_combination (4 * WtoW_cB q 0) * hc
  · simp only [hj, ↓reduceIte, WtoW_X] at *
    linear_combination (4 * WtoW_cB q j) * hc

end Work.Elliptic
