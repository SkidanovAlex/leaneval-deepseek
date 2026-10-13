/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular coefficients `c_{q,j}` of the identity `sin(2θ)·D_θ^q(∂_θ g) = Σ_j c_{q,j} D_θ^{j+1} g`

`Work.Elliptic.WtoW_g_bound` controls `(z+1)^m ∂_z^m D_θ^q(∂_θ g) · sin(2θ)` by
`WlInf α 5 g · (α + sin 2θ) sin(2θ)^{α/5}` for `m + q ≤ 4`.  The proof rests on the
*identity* (`Work.Elliptic.WtoW_g_ident`)

  `sin(2θ) · D_θ^q (∂_θ g) = Σ_{j ≤ q} c_{q,j}(θ) · D_θ^{j+1} g`,

which is proved by induction on `q` from the recurrence

  `c_{q+1,j} = D_θ(c_{q,j}) - X·c_{q,j} + c_{q,j-1}`,   `c_{0,0} = 1`,   `c_{q,j} = 0` for `j > q`,

with `X = ∂_θ (sin 2·) = 2 cos 2θ` and `D_θ = sin(2θ) ∂_θ`.  Writing each coefficient as
`c_{q,j}(θ) = A_{q,j} + B_{q,j}·X(θ)`, the recurrence becomes the *integer* recursion

  `A_{q+1,j} = A_{q,j-1} - 4 B_{q,j}`,   `B_{q+1,j} = B_{q,j-1} - A_{q,j}`,

using `4 sin²(2θ) + X(θ)² = 4`: this is why the coefficients are bounded, and it makes
them computable without any derivative (`Work.Elliptic.WtoW_AB`).

The first few coefficients are `c_{0,0} = 1`; `c_{1,•} = -X, 1`; `c_{2,•} = 4, -2X, 1`;
`c_{3,•} = -4X, 12, -3X, 1`; `c_{4,•} = 16, -16X, 24, -4X, 1`.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Spaces.Defs

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

/-- The bounded angular function `X = ∂_θ(sin 2·) = 2 cos 2θ`. -/
def WtoW_X : ℝ → ℝ := fun θ => 2 * Real.cos (2 * θ)

/-- The integer coefficients `(A_{q,j}, B_{q,j})` of the expansion
`c_{q,j} = A_{q,j} + B_{q,j} X`: `A_{q+1,j} = A_{q,j-1} - 4B_{q,j}`,
`B_{q+1,j} = B_{q,j-1} - A_{q,j}`, `(A_{0,0},B_{0,0}) = (1,0)`. -/
def WtoW_AB : ℕ → ℕ → ℤ × ℤ
  | 0, j => if j = 0 then (1, 0) else (0, 0)
  | (q + 1), j =>
      let a : ℤ := if j = 0 then 0 else (WtoW_AB q (j - 1)).1
      let b : ℤ := if j = 0 then 0 else (WtoW_AB q (j - 1)).2
      (a - 4 * (WtoW_AB q j).2, b - (WtoW_AB q j).1)

/-- The real part of the coefficient `c_{q,j}`. -/
def WtoW_cA (q j : ℕ) : ℝ := ((WtoW_AB q j).1 : ℝ)

/-- The coefficient of `X` in the coefficient `c_{q,j}`. -/
def WtoW_cB (q j : ℕ) : ℝ := ((WtoW_AB q j).2 : ℝ)

/-- The angular coefficient `c_{q,j}(θ) = A_{q,j} + B_{q,j}·2cos(2θ)`. -/
def WtoW_ccoeff (q j : ℕ) : ℝ → ℝ := fun θ => WtoW_cA q j + WtoW_cB q j * WtoW_X θ

@[simp] theorem WtoW_cA_zero_zero : WtoW_cA 0 0 = 1 := by
  simp [WtoW_cA, WtoW_AB]
@[simp] theorem WtoW_cB_zero_zero : WtoW_cB 0 0 = 0 := by
  simp [WtoW_cB, WtoW_AB]

theorem WtoW_cA_succ (q j : ℕ) :
    WtoW_cA (q + 1) j = (if j = 0 then 0 else WtoW_cA q (j - 1)) - 4 * WtoW_cB q j := by
  simp only [WtoW_cA, WtoW_cB, WtoW_AB]
  by_cases hj : j = 0
  · subst hj; simp
  · simp [hj]

theorem WtoW_cB_succ (q j : ℕ) :
    WtoW_cB (q + 1) j = (if j = 0 then 0 else WtoW_cB q (j - 1)) - WtoW_cA q j := by
  simp only [WtoW_cA, WtoW_cB, WtoW_AB]
  by_cases hj : j = 0
  · subst hj; simp
  · simp [hj]

@[simp] theorem WtoW_ccoeff_zero_zero : WtoW_ccoeff 0 0 = fun _ => 1 := by
  funext θ
  simp [WtoW_ccoeff]

end Work.Elliptic
