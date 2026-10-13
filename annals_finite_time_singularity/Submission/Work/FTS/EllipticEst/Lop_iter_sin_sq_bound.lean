import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.LopIterSinSqDefs
import Submission.Work.FTS.EllipticEst.GfunContDiff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The coefficient functions `gfun` attached to `L^i (sin(2θ)²)`

`L = Work.Spaces.Lop` is the one-dimensional angular operator `L u θ = sin(2θ) u'(θ)`, whose
iterates are `LopIter i u = (L^[i]) u`.  The operator is a derivation (`Work.Spaces.Lop_mul`),
so `L(s·h) = L(s)·h + s·L(h)`; since `deriv (sin(2θ)²) = 4 sin(2θ) cos(2θ)` the identity
`L(sin(2θ)²·h) = sin(2θ)²·(4 cos(2θ)·h + sin(2θ)·h')` holds wherever `h` is differentiable.
Iterating it, `L^i (sin(2θ)²)` is divisible by `sin(2θ)²`, with quotient the coefficient
function `gfun i` of `LopIterSinSqDefs`. -/

/-- `deriv (fun θ => sin(2θ)²) θ = 4 sin(2θ) cos(2θ)`. -/
theorem lopSq_deriv_sin_two_sq (θ : ℝ) :
    deriv (fun t : ℝ => (Real.sin (2 * t)) ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h1 : deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    simpa [Function.comp_def, mul_comm] using h.deriv
  have hfun : (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      = (fun t : ℝ => Real.sin (2 * t)) ^ 2 := rfl
  rw [hfun, deriv_pow (by fun_prop), h1]
  ring

/-- The one-step recursion `L(sin(2θ)² · h) = sin(2θ)² · (4 cos(2θ) h + sin(2θ) h')`, at every
point where `h` is differentiable. -/
theorem lopSq_Lop_sin_sq_mul (h : ℝ → ℝ) (θ : ℝ) (hh : DifferentiableAt ℝ h θ) :
    Work.Spaces.Lop (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 * h θ) θ
      = (Real.sin (2 * θ)) ^ 2 * (4 * Real.cos (2 * θ) * h θ
          + Real.sin (2 * θ) * deriv h θ) := by
  have hsin : DifferentiableAt ℝ (fun t : ℝ => (Real.sin (2 * t)) ^ 2) θ := by fun_prop
  have hfun : (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 * h θ)
      = (fun t : ℝ => (Real.sin (2 * t)) ^ 2) * h := rfl
  rw [hfun, Work.Spaces.Lop_mul _ _ θ hsin hh]
  simp only [Work.Spaces.Lop]
  rw [lopSq_deriv_sin_two_sq]
  ring

/-- The iterates of `sin(2θ)²` under `L = sin(2θ) ∂_θ` are `sin(2θ)²` times the coefficient
functions of the recursion:  `L^i (sin(2θ)²) = fun θ => sin(2θ)² · gfun i θ`. -/
theorem lopSq_factor (i : ℕ) :
    LopIter i (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2)
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 * gfun i θ := by
  induction i with
  | zero => simp [LopIter]
  | succ n ih =>
      rw [LopIter_succ, ih, gfun_succ]
      funext θ
      have hd : DifferentiableAt ℝ (gfun n) θ :=
        ((GfunContDiff n).differentiable (by simp)).differentiableAt
      simpa only [Pi.mul_apply] using lopSq_Lop_sin_sq_mul (gfun n) θ hd

/-- A common bound for the finitely many coefficient functions `gfun i`, `i ≤ K`, on the
compact interval `Iθ = [0, π/2]` (each `gfun i` is continuous there by `GfunContDiff`). -/
theorem lopSq_exists_bound_gfun (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ K, ∀ θ ∈ Work.Spaces.Iθ, |gfun i θ| ≤ C := by
  induction K with
  | zero =>
      refine ⟨1, one_pos, ?_⟩
      intro i hi θ _
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      simp
  | succ K ih =>
      obtain ⟨C, hCpos, hC⟩ := ih
      obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := gfun (K + 1)) ((GfunContDiff (K + 1)).continuous.continuousOn)
      refine ⟨max C (D + 1), lt_max_of_lt_left hCpos, ?_⟩
      intro i hi θ hθ
      rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · exact le_trans (hC i (Nat.lt_succ_iff.mp hlt) θ hθ) (le_max_left _ _)
      · subst heq
        have hDθ := hD θ hθ
        rw [Real.norm_eq_abs] at hDθ
        exact le_trans hDθ
          (le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _))

/-- Every iterate `L^i (sin(2θ)²)` of `L = sin(2θ) ∂_θ` is `O(sin(2θ)²)` on `Iθ = [0,π/2]`
(these are concrete coefficient functions occurring in the proof of `slice_f_bound`).

Recommended route (much simpler than a derivative ladder): by induction on `i` one has
`L^i (sin²) = fun θ => sin(2θ)^2 * g i θ` with `g : ℕ → ℝ → ℝ` the recursively defined
`g 0 = 1`, `g (i+1) = fun θ => 2 * cos (2θ) * g i θ + sin (2θ) * deriv (g i) θ`
(use `L(f·h) = sin(2θ)·deriv (f·h)` and the product rule: `L(sin²·h) = sin²·(2·deriv(sin²)/sin·h + sin·h')`,
i.e. `deriv (sin(2θ)^2) = 4 sin(2θ) cos(2θ)`, so `g (i+1) = 4cos(2θ)·g i + sin(2θ)·deriv (g i)`).
Each `g i` is `C^∞` on `ℝ` (induction on `i`, using `ContDiff.deriv`), so each is continuous,
hence bounded on the compact `Iθ`; taking the maximum over the finitely many `i ≤ K` gives
`C > 0` with `|g i θ| ≤ C` for `i ≤ K`, `θ ∈ Iθ`, and then
`|L^i (sin²) θ| = sin(2θ)^2 · |g i θ| ≤ C · sin(2θ)^2` (using `sin(2θ) ≥ 0` on `Iθ`).
At `θ = 0, π/2` this is `0 ≤ 0`. -/
theorem Lop_iter_sin_sq_bound (K : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ i ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ|
      ≤ C * (Real.sin (2 * θ)) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := lopSq_exists_bound_gfun K
  refine ⟨C, hCpos, ?_⟩
  intro i hi θ hθ
  rw [lopSq_factor i]
  have hs : 0 ≤ (Real.sin (2 * θ)) ^ 2 := sq_nonneg _
  rw [abs_mul, abs_of_nonneg hs]
  calc (Real.sin (2 * θ)) ^ 2 * |gfun i θ|
        ≤ (Real.sin (2 * θ)) ^ 2 * C := mul_le_mul_of_nonneg_left (hC i hi θ hθ) hs
    _ = C * (Real.sin (2 * θ)) ^ 2 := mul_comm _ _

end Work.FTS.EllipticEst
