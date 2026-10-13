/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular factor `2 cos 2θ` is bounded by `sin²2θ` under iterated `D_θ`

`Work.Elliptic.Dth1Iter` is the `n`-th iterate of the angular operator `D_θ = sin(2θ) ∂_θ`.
For the specific angular profile `f(θ) = 2 cos(2θ)` the iterates `D_θ^k f`, `k = 1,2,3`, are
multiples of `sin²(2θ)` with bounded coefficients, and `|f|` is bounded as well. This is the
elementary input used to bound the angular slices of the terms produced by `D_θ^k` acting on
products.

Concretely:
* `Dth1Iter 1 f θ = -4 sin²2θ`,
* `Dth1Iter 2 f θ = -16 sin²2θ cos 2θ`,
* `Dth1Iter 3 f θ = -64 sin²2θ cos²2θ + 32 sin⁴2θ`,

so with `M = 100` all the required inequalities hold.

Everything is pointwise and global (no smoothness hypothesis is needed: `deriv` is a total
function and the explicit formulas are valid at every `θ`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.Algebra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

set_option linter.unusedSimpArgs false

/-! ## Auxiliary derivatives -/

private lemma deriv_sin_two_sq (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have h3 := h2.pow 2
  have h4 : deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ
      = 2 * Real.sin (2 * θ) ^ (2 - 1) * (Real.cos (2 * θ) * 2) := h3.deriv
  rw [h4]; ring

private lemma deriv_sin_two_sq_mul_cos (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t) ^ 2 * Real.cos (2 * t)) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) ^ 2 - 2 * Real.sin (2 * θ) ^ 3 := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h1
  have hp := hs.pow 2
  have hm := hp.mul hc
  have h4 : deriv (fun t : ℝ => Real.sin (2 * t) ^ 2 * Real.cos (2 * t)) θ
      = (2 * Real.sin (2 * θ) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) * Real.cos (2 * θ)
        + Real.sin (2 * θ) ^ 2 * (-Real.sin (2 * θ) * 2) := hm.deriv
  rw [h4]; ring

/-! ## The first three iterates of `D_θ` applied to `θ ↦ 2 cos 2θ` -/

private lemma Dth1Iter_one_two_cos (θ : ℝ) :
    Dth1Iter 1 (fun t : ℝ => 2 * Real.cos (2 * t)) θ = -4 * Real.sin (2 * θ) ^ 2 := by
  simp only [Dth1Iter_succ, Dth1Iter_zero, Dth1]
  rw [deriv_two_cos_two θ]
  ring

private lemma Dth1Iter_two_two_cos (θ : ℝ) :
    Dth1Iter 2 (fun t : ℝ => 2 * Real.cos (2 * t)) θ
      = -16 * (Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ)) := by
  have h1 : Dth1Iter 1 (fun t : ℝ => 2 * Real.cos (2 * t))
      = fun x : ℝ => -4 * Real.sin (2 * x) ^ 2 := funext Dth1Iter_one_two_cos
  rw [show Dth1Iter 2 (fun t : ℝ => 2 * Real.cos (2 * t))
        = Dth1 (Dth1Iter 1 (fun t : ℝ => 2 * Real.cos (2 * t))) from rfl, h1]
  simp only [Dth1]
  rw [deriv_const_mul_field, deriv_sin_two_sq]
  ring

private lemma Dth1Iter_three_two_cos (θ : ℝ) :
    Dth1Iter 3 (fun t : ℝ => 2 * Real.cos (2 * t)) θ
      = -64 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ) ^ 2 + 32 * Real.sin (2 * θ) ^ 4 := by
  have h2 : Dth1Iter 2 (fun t : ℝ => 2 * Real.cos (2 * t))
      = fun x : ℝ => -16 * (Real.sin (2 * x) ^ 2 * Real.cos (2 * x)) :=
    funext Dth1Iter_two_two_cos
  rw [show Dth1Iter 3 (fun t : ℝ => 2 * Real.cos (2 * t))
        = Dth1 (Dth1Iter 2 (fun t : ℝ => 2 * Real.cos (2 * t))) from rfl, h2]
  simp only [Dth1]
  rw [deriv_const_mul_field, deriv_sin_two_sq_mul_cos]
  ring

/-! ## The bound -/

theorem DivSinPhiBound :
    ∃ M : ℝ, 0 < M ∧
      (∀ θ : ℝ, |2 * Real.cos (2 * θ)| ≤ M) ∧
      (∀ k ∈ Finset.Icc 1 3, ∀ θ : ℝ,
        |Work.Elliptic.Dth1Iter k (fun t : ℝ => 2 * Real.cos (2 * t)) θ|
          ≤ M * (Real.sin (2 * θ)) ^ 2) := by
  refine ⟨100, by norm_num, ?_, ?_⟩
  · intro θ
    rw [abs_le]
    constructor <;> nlinarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
  · intro k hk θ
    obtain ⟨hk1, hk3⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · rw [Dth1Iter_one_two_cos]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (Real.sin (2 * θ))]
    · rw [Dth1Iter_two_two_cos]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (Real.sin (2 * θ)), Real.neg_one_le_cos (2 * θ),
        Real.cos_le_one (2 * θ)]
    · rw [Dth1Iter_three_two_cos]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (Real.sin (2 * θ)), sq_nonneg (Real.cos (2 * θ)),
        Real.sin_sq_le_one (2 * θ), Real.cos_sq_le_one (2 * θ)]

end Work.Elliptic
