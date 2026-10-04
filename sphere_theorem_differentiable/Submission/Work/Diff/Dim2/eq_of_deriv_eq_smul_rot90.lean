import Mathlib
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

/-- **The quarter turn is skew-adjoint** for the Euclidean inner product on `ℝ²`:
`⟪J a, b⟫ = −⟪a, J b⟫`. -/
lemma inner_rot90_left (a b : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (rot90 a) b = - inner ℝ a (rot90 b) := by
  rw [inner_fin_two, inner_fin_two, rot90_apply_zero, rot90_apply_one,
    rot90_apply_zero, rot90_apply_one]
  ring

/-- **Uniqueness for the linear ODE `u' = f • J u` on the plane.**  If two unit-norm plane curves
`u, v : ℝ → ℝ²` satisfy `u' = f • J u` and `v' = f • J v` (where `J = rot90`) and agree at `0`,
then they coincide.  Indeed `θ ↦ ⟪u θ, v θ⟫` has derivative
`f θ (⟪J u, v⟫ + ⟪u, J v⟫) = f θ (−⟪u, J v⟫ + ⟪u, J v⟫) = 0` (the quarter turn is skew-adjoint),
so it is constantly `1`; with `‖u θ‖ = ‖v θ‖ = 1` this gives `‖u θ − v θ‖² = 0`. -/
theorem eq_of_deriv_eq_smul_rot90
    {f : ℝ → ℝ} {u v : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hu : ∀ θ, HasDerivAt u ((f θ) • Work.Diff.Dim2.rot90 (u θ)) θ)
    (hv : ∀ θ, HasDerivAt v ((f θ) • Work.Diff.Dim2.rot90 (v θ)) θ)
    (hu1 : ∀ θ, ‖u θ‖ = 1) (hv1 : ∀ θ, ‖v θ‖ = 1) (h0 : u 0 = v 0) :
    u = v := by
  -- The pairing `θ ↦ ⟪u θ, v θ⟫` has vanishing derivative everywhere.
  have key : ∀ θ, inner ℝ (u θ) (v θ) = 1 := by
    intro θ
    have hd : ∀ x, deriv (fun t => inner ℝ (u t) (v t)) x = 0 := by
      intro x
      have h := (hu x).inner ℝ (hv x)
      have hzero : inner ℝ (u x) ((f x) • rot90 (v x))
          + inner ℝ ((f x) • rot90 (u x)) (v x) = 0 := by
        rw [real_inner_smul_right, real_inner_smul_left, inner_rot90_left]
        ring
      rw [hzero] at h
      exact h.deriv
    have hdiff : Differentiable ℝ (fun t => inner ℝ (u t) (v t)) :=
      fun t => ((hu t).inner ℝ (hv t)).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff hd θ 0
    rw [hc, ← h0, real_inner_self_eq_norm_sq, hu1 0]
    norm_num
  funext θ
  have h2 : ‖u θ - v θ‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm (u θ) (v θ), real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      hu1 θ, hv1 θ, key θ]
    ring
  have h4 : ‖u θ - v θ‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

end Work.Diff.Dim2

/-- The requested statement, available under its advertised name `Work.Diff.Dim2.eq_of_deriv_eq_smul_rot90`
(the file above wraps it in a further `namespace Work.Diff.Dim2`, which is why the primary declaration
is spelled `Work.Diff.Dim2.Work.Diff.Dim2.eq_of_deriv_eq_smul_rot90`). -/
theorem eq_of_deriv_eq_smul_rot90
    {f : ℝ → ℝ} {u v : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hu : ∀ θ, HasDerivAt u ((f θ) • rot90 (u θ)) θ)
    (hv : ∀ θ, HasDerivAt v ((f θ) • rot90 (v θ)) θ)
    (hu1 : ∀ θ, ‖u θ‖ = 1) (hv1 : ∀ θ, ‖v θ‖ = 1) (h0 : u 0 = v 0) :
    u = v :=
  Work.Diff.Dim2.Work.Diff.Dim2.eq_of_deriv_eq_smul_rot90 hu hv hu1 hv1 h0
