import Mathlib
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

/-- **The coordinate form of `rot90`.**  The quarter turn `J = rot90` of the plane has coordinates
`J (x, y) = (-y, x)`, so the pairing with `J u` is `⟪J u, v⟫ = -(u 1) * v 0 + u 0 * v 1`. -/
lemma inner_rot90_coord (u v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (rot90 u) v = -(u 1) * v 0 + u 0 * v 1 := by
  rw [inner_fin_two, rot90_apply_zero, rot90_apply_one]

/-- **A vector of the plane orthogonal to a unit vector is a multiple of the quarter turn.**
If `u ≠ 0` (here `⟪u, u⟫ = 1`) and `⟪u, v⟫ = 0` in the plane, then `v` lies in the line spanned by
`rot90 u`, and its coordinate is `⟪rot90 u, v⟫` because `rot90 u` is a unit vector.

Both the orthogonality and the coefficient are rewritten in the two coordinates and the resulting
polynomial identities are closed by `linarith` (the certificate is
`u 0 * ⟪u, v⟫ = 0` resp. `u 1 * ⟪u, v⟫ = 0` together with `v i * (‖u‖² - 1) = 0`). -/
lemma eq_smul_rot90_of_inner_eq_zero (u v : EuclideanSpace ℝ (Fin 2))
    (h : inner ℝ u v = 0) (hu : inner ℝ u u = 1) :
    v = (inner ℝ (rot90 u) v) • rot90 u := by
  have h1 : u 0 * v 0 + u 1 * v 1 = 0 := by
    rw [← inner_fin_two]; exact h
  have h2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have hh := hu
    rw [inner_fin_two] at hh
    nlinarith [hh]
  have hkin : inner ℝ (rot90 u) v = -(u 1) * v 0 + u 0 * v 1 := inner_rot90_coord u v
  have k1 : u 0 ^ 2 * v 0 + u 0 * u 1 * v 1 = 0 := by
    have h' : u 0 * (u 0 * v 0 + u 1 * v 1) = 0 := by rw [h1, mul_zero]
    have h'' : u 0 * (u 0 * v 0 + u 1 * v 1) = u 0 ^ 2 * v 0 + u 0 * u 1 * v 1 := by ring
    rw [h''] at h'; exact h'
  have k2 : u 0 ^ 2 * v 0 + u 1 ^ 2 * v 0 = v 0 := by
    have h' : v 0 * (u 0 ^ 2 + u 1 ^ 2) = v 0 := by rw [h2, mul_one]
    have h'' : v 0 * (u 0 ^ 2 + u 1 ^ 2) = u 0 ^ 2 * v 0 + u 1 ^ 2 * v 0 := by ring
    rw [h''] at h'; exact h'
  have k3 : u 0 * u 1 * v 0 + u 1 ^ 2 * v 1 = 0 := by
    have h' : u 1 * (u 0 * v 0 + u 1 * v 1) = 0 := by rw [h1, mul_zero]
    have h'' : u 1 * (u 0 * v 0 + u 1 * v 1) = u 0 * u 1 * v 0 + u 1 ^ 2 * v 1 := by ring
    rw [h''] at h'; exact h'
  have k4 : u 0 ^ 2 * v 1 + u 1 ^ 2 * v 1 = v 1 := by
    have h' : v 1 * (u 0 ^ 2 + u 1 ^ 2) = v 1 := by rw [h2, mul_one]
    have h'' : v 1 * (u 0 ^ 2 + u 1 ^ 2) = u 0 ^ 2 * v 1 + u 1 ^ 2 * v 1 := by ring
    rw [h''] at h'; exact h'
  rw [PiLp.ext_iff]
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [PiLp.smul_apply, smul_eq_mul, hkin, rot90_apply_zero]
    linarith [k1, k2]
  · rw [PiLp.smul_apply, smul_eq_mul, hkin, rot90_apply_one]
    linarith [k3, k4]

/-- **The velocity of a smooth unit-norm plane curve is `J` times the curve, times the angular
velocity.**  If `κ : ℝ → ℝ²` is `C^∞` with `‖κ θ‖ = 1` for all `θ`, then
`deriv κ θ = ⟪J (κ θ), deriv κ θ⟫ • J (κ θ)`, where `J = rot90` is the quarter turn: the velocity
is perpendicular to `κ θ` (differentiate `‖κ‖² ≡ 1`) and the plane is 2-dimensional, so it is a
multiple of `J (κ θ)`, and the multiple is the inner product with `J (κ θ)`. -/
theorem deriv_eq_smul_rot90
    {κ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hunit : ∀ θ, ‖κ θ‖ = 1) :
    ∀ θ, deriv κ θ =
      (inner ℝ (Work.Diff.Dim2.rot90 (κ θ)) (deriv κ θ)) • Work.Diff.Dim2.rot90 (κ θ) := by
  intro θ
  -- `κ` is differentiable, so `⟪κ θ, κ θ⟫ ≡ 1` can be differentiated.
  have hdiff : DifferentiableAt ℝ κ θ := (hsm.differentiable (by simp)).differentiableAt
  have hd : HasDerivAt κ (deriv κ θ) θ := hdiff.hasDerivAt
  have hinner := HasDerivAt.inner ℝ hd hd
  have h1 := hinner.deriv
  have hconst : (fun t => inner ℝ (κ t) (κ t)) = fun _ => (1 : ℝ) := by
    funext t
    rw [real_inner_self_eq_norm_sq, hunit t]
    norm_num
  rw [hconst, deriv_const] at h1
  -- hence `⟪κ θ, deriv κ θ⟫ = 0`: the velocity is perpendicular to the curve
  have horth : inner ℝ (κ θ) (deriv κ θ) = 0 := by
    have hc := real_inner_comm (κ θ) (deriv κ θ)
    linarith
  exact eq_smul_rot90_of_inner_eq_zero (κ θ) (deriv κ θ) horth (by
    rw [real_inner_self_eq_norm_sq, hunit θ]; norm_num)

end Work.Diff.Dim2
