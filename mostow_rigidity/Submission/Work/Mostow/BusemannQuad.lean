import Mathlib
import Submission.Work.Mostow.BaryBase

/-!
# The Busemann quadrangle inequality (Lorentz-form proof)

For `ξ ∈ Sph n` (a point of the boundary sphere) and `u v : E n` we prove

`(tpart u - ⟪u,ξ⟫)² + (tpart v - ⟪v,ξ⟫)²
   - 2 (tpart u * tpart v - ⟪u,v⟫) (tpart u - ⟪u,ξ⟫) (tpart v - ⟪v,ξ⟫) ≤ 0`.

Since `tpart w - ⟪w,ξ⟫ = exp (busemann ξ w)`, this is exactly
`cosh (B_ξ u - B_ξ v) ≤ cosh (hdist u v)`, i.e. the statement that the Busemann function is
1-Lipschitz, in the polynomial form used by the barycentre argument (`BaryProp`).

## Proof

Work in the Lorentz space `E n × ℝ` with the form `B((x,s),(y,t)) = s * t - ⟪x,y⟫` and
`Q(z) = B(z,z)`. Put `X = (u, tpart u)`, `Y = (v, tpart v)` and `N = (ξ, 1)`, so that
`Q X = Q Y = 1`, `Q N = ‖ξ‖² - 1 = 0` and

* `a := B(X,N) = tpart u - ⟪u,ξ⟫`,
* `b := B(Y,N) = tpart v - ⟪v,ξ⟫`,
* `B(X,Y) = tpart u * tpart v - ⟪u,v⟫`.

The quantity in the statement is

`Q (b • X - a • Y) = b² Q X - 2 a b B(X,Y) + a² Q Y
   = (tpart u - ⟪u,ξ⟫)² + (tpart v - ⟪v,ξ⟫)² - 2 (tpart u * tpart v - ⟪u,v⟫) (tpart u - ⟪u,ξ⟫) (tpart v - ⟪v,ξ⟫)`,

and `B (b • X - a • Y) N = b * a - a * b = 0`, so `b • X - a • Y` lies in the null hyperplane
`N^⊥ = {(x,s) : s = ⟪x,ξ⟫}`. On that hyperplane `Q` is nonpositive: for `z = (x, ⟪x,ξ⟫)` one has
`Q z = ⟪x,ξ⟫² - ‖x‖² ≤ 0` by Cauchy–Schwarz and `‖ξ‖ = 1`. Hence the quantity is `≤ 0`.

In coordinates this says: writing `w := b • u - a • v`, the time coordinate of `b • X - a • Y` is
`b * tpart u - a * tpart v = ⟪w,ξ⟫`, so the quantity equals `⟪w,ξ⟫² - ‖w‖² ≤ 0`.
-/

namespace Work.Mostow

open Submission.Mostow
open scoped Real

variable {n : ℕ}

/-- Expansion of the squared norm of a difference of two multiples of vectors. -/
lemma norm_sq_smul_sub (a b : ℝ) (u v : E n) :
    ‖b • u - a • v‖ ^ 2 = b ^ 2 * ‖u‖ ^ 2 - 2 * (b * a) * inner ℝ u v + a ^ 2 * ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm v u]
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  ring_nf
  rw [sq_abs, sq_abs]
  ring

theorem BusemannQuad (n : ℕ) (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (u v : Submission.Mostow.E n) :
    (Submission.Mostow.tpart u - inner ℝ u ξ) ^ 2 + (Submission.Mostow.tpart v - inner ℝ v ξ) ^ 2
      - 2 * (Submission.Mostow.tpart u * Submission.Mostow.tpart v - inner ℝ u v) * (Submission.Mostow.tpart u - inner ℝ u ξ)
          * (Submission.Mostow.tpart v - inner ℝ v ξ) ≤ 0 := by
  have hξ1 : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  -- replace the three recurring quantities by atoms
  set a : ℝ := tpart u - inner ℝ u ξ with ha
  set b : ℝ := tpart v - inner ℝ v ξ with hb
  set w : E n := b • u - a • v with hw
  -- the Lorentz pairing of `b • X - a • Y` with the null vector `N = (ξ,1)` vanishes, and the
  -- "time" coordinate of `b • X - a • Y` is `⟪w, ξ⟫`
  have hwξ : inner ℝ w ξ = b * tpart u - a * tpart v := by
    rw [hw]
    simp only [inner_sub_left, real_inner_smul_left]
    ring
  have hnorm : ‖w‖ ^ 2 = b ^ 2 * ‖u‖ ^ 2 - 2 * (b * a) * inner ℝ u v + a ^ 2 * ‖v‖ ^ 2 := by
    rw [hw]
    exact norm_sq_smul_sub a b u v
  have hidentity : a ^ 2 + b ^ 2 - 2 * (tpart u * tpart v - inner ℝ u v) * a * b
      = (inner ℝ w ξ) ^ 2 - ‖w‖ ^ 2 := by
    rw [hwξ, hnorm]
    nlinarith [tpart_sq u, tpart_sq v]
  -- `Q (b • X - a • Y) = ⟪w,ξ⟫² - ‖w‖² ≤ 0` by Cauchy–Schwarz and `‖ξ‖ = 1`
  have hCS : (inner ℝ w ξ) ^ 2 ≤ ‖w‖ ^ 2 := by
    have h := abs_real_inner_le_norm w ξ
    rw [hξ1, mul_one] at h
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg w)]
    exact h
  linarith [hidentity, hCS]

end Work.Mostow
