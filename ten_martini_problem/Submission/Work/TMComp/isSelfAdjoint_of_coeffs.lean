/-
# Self-adjointness of a Jacobi operator with real coefficients (`P_OpBasics`, C1)

An operator `H` on `ℓ²(ℤ)` given by the shift-plus-diagonal coordinate formula

`(H u) n = u (n+1) + u (n-1) + c n * u n`

is self-adjoint as soon as the coefficient sequence `c` is real-valued: the two shifts are
adjoints of one another and the diagonal part `c n * u n` is real.

The proof evaluates the adjoint on the standard basis `e_n = lp.single 2 n 1` of `ℓ²(ℤ)`:
the fundamental property of the adjoint gives

`(H† u) n = ⟪e_n, H† u⟫ = ⟪H e_n, u⟫`,

and the coordinate formula for `H` shows `H e_n = e_{n-1} + e_{n+1} + c n • e_n` ("the sum of the
two neighbouring basis vectors and the diagonal contribution").  Taking inner products with `u`
yields exactly the same coordinate formula for `H† u` as for `H u`, hence `H† = H`.
-/
import Mathlib
import Submission.Work.TMComp.Defs

open scoped ComplexInnerProductSpace

namespace Work.TMComp

open LeanEval.Analysis.TenMartini

/-- The shift `u ↦ u(· + 1)` sends the basis vector `e_n` to `e_{n-1}`. -/
private lemma single_shift_add_one (n m : ℤ) :
    (lp.single 2 n (1 : ℂ) : EllTwo) (m + 1) = (lp.single 2 (n - 1) (1 : ℂ) : EllTwo) m := by
  by_cases hm : m = n - 1
  · subst hm
    simp
  · have h2 : m + 1 ≠ n := by omega
    simp [lp.single_apply, hm, h2]

/-- The shift `u ↦ u(· - 1)` sends the basis vector `e_n` to `e_{n+1}`. -/
private lemma single_shift_sub_one (n m : ℤ) :
    (lp.single 2 n (1 : ℂ) : EllTwo) (m - 1) = (lp.single 2 (n + 1) (1 : ℂ) : EllTwo) m := by
  by_cases hm : m = n + 1
  · subst hm
    simp
  · have h2 : m - 1 ≠ n := by omega
    simp [lp.single_apply, hm, h2]

/-- The diagonal part `u ↦ (c m * u m)_m` sends the basis vector `e_n` to `c n • e_n`. -/
private lemma single_diag (c : ℤ → ℂ) (n m : ℤ) :
    c m * (lp.single 2 n (1 : ℂ) : EllTwo) m = (lp.single 2 n (c n) : EllTwo) m := by
  by_cases hm : m = n
  · subst hm
    simp
  · simp [lp.single_apply, hm]

/-- Testing the coordinate identity on the basis vectors: a Jacobi operator sends the basis
vector `e_n` to `e_{n-1} + e_{n+1} + c n • e_n`. -/
private lemma jacobiOp_apply_single {c : ℤ → ℂ} {H : EllTwo →L[ℂ] EllTwo}
    (h : IsJacobiOp c H) (n : ℤ) :
    H (lp.single 2 n (1 : ℂ)) =
      lp.single 2 (n - 1) (1 : ℂ) + lp.single 2 (n + 1) (1 : ℂ) + lp.single 2 n (c n) := by
  apply lp.ext
  funext m
  rw [h (lp.single 2 n (1 : ℂ)) m]
  simp only [lp.coeFn_add, Pi.add_apply]
  rw [single_shift_add_one n m, single_shift_sub_one n m, single_diag c n m]

theorem isSelfAdjoint_of_coeffs {c : ℤ → ℂ} (hc : ∀ n, ∃ r : ℝ, c n = (r : ℂ))
    {H : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo}
    (h : Work.TMComp.IsJacobiOp c H) : IsSelfAdjoint H := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext n
  -- `(H† u) n = ⟪e_n, H† u⟫ = ⟪H e_n, u⟫`, then use the coordinate formula for `H e_n`.
  have hstep : (H.adjoint u) n = ⟪H (lp.single 2 n (1 : ℂ)), u⟫ := by
    rw [← ContinuousLinearMap.adjoint_inner_right H (lp.single 2 n (1 : ℂ)) u]
    rw [lp.inner_single_left]
    simp
  rw [h u n, hstep, jacobiOp_apply_single h n,
    inner_add_left, inner_add_left, lp.inner_single_left, lp.inner_single_left,
    lp.inner_single_left]
  obtain ⟨r, hr⟩ := hc n
  rw [hr]
  simp only [RCLike.inner_apply, Complex.conj_ofReal, map_one]
  ring

end Work.TMComp
