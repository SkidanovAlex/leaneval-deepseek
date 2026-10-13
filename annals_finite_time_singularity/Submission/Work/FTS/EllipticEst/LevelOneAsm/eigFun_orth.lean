/-
Copyright: work module for the Elgindi finite-time singularity project.

# Orthogonality of the angular eigenfunctions `Θ_n` for the weight `cos θ dθ`

`Work.FTS.EllipticEst.LevelOneAsm.eigFun_orth`:

  `∫_{Iθ} Θ_n(θ) · Θ_m(θ) · cos θ dθ = 0`  for `n ≠ m`,

with `Θ_n(θ) = cos θ · p_n(sin θ)` the angular eigenfunctions of `EigBasis`.

This is the orthogonality of the eigenbasis of the angular operator `L₀` in the
self-adjointness weight `ρ(θ) = cos³θ` (the one for which `M v = -v'' + 3 tanθ·v' - 4v` on
`v(θ) = p(sin θ)` is self-adjoint): since `Θ_n Θ_m cos θ = cos³θ · p_n(sinθ) p_m(sinθ)`,
the statement is `∫₀^{π/2} ρ v_n v_m dθ = 0`.

## The proof, in the `u = sin θ` variable

Substituting `u = sin θ` (`du = cos θ dθ`, `ρ = 1 - u²`) the identity becomes the
polynomial statement

  `∫₀¹ (1 - u²) p_n(u) p_m(u) du = 0`  for `n ≠ m`   `(∗)`.

The eigenpolynomials satisfy the Jacobi equation (proved in `eigFun_moment` as `eigMom_ode`)

  `(1 - u²) p_n''(u) - 4u p_n'(u) + (4 + λ_n) p_n(u) = 0`

with `λ_n = 4(n-1)² + 10(n-1)` (the sequence `λ_n` is injective on `n ≥ 1`).  Writing

  `F_n(u) := (1 - u²)² p_n'(u)`

the Jacobi equation is exactly the statement `F_n'(u) = -(λ_n + 4)(1 - u²) p_n(u)`, so an
integration by parts against `p_m` (the boundary terms vanish because `F_n(1) = 0` and
`p_m(0) = 0`) gives

  `∫₀¹ (1-u²)² p_n' p_m' = (λ_n + 4) ∫₀¹ (1-u²) p_n p_m .`

The left-hand side is symmetric in `n` and `m`, so the same identity with `n`, `m` exchanged
yields `(λ_n - λ_m) ∫₀¹ (1-u²) p_n p_m = 0`, and `(∗)` follows because `λ_n ≠ λ_m` for
`n ≠ m`, `n, m ≥ 1`.  The degenerate cases `n = 0` or `m = 0` are trivial since
`p_0 = 0`.
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigBasis
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_moment
import Submission.Work.FTS.EllipticEst.LevelOneAsm.subst_cos_cube_sin
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigLam_ne_of_ne

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

/-- The primitive used for the integration by parts: `F_n(u) = (1 - u²)² p_n'(u)`. -/
def eigOrthF (n : ℕ) : ℝ → ℝ := fun u => (1 - u ^ 2) * ((1 - u ^ 2) * eigMomD n u)

/-- `deriv (1 - u²) = -2u`. -/
lemma hasDerivAt_one_sub_sq (u : ℝ) :
    HasDerivAt (fun u : ℝ => (1 : ℝ) - u ^ 2) (-(2 * u)) u := by
  have h := (hasDerivAt_pow 2 u).const_sub (1 : ℝ)
  simpa using h

/-- `(1 - u²) p_n'` has derivative `-2u p_n' + (1 - u²) p_n''`. -/
lemma hasDerivAt_eigOrthInner (n : ℕ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => (1 - u ^ 2) * eigMomD n u)
      (-(2 * u) * eigMomD n u + (1 - u ^ 2) * eigMomD2 n u) u :=
  (hasDerivAt_one_sub_sq u).mul (hasDerivAt_eigMomD n u)

/-- **The key derivative identity**: the Jacobi equation `eigMom_ode` says exactly that the
derivative of `F_n(u) = (1-u²)² p_n'(u)` is `-(λ_n + 4)(1-u²) p_n(u)`. -/
lemma hasDerivAt_eigOrthF (n : ℕ) (u : ℝ) :
    HasDerivAt (eigOrthF n) (-(eigLam n + 4) * (1 - u ^ 2) * eigPoly n u) u := by
  have hm := (hasDerivAt_one_sub_sq u).mul (hasDerivAt_eigOrthInner n u)
  refine hm.congr_deriv ?_
  have hode := eigMom_ode n u
  linear_combination (1 - u ^ 2) * hode

/-- The integration by parts, in the form
`∫₀¹ F_n p_m' = (λ_n + 4) ∫₀¹ (1-u²) p_n p_m`. -/
lemma integral_eigOrthF (n m : ℕ) :
    ∫ u in (0 : ℝ)..1, eigOrthF n u * eigMomD m u
      = (eigLam n + 4) * ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * (eigPoly n u * eigPoly m u) := by
  have hcontD : Continuous (eigMomD m) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_eigMomD m u).continuousAt
  have hcontP : Continuous (eigPoly n) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_eigMom n u).continuousAt
  have hcontPm : Continuous (eigPoly m) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_eigMom m u).continuousAt
  have hcont1 : Continuous (fun x : ℝ => (1 : ℝ) - x ^ 2) :=
    continuous_const.sub (continuous_id.pow 2)
  have hcont2 : Continuous (fun x : ℝ => -(eigLam n + 4) * (1 - x ^ 2)) :=
    continuous_const.mul hcont1
  have hcont3 : Continuous (fun x : ℝ => -(eigLam n + 4) * (1 - x ^ 2) * eigPoly n x) :=
    hcont2.mul hcontP
  have hI : IntervalIntegrable (fun x : ℝ => -(eigLam n + 4) * (1 - x ^ 2) * eigPoly n x)
      volume 0 1 := hcont3.intervalIntegrable 0 1
  have hI2 : IntervalIntegrable (eigMomD m) volume 0 1 := hcontD.intervalIntegrable 0 1
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := eigOrthF n) (u' := fun x : ℝ => -(eigLam n + 4) * (1 - x ^ 2) * eigPoly n x)
    (v := eigPoly m) (v' := eigMomD m) (a := 0) (b := 1)
    (fun x _ => hasDerivAt_eigOrthF n x) (fun x _ => hasDerivAt_eigMom m x) hI hI2
  rw [h]
  have hbd : eigOrthF n 1 * eigPoly m 1 - eigOrthF n 0 * eigPoly m 0 = 0 := by
    rw [eigOrthF, eigMomPoly_zero]
    norm_num
  rw [hbd, zero_sub]
  have hcongr : (∫ x in (0 : ℝ)..1, (-(eigLam n + 4) * (1 - x ^ 2) * eigPoly n x) * eigPoly m x)
      = -(eigLam n + 4)
          * ∫ x in (0 : ℝ)..1, (1 - x ^ 2) * (eigPoly n x * eigPoly m x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hcongr]
  ring

/-- The polynomial orthogonality `∫₀¹ (1-u²) p_n p_m = 0` for `n ≠ m`. -/
lemma eigPoly_u_orth (n m : ℕ) (h : n ≠ m) :
    ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * (eigPoly n u * eigPoly m u) = 0 := by
  rcases eq_or_ne n 0 with hn0 | hn0
  · subst hn0
    have hz : (fun u : ℝ => (1 - u ^ 2) * (eigPoly 0 u * eigPoly m u)) = fun _ => (0 : ℝ) := by
      funext u
      simp [eigPoly]
    rw [hz]
    simp
  rcases eq_or_ne m 0 with hm0 | hm0
  · subst hm0
    have hz : (fun u : ℝ => (1 - u ^ 2) * (eigPoly n u * eigPoly 0 u)) = fun _ => (0 : ℝ) := by
      funext u
      simp [eigPoly]
    rw [hz]
    simp
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hlam : eigLam n ≠ eigLam m := eigLam_ne_of_ne hn1 hm1 h
  have hnm := integral_eigOrthF n m
  have hmn := integral_eigOrthF m n
  have hsym : (∫ x in (0 : ℝ)..1, eigOrthF n x * eigMomD m x)
      = ∫ x in (0 : ℝ)..1, eigOrthF m x * eigMomD n x := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [eigOrthF]
    ring
  rw [hsym] at hnm
  have hmn' : (∫ x in (0 : ℝ)..1, eigOrthF m x * eigMomD n x)
      = (eigLam m + 4)
          * ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * (eigPoly n u * eigPoly m u) := by
    rw [hmn]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have heq : (eigLam n + 4) * (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * (eigPoly n u * eigPoly m u))
      = (eigLam m + 4)
          * ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * (eigPoly n u * eigPoly m u) := by
    rw [← hnm, hmn']
  have hzero : (eigLam n - eigLam m)
      * ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * (eigPoly n u * eigPoly m u) = 0 := by
    rw [sub_mul]
    linarith [heq]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hlam)

theorem eigFun_orth (n m : ℕ) (h : n ≠ m) :
    ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.LevelOneAsm.eigFun n θ *
        Work.FTS.EllipticEst.LevelOneAsm.eigFun m θ * Real.cos θ = 0 := by
  have hc1 : Continuous (eigPoly n) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_eigMom n u).continuousAt
  have hc2 : Continuous (eigPoly m) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_eigMom m u).continuousAt
  have hcont : Continuous (fun u : ℝ => eigPoly n u * eigPoly m u) := hc1.mul hc2
  have hcongr : (∫ θ in Work.Spaces.Iθ, eigFun n θ * eigFun m θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, Real.cos θ ^ 3 *
          ((fun u : ℝ => eigPoly n u * eigPoly m u) (Real.sin θ)) := by
    apply integral_congr_ae
    filter_upwards with θ
    simp only [eigFun]
    ring
  rw [hcongr, subst_cos_cube_sin (fun u : ℝ => eigPoly n u * eigPoly m u) hcont]
  exact eigPoly_u_orth n m h

end Work.FTS.EllipticEst.LevelOneAsm
