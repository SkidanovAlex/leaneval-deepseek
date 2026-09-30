import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- Zero-order transfer across the functional equation for the completed Dirichlet L-function.

For a **primitive** non-trivial character `χ`, the functional equation
`Λ(χ)(s) = N^(1/2-s) · ε(χ) · Λ(χ⁻¹)(1-s)` (`Commons.NumberTheory.DirichletCharacter.completedLFunction_eq`)
shows that the zeros of `Λ(χ, ·)` are in bijection with those of `Λ(χ⁻¹, ·)` through
`s ↦ 1-s`, with equal multiplicities.  The prefactor is analytic and nowhere zero
(`(N : ℂ) ^ z ≠ 0` since `N ≠ 0`, and `|χ.rootNumber| = 1` by
`Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one`).

Concretely: if `u` is a zero of `Λ(χ, ·)` then the (finite) meromorphic orders satisfy

    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) u =
      meromorphicOrderAt (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - u)

(equality in `WithTop ℤ`; both sides are non-negative finite integers because both
functions are entire and vanish there).

Proof route: `u` is a zero, so (e.g. from `Commons.NumberTheory.DirichletCharacter.zerosInStrip`)
`0 < u.re ∧ u.re < 1`.  Use the order-at-a-point API of `meromorphicOrderAt` /
`analyticOrderAt` (Mathlib `Analysis.Analytic.Meromorphic`, `Analysis.Complex.AnalyticOrderAt`):
write the functional equation as an equality of two entire functions
`Λ(χ)(s) = c(s) · (Λ(χ⁻¹) ∘ (fun s => 1 - s))(s)` with `c` analytic and nonzero on a
neighbourhood of `u`; then `meromorphicOrderAt` of a product is the sum of the orders
(`meromorphicOrderAt_mul`-type lemma), the order of a nowhere-vanishing analytic `c` is `0`,
and composing with the affine map `s ↦ 1-s` (derivative `-1 ≠ 0`) preserves the order
(`meromorphicOrderAt` under local biholomorphism / direct `(z - w)^n` factorisation).
You may state and prove as intermediate lemmas whatever variants you need; they may go in
this same module (they are generic complex analysis). -/
theorem completedL_order_eq_one_sub {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {u : ℂ}
    (hu : DirichletCharacter.completedLFunction χ u = 0) :
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) u =
      meromorphicOrderAt (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - u) := by
  let a : ℂ → ℂ := fun s => (N : ℂ) ^ ((1 / 2 : ℂ) - s) * χ.rootNumber
  let φ : ℂ → ℂ := fun s => 1 - s
  let Λi : ℂ → ℂ := fun s => DirichletCharacter.completedLFunction (χ⁻¹) s
  -- functional equation as an equality of functions
  have hFE : DirichletCharacter.completedLFunction χ = a * (Λi ∘ φ) := by
    funext s
    simpa [a, φ, Λi] using completedLFunction_eq χ hχprim s
  -- the prefactor is analytic at `u`
  have hNslit : (N : ℂ) ∈ slitPlane := (natCast_mem_slitPlane (n := N)).2 (NeZero.ne N)
  have ha_an : AnalyticAt ℂ a u := by
    dsimp [a]
    fun_prop (disch := exact hNslit)
  -- ... and nowhere zero at `u`
  have ha_ne : a u ≠ 0 := by
    dsimp [a]
    have hA : (N : ℂ) ^ ((1 / 2 : ℂ) - u) ≠ 0 := by
      rw [cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast (NeZero.ne N : N ≠ 0))
    have hB : χ.rootNumber ≠ 0 := by
      intro h
      have hnorm : ‖χ.rootNumber‖ = 1 := rootNumber_norm_eq_one χ hχprim
      rw [h] at hnorm
      norm_num at hnorm
    exact mul_ne_zero hA hB
  -- the reflection map `φ : s ↦ 1 - s` is a local biholomorphism at `u`
  have hφ_an : AnalyticAt ℂ φ u := by
    dsimp [φ]
    fun_prop
  have hφ'_ne : deriv φ u ≠ 0 := by
    dsimp [φ]
    simp
  -- order is preserved under multiplying by the nowhere-zero analytic prefactor
  have hprod : meromorphicOrderAt (a * (Λi ∘ φ)) u = meromorphicOrderAt (Λi ∘ φ) u :=
    meromorphicOrderAt_mul_of_ne_zero (f := Λi ∘ φ) (g := a) (x := u) ha_an ha_ne
  -- order is preserved under composing with the affine reflection
  have hcomp : meromorphicOrderAt (Λi ∘ φ) u = meromorphicOrderAt Λi (φ u) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero (f := Λi) (g := φ) (x := u) hφ_an hφ'_ne
  calc
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) u
        = meromorphicOrderAt (a * (Λi ∘ φ)) u := by rw [hFE]
    _ = meromorphicOrderAt (Λi ∘ φ) u := hprod
    _ = meromorphicOrderAt Λi (φ u) := hcomp
    _ = meromorphicOrderAt (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - u) := by
        dsimp [Λi, φ]

end Commons.NumberTheory.DirichletCharacter