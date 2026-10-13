/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EigBasis`: the angular eigenbasis of `L₀`, and the spectral-gap mechanism for `ASlotOne`

The level-`1` `A`-slot `α²√(Tk α 1 (z²∂_z²Ψ))` is bounded by `C|F|_{ℋ¹}` only because the
*angular* eigenvalue `λ_n` of `Lzero` — which the equation produces as
`F = λ_n a_n - α²z²a_n'' - α(5+α)za_n'` on each `θ`-mode — supplies room.  Every triangle
inequality destroys that room (see `NOTES_ASlotOne.md` §2–§4), so the estimate has to be read
mode by mode, and the modes are the eigenfunctions of `Lzero`:

* in the basis `u = cos θ · v` the operator becomes `M v = -v'' + 3 tan θ · v' - 4 v`, which is
  self-adjoint w.r.t. the weight `ρ = cos³θ`, has `⟨Mv,v⟩_ρ = ∫((v')² - 4v²)cos³θ`, and has
  kernel spanned by `v = sin θ` (i.e. by `sin 2θ` in the `Θ`-picture);
* consequently the moment condition of the weak class, `Fstar Ψ z = ∫Ψ(z,θ)sinθcos²θ dθ = 0`,
  is exactly `v(z,·) ⊥ sin θ` in `L²(cos³θ dθ)` — the condition that removes the kernel;
* the eigenfunctions are explicit polynomials,
  `Θ_n(θ) = cos θ · p_n(sin θ)`, `p_n(u) = Σ_{k<n} c_k u^{2k+1}`,
  `c_{k+1}/c_k = (4k²+10k-λ_n)/((2k+3)(2k+2))`, `c_0 = 1`, `λ_n = 4(n-1)²+10(n-1)`
  (`λ_1 = 0` kernel mode, `λ_2 = 14`, `λ_3 = 36`, …), all of them vanishing at `θ = 0, π/2`
  and, for `n ≥ 2`, orthogonal to the moment profile `sinθcos²θ`.

The orthogonality statement has to be stated with the right weight: the natural form of the
eigenvalue problem is `∫ v_n v_m cos³θ dθ = 0` for the `v`-functions (`ρ = cos³θ` is the
self-adjointness weight of `M`), which for `Θ_n = cos θ · v_n` becomes
`∫ Θ_n Θ_m cos θ dθ = 0` (`n ≠ m`); the moment condition is
`∫ Θ_n sin θ cos²θ dθ = 0` for `n ≥ 2`, i.e. `∫ v_n sin θ cos³θ dθ = 0`.

This module only fixes the vocabulary (the coefficients, the eigenvalue, the eigenfunctions);
the identities about them (`Lzero (Θ_n) = λ_n Θ_n`, orthogonality for the weight `cos³θ`, and the
vanishing of the moment for `n ≥ 2`) are separate lemmas.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

set_option autoImplicit false

/-- `λ_n = 4(n-1)² + 10(n-1)`, the `n`-th eigenvalue of the angular operator (in `ℕ`, cast to `ℝ`). -/
def eigLamNat (n : ℕ) : ℕ := 4 * (n - 1) ^ 2 + 10 * (n - 1)

/-- The eigenvalue `λ_n` as a real number. -/
def eigLam (n : ℕ) : ℝ := (eigLamNat n : ℝ)

/-- The coefficients of the eigenpolynomial: `c_{k+1}/c_k = (4k²+10k-λ_n)/((2k+3)(2k+2))`,
`c_0 = 1`. -/
def eigCoef (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => eigCoef n k * ((4 * (k : ℝ) ^ 2 + 10 * (k : ℝ) - eigLam n)
      / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2)))

@[simp] theorem eigCoef_zero (n : ℕ) : eigCoef n 0 = 1 := rfl

/-- `p_n(u) = Σ_{k<n} c_k u^{2k+1}`. -/
def eigPoly (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, eigCoef n k * u ^ (2 * k + 1)

/-- The `n`-th angular eigenfunction `Θ_n(θ) = cos θ · p_n(sin θ)`. -/
def eigFun (n : ℕ) (θ : ℝ) : ℝ := Real.cos θ * eigPoly n (Real.sin θ)

@[simp] theorem eigLam_one : eigLam 1 = 0 := by
  simp [eigLam, eigLamNat]

theorem eigLam_two : eigLam 2 = 14 := by
  norm_num [eigLam, eigLamNat]

theorem eigLam_three : eigLam 3 = 36 := by
  norm_num [eigLam, eigLamNat]

theorem eigLam_four : eigLam 4 = 66 := by
  norm_num [eigLam, eigLamNat]

/-- The kernel mode: `Θ_1 = sin θ cos θ = sin 2θ / 2`. -/
theorem eigFun_one (θ : ℝ) : eigFun 1 θ = Real.sin θ * Real.cos θ := by
  simp only [eigFun, eigPoly, Finset.range_one, Finset.sum_singleton, eigCoef_zero, one_mul]
  ring

/-- `Θ_1` is the kernel profile: `sin 2θ = 2 cos θ sin θ`. -/
theorem eigFun_one_eq_sin_two (θ : ℝ) :
    eigFun 1 θ = Real.sin (2 * θ) / 2 := by
  rw [eigFun_one, Real.sin_two_mul]
  ring

/-- The second eigenpolynomial explicitly: `p_2(u) = u - (7/3)u³`. -/
theorem eigPoly_two (u : ℝ) : eigPoly 2 u = u - (7 / 3) * u ^ 3 := by
  rw [eigPoly, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [eigCoef, eigLam, eigLamNat]
  ring

/-- The second eigenfunction explicitly: `Θ_2 = cos θ (sin θ - (7/3) sin³θ)`. -/
theorem eigFun_two (θ : ℝ) :
    eigFun 2 θ = Real.cos θ * (Real.sin θ - (7 / 3) * Real.sin θ ^ 3) := by
  rw [eigFun, eigPoly_two]

end Work.FTS.EllipticEst.LevelOneAsm
