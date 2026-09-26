/-
# The hypotheses of CKMRV Theorem 3.1 and the generating functions `F`, `F̃`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) reduce
Fourier interpolation in dimensions `d = 8` and `d = 24` to the existence of two functions
`F, F̃ : ℍ × ℝ^d → ℂ` that are holomorphic in `τ`, radial in `x`, satisfy uniform
growth bounds in the strip `-1 ≤ Re τ ≤ 1`, and satisfy the three functional equations

  `F(τ+2,x) - 2F(τ+1,x) + F(τ,x) = 0`,
  `F̃(τ+2,x) - 2F̃(τ+1,x) + F̃(τ,x) = 0`,
  `F(τ,x) + (i/τ)^{d/2} F̃(-1/τ,x) = e^{πiτ|x|²}`

(Theorem 3.1 of the paper, labelled `thm:FEimpliesIF`).

Since every function here is radial, we identify `x ∈ ℝ^d` with `r = |x| ∈ ℝ` and work with
functions `ℍ → ℝ → ℂ`, as the paper does after fixing a radial variable.

## Main definitions

* `Work.Kernels.SatisfiesThm31 d k₀ F Ftilde` : the hypotheses (1)--(5) of Theorem 3.1, for
  dimension `d` and starting index `k₀`.
* `Work.Kernels.Thm31Conclusion d k₀` : `∃ F Ftilde, SatisfiesThm31 d k₀ F Ftilde`.
* `Work.Kernels.imagAxis`, `Kaxis`, `Fgen`, `Ftgen` : the contour-integral construction
  (5.2) of `F` and `F̃` from a kernel `K` and the "hatted" kernel `K̂ = -K|^τ_{d/2}S`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-! ## The construction of `F` and `F̃` from a kernel -/

/-- The point `it` of the imaginary axis, for `t > 0`. -/
def imagAxis (t : ℝ) (ht : 0 < t) : ℍ := ⟨(t : ℂ) * Complex.I, by simpa using ht⟩

/-- The value `K(τ, it)` of a kernel on the imaginary axis, extended by `0` off `t > 0`.
This is the integrand appearing in (5.2) of the paper. -/
def Kaxis (K : ℍ → ℍ → ℂ) (τ : ℍ) (t : ℝ) : ℂ :=
  if h : 0 < t then K τ (imagAxis t h) else 0

/-- The Gaussian `e^{πiτr²}`. -/
def gaussTerm (τ : ℍ) (r : ℝ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (τ : ℂ) * (r : ℂ) ^ 2)

/-- The kernel transform `4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt` of (5.2). -/
def kernelTransform (K : ℍ → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 *
    ∫ t in Set.Ioi 0, Kaxis K τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))

/-- The generating function `F = F₁ + F₂` of (5.2) of the paper, attached to a kernel `K`. -/
def Fgen (K : ℍ → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  gaussTerm τ r + kernelTransform K τ r

/-- The generating function `F̃` of (5.4) of the paper, attached to the kernel `K̂`. -/
def Ftgen (Khat : ℍ → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ := kernelTransform Khat τ r

/-! ## The hypotheses of Theorem 3.1 -/

/-- The hypotheses (1)--(5) of CKMRV Theorem 3.1 for the pair `(F, F̃)`, in dimension `d`
with starting index `k₀`.  The functions `F, F̃ : ℍ → ℝ → ℂ` encode the radial functions of
`τ` and `r = |x|`. -/
def SatisfiesThm31 (d k₀ : ℕ) (F Ft : ℍ → ℝ → ℂ) : Prop :=
  -- (1) holomorphic in `τ`
  (∀ r : ℝ, MDiff (fun τ : ℍ => F τ r)) ∧
  (∀ r : ℝ, MDiff (fun τ : ℍ => Ft τ r)) ∧
  -- (3) radial-derivative growth bounds, uniform in `r` and polynomial in `τ`
  (∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
    ∀ (τ : ℍ) (r : ℝ),
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => F τ s) r‖
        ≤ α * (τ.im) ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ) ∧
  (∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
    ∀ (τ : ℍ) (r : ℝ),
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Ft τ s) r‖
        ≤ α * (τ.im) ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ) ∧
  -- (4) uniform bound in the strip `-1 ≤ Re τ ≤ 1`
  (∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧
    ∀ (τ : ℍ) (r : ℝ), -1 ≤ τ.re → τ.re ≤ 1 →
      max ‖F τ r‖ ‖Ft τ r‖ ≤ α * (τ.im) ^ (-β)) ∧
  -- (5) the three functional equations
  (∀ (τ : ℍ) (r : ℝ),
    F ((2 : ℝ) +ᵥ τ) r - 2 * F ((1 : ℝ) +ᵥ τ) r + F τ r = 0) ∧
  (∀ (τ : ℍ) (r : ℝ),
    Ft ((2 : ℝ) +ᵥ τ) r - 2 * Ft ((1 : ℝ) +ᵥ τ) r + Ft τ r = 0) ∧
  (∀ (τ : ℍ) (r : ℝ),
    F τ r + (Complex.I / (τ : ℂ)) ^ (d / 2) * Ft (ModularGroup.S • τ) r
      = gaussTerm τ r)

/-- The conclusion of CKMRV Theorem 3.1: there exist `F`, `F̃` satisfying its hypotheses. -/
def Thm31Conclusion (d k₀ : ℕ) : Prop := ∃ F Ft : ℍ → ℝ → ℂ, SatisfiesThm31 d k₀ F Ft

/-- The construction discharges the conclusion of Theorem 3.1 as soon as the constructed
functions `F = Fgen K`, `F̃ = Ftgen K̂` satisfy the stated hypotheses. -/
theorem thm31Conclusion_of_constructed {d k₀ : ℕ} {K Khat : ℍ → ℍ → ℂ}
    (h : SatisfiesThm31 d k₀ (Fgen K) (Ftgen Khat)) : Thm31Conclusion d k₀ :=
  ⟨Fgen K, Ftgen Khat, h⟩

/-- The two relations between the kernels `K`, `K_±`, `K̂` used in Section 5:
`K = (K_+ + K_-)/2` and `K̂ = -K|^τ_{d/2}S`. -/
theorem Kfun_eq (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) :
    Kfun ℓ d τ z = (KPlus d τ z + KMinus ℓ d τ z) / 2 := rfl

theorem Khat_eq (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) :
    Khat ℓ d τ z = (KPlus d τ z - KMinus ℓ d τ z) / 2 := rfl

end Work.Kernels
