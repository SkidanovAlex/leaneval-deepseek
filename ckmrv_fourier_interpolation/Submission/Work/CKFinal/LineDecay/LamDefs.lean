import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs

/-!
# The complex-`λ` form of the layer and of the shifted representation

The CKMRV identity `F = P₁ + P₂ + P₃` on the lines `Re τ = ±1/2` is derived under the assumption
`λ = π r² > 2π` (which is what makes the tails of the shifted contours vanish).  To reach the
remaining range `λ ≤ 2π` we extend the identity analytically in the *complex* variable `z = λ`:
both sides are holomorphic on `{z : -π < z.re}`, and they agree on the real interval `(2π, ∞)`.

This file only records the objects:

* `lamS z = 2 - e^{iz} - e^{-iz}`, the entire extension of `sinSqC r` at `z = π r²`;
* `psi1C`, the entire extension of `psi1`;
* `highPartC`, the entire extension of `highPart`;
* `lowInt`, `tailInt`, `phiInt`, `horInt1`, `horInt2`, the five parametric integrals;
* `LHSz`, `RHSz`, the two functions of `z` whose values at `z = π r²` are the two sides of the
  identity.
-/

noncomputable section

namespace Work.CKFinal

open UpperHalfPlane MeasureTheory
open scoped Topology Manifold

/-- `λ ↦ 2 - e^{iλ} - e^{-iλ}`, the entire extension of `sinSqC r` along `λ = π r²`. -/
def lamS (z : ℂ) : ℂ := 2 - Complex.exp (Complex.I * z) - Complex.exp (-(Complex.I * z))

/-- The entire extension of `psi1`: `2 ∫_0^1 (1-s) cos(s z) ds`. -/
def psi1C (z : ℂ) : ℂ := 2 * ∫ s in (0 : ℝ)..1, ((1 - s : ℝ) : ℂ) * Complex.cos ((s : ℂ) * z)

/-- The entire extension of `highPart`: the closed form of `sinSqC r ∫_1^∞ Aexp(τ,t)e^{-λt}dt`
with the double zeros at `λ = 0` and `λ = 2π` regularised by `psi1`. -/
def highPartC (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  let m : ℂ := z - (2 * Real.pi : ℂ)
  z * psi1C z * Complex.exp (-z) * G 0 0 τ
    + Complex.I * psi1C z * (z + 1) * Complex.exp (-z) * G 0 1 τ
    + m * psi1C m * Complex.exp (-m) * G 1 0 τ
    + Complex.I * psi1C m * (m + 1) * Complex.exp (-m) * G 1 1 τ

/-- `∫_0^1 K(τ, i t) e^{-z t} dt`. -/
def lowInt (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, Kax K τ 0 t * Complex.exp (-(z * (t : ℂ)))

/-- `∫_1^∞ (K(τ, i t) - Aexp(τ,t)) e^{-z t} dt`. -/
def tailInt (K : UpperHalfPlane → UpperHalfPlane → ℂ)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  ∫ t in Set.Ici (1 : ℝ),
    (Kax K τ 0 t - Work.Asymptotics.Aexp G τ t) * Complex.exp (-(z * (t : ℂ)))

/-- `∫_1^∞ Φ(τ, t) e^{-z t} dt`. -/
def phiInt (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  ∫ t in Set.Ici (1 : ℝ), Phi K τ t * Complex.exp (-(z * (t : ℂ)))

/-- The first horizontal segment of `P₂`, as a function of `z`. -/
def horInt1 (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    Kax K τ (x - 1) hsplit
      * Complex.exp (Complex.I * z * ((x : ℂ) + (hsplit : ℂ) * Complex.I))

/-- The second horizontal segment of `P₂`, as a function of `z`. -/
def horInt2 (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  ∫ x in (-1 : ℝ)..0,
    Kax K τ (x + 1) hsplit
      * Complex.exp (Complex.I * z * ((x : ℂ) + (hsplit : ℂ) * Complex.I))

/-- **The left-hand side of the hatted CKMRV identity (`F̃ = -F₂|^τ_{d/2}S`), as a function of
`z = λ`.**  At `z = π r²` this is `paperLayerK (Khat ℓ d) (Ghat ℓ d) r τ`; it is `LHSz` minus the
Gaussian term. -/
def LHSzHat (K : UpperHalfPlane → UpperHalfPlane → ℂ)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  lamS z * (lowInt K τ z + tailInt K G τ z) + highPartC G τ z

/-- **The left-hand side of the CKMRV identity, as a function of `z = λ`.**
At `z = π r²` this is `gaussTerm τ r + paperLayer (Gcusp ℓ d) ℓ d τ r`. -/
def LHSz (K : UpperHalfPlane → UpperHalfPlane → ℂ)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (τ : ℂ) * z) + LHSzHat K G τ z

/-- `LHSz` is `LHSzHat` plus the Gaussian. -/
lemma LHSz_eq (K : UpperHalfPlane → UpperHalfPlane → ℂ)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) :
    LHSz K G τ z = Complex.exp (Complex.I * (τ : ℂ) * z) + LHSzHat K G τ z := rfl

/-- **The right-hand side of the CKMRV identity, as a function of `z = λ`.**
At `z = π r²` this is `P₁(K) r τ + P₂(K) r τ + P₃(K) r τ`. -/
def RHSz (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  lamS z * lowInt K τ z
    + (-Complex.I * horInt1 K τ z + Complex.I * horInt2 K τ z) + phiInt K τ z

end Work.CKFinal
