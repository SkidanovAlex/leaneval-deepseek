/-
# P9F — definitions for the `F`-method of Heath-Brown §9 (Lemma 9.2)

The real-axis Laplace transform of HB Lemma 7.1's test function (`tf71f` of
`Work.ZeroFreeTables.testFn71_defs`) is an elementary integral: with
`ζ = λ tan θ`, `γ = θ/ζ`, `x₀ = 2γ`, `E = e^{-z x₀}`, `D = z² + ζ²`,

`∫₀^{x₀} e^{-zx} f(x) dx = A·[ A(γ Jc − Kc/2) − Jc + B Js + λ(2γ I4 − I5) − 2 I4 ]`

with `A = λ(1+tan²θ)`, `B = 2 cot θ − cot 2θ = (3+tan²θ)/(2 tan θ)` and the five
elementary integrals `Jc, Js, I4, I5, Kc` below (each evaluated by an explicit
antiderivative; the boundary terms use `ζx₀ = 2θ`).

This file only *defines* the closed form (and its ingredients); the identity is
proved in `Work.ZeroFreeTables.P9F.tf71F_real`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

/-- `B = (3 + tan²θ)/(2 tan θ)` is `2 cot θ − cot 2θ`, the coefficient of
`sin(ζx)` in the closed form of HB Lemma 7.1's test function. -/
def tf71Bcf (θ : ℝ) : ℝ := (3 + Real.tan θ ^ 2) / (2 * Real.tan θ)

/-- `E = e^{-z x₀}` with `x₀ = 2γ` the right end of the support. -/
def tf71Ec (θ lam z : ℝ) : ℝ := Real.exp (-(z * (2 * tf71γ θ lam)))

/-- `D = z² + ζ²` with `ζ = lam · tan θ`. -/
def tf71Dc (θ lam z : ℝ) : ℝ := z ^ 2 + (lam * Real.tan θ) ^ 2

/-- `sin 2θ`, as a rational function of `tan θ`. -/
def tf71s2 (θ : ℝ) : ℝ := 2 * Real.tan θ / (1 + Real.tan θ ^ 2)

/-- `cos 2θ`, as a rational function of `tan θ`. -/
def tf71c2 (θ : ℝ) : ℝ := (1 - Real.tan θ ^ 2) / (1 + Real.tan θ ^ 2)

/-- `∫₀^{x₀} cos(ζx) e^{-zx} dx`. -/
def tf71Jc (θ lam z : ℝ) : ℝ :=
  (tf71Ec θ lam z * (lam * Real.tan θ * tf71s2 θ - z * tf71c2 θ) + z) / tf71Dc θ lam z

/-- `∫₀^{x₀} sin(ζx) e^{-zx} dx`. -/
def tf71Js (θ lam z : ℝ) : ℝ :=
  (-(tf71Ec θ lam z * (z * tf71s2 θ + lam * Real.tan θ * tf71c2 θ)) + lam * Real.tan θ) /
    tf71Dc θ lam z

/-- `∫₀^{x₀} e^{-zx} dx`. -/
def tf71I4 (θ lam z : ℝ) : ℝ := (1 - tf71Ec θ lam z) / z

/-- `∫₀^{x₀} x e^{-zx} dx`. -/
def tf71I5 (θ lam z : ℝ) : ℝ := (1 - tf71Ec θ lam z * (1 + z * (2 * tf71γ θ lam))) / z ^ 2

/-- `∫₀^{x₀} x cos(ζx) e^{-zx} dx`. -/
def tf71Kc (θ lam z : ℝ) : ℝ :=
  (2 * tf71γ θ lam) * (tf71Ec θ lam z * (lam * Real.tan θ * tf71s2 θ - z * tf71c2 θ) /
      tf71Dc θ lam z)
    - (tf71Ec θ lam z * (-(2 * (lam * Real.tan θ) * z * tf71s2 θ) +
          (z ^ 2 - (lam * Real.tan θ) ^ 2) * tf71c2 θ) - (z ^ 2 - (lam * Real.tan θ) ^ 2)) /
        (tf71Dc θ lam z) ^ 2

/-- The closed form of the real-axis Laplace transform of HB Lemma 7.1's test
function: `∫₀^{x₀} e^{-zx} f(x) dx`. -/
def tf71Fr (θ lam z : ℝ) : ℝ :=
  (lam * (1 + Real.tan θ ^ 2)) *
    ((lam * (1 + Real.tan θ ^ 2)) * (tf71γ θ lam * tf71Jc θ lam z - tf71Kc θ lam z / 2)
      - tf71Jc θ lam z + tf71Bcf θ * tf71Js θ lam z
      + lam * (2 * tf71γ θ lam * tf71I4 θ lam z - tf71I5 θ lam z) - 2 * tf71I4 θ lam z)

end Work.ZeroFreeTables

namespace Work.ZeroFreeTables

/-! ## The bilinear coefficients of `tf71Fr`

`tf71Fr θ lam z` is an affine function of `tf71Ec θ lam z` whose coefficients are
rational functions of `θ` (through `tan θ` and `θ` itself); explicitly

`tf71Fr θ lam z = P00 + P10·θ + E·(P01 + P11·θ)`,  `E = tf71Ec θ lam z`,

with the rational functions `P**` below (obtained by expanding the definitions of
`tf71Jc, tf71Js, tf71I4, tf71I5, tf71Kc` in `tf71Fr`). -/

/-- `Jc` at `E = 0`: `z/D`. -/
def tf71Jc0 (θ lam z : ℝ) : ℝ := z / tf71Dc θ lam z
/-- coefficient of `E` in `Jc`: `(ζ sin 2θ − z cos 2θ)/D`. -/
def tf71JcE (θ lam z : ℝ) : ℝ :=
  (lam * Real.tan θ * tf71s2 θ - z * tf71c2 θ) / tf71Dc θ lam z
/-- `Js` at `E = 0`: `ζ/D`. -/
def tf71Js0 (θ lam z : ℝ) : ℝ := lam * Real.tan θ / tf71Dc θ lam z
/-- coefficient of `E` in `Js`. -/
def tf71JsE (θ lam z : ℝ) : ℝ :=
  -(z * tf71s2 θ + lam * Real.tan θ * tf71c2 θ) / tf71Dc θ lam z
/-- coefficient of `θ·E` in `Kc`. -/
def tf71KcTE (θ lam z : ℝ) : ℝ := 2 * tf71JcE θ lam z / (lam * Real.tan θ)
/-- coefficient of `E` in `Kc`. -/
def tf71KcE (θ lam z : ℝ) : ℝ :=
  (2 * (lam * Real.tan θ) * z * tf71s2 θ - (z ^ 2 - (lam * Real.tan θ) ^ 2) * tf71c2 θ) /
    (tf71Dc θ lam z) ^ 2

/-- The constant coefficient of the bilinear form. -/
def tf71P00 (θ lam z : ℝ) : ℝ :=
  (lam * (1 + Real.tan θ ^ 2)) *
    (-(lam * (1 + Real.tan θ ^ 2)) * ((z ^ 2 - (lam * Real.tan θ) ^ 2) /
          (tf71Dc θ lam z) ^ 2) / 2
      - tf71Jc0 θ lam z + tf71Bcf θ * tf71Js0 θ lam z
      - lam / z ^ 2 - 2 / z)

/-- The coefficient of `θ`. -/
def tf71P10 (θ lam z : ℝ) : ℝ :=
  (lam * (1 + Real.tan θ ^ 2)) *
    ((lam * (1 + Real.tan θ ^ 2)) * tf71Jc0 θ lam z / (lam * Real.tan θ) + 2 / z / Real.tan θ)

/-- The coefficient of `E`. -/
def tf71P01 (θ lam z : ℝ) : ℝ :=
  (lam * (1 + Real.tan θ ^ 2)) *
    (-(lam * (1 + Real.tan θ ^ 2)) * tf71KcE θ lam z / 2 - tf71JcE θ lam z
      + tf71Bcf θ * tf71JsE θ lam z - lam * (-(1 / z ^ 2)) - 2 * (-(1 / z)))

/-- The coefficient of `θ·E`. -/
def tf71P11 (θ lam z : ℝ) : ℝ :=
  (lam * (1 + Real.tan θ ^ 2)) *
    ((lam * (1 + Real.tan θ ^ 2)) * tf71JcE θ lam z / (lam * Real.tan θ)
      - (lam * (1 + Real.tan θ ^ 2)) * tf71KcTE θ lam z / 2
      + 2 * (-(1 / z)) / Real.tan θ - lam * (-(2 / (z * (lam * Real.tan θ)))))

end Work.ZeroFreeTables
