import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.CDT.SympDescent
import Submission.CDT.RatFuncDeriv

/-!
# A14 — definitions for the `x`-side route to Lemma `14functions` (`Fourteen`)

Definitions of the lead's design `REFS/design/a14/A14_design.lean.txt` (namespace `Work.A14D`),
self-contained: the analytic functions `Hfun` (the `x`-side series `H = aH_A+bH_B+cH_C`), the
Zagier operator `LZ` (self-adjoint `(P y')' + R y`, `P = x(1−x)(1−9x)`) and its `w`-conjugate `LZw`,
the half-planes `SU`, `SL` and the slit plane `Om1`, the log-coefficient functional `LogCoeff`,
the holomorphic solution data `Y9`, and the `x`-side `ℚ(x)`-module data `dZ`, `clsZ` for the
algebraic endgame.
-/

open Complex Metric Filter Polynomial
open scoped Topology BigOperators

noncomputable section
namespace Work.A14D

/-! ## 0. Zagier's operator, the sets, the functions -/

/-- `P = z(1−z)(1−9z)` (the `H''`-coefficient of `HA_odeLHS`). -/
def PZ (z : ℂ) : ℂ := z * (1 - z) * (1 - 9 * z)

/-- `P' = 1 − 20z + 27z²`. -/
def PZ' (z : ℂ) : ℂ := 1 - 20 * z + 27 * z ^ 2

/-- `R = 9z − 3`. -/
def RZ (z : ℂ) : ℂ := 9 * z - 3

/-- The self-adjoint form `L y = (P y')' + R y`. -/
def LZ (f : ℂ → ℂ) (z : ℂ) : ℂ := PZ z * deriv (deriv f) z + PZ' z * deriv f z + RZ z * f z

/-- The inhomogeneity `b + c/(1−x)`. -/
def rhsZ (b c : ℤ) (z : ℂ) : ℂ := (b : ℂ) + (c : ℂ) / (1 - z)

/-- `L^w`, the operator annihilating `f ∘ w`, `w = z/(z−1)` (singular at `0, −1/8, 1`). -/
def LZw (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (z - 1) ^ 2 * (8 * z + 1) * deriv (deriv f) z
    + (z - 1) * (8 * z ^ 2 - 16 * z - 1) * deriv f z + 3 * (2 * z + 1) * f z

/-- `H(x) = aH_A(x) + bH_B(x) + cH_C(x)` as a function of a complex variable. -/
def Hfun (a b c : ℤ) (z : ℂ) : ℂ :=
  ∑' n, ((PowerSeries.coeff n (Submission.CDTPlan.HZ a b c) : ℚ) : ℂ) * z ^ n

/-- The deck involution `w(z) = z/(z−1)`. -/
def wC (z : ℂ) : ℂ := z / (z - 1)

/-- `y(z) = z²/(z−1)`. -/
def yC (z : ℂ) : ℂ := z ^ 2 / (z - 1)

/-- `∂_y = y'^{-1} d/dz`. -/
def Dy (f : ℂ → ℂ) : ℂ → ℂ := fun z => deriv f z * (z - 1) ^ 2 / (z ^ 2 - 2 * z)

/-- The `k`-fold iterate of `D_y`. -/
def DyIter (k : ℕ) (f : ℂ → ℂ) : ℂ → ℂ := (Dy^[k]) f

/-- `dyC z = y'(z)`. -/
def dyC (z : ℂ) : ℂ := (z ^ 2 - 2 * z) / (z - 1) ^ 2

/-- `p` evaluated at `y(z)`. -/
def pAtY (p : Polynomial ℚ) (z : ℂ) : ℂ := p.eval₂ (algebraMap ℚ ℂ) (yC z)

/-- `1/9`. -/
def ninth : ℂ := 1 / 9

/-- `SU = {Im z > (1 − Re z)/8}`: a half-plane containing `(1,∞)`, convex, avoiding `0, 1/9, 1, −1/8`. -/
def SU : Set ℂ := {z | (1 - z.re) / 8 < z.im}

/-- `SL = {Im z < (Re z − 1)/8}`. -/
def SL : Set ℂ := {z | z.im < (z.re - 1) / 8}

/-- The slit plane `ℂ ∖ (−∞, 1]`. -/
def Om1 : Set ℂ := {z | z.im ≠ 0 ∨ 1 < z.re}

/-- `S* = ball 0 1 ∩ {z | 1/9 < Re z}`: convex, `L`-regular. -/
def Sstar : Set ℂ := ball 0 1 ∩ {z | 1 / 9 < z.re}

/-- The upper half of a ball around `1/9`. -/
def halfU (δ : ℝ) : Set ℂ := ball ninth δ ∩ {z | 0 < z.im}

/-- The lower half of a ball around `1/9`. -/
def halfL (δ : ℝ) : Set ℂ := ball ninth δ ∩ {z | z.im < 0}

/-- The lens `ball(1,δ) ∩ ball(0,1)`. -/
def lens1 (δ : ℝ) : Set ℂ := ball 1 δ ∩ ball 0 1

/-- `ℓ = log(1−z)` (a branch on the slit plane). -/
def ell (z : ℂ) : ℂ := Complex.log (1 - z)

/-- The coefficients `aₙ` of the holomorphic solution `u_h` of `L` at `x = 1`. -/
def uhCoeff : ℕ → ℚ
  | 0 => 1
  | 1 => 3 / 4
  | (k + 2) =>
      ((17 * (k + 1) * (k + 2) + 6) * uhCoeff (k + 1) - 9 * (k + 1) ^ 2 * uhCoeff k)
        / (8 * (k + 2) ^ 2)

/-- `u_h(z) = Σ aₙ(1−z)ⁿ`, the holomorphic solution of `L` at `x = 1`, `u_h(1) = 1`. -/
def uh (z : ℂ) : ℂ := ∑' n, (uhCoeff n : ℂ) * (1 - z) ^ n

/-- `f` has log-coefficient `κ` at `1/9` on the open piece `V`: `f = κ·y9·log(z−1/9) + h` with `h`
holomorphic on the ball. -/
def LogCoeff (y9 : ℂ → ℂ) (δ : ℝ) (V : Set ℂ) (f : ℂ → ℂ) (κ : ℂ) : Prop :=
  ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball ninth δ) ∧
    ∀ z ∈ V, f z = κ * y9 z * Complex.log (z - ninth) + h z

/-- The data of the holomorphic solution `y9` of `L` at `x = 1/9`. -/
def Y9 (y9 : ℂ → ℂ) (δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 / 20 ∧ DifferentiableOn ℂ y9 (ball ninth δ) ∧ y9 ninth ≠ 0 ∧
    ∀ z ∈ ball ninth δ, LZ y9 z = 0

/-! ## 1. The `ℚ(x)`-module data of the algebraic endgame -/

/-- `x` as an element of `ℚ(x)`. -/
def xQ' : RatFunc ℚ := RatFunc.X

/-- `y = x²/(x−1)` as an element of `ℚ(x)`. -/
def yQs : RatFunc ℚ := xQ' ^ 2 / (xQ' - 1)

/-- `1/y' = (x−1)²/(x²−2x)` as an element of `ℚ(x)`. -/
def rhos : RatFunc ℚ := (xQ' - 1) ^ 2 / (xQ' ^ 2 - 2 * xQ')

/-- `P` as an element of `ℚ(x)`. -/
def PZQ : RatFunc ℚ := xQ' - 10 * xQ' ^ 2 + 9 * xQ' ^ 3

/-- `P'` as an element of `ℚ(x)`. -/
def PZQ' : RatFunc ℚ := 1 - 20 * xQ' + 27 * xQ' ^ 2

/-- `R` as an element of `ℚ(x)`. -/
def RZQ : RatFunc ℚ := -3 + 9 * xQ'

/-- `∂_y` on `ℚ(x)e₀ ⊕ ℚ(x)e₁` (`e₀ = f`, `e₁ = f'`, `f'' = −(P'f' + Rf)/P`). -/
def dZ (uv : RatFunc ℚ × RatFunc ℚ) : RatFunc ℚ × RatFunc ℚ :=
  (rhos * (Submission.CDT.dRat uv.1 - uv.2 * RZQ / PZQ),
   rhos * (uv.1 + Submission.CDT.dRat uv.2 - uv.2 * PZQ' / PZQ))

/-- The class of `∂_y^k` (`k ≤ 3`) in the `P`-branch module. -/
def clsZ (k : Fin 4) : RatFunc ℚ × RatFunc ℚ := (dZ^[(k : ℕ)]) (1, 0)

/-- `dy/dx = (x²−2x)/(x−1)²` as an element of `ℚ(x)`. -/
def dyQ : RatFunc ℚ := (xQ' ^ 2 - 2 * xQ') / (xQ' - 1) ^ 2

/-- The three ratios `y^{−i}·y'` (`i = 0,1,2`) as elements of `ℚ(x)`. -/
def rQ (i : Fin 3) : RatFunc ℚ := (yQs ^ (i : ℕ))⁻¹ * dyQ

/-- `y = x²/(x−1)` as an element of `ℂ(x)` (division inside `RatFunc`, NOT polynomial
division). -/
def yQc : RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ) X) ^ 2 / (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - 1))

/-- `dy/dx = (x²−2x)/(x−1)²` as an element of `ℂ(x)`. -/
def dyQc : RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X ^ 2 - 2 * X))
    / (algebraMap (Polynomial ℂ) (RatFunc ℂ) ((X - 1) ^ 2))

/-- The three ratios `y^{−i}·y'` (`i = 0,1,2`) over `ℂ(x)`. -/
def rQc (i : Fin 3) : RatFunc ℂ := (yQc ^ (i : ℕ))⁻¹ * dyQc

/-- Polynomial numerators of `y^{−i}·y'` over `ℂ`. -/
def rnC (i : Fin 3) : Polynomial ℂ :=
  ![X ^ 2 - 2 * X, X - 2, X - 2] i

/-- Polynomial denominators of `y^{−i}·y'` over `ℂ`. -/
def rdC (i : Fin 3) : Polynomial ℂ :=
  ![(X - 1) ^ 2, X * (X - 1), X ^ 3] i

/-- Evaluation of a rational function at a complex point. -/
def rval (f : RatFunc ℚ) (z : ℂ) : ℂ :=
  f.num.eval₂ (algebraMap ℚ ℂ) z / f.denom.eval₂ (algebraMap ℚ ℂ) z

end A14D

end Work
