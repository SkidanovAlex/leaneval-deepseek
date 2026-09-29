import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.CDcl.xrel_defs
import Submission.Work.CDcl.xco_iter
import Submission.Work.CDcl.xco_pw_defs
import Submission.CDT.ZagierHBC

/-!
# Area ADcl — the `x`-side ODE data for `H = a·H_A + b·H_B + c·H_C`

This is the setup for `Work.ADcl.a_dclosed` (the `d/dy`-closure of the fourteen functions of
Theorem A of CDT).  Following `Work.CDcl.c_dclosed`, we work in the field `ℚ((x)) = Frac ℚ⟦x⟧`
(`Work.CDcl.LF`) with the derivation `dL`, the embedding `toL : ℚ(x) → ℚ((x))` and the
`y`-derivative `Aop f = ρ·f'` (`ρ = dx/dy`).

The two power series that matter are

* `Hfun a b c  = H(x)   = a·H_A + b·H_B + c·H_C`         (Zagier's `defH`), and
* `Hwfun a b c = H(x/(x-1))`,                             its pullback by `φ = x/(x-1)`.

`H` satisfies Zagier's order-two inhomogeneous ODE
`aZ·H'' + bZ·H' + cZ·H = b + c/(1-x)` (`Submission.CDT.functionsH_ode`), which we put in the
normal form `H'' = α·H' + β·H + γ`; the pullback `Hw` satisfies the conjugate ODE with the
pulled-back coefficients `α̃, β̃, γ̃`.  `A^k` of a solution of `f'' = αf' + βf + γ` is again a
`ℚ(x)`-combination of `f, f'` and a constant (`seqA`, `seqAt`).

All definitions only; the lemmas about them are in the sibling modules
(`Work.ADcl.ode_H`, `Work.ADcl.ode_Hw`, `Work.ADcl.reduce`, `Work.ADcl.x_relation_A`).
-/


namespace Work.ADcl

noncomputable section

/-! ## The order-two operator of Zagier's ODE, as a polynomial and as a rational function -/

/-- `A(x) = x - 10x² + 9x³ = x(1-x)(1-9x)`, the leading coefficient of `HA_odeLHS`. -/
def aZ : Polynomial ℚ := Polynomial.X - Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 9 * Polynomial.X ^ 3

/-- `B(x) = 1 - 20x + 27x²`. -/
def bZ : Polynomial ℚ := 1 - Polynomial.C 20 * Polynomial.X + Polynomial.C 27 * Polynomial.X ^ 2

/-- `C(x) = -3 + 9x`. -/
def cZ : Polynomial ℚ := -Polynomial.C 3 + Polynomial.C 9 * Polynomial.X

/-- `A` as a rational function. -/
def aK : RatFunc ℚ := (aZ : RatFunc ℚ)

/-- `B` as a rational function. -/
def bK : RatFunc ℚ := (bZ : RatFunc ℚ)

/-- `C` as a rational function. -/
def cK : RatFunc ℚ := (cZ : RatFunc ℚ)

/-- the inhomogeneity `r = b + c/(1-x)` of Zagier's ODE, as a rational function. -/
def rK (b c : ℚ) : RatFunc ℚ := (b : RatFunc ℚ) + (c : RatFunc ℚ) / (1 - Work.CDcl.xK)

/-- the normal-form coefficient `α = -B/A`. -/
def alphaA : RatFunc ℚ := -bK / aK

/-- the normal-form coefficient `β = -C/A`. -/
def betaA : RatFunc ℚ := -cK / aK

/-- the normal-form coefficient `γ = r/A`. -/
def gammaA (b c : ℚ) : RatFunc ℚ := rK b c / aK

/-! ## The pullback (`φ = x/(x-1)`) data -/

/-- `A(φ(x))`. -/
def aPhiK : RatFunc ℚ := aZ.eval₂ (algebraMap ℚ (RatFunc ℚ)) Work.CDcl.phiK

/-- `B(φ(x))`. -/
def bPhiK : RatFunc ℚ := bZ.eval₂ (algebraMap ℚ (RatFunc ℚ)) Work.CDcl.phiK

/-- `C(φ(x))`. -/
def cPhiK : RatFunc ℚ := cZ.eval₂ (algebraMap ℚ (RatFunc ℚ)) Work.CDcl.phiK

/-- `φ' = -1/(x-1)²`. -/
def sK : RatFunc ℚ := Submission.CDT.dRat Work.CDcl.phiK

/-- `φ'' = 2/(x-1)³`. -/
def tK : RatFunc ℚ := Submission.CDT.dRat sK

/-- the pulled-back normal-form coefficient `α̃ = φ''/φ' + φ'·(α∘φ)` of the ODE for `H∘φ`. -/
def alphaAt : RatFunc ℚ := tK / sK - bPhiK * sK / aPhiK

/-- `β̃ = (φ')²·(β∘φ)`. -/
def betaAt : RatFunc ℚ := -(cPhiK * sK ^ 2 / aPhiK)

/-- `γ̃ = (φ')²·(γ∘φ)`, using `(1-φ)⁻¹ = 1-x`. -/
def gammaAt (b c : ℚ) : RatFunc ℚ :=
  sK ^ 2 * ((b : RatFunc ℚ) + (c : RatFunc ℚ) * (1 - Work.CDcl.xK)) / aPhiK

/-! ## The two power series, in `ℚ((x))` -/

/-- `H = a·H_A + b·H_B + c·H_C` as an element of `ℚ((x))`. -/
def Hfun (a b c : ℚ) : Work.CDcl.LF :=
  algebraMap (PowerSeries ℚ) Work.CDcl.LF (Submission.CDT.ZagierH a b c)

/-- `H(x/(x-1))` as an element of `ℚ((x))`. -/
def Hwfun (a b c : ℚ) : Work.CDcl.LF :=
  algebraMap (PowerSeries ℚ) Work.CDcl.LF
    ((Submission.CDT.ZagierH a b c).subst Submission.CDT.sympPhi)

/-- `G = Sym⁺H` (the Theorem-A `G` of `defG`). -/
def Gz (a b c : ℚ) : PowerSeries ℚ :=
  Submission.CDT.sympSym (Submission.CDT.ZagierH a b c)

/-- `T k = (G^{(k)})∘y`, the pullback of the `k`-th `y`-derivative of `G`. -/
def Tz (a b c : ℚ) (k : ℕ) : PowerSeries ℚ :=
  ((PowerSeries.derivative (R := ℚ))^[k] (Gz a b c)).subst Submission.CDT.sympY

/-- `T k` in `ℚ((x))`. -/
def Tfun (a b c : ℚ) (k : ℕ) : Work.CDcl.LF :=
  algebraMap (PowerSeries ℚ) Work.CDcl.LF (Tz a b c k)

/-! ## The coefficient sequences of the reduction `A^k f = a_k·f + b_k·f' + d_k` -/

/-- `(a_k, b_k, d_k)` for the ODE data `(α, β, γ)`: `A^k f = a_k f + b_k f' + d_k` for every
solution of `f'' = α f' + β f + γ`. -/
def seqOf (aa bb gg : RatFunc ℚ) : ℕ → RatFunc ℚ × RatFunc ℚ × RatFunc ℚ
  | 0 => (1, 0, 0)
  | (k + 1) =>
      let t := seqOf aa bb gg k
      (Work.CDcl.rhoK * (Submission.CDT.dRat t.1 + t.2.1 * bb),
       Work.CDcl.rhoK * (t.1 + Submission.CDT.dRat t.2.1 + t.2.1 * aa),
       Work.CDcl.rhoK * (Submission.CDT.dRat t.2.2 + t.2.1 * gg))

/-- the sequence for `H` (the ODE `H'' = α H' + β H + γ`). -/
def seqA (b c : ℚ) : ℕ → RatFunc ℚ × RatFunc ℚ × RatFunc ℚ :=
  seqOf alphaA betaA (gammaA b c)

/-- the sequence for `Hw` (the conjugate ODE). -/
def seqAt (b c : ℚ) : ℕ → RatFunc ℚ × RatFunc ℚ × RatFunc ℚ :=
  seqOf alphaAt betaAt (gammaAt b c)

end

end Work.ADcl
