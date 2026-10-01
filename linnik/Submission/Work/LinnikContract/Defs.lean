/-
# LinnikContract — Defs.lean  (FROZEN)

FROZEN 2026-09-25.  Definitions for the Linnik L = 5.5 contract, following
`Submission/Work/LinnikPlan/ROUTE_LEAD.md` §3.0 verbatim in mathematical content.

Conventions (fixed here, everything above depends on them):
* `DirichletCharacter ℂ q` (Mathlib `MulChar (ZMod q) ℂ`), level `q`, `[NeZero q]`.
* `completedLFunction χ s` (Mathlib, `NumberTheory.LSeries.DirichletContinuation`):
  entire for `χ ≠ 1`; its zeros are the non-trivial zeros of `L(s,χ)`.
* `zeroMult χ ρ = analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ`
  is the *multiplicity* of `ρ` as a non-trivial zero of `L(s,χ)` — note it uses the
  **primitive** character inducing `χ`, so multiplicities are level-independent.
* `lamOf q ρ = (1 - Re ρ) log q`; `IsZ χ ρ` is the working region
  `χ ≠ 1`, `ρ` a zero, `|Im ρ| ≤ 1`.
* `boxSum`/`boxAbs` are the (finitely supported) sums over zeros in `InBox q R`.
-/
import Mathlib

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract

/-- `λ(ρ) = (1 - Re ρ) log q`. -/
def lamOf (q : ℕ) (ρ : ℂ) : ℝ := (1 - ρ.re) * Real.log q

/-- multiplicity of `ρ` as a zero of `L(s,χ*)`, `χ*` the primitive character inducing `χ`
    (via the completed L-function, which is entire for `χ ≠ 1`; its zeros = the non-trivial zeros). -/
def zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ

/-- HB's working region: a zero of a non-principal `L(s,χ)` with `|γ| ≤ 1`. -/
def IsZ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1

/-- `(χ₁,ρ₁)` realises `λ₁` (HB §6: the zero of largest real part). -/
def IsMin1 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  IsZ χ₁ ρ₁ ∧ ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → lamOf q ρ₁ ≤ lamOf q ρ

/-- HB's `λ₀ ≥ c`: every other zero of `χ₁` (and `ρ₁` itself if it is multiple) has `λ ≥ c`.
    When `χ₁` is real, `conj ρ₁` is excluded as well (HB §6, cases 1–3 for `ρ⁰`). -/
def Lam0Bound {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (c : ℝ) : Prop :=
  (2 ≤ zeroMult χ₁ ρ₁ → c ≤ lamOf q ρ₁) ∧
  ∀ ρ, IsZ χ₁ ρ → ρ ≠ ρ₁ → (χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) → c ≤ lamOf q ρ

/-- HB's `λ₂ ≥ c`: all zeros of characters other than `χ₁, χ̄₁`. -/
def Lam2Bound {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (c : ℝ) : Prop :=
  ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → c ≤ lamOf q ρ

/-- HB's `λ₃ ≥ c`: all zeros outside at most two conjugate pairs `{χ₁^{±1}, χ₂^{±1}}`. -/
def Lam3Bound {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (c : ℝ) : Prop :=
  ∃ χ₂ : DirichletCharacter ℂ q, ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ →
    χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ → c ≤ lamOf q ρ

/-- `N(λ)` of HB §11: number of non-principal `χ` with a zero, `|γ| ≤ 1`, `λ(ρ) ≤ λ`. -/
def Ncount (q : ℕ) [NeZero q] (lam : ℝ) : ℕ :=
  (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ∃ ρ, IsZ χ ρ ∧ lamOf q ρ ≤ lam)).card

/-- HB's `λ₀` of §11: `(1/3) log log log q`. -/
def lamMax (q : ℕ) : ℝ := Real.log (Real.log (Real.log q)) / 3

/-- `λ^{(χ)}`: least `λ` over zeros of `χ` with `|γ| ≤ 1` (`0` if there are none). -/
def lamChar {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  sInf {x | ∃ ρ, IsZ χ ρ ∧ lamOf q ρ = x}

/-- HB's density weight `w(λ) = λ / (e^{73λ/30} - e^{16λ/15})` (Lemma 11.1). -/
def wHB (x : ℝ) : ℝ := x / (Real.exp (73/30 * x) - Real.exp (16/15 * x))

/-- HB's test function `F₂(z) = ((1 - e^{-Kz})/z)^2`. -/
def F2 (K : ℝ) (z : ℂ) : ℂ := ((1 - Complex.exp (-(K:ℂ) * z)) / z) ^ 2

/-- HB's `F(z) = e^{-az}F₂(z)` with `a = L - 2K`. -/
def Hk (L K : ℝ) (z : ℂ) : ℂ := Complex.exp (-((L - 2*K : ℝ) : ℂ) * z) * F2 K z

/-- The per-character bound `B(λ)` of HB Lemma 13.3 (with `φ = 1/3`). -/
def Bfun (K lam : ℝ) : ℝ :=
  if lam = 0 then 1/(3*K) + 1
  else (1 - Real.exp (-2*K*lam))/(6*K^2*lam) + (2*K*lam - 1 + Real.exp (-2*K*lam))/(2*K^2*lam^2)

/-- HB's box `1 - R/𝓛 ≤ β, |γ| ≤ R/𝓛` (Lemma 13.2). -/
def InBox (q : ℕ) (R : ℝ) (ρ : ℂ) : Prop := lamOf q ρ ≤ R ∧ |ρ.im| * Real.log q ≤ R

/-- `Σ'_ρ H((1-ρ)𝓛)` for one character (with multiplicity). The support is finite. -/
def boxSum (q : ℕ) [NeZero q] (L K R : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ᶠ ρ : ℂ, if InBox q R ρ then (zeroMult χ ρ : ℂ) * Hk L K ((1 - ρ) * Real.log q) else 0

/-- `Σ'_ρ ‖F₂((1-ρ)𝓛)‖` for one character (with multiplicity). -/
def boxAbs (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ᶠ ρ : ℂ, if InBox q R ρ then (zeroMult χ ρ : ℝ) * ‖F2 K ((1 - ρ) * Real.log q)‖ else 0

/-- a real zero of a real character with `λ ≤ lamS` (Siegel/exceptional zero). -/
def SiegelZero (q : ℕ) [NeZero q] (lamS : ℝ) : Prop :=
  ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 ∧ χ ^ 2 = 1 ∧
    ∃ β : ℝ, β < 1 ∧ zeroMult χ (β : ℂ) ≠ 0 ∧ (1 - β) * Real.log q ≤ lamS

end Work.LinnikContract
