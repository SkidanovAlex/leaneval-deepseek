import Submission.CDTPlan.InterfacesA
import Submission.CDTPlan.InterfacesC
import Submission.CDT.EichlerInput
import Submission.CDT.TheoremA_leaf

/-!
# cdt_linearIndependent — Theorem A template contracts (wave A2, orchestrator-owned)

Absurd relation (paper eq. (absurd)): `a + b·L(2,χ₋₃)/2 + c·ζ(2)/4 = 0`, `a b c ∈ ℤ`, `b ≠ 0`.
`H = a H_A + b H_B + c H_C` (`Submission.CDT.ZagierH`, Zagier's sequence C and its two companions),
`G = Sym⁺H` in `y = x²/(x−1)`, and the paper's 14 functions (§`sec:proofA`), matching `bA`, `eA`.
Generic pullback contracts (`LiftData`, `PurePullbacks`, `PullbackScale`) are shared with Theorem C.
-/

open Complex Metric Filter Topology
open scoped BigOperators

namespace Submission.CDTPlan

/-- `H = a H_A + b H_B + c H_C`. -/
noncomputable def HZ (a b c : ℤ) : PowerSeries ℚ := Submission.CDT.ZagierH a b c

/-- `G = Sym⁺ H`. -/
noncomputable def GZ (a b c : ℤ) : PowerSeries ℚ := Submission.CDT.sympSym (HZ a b c)

/-- The 14 functions of Theorem A: `B₁,B₂,B₃,B₄,B₅,G,G',G'',G''',B₆,B₇, ∫G, ∫(G−G(0))/y,
∫(G−G(0)−G'(0)y)/y²`. -/
noncomputable def fourteen (a b c : ℤ) : Fin 14 → PowerSeries ℚ :=
  let G := GZ a b c
  ![B1, B2, B3, B4, B5, G, dY G, dY (dY G), dY (dY (dY G)), B6, B7,
    intY G, intY (tq 1 G), intY (tq 2 G)]

/-- The absurd relation. -/
def ARel (a b c : ℤ) : Prop :=
  (a : ℝ) + (b : ℝ) * (Submission.CDT.L2chi3Real / 2) + (c : ℝ) * (Submission.CDT.zeta2Real / 4) = 0

/-- Lemma `14functions` (ℚ(y)-linear independence), under the absurd relation with `b ≠ 0`. -/
def Fourteen : Prop :=
  ∀ a b c : ℤ, ARel a b c → b ≠ 0 → PolyIndependent (fourteen a b c)

/-- Denominator types of the 14 functions (arrays `eA`, `bA`). -/
def ADenoms : Prop := ∀ (a b c : ℤ) (i : Fin 14), HasDenomType (eA i) (bA i) (fourteen a b c i)

/-- The ℚ(y)-span of the 14 functions is closed under `d/dy`. -/
def ADClosed : Prop := ∀ a b c : ℤ, DClosed (fourteen a b c)

/-! ## Generic pullback machinery (shared with Theorem C) -/

/-- `Φ` lifts `z ↦ φ(z²)` through `y = x²/(x−1)`, with `w(Φ(z)) = Φ(−z)`. -/
def LiftData (φ Φ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Φ (ball 0 1) ∧
    (∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = φ (z ^ 2) ∧ Φ z * Φ (-z) = φ (z ^ 2)) ∧
    (∀ z ∈ ball (0 : ℂ) 1, Φ z = 0 → z = 0)

/-- Lift of `h ∘ ψ` for any admissible inner map `ψ` (generalises `PhiLift`). -/
def PhiLiftGen : Prop :=
  ∀ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (ball 0 1) → ψ 0 = 0 → deriv ψ 0 ≠ 0 →
    (∀ z ∈ ball (0 : ℂ) 1, ‖ψ z‖ < 1) → (∀ z ∈ ball (0 : ℂ) 1, ψ z = 0 → z = 0) →
    ∃ Φ, LiftData (fun z => hauptH (ψ z)) Φ

/-- Pure functions pull back meromorphically along any map with a lift. -/
def PurePullbacks : Prop :=
  ∀ φ Φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball 0 1) → φ 0 = 0 → LiftData φ Φ →
    ∀ i : Fin 7, PullbackMero (pureB i) φ

/-- Pullbacks are stable under shrinking the disc. -/
def PullbackScale : Prop :=
  ∀ (f : PowerSeries ℚ) (φ : ℂ → ℂ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → PullbackMero f φ →
    PullbackMero f (fun z => φ (ρ * z))

/-! ## Theorem A analytic data -/

/-- Continuation of `H` along a lift of `φ_A` (under (absurd), `H` converges on `|x| < 1`). -/
def HLiftContA : Prop :=
  ∀ a b c : ℤ, ARel a b c → ∀ Φ : ℂ → ℂ, LiftData phiA Φ →
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 1) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun k : ℕ =>
        ((PowerSeries.coeff k (HZ a b c) : ℚ) : ℂ) * Φ z ^ k) (F z)

/-- Meromorphic pullbacks of the 14 functions along `φ_A`. -/
def APullbacks : Prop :=
  ∀ a b c : ℤ, ARel a b c → ∀ i, PullbackMero (fourteen a b c i) phiA

/-- Theorem A's absurd-relation refutation, in the leaf form of the seed. -/
def ALeaf : Prop := Submission.CDT.theoremA_leaf

end Submission.CDTPlan
