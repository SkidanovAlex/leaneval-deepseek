import Submission.CDTPlan.InterfacesK
import Submission.CDT.LogUnlikelyG

/-!
# cdt_linearIndependent — Theorem C template contracts (wave 2, orchestrator-owned)

Absurd relation (paper eq. (rabc)) with `a = 2m+1`, `b = 2n+1`:
`r_a η_a + r_b η_b + r_ab η_a η_b = r₀`, `η_a = ½ log((a+1)/(a−1)) = ½ log(1 + 1/m)`.
`P = logP a b r_a r_b r_ab r₀` (prior run, `LogUnlikelyG`), `G = Sym⁺P` (`sympSym`, series in
`y = x²/(x−1)`), and the paper's ordered list of 17 functions (§`sec:proofC`), matching the
arrays `bC`, `eC` of `Interfaces`.
-/

open Complex Metric Filter Topology
open scoped BigOperators

namespace Submission.CDTPlan

/-- Formal integral with constant term `0`: `∫₀ f`. -/
noncomputable def intY (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) f / n

/-- `(f − (Taylor polynomial of degree < k)) / y^k`. -/
noncomputable def tq (k : ℕ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + k) f

/-- `d/dy`. -/
noncomputable def dY (f : PowerSeries ℚ) : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) f

/-- `P` of the paper (eq. (defP)) for `a = 2m+1`, `b = 2n+1`. -/
noncomputable def PC (m n : ℕ) (ra rb rab r0 : ℤ) : PowerSeries ℚ :=
  Submission.CDT.logP (2 * m + 1) (2 * n + 1) ra rb rab r0

/-- `G = Sym⁺P` (Definition `PtoG`). -/
noncomputable def GC (m n : ℕ) (ra rb rab r0 : ℤ) : PowerSeries ℚ :=
  Submission.CDT.sympSym (PC m n ra rb rab r0)

/-- The 17 functions of Theorem C in the paper's order: `B₁,B₂,B₃,B₄,B₅,G,G',G'',G''',B₆,B₇,
∫yG, ∫G, ∫(G−G(0))/y, …, ∫(G − jet₃)/y⁴`. -/
noncomputable def seventeen (m n : ℕ) (ra rb rab r0 : ℤ) : Fin 17 → PowerSeries ℚ :=
  let G := GC m n ra rb rab r0
  ![B1, B2, B3, B4, B5, G, dY G, dY (dY G), dY (dY (dY G)), B6, B7,
    intY (PowerSeries.X * G), intY G, intY (tq 1 G), intY (tq 2 G), intY (tq 3 G), intY (tq 4 G)]

/-- Admissible pairs (positive, non-strict gap). -/
def CAdm (m n : ℕ) : Prop := 1 ≤ m ∧ 1 ≤ n ∧ m ≠ n ∧ 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n

/-- The absurd relation (rabc). -/
def CRel (m n : ℕ) (ra rb rab r0 : ℤ) : Prop :=
  (ra : ℝ) * Submission.CDT.beukersEta (2 * (m : ℝ) + 1) +
      (rb : ℝ) * Submission.CDT.beukersEta (2 * (n : ℝ) + 1) +
      (rab : ℝ) * (Submission.CDT.beukersEta (2 * (m : ℝ) + 1) *
        Submission.CDT.beukersEta (2 * (n : ℝ) + 1)) = r0

/-- Lemma `17functions` (ℚ(y)-linear independence). -/
def Seventeen : Prop :=
  ∀ (m n : ℕ) (ra rb rab r0 : ℤ), CAdm m n → CRel m n ra rb rab r0 → rab ≠ 0 →
    PolyIndependent (seventeen m n ra rb rab r0)

/-- Lemma `seven`: the pure functions `B₁,…,B₇` are ℚ(y)-linearly independent. -/
def LemmaSeven : Prop := PolyIndependent pureB

/-- Denominator types of the 17 functions (arrays `eC`, `bC`). -/
def CDenoms : Prop :=
  ∀ (m n : ℕ) (ra rb rab r0 : ℤ), ∀ i, HasDenomType (eC i) (bC i) (seventeen m n ra rb rab r0 i)

/-- The ℚ(y)-span of the 17 functions is closed under `d/dy` (needs `LL(G) ∈ ℚ[y]`). -/
def CDClosed : Prop :=
  ∀ (m n : ℕ) (ra rb rab r0 : ℤ), CAdm m n → DClosed (seventeen m n ra rb rab r0)

/-- Under (rabc), `P` converges on `|x| < 2/3` (its true radius is
`x_s = min(α_a/α_b, α_b/α_a) ≈ 1 − 1e-6`, `α_a = a + √(a²−1)`). -/
def PRadius : Prop :=
  ∀ (m n : ℕ) (ra rb rab r0 : ℤ), CAdm m n → CRel m n ra rb rab r0 →
    ∃ C : ℝ, ∀ k : ℕ, |((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℝ)| ≤ C * (3 / 2) ^ k

/-- Continuation of `P` along any lift `Φ` of `z ↦ φ_C(z²)` (as produced by `PhiLift`). -/
def PLiftCont : Prop :=
  ∀ (m n : ℕ) (ra rb rab r0 : ℤ), CAdm m n → CRel m n ra rb rab r0 →
    ∀ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ (ball 0 1) →
      (∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2)) →
      (∀ z ∈ ball (0 : ℂ) 1, Φ z = 0 → z = 0) →
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 1) ∧
        ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun k : ℕ =>
          ((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ) * Φ z ^ k) (F z)

/-- Meromorphic pullbacks of the 17 functions along `φ_C`. -/
def CPullbacks : Prop :=
  ∀ (m n : ℕ) (ra rb rab r0 : ℤ), CAdm m n → CRel m n ra rb rab r0 →
    ∀ i, PullbackMero (seventeen m n ra rb rab r0 i) phiC

end Submission.CDTPlan
