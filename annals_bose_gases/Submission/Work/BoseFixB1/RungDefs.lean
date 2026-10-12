import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.PerBoxNames
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.RungDefs` — the vocabulary of the `A₀+A₂` rung

Abbreviations for FS `eq:Q1n0` / `eq:Q3+Q4CS` / `eq:Q2n0` at the box projections
`P_i = boxPInd V A i`, `Q_i = boxQInd V A i` of the sliding box `A = dlBox ℓ d u`
(volume `V = boxMass ℓ d u`), with the localised kernels

* `w = wSmallPair M ℓ d u v`,  `w₁ = wSmall1Pair h M ℓ d u`,  `w₂ = wSmallPair M ℓ d u (g₂ v h)`,
* `fib₁ = w1Fibre ℓ w₁`,  `fib₂ = w1Fibre ℓ w₂`.

Everything here is a definition; the lemmas live with the pieces of the bracket.
-/

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

noncomputable section

set_option autoImplicit false

/-- Abbreviation for `ℝ³` (kept local to avoid the corpus notations). -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- `n₀Φ = Σ_j P_jΦ` — the function `F` of FS `eq:Q1n0`. -/
noncomputable def rungF {N : ℕ} (V : ℝ) (A : Set E3) (Φ : X N → ℝ) : X N → ℝ :=
  fun x => ∑ j : Fin N, Work.UBBInputs8.boxPInd V A j Φ x

/-- The `w₁`-box-fibre `fib₁ = w1Fibre ℓ (wSmall1Pair h M ℓ d u)`. -/
noncomputable def rungFib1 (ℓ : ℝ) {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (d : ℝ)
    (u : E3) : E3 → ℝ :=
  w1Fibre ℓ (wSmall1Pair h M ℓ d u)

/-- The `w₂`-box-fibre `fib₂ = w1Fibre ℓ (wSmallPair M ℓ d u (g₂ v h))`. -/
noncomputable def rungFib2 (ℓ : ℝ) {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (d : ℝ)
    (u : E3) : E3 → ℝ :=
  w1Fibre ℓ (wSmallPair M ℓ d u (g2 v h))

/-- **The first line of FS `eq:Q1n0`**:
`2·Σ_i ∫ Q_i((F/V − μ)Φ)·fib₁(x_i)·(P_iΦ)`. -/
noncomputable def rungLine1 {N : ℕ} (V ℓ μ : ℝ) (A : Set E3) {v : E3 → ℝ}
    (h : Work.UBB.ScatSol v) (M : ℕ) (d : ℝ) (u : E3) (Φ : X N → ℝ) : ℝ :=
  2 * ∑ i : Fin N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxQInd V A i (fun y => rungF V A Φ y / V - μ * Φ y) x)
      * rungFib1 ℓ h M d u (x i) * (Work.UBBInputs8.boxPInd V A i Φ x)

/-- **The second line of FS `eq:Q1n0`**:
`(2/V)·Σ_i ∫ Q_i(F)·(fib₂ − fib₁)(x_i)·(P_iΦ)` — the partner of the `ω`-cross of
`eq:Q3+Q4CS`. -/
noncomputable def rungLine2 {N : ℕ} (V ℓ : ℝ) (A : Set E3) {v : E3 → ℝ}
    (h : Work.UBB.ScatSol v) (M : ℕ) (d : ℝ) (u : E3) (Φ : X N → ℝ) : ℝ :=
  (2 / V) * ∑ i : Fin N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxQInd V A i (rungF V A Φ) x)
      * (rungFib2 ℓ h M d u (x i) - rungFib1 ℓ h M d u (x i))
      * (Work.UBBInputs8.boxPInd V A i Φ x)

/-- `XB = Σ_p ∫ (P_{p.1}Q_{p.2}Φ)²·w₁` — the `(P Q)`-pair mass that FS `eq:BQwQleq`
controls (the asset `boxPQw_mass_leB1`). -/
noncomputable def rungXB {N : ℕ} (V ℓ : ℝ) (A : Set E3) {v : E3 → ℝ}
    (h : Work.UBB.ScatSol v) (M : ℕ) (d : ℝ) (u : E3) (Φ : X N → ℝ) : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxQInd V A p.2 Φ) x) ^ 2
      * wSmall1Pair h M ℓ d u (x p.1) (x p.2)

end

end Work.BoseFixB1
