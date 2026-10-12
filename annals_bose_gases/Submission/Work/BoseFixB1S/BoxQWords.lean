import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

/-- `Q₀` — the condensate/`A₀` word at the box projections:
`½ Σ_{i<j}∫(P_iP_jΦ)² w₂ − μ Σ_i∫(P_iΦ)² (w₁-fibre)`. -/
def boxQ0 {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 w2 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ)
    (Φ : X N → ℝ) : ℝ :=
  (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
        * w2 (x p.1) (x p.2))
    - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i))

/-- `Q₁` — the `PP`–`PQ` cross word (doubled), with its `μ`-line. -/
def boxQ1 {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 w2 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ)
    (Φ : X N → ℝ) : ℝ :=
  2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w2 (x p.1) (x p.2))
    - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
          * w1Fibre ℓ w1 (x i))

/-- `Q₂` — the mixed word (the two `PQ`-pair families, the `μ`-line on `Q²`, and the
`PP`–`QQ` pairing against `w₁`). -/
def boxQ2 {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 w2 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ)
    (Φ : X N → ℝ) : ℝ :=
  (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w2 (x p.1) (x p.2))
    + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w2 (x p.1) (x p.2))
    - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i))
    + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w1 (x p.1) (x p.2))

/-- `Q₃` — the `PQ`–`QQ` cross word (doubled). -/
def boxQ3 {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ)
    (Φ : X N → ℝ) : ℝ :=
  2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w1 (x p.1) (x p.2))

/-- The `Q₄` bracket (operating on `Φ` in the quadratic form `½Σ∫(Q₄B)²w`). -/
def boxQ4B {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (om : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ)
    (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) : ℝ :=
  Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x
    + om (x p.1) (x p.2) *
        ((Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          + (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          + (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x))

/-- `Q₄` — the manifest square against the two-body kernel `w`. -/
def boxQ4 {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w om : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ)
    (Φ : X N → ℝ) : ℝ :=
  (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))

/-- The localised flat (condensate) count `S = Σ_i ∫ (P_iΦ)²`. -/
def boxFlatCount {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2

/-- The localised pair-condensate count `cS₂ = Σ_{i<j}∫(P_iP_jΦ)²`. -/
def boxPairCount {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : X N → ℝ) : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2

/-- The `w₂`-mass over `A × A` (the coefficient of the flat pair term). -/
def boxM2 (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w2 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ) : ℝ :=
  ∫ p in A ×ˢ A, w2 p.1 p.2

/-- The `w₁`-fibre mass over `A` (the coefficient of the one-body line). -/
def boxM1 (ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ) : ℝ :=
  ∫ z in A, w1Fibre ℓ w1 z

/-- The localised excited count `n₊ = Σ_i ∫ (Q_iΦ)²` at the box projections — definitionally
`Work.UBBInputs8.cnPlusBoxInd ℓ A volA Φ`. -/
def boxQCount {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2

/-- The five-word sum. -/
def boxQSum {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ)
    (Φ : X N → ℝ) : ℝ :=
  boxQ0 volA ℓ μ A w1 w2 Φ + boxQ1 volA ℓ μ A w1 w2 Φ + boxQ2 volA ℓ μ A w1 w2 Φ
    + boxQ3 volA ℓ A w1 Φ + boxQ4 volA ℓ A w om Φ

end Work.BoseFixB1S
