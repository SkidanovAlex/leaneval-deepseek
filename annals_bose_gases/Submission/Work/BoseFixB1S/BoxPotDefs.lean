import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The box indicator `1_A`, as a real-valued function on `ℝ³`. -/
def Aind (A : Set (EuclideanSpace ℝ (Fin 3))) (y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  A.indicator (fun _ => (1 : ℝ)) y

/-- The `j`-th slot reading of the box indicator: `x ↦ 1_A(x j)`. -/
def sigAt (A : Set (EuclideanSpace ℝ (Fin 3))) {N : ℕ} (j : Fin N) :
    Submission.BoseGases.X N → ℝ := fun x => Aind A (x j)

theorem sigAt_apply (A : Set (EuclideanSpace ℝ (Fin 3))) {N : ℕ} (j : Fin N)
    (x : Submission.BoseGases.X N) : sigAt A j x = Aind A (x j) := rfl

/-- `1_A` is idempotent as a real number: `1_A(y)² = 1_A(y)` (the values are `0` and `1`). -/
theorem Aind_mul_self (A : Set (EuclideanSpace ℝ (Fin 3))) (y : EuclideanSpace ℝ (Fin 3)) :
    Aind A y * Aind A y = Aind A y := by
  unfold Aind
  by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]

/-- `|1_A| ≤ 1`. -/
theorem Aind_abs_le_one (A : Set (EuclideanSpace ℝ (Fin 3))) (y : EuclideanSpace ℝ (Fin 3)) :
    |Aind A y| ≤ 1 := by
  unfold Aind
  by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]

theorem Aind_nonneg (A : Set (EuclideanSpace ℝ (Fin 3))) (y : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Aind A y := by
  unfold Aind
  by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]

/-- The `i`-slot mean of `Φ` over the box `A` (independent of the `i`-th slot). -/
def oneMean (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) {N : ℕ} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) : ℝ :=
  (1 / volA) * ∫ z in A, Φ (Function.update x i z)

/-- The two-slot mean of `Φ` over `A × A` (the ordered double integral). -/
def twoMean (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) {N : ℕ} (i j : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) : ℝ :=
  (1 / volA) *
    ((1 / volA) * ∫ z in A, ∫ w in A, Φ (Function.update (Function.update x i z) j w))

/-! ## The seven pair-fragment integrands of the box words -/

/-- `boxQ0` pair-summand integrand. -/
def fg0 {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  (1 / 2) * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
    * w2 (x i) (x j)

/-- `boxQ1` pair-summand integrand (the doubled `P Q`–`P P` term). -/
def fg1 {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
    * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) * w2 (x i) (x j)

/-- `boxQ2` first pair-summand integrand. -/
def fg2a {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
    * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) * w2 (x i) (x j)

/-- `boxQ2` second pair-summand integrand. -/
def fg2b {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
    * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) * w2 (x i) (x j)

/-- `boxQ2` third pair-summand integrand (the `w₁`-pairing term). -/
def fg2c {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
    * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) * w1 (x i) (x j)

/-- `boxQ3` pair-summand integrand (the doubled `P Q`–`Q Q` term). -/
def fg3 {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
    * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) * w1 (x i) (x j)

/-- `boxQ4` pair-summand integrand (the manifest square). -/
def fg4 {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  (1 / 2) * (boxQ4B volA A om Φ (i, j) x) ^ 2 * w (x i) (x j)

/-- The combined pointwise value of the five words' pair summands at the two orientations
`(i,j)` and `(j,i)`. -/
def fgsum {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  fg0 volA A w2 Φ i j x + fg1 volA A w2 Φ i j x + fg2a volA A w2 Φ i j x
    + fg2b volA A w2 Φ i j x + fg2c volA A w1 Φ i j x + fg3 volA A w1 Φ i j x
    + fg4 volA A w om Φ i j x
    + fg0 volA A w2 Φ j i x + fg1 volA A w2 Φ j i x + fg2a volA A w2 Φ j i x
    + fg2b volA A w2 Φ j i x + fg2c volA A w1 Φ j i x + fg3 volA A w1 Φ j i x
    + fg4 volA A w om Φ j i x

/-- The seven word-fragment integrals at one orientation `(i,j)` (the `pairSet`-summands of
`boxQ0`..`boxQ4` restricted to the pair `(i,j)`). -/
def pairInts {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) : ℝ :=
  (∫ x in abox N ℓ, fg0 volA A w2 Φ i j x) + (∫ x in abox N ℓ, fg1 volA A w2 Φ i j x)
    + (∫ x in abox N ℓ, fg2a volA A w2 Φ i j x) + (∫ x in abox N ℓ, fg2b volA A w2 Φ i j x)
    + (∫ x in abox N ℓ, fg2c volA A w1 Φ i j x) + (∫ x in abox N ℓ, fg3 volA A w1 Φ i j x)
    + (∫ x in abox N ℓ, fg4 volA A w om Φ i j x)

/-- The seven raw pair sums carried by `boxQ0`..`boxQ4` (before the `pairSet`-reassembly). -/
def pairRaw {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) : ℝ :=
  (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
        * w2 (x p.1) (x p.2))
    + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w2 (x p.1) (x p.2))
    + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w2 (x p.1) (x p.2))
    + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
        * w2 (x p.1) (x p.2))
    + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w1 (x p.1) (x p.2))
    + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w1 (x p.1) (x p.2))
    + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))

/-! ## The `μ`-integrands of the box words -/

/-- `μ`-weight integrand value for slot `i`: `(P_iΦ)² · (∫_y w1(x_i,y))`. -/
def boxMuP {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i : Fin N) : ℝ :=
  ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i)

/-- `μ`-weight integrand value: `(Q_iΦ)·(P_iΦ)·(∫_y w1(x_i,y))`. -/
def boxMuQP {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i : Fin N) : ℝ :=
  ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
      * w1Fibre ℓ w1 (x i)

/-- `μ`-weight integrand value: `(Q_iΦ)² · (∫_y w1(x_i,y))`. -/
def boxMuQ {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i : Fin N) : ℝ :=
  ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i)

/-- The full `μ`-weight of slot `i`: `Φ² · (∫_y w1(x_i,y))`. -/
def boxMuPhi {N : ℕ} (ℓ : ℝ)
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i : Fin N) : ℝ :=
  ∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)

end Work.BoseFixB1S
