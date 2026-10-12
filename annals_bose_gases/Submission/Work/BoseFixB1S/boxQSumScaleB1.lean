import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQWords
import Submission.Work.hlocWire.boxPInd_smul
import Submission.Work.hlocWire.boxQInd_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxQSumScaleB1` — `boxQSum` is homogeneous of degree two

The five-word sum `Work.BoseFixB1S.boxQSum` is built from the two box projections
`P_{B,i}` and `Q_{B,i} = 1_{B,i} − P_{B,i}`, which are **linear** in the state
(`Work.hlocWire.boxPInd_smul`, `Work.hlocWire.boxQInd_smul`).  Every one of its terms is an
integral of a product of *two* such linear expressions times a weight, hence homogeneous of
degree two:

`boxQSum volA ℓ μ A w w₁ w₂ om (t • Φ) = t² boxQSum volA ℓ μ A w w₁ w₂ om Φ`.

The proof is purely algebraic: normalise the projections with the two scaling lemmas, pull the
constant factors out of the one-body integrals (`MeasureTheory.integral_const_mul`) and out of
the pair sums (`Finset.mul_sum`), then `ring`.
-/

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

/-- The one-body integral of a squared linear expression times a weight is homogeneous of
degree two. -/
private lemma int_sq_scale {N : ℕ} (t : ℝ) (B : Set (X N)) (f g : X N → ℝ) :
    ∫ x in B, (t * f x) ^ 2 * g x = t ^ 2 * ∫ x in B, (f x) ^ 2 * g x := by
  have hh : (fun x => (t * f x) ^ 2 * g x) = fun x => t ^ 2 * ((f x) ^ 2 * g x) := by
    funext x; ring
  rw [hh, MeasureTheory.integral_const_mul]

/-- The one-body integral of a product of two linear expressions times a weight is homogeneous
of degree two. -/
private lemma int_two_scale {N : ℕ} (t : ℝ) (B : Set (X N)) (f g h : X N → ℝ) :
    ∫ x in B, (t * f x) * (t * g x) * h x = t ^ 2 * ∫ x in B, f x * g x * h x := by
  have hh : (fun x => (t * f x) * (t * g x) * h x) = fun x => t ^ 2 * (f x * g x * h x) := by
    funext x; ring
  rw [hh, MeasureTheory.integral_const_mul]

/-- `int_sq_scale` summed over a finite index set (the pair sum of `boxQSum`). -/
private lemma sum_int_sq_scale {N : ℕ} {ι : Type*} (s : Finset ι) (t : ℝ) (B : Set (X N))
    (F H : ι → X N → ℝ) :
    (∑ p ∈ s, ∫ x in B, (t * F p x) ^ 2 * H p x)
      = t ^ 2 * ∑ p ∈ s, ∫ x in B, (F p x) ^ 2 * H p x := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => int_sq_scale t B (F p) (H p))

/-- `int_two_scale` summed over a finite index set (the pair sums of `boxQSum`). -/
private lemma sum_int_two_scale {N : ℕ} {ι : Type*} (s : Finset ι) (t : ℝ) (B : Set (X N))
    (F G H : ι → X N → ℝ) :
    (∑ p ∈ s, ∫ x in B, (t * F p x) * (t * G p x) * H p x)
      = t ^ 2 * ∑ p ∈ s, ∫ x in B, F p x * G p x * H p x := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => int_two_scale t B (F p) (G p) (H p))

/-- `Q₀` is homogeneous of degree two. -/
lemma boxQ0_smul {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ)
    (t : ℝ) :
    boxQ0 volA ℓ μ A w1 w2 (t • Φ) = t ^ 2 * boxQ0 volA ℓ μ A w1 w2 Φ := by
  unfold boxQ0
  simp only [Work.hlocWire.boxPInd_smul, Pi.smul_apply, smul_eq_mul]
  rw [sum_int_sq_scale, sum_int_sq_scale]
  ring

/-- `Q₁` is homogeneous of degree two. -/
lemma boxQ1_smul {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ)
    (t : ℝ) :
    boxQ1 volA ℓ μ A w1 w2 (t • Φ) = t ^ 2 * boxQ1 volA ℓ μ A w1 w2 Φ := by
  unfold boxQ1
  simp only [Work.hlocWire.boxPInd_smul, Work.hlocWire.boxQInd_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [sum_int_two_scale, sum_int_two_scale]
  ring

/-- `Q₂` is homogeneous of degree two. -/
lemma boxQ2_smul {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ)
    (t : ℝ) :
    boxQ2 volA ℓ μ A w1 w2 (t • Φ) = t ^ 2 * boxQ2 volA ℓ μ A w1 w2 Φ := by
  unfold boxQ2
  simp only [Work.hlocWire.boxPInd_smul, Work.hlocWire.boxQInd_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [sum_int_two_scale, sum_int_two_scale, sum_int_sq_scale, sum_int_two_scale]
  ring

/-- `Q₃` is homogeneous of degree two. -/
lemma boxQ3_smul {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ) (t : ℝ) :
    boxQ3 volA ℓ A w1 (t • Φ) = t ^ 2 * boxQ3 volA ℓ A w1 Φ := by
  unfold boxQ3
  simp only [Work.hlocWire.boxPInd_smul, Work.hlocWire.boxQInd_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [sum_int_two_scale]
  ring

/-- The `Q₄` bracket `boxQ4B` is linear in the state (pointwise). -/
lemma boxQ4B_smul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ) (t : ℝ)
    (p : Fin N × Fin N) (x : X N) :
    boxQ4B volA A om (t • Φ) p x = t * boxQ4B volA A om Φ p x := by
  unfold boxQ4B
  simp only [Work.hlocWire.boxQInd_smul, Work.hlocWire.boxPInd_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- `Q₄` is homogeneous of degree two. -/
lemma boxQ4_smul {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ)
    (t : ℝ) :
    boxQ4 volA ℓ A w om (t • Φ) = t ^ 2 * boxQ4 volA ℓ A w om Φ := by
  unfold boxQ4
  simp only [boxQ4B_smul]
  rw [sum_int_sq_scale]
  ring

/-- `boxQSum` is homogeneous of degree two. -/
lemma boxQSum_smul {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ)
    (t : ℝ) :
    boxQSum volA ℓ μ A w w1 w2 om (t • Φ)
      = t ^ 2 * boxQSum volA ℓ μ A w w1 w2 om Φ := by
  unfold boxQSum
  rw [boxQ0_smul, boxQ1_smul, boxQ2_smul, boxQ3_smul, boxQ4_smul]
  ring

theorem boxQSumScaleB1 {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (t : ℝ) :
    Work.BoseFixB1S.boxQSum volA ℓ μ A w w1 w2 om (fun x => t * Φ x)
      = t ^ 2 * Work.BoseFixB1S.boxQSum volA ℓ μ A w w1 w2 om Φ :=
  boxQSum_smul volA ℓ μ A w w1 w2 om Φ t

end Work.BoseFixB1S
