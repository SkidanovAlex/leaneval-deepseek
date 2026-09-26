/-
# The algebraic decomposition of `K_-^{(d)}` in terms of the cusp bracket

`Work.Kernels.KMinus` is defined through the matrix `Υ_-^{(d)}`; writing out the matrix product
expresses it as `(kpre z τ)⁻¹` times an explicit bracket (CKMRV Theorem 4.9):

* `KMinus8_eq`  : `K_-^{(8)}(τ,z) = (kpre z τ)⁻¹ * bracket8e ℓ z τ`,
* `KMinus24_eq` : `K_-^{(24)}(τ,z) = (kpre z τ)⁻¹ * bracket24e ℓ z τ`.

This file is a *self-contained copy* of that reduction: it depends only on `Kernels` and
`KMinusCuspDefs`, so that the cusp-tail estimate for `K_-` does not have to import the
(comparatively heavy) module `Work.Residues.KMinus_isBigO_atImInfty` with its analytic cusp
bounds.  The proof is the same row/column bookkeeping as in the original.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Classical
import Submission.Work.Residues.KMinusCuspDefs

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold Topology

namespace Work.Asymptotics.Compact

open Work.Kernels

/-! ### The matrices `B` and the vectors as functions -/

/-- The `d = 8` matrix `B₈` as a function of its entries. -/
def B8f (τ : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-2 : ℂ) * c1728, 0, 0; 0, 1, -1; 0, c1728 - jInvariantFun τ, jInvariantFun τ]

/-- The `d = 24` matrix `B₂₄` as a function of its entries. -/
def B24f (τ z : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-2 : ℂ) * c1728, (-2 : ℂ) * c1728 * (jInvariantFun τ - jInvariantFun z), 0;
     0, jInvariantFun τ + 2 * (jInvariantFun τ - jInvariantFun z), -1;
     0, c1728 - 2 * (jInvariantFun τ - jInvariantFun z) - jInvariantFun τ, 1]

/-- The τ-vector `(f₄, f₂, f₀) = (E₄, E₁₄/Δ, 1)` of `d = 8`. -/
def dvec8 (τ : ℍ) (i : Fin 3) : ℂ :=
  if i = 0 then E4Fun τ else if i = 1 then E14Fun τ / DeltaFun τ else 1

/-- The z-vector `(f₁₀, f₈, f₆) = (E₁₀, E₈, E₆)` of `d = 8`. -/
def evec8 (z : ℍ) (j : Fin 3) : ℂ :=
  if j = 0 then E10Fun z else if j = 1 then E8Fun z else E6Fun z

/-- The τ-vector `(f₁₂, f₁₀, f₈) = (Δ, E₁₀, E₈)` of `d = 24`. -/
def dvec24 (τ : ℍ) (i : Fin 3) : ℂ :=
  if i = 0 then DeltaFun τ else if i = 1 then E10Fun τ else E8Fun τ

/-- The z-vector `(f₂, f₀, f_{-2}) = (E₁₄/Δ, 1, E₁₀/Δ)` of `d = 24`. -/
def evec24 (z : ℍ) (j : Fin 3) : ℂ :=
  if j = 0 then E14Fun z / DeltaFun z else if j = 1 then 1 else E10Fun z / DeltaFun z

/-! ### The values of `B` and of the two vectors -/

lemma B8_00 (τ : ℍ) : B8f τ 0 0 = (-2 : ℂ) * c1728 := by simp [B8f]
lemma B8_01 (τ : ℍ) : B8f τ 0 1 = 0 := by simp [B8f]
lemma B8_02 (τ : ℍ) : B8f τ 0 2 = 0 := by simp [B8f]
lemma B8_10 (τ : ℍ) : B8f τ 1 0 = 0 := by simp [B8f]
lemma B8_11 (τ : ℍ) : B8f τ 1 1 = 1 := by simp [B8f]
lemma B8_12 (τ : ℍ) : B8f τ 1 2 = -1 := by simp [B8f]
lemma B8_20 (τ : ℍ) : B8f τ 2 0 = 0 := by simp [B8f]
lemma B8_21 (τ : ℍ) : B8f τ 2 1 = c1728 - jInvariantFun τ := by simp [B8f]
lemma B8_22 (τ : ℍ) : B8f τ 2 2 = jInvariantFun τ := by simp [B8f]

lemma B24_00 (τ z : ℍ) : B24f τ z 0 0 = (-2 : ℂ) * c1728 := by simp [B24f]
lemma B24_01 (τ z : ℍ) :
    B24f τ z 0 1 = (-2 : ℂ) * c1728 * (jInvariantFun τ - jInvariantFun z) := by simp [B24f]
lemma B24_02 (τ z : ℍ) : B24f τ z 0 2 = 0 := by simp [B24f]
lemma B24_10 (τ z : ℍ) : B24f τ z 1 0 = 0 := by simp [B24f]
lemma B24_11 (τ z : ℍ) :
    B24f τ z 1 1 = jInvariantFun τ + 2 * (jInvariantFun τ - jInvariantFun z) := by simp [B24f]
lemma B24_12 (τ z : ℍ) : B24f τ z 1 2 = -1 := by simp [B24f]
lemma B24_20 (τ z : ℍ) : B24f τ z 2 0 = 0 := by simp [B24f]
lemma B24_21 (τ z : ℍ) :
    B24f τ z 2 1 = c1728 - 2 * (jInvariantFun τ - jInvariantFun z) - jInvariantFun τ := by
  simp [B24f]
lemma B24_22 (τ z : ℍ) : B24f τ z 2 2 = 1 := by simp [B24f]

lemma dvec8_0 (τ : ℍ) : dvec8 τ 0 = E4Fun τ := by simp [dvec8]
lemma dvec8_1 (τ : ℍ) : dvec8 τ 1 = E14Fun τ / DeltaFun τ := by simp [dvec8]
lemma dvec8_2 (τ : ℍ) : dvec8 τ 2 = 1 := by simp [dvec8]
lemma evec8_0 (z : ℍ) : evec8 z 0 = E10Fun z := by simp [evec8]
lemma evec8_1 (z : ℍ) : evec8 z 1 = E8Fun z := by simp [evec8]
lemma evec8_2 (z : ℍ) : evec8 z 2 = E6Fun z := by simp [evec8]
lemma dvec24_0 (τ : ℍ) : dvec24 τ 0 = DeltaFun τ := by simp [dvec24]
lemma dvec24_1 (τ : ℍ) : dvec24 τ 1 = E10Fun τ := by simp [dvec24]
lemma dvec24_2 (τ : ℍ) : dvec24 τ 2 = E8Fun τ := by simp [dvec24]
lemma evec24_0 (z : ℍ) : evec24 z 0 = E14Fun z / DeltaFun z := by simp [evec24]
lemma evec24_1 (z : ℍ) : evec24 z 1 = 1 := by simp [evec24]
lemma evec24_2 (z : ℍ) : evec24 z 2 = E10Fun z / DeltaFun z := by simp [evec24]

/-! ### `UpsilonMinus` in terms of the entries -/

lemma um8_eq (τ z : ℍ) : UpsilonMinus 8 τ z = (Work.Residues.kpre z τ)⁻¹ • (PiMat ![4,2,0] τ * B8f τ * PiMat ![10,8,6] z) := by
  simp only [UpsilonMinus, B8f, Work.Residues.kpre, if_true]

lemma um24_eq (τ z : ℍ) :
    UpsilonMinus 24 τ z = (Work.Residues.kpre z τ)⁻¹ • (PiMat ![12,10,8] τ * B24f τ z * PiMat ![2,0,-2] z) := by
  simp only [UpsilonMinus, B24f, Work.Residues.kpre]
  rw [if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  simp only [if_true]

lemma um8_apply (τ z : ℍ) (i j : Fin 3) : UpsilonMinus 8 τ z i j =
    (Work.Residues.kpre z τ)⁻¹ * (dvec8 τ i * B8f τ i j * evec8 z j) := by
  rw [um8_eq]
  simp only [Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) only [B8_00, B8_01, B8_02, B8_10, B8_11, B8_12,
      B8_20, B8_21, B8_22, dvec8_0, dvec8_1, dvec8_2, evec8_0, evec8_1, evec8_2,
      PiMat, dvec8, evec8, B8f, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three,
      fk, if_true, if_false, smul_eq_mul, Fin.reduceFinMk] <;>
    ring

lemma um24_apply (τ z : ℍ) (i j : Fin 3) : UpsilonMinus 24 τ z i j =
    (Work.Residues.kpre z τ)⁻¹ * (dvec24 τ i * B24f τ z i j * evec24 z j) := by
  rw [um24_eq]
  simp only [Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) only [B24_00, B24_01, B24_02, B24_10, B24_11, B24_12,
      B24_20, B24_21, B24_22, dvec24_0, dvec24_1, dvec24_2, evec24_0, evec24_1, evec24_2,
      PiMat, dvec24, evec24, B24f, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three,
      fk, if_true, if_false, smul_eq_mul, Fin.reduceFinMk] <;>
    ring

/-! ### The row sums -/

lemma psiVec_0 (ℓ : LogLambdaData) (τ : ℍ) : psiVec ℓ τ 0 = 1 := by simp [psiVec]
lemma psiVec_1 (ℓ : LogLambdaData) (τ : ℍ) : psiVec ℓ τ 1 = psi2 ℓ τ := by simp [psiVec]
lemma psiVec_2 (ℓ : LogLambdaData) (τ : ℍ) : psiVec ℓ τ 2 = psi4 ℓ τ := by simp [psiVec]
lemma psitVec_0 (ℓ : LogLambdaData) (z : ℍ) : psitVec ℓ z 0 = ℓ.L z := by simp [psitVec]
lemma psitVec_1 (ℓ : LogLambdaData) (z : ℍ) : psitVec ℓ z 1 = WFun z := by simp [psitVec]
lemma psitVec_2 (ℓ : LogLambdaData) (z : ℍ) :
    psitVec ℓ z 2 = UFun z ^ 2 - VFun z ^ 2 := by simp [psitVec]

lemma row8_zero (ℓ : LogLambdaData) (τ z : ℍ) :
    (∑ j : Fin 3, B8f τ 0 j * evec8 z j * psitVec ℓ z j) =
      ((-2 : ℂ) * c1728) * E10Fun z * ℓ.L z := by
  rw [Fin.sum_univ_three, B8_00, B8_01, B8_02, evec8_0, evec8_1, evec8_2,
    psitVec_0, psitVec_1, psitVec_2]
  ring

lemma row8_one (ℓ : LogLambdaData) (τ z : ℍ) :
    (∑ j : Fin 3, B8f τ 1 j * evec8 z j * psitVec ℓ z j) =
      E8Fun z * WFun z - E6Fun z * (UFun z ^ 2 - VFun z ^ 2) := by
  rw [Fin.sum_univ_three, B8_10, B8_11, B8_12, evec8_0, evec8_1, evec8_2,
    psitVec_0, psitVec_1, psitVec_2]
  ring

lemma row8_two (ℓ : LogLambdaData) (τ z : ℍ) :
    (∑ j : Fin 3, B8f τ 2 j * evec8 z j * psitVec ℓ z j) =
      (c1728 - jInvariantFun τ) * E8Fun z * WFun z
        + jInvariantFun τ * E6Fun z * (UFun z ^ 2 - VFun z ^ 2) := by
  rw [Fin.sum_univ_three, B8_20, B8_21, B8_22, evec8_0, evec8_1, evec8_2,
    psitVec_0, psitVec_1, psitVec_2]
  ring

lemma row24_zero (ℓ : LogLambdaData) (τ z : ℍ) :
    (∑ j : Fin 3, B24f τ z 0 j * evec24 z j * psitVec ℓ z j) =
      ((-2 : ℂ) * c1728) * (E14Fun z / DeltaFun z) * ℓ.L z
        + ((-2 : ℂ) * c1728) * (jInvariantFun τ - jInvariantFun z) * WFun z := by
  rw [Fin.sum_univ_three, B24_00, B24_01, B24_02, evec24_0, evec24_1, evec24_2,
    psitVec_0, psitVec_1, psitVec_2]
  ring

lemma row24_one (ℓ : LogLambdaData) (τ z : ℍ) :
    (∑ j : Fin 3, B24f τ z 1 j * evec24 z j * psitVec ℓ z j) =
      (jInvariantFun τ + 2 * (jInvariantFun τ - jInvariantFun z)) * WFun z
        - (E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2) := by
  rw [Fin.sum_univ_three, B24_10, B24_11, B24_12, evec24_0, evec24_1, evec24_2,
    psitVec_0, psitVec_1, psitVec_2]
  ring

lemma row24_two (ℓ : LogLambdaData) (τ z : ℍ) :
    (∑ j : Fin 3, B24f τ z 2 j * evec24 z j * psitVec ℓ z j) =
      (c1728 - 2 * (jInvariantFun τ - jInvariantFun z) - jInvariantFun τ) * WFun z
        + (E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2) := by
  rw [Fin.sum_univ_three, B24_20, B24_21, B24_22, evec24_0, evec24_1, evec24_2,
    psitVec_0, psitVec_1, psitVec_2]
  ring

/-! ### The decomposition of `K_-` -/

lemma KMinus_eq_row (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) :
    KMinus ℓ d τ z = ∑ i : Fin 3, psiVec ℓ τ i *
      (∑ j : Fin 3, UpsilonMinus d τ z i j * psitVec ℓ z j) := by
  simp only [KMinus, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma col8 (ℓ : LogLambdaData) (τ z : ℍ) (i : Fin 3) :
    (∑ j : Fin 3, UpsilonMinus 8 τ z i j * psitVec ℓ z j) =
      (Work.Residues.kpre z τ)⁻¹ * dvec8 τ i * (∑ j : Fin 3, B8f τ i j * evec8 z j * psitVec ℓ z j) := by
  have h : ∀ j : Fin 3, UpsilonMinus 8 τ z i j * psitVec ℓ z j =
      (Work.Residues.kpre z τ)⁻¹ * dvec8 τ i * (B8f τ i j * evec8 z j * psitVec ℓ z j) := by
    intro j
    rw [um8_apply]
    ring
  simp only [h]
  rw [Finset.mul_sum]

lemma col24 (ℓ : LogLambdaData) (τ z : ℍ) (i : Fin 3) :
    (∑ j : Fin 3, UpsilonMinus 24 τ z i j * psitVec ℓ z j) =
      (Work.Residues.kpre z τ)⁻¹ * dvec24 τ i * (∑ j : Fin 3, B24f τ z i j * evec24 z j * psitVec ℓ z j) := by
  have h : ∀ j : Fin 3, UpsilonMinus 24 τ z i j * psitVec ℓ z j =
      (Work.Residues.kpre z τ)⁻¹ * dvec24 τ i * (B24f τ z i j * evec24 z j * psitVec ℓ z j) := by
    intro j
    rw [um24_apply]
    ring
  simp only [h]
  rw [Finset.mul_sum]

/-- **The `d = 8` decomposition.** -/
theorem KMinus8_eq (ℓ : LogLambdaData) (τ z : ℍ) :
    KMinus ℓ 8 τ z = (Work.Residues.kpre z τ)⁻¹ *
      (((-2 : ℂ) * c1728) * E4Fun τ * E10Fun z * ℓ.L z
        + psi2 ℓ τ * (E14Fun τ / DeltaFun τ) * (E8Fun z * WFun z
            - E6Fun z * (UFun z ^ 2 - VFun z ^ 2))
        + psi4 ℓ τ * ((c1728 - jInvariantFun τ) * E8Fun z * WFun z
            + jInvariantFun τ * E6Fun z * (UFun z ^ 2 - VFun z ^ 2))) := by
  rw [KMinus_eq_row, Fin.sum_univ_three, psiVec_0, psiVec_1, psiVec_2]
  rw [col8 ℓ τ z 0, col8 ℓ τ z 1, col8 ℓ τ z 2]
  rw [row8_zero, row8_one, row8_two]
  simp only [dvec8_0, dvec8_1, dvec8_2]
  ring

lemma col24b (ℓ : LogLambdaData) (τ z : ℍ) (i : Fin 3) :
    (∑ j : Fin 3, UpsilonMinus 24 τ z i j * psitVec ℓ z j) =
      (Work.Residues.kpre z τ)⁻¹ * dvec24 τ i * (∑ j : Fin 3, B24f τ z i j * evec24 z j * psitVec ℓ z j) :=
  col24 ℓ τ z i

/-- **The `d = 24` decomposition.** -/
theorem KMinus24_eq (ℓ : LogLambdaData) (τ z : ℍ) :
    KMinus ℓ 24 τ z = (Work.Residues.kpre z τ)⁻¹ *
      (DeltaFun τ * (((-2 : ℂ) * c1728) * (E14Fun z / DeltaFun z) * ℓ.L z
            + ((-2 : ℂ) * c1728) * (jInvariantFun τ - jInvariantFun z) * WFun z)
        + psi2 ℓ τ * E10Fun τ *
            ((jInvariantFun τ + 2 * (jInvariantFun τ - jInvariantFun z)) * WFun z
              - (E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2))
        + psi4 ℓ τ * E8Fun τ *
            ((c1728 - 2 * (jInvariantFun τ - jInvariantFun z) - jInvariantFun τ) * WFun z
              + (E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2))) := by
  rw [KMinus_eq_row, Fin.sum_univ_three, psiVec_0, psiVec_1, psiVec_2]
  rw [col24 ℓ τ z 0, col24 ℓ τ z 1, col24 ℓ τ z 2]
  rw [row24_zero, row24_one, row24_two]
  simp only [dvec24_0, dvec24_1, dvec24_2]
  ring_nf

end Work.Asymptotics.Compact
