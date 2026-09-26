/-
# The cusp expansion of `K^{(d)}` in terms of the explicit model `MK`, without `KPlusXiDefs`

This file proves `Work.Asymptotics.CuspExp.kernelKfun_cuspExp`:

`‖K^{(d)}(τ,z) - MK ℓ d τ z‖ ≤ C (1+|Re z|+Im z)^3 ‖E(z)‖`  (`E(z) = e^{πiz}`)

for `d = 8` and `d = 24`, uniformly for `τ` in a compact `K ⊆ ℍ` and `T ≤ Im z`.

The workspace contains a name clash: `Submission/Work/Asymptotics/KPlusXiDefs.lean` and
`Submission/Work/Asymptotics/MiddleRange/Main.lean` both declare
`Work.Asymptotics.continuous_jInvariantFun`, so no lean environment may contain both.  The
existing proofs of the two estimates (`CuspExp/kernel8_cuspExp.lean`,
`CuspExp/kernel24_defs.lean`, `CuspExp/kernel24_cuspExp.lean`) import `KPlusXiDefs`
(for the two Eisenstein-series estimates `E2Fun_two_term`, `E2Fun_bound`), and hence cannot be
imported here.  Instead their statements and proofs are reproduced in this file, in the
auxiliary namespace `Work.Asymptotics.CuspExp.Loc`, with the two `E2`-estimates taken from the
`KPlusXiDefs`-free copy `Submission.Work.Asymptotics.MFix.KXiDefs` (whose `E2Fun_two_term`,
`E2Fun_bound` are proven from `Submission.Work.Residues.QExpansionTail` and
`Submission.Work.Modular.E2_qExpansion_coeff`).  Nothing else from `KPlusXiDefs` is used: the
input `Xi24_eq` of `kernel24_defs`/`kernel24_cuspExp` is only needed for the `Xi`-identities,
which those files do not use.  All the declarations are placed in the namespace `...Loc` so
that this module can be imported side by side with the original `CuspExp` modules.
-/
import Mathlib
import Submission.Work.Asymptotics.CuspExp.Models
import Submission.Work.Asymptotics.CuspExp.Basic
import Submission.Work.Asymptotics.CuspExp.Exp
import Submission.Work.Asymptotics.MFix.KXiDefs
import Submission.Work.Asymptotics.cusp_inv_divisor_second
import Submission.Work.Asymptotics.cusp_invJ_second
import Submission.Work.Asymptotics.cusp_U_second
import Submission.Work.Asymptotics.cusp_W_second
import Submission.Work.Asymptotics.cusp_D_second
import Submission.Work.Asymptotics.cusp_L_second
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.MiddleRange.exists_bound_fk
import Submission.Work.Asymptotics.MiddleRange.exists_bound_phiVec_phitVec
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Asymptotics.Ncusp_bound_ball

namespace Work.Residues.Loc

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold

open Work.Kernels

noncomputable section

/-! ## The explicit decomposition of `K_-^{(d)}` (copied from
`Submission/Work/Residues/KMinus_isBigO_atImInfty.lean`, with the same proofs)

`Υ_-^{(d)}` is a product of three explicit matrices; expanding it gives the two decompositions
`KMinus8_eq` and `KMinus24_eq` used by the cusp expansion.  The originals live in
`Work.Residues.KMinus_isBigO_atImInfty`, whose import of `KPlus_isBigO_atImInfty` (a file
unrelated to these identities, and one of the endpoints of the `continuous_jInvariantFun` name
clash) makes that module unusable here; the statements and proofs are therefore reproduced,
unchanged, in this namespace. -/

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

lemma um8_eq (τ z : ℍ) : UpsilonMinus 8 τ z = (kpre z τ)⁻¹ • (PiMat ![4,2,0] τ * B8f τ * PiMat ![10,8,6] z) := by
  simp only [UpsilonMinus, B8f, kpre, if_true]

lemma um24_eq (τ z : ℍ) :
    UpsilonMinus 24 τ z = (kpre z τ)⁻¹ • (PiMat ![12,10,8] τ * B24f τ z * PiMat ![2,0,-2] z) := by
  simp only [UpsilonMinus, B24f, kpre]
  rw [if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  simp only [if_true]

lemma um8_apply (τ z : ℍ) (i j : Fin 3) : UpsilonMinus 8 τ z i j =
    (kpre z τ)⁻¹ * (dvec8 τ i * B8f τ i j * evec8 z j) := by
  rw [um8_eq]
  simp only [Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) only [B8_00, B8_01, B8_02, B8_10, B8_11, B8_12,
      B8_20, B8_21, B8_22, dvec8_0, dvec8_1, dvec8_2, evec8_0, evec8_1, evec8_2,
      PiMat, dvec8, evec8, B8f, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three,
      fk, if_true, if_false, smul_eq_mul, Fin.reduceFinMk] <;>
    ring

lemma um24_apply (τ z : ℍ) (i j : Fin 3) : UpsilonMinus 24 τ z i j =
    (kpre z τ)⁻¹ * (dvec24 τ i * B24f τ z i j * evec24 z j) := by
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
      (kpre z τ)⁻¹ * dvec8 τ i * (∑ j : Fin 3, B8f τ i j * evec8 z j * psitVec ℓ z j) := by
  have h : ∀ j : Fin 3, UpsilonMinus 8 τ z i j * psitVec ℓ z j =
      (kpre z τ)⁻¹ * dvec8 τ i * (B8f τ i j * evec8 z j * psitVec ℓ z j) := by
    intro j
    rw [um8_apply]
    ring
  simp only [h]
  rw [Finset.mul_sum]

lemma col24 (ℓ : LogLambdaData) (τ z : ℍ) (i : Fin 3) :
    (∑ j : Fin 3, UpsilonMinus 24 τ z i j * psitVec ℓ z j) =
      (kpre z τ)⁻¹ * dvec24 τ i * (∑ j : Fin 3, B24f τ z i j * evec24 z j * psitVec ℓ z j) := by
  have h : ∀ j : Fin 3, UpsilonMinus 24 τ z i j * psitVec ℓ z j =
      (kpre z τ)⁻¹ * dvec24 τ i * (B24f τ z i j * evec24 z j * psitVec ℓ z j) := by
    intro j
    rw [um24_apply]
    ring
  simp only [h]
  rw [Finset.mul_sum]

/-- **The `d = 8` decomposition.** -/
theorem KMinus8_eq (ℓ : LogLambdaData) (τ z : ℍ) :
    KMinus ℓ 8 τ z = (kpre z τ)⁻¹ *
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
      (kpre z τ)⁻¹ * dvec24 τ i * (∑ j : Fin 3, B24f τ z i j * evec24 z j * psitVec ℓ z j) :=
  col24 ℓ τ z i

/-- **The `d = 24` decomposition.** -/
theorem KMinus24_eq (ℓ : LogLambdaData) (τ z : ℍ) :
    KMinus ℓ 24 τ z = (kpre z τ)⁻¹ *
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

end

end Work.Residues.Loc

namespace Work.Asymptotics.CuspExp.Loc



open UpperHalfPlane
open Work.Asymptotics
open Work.Kernels.TildeFacts

/-- `E₂` is bounded on `{1 ≤ Im τ}` (copy of `Work.Asymptotics.MFix.E2Fun_bound`, the
`KPlusXiDefs`-free version of `Work.Asymptotics.E2Fun_bound`). -/
lemma E2Fun_bound : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖Work.Kernels.E2Fun τ‖ ≤ C :=
  Work.Asymptotics.MFix.E2Fun_bound

/-- `E₂ = 1 - 24 q + O(q²)` (copy of `Work.Asymptotics.MFix.E2Fun_two_term`, the
`KPlusXiDefs`-free version of `Work.Asymptotics.E2Fun_two_term`). -/
lemma E2Fun_two_term : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ‖ ≤
      C * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
  Work.Asymptotics.MFix.E2Fun_two_term

noncomputable section

/-! ## §1  Elementary glue -/

lemma qParamFun_eq_Ept_sq (z : ℍ) : Work.Kernels.qParamFun z = Work.Residues.Ept z ^ 2 := by
  rw [Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]
  congr 1
  ring

lemma norm_qParamFun_eq_Ept_sq (z : ℍ) :
    ‖Work.Kernels.qParamFun z‖ = ‖Work.Residues.Ept z‖ ^ 2 := by
  rw [qParamFun_eq_Ept_sq, norm_pow]

lemma norm_qParamFun_le_one (z : ℍ) : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
  rw [norm_qParamFun_eq_Ept_sq]
  have h := Work.Residues.norm_Ept_lt_one z
  nlinarith [norm_nonneg (Work.Residues.Ept z)]

lemma norm_Ept_le_one' (z : ℍ) : ‖Work.Residues.Ept z‖ ≤ 1 :=
  le_of_lt (Work.Residues.norm_Ept_lt_one z)

lemma norm_Ept_pow_le_one (z : ℍ) (k : ℕ) : ‖Work.Residues.Ept z‖ ^ k ≤ 1 :=
  pow_le_one₀ (norm_nonneg _) (norm_Ept_le_one' z)

lemma norm_Ept_sq_le_one (z : ℍ) : ‖Work.Residues.Ept z‖ ^ 2 ≤ 1 := norm_Ept_pow_le_one z 2

lemma norm_ofReal_pi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
  have h : ‖((Real.pi : ℝ) : ℂ)‖ ^ 2 = Real.pi ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  nlinarith [norm_nonneg ((Real.pi : ℝ) : ℂ), Real.pi_pos]

lemma norm_six_I_div_pi : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, norm_ofReal_pi]

lemma norm_qParamFun_eq_exp (z : ℍ) :
    ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [Work.Kernels.qParamFun, Complex.norm_exp]
  congr 1
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (z : ℂ)
      = ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (z : ℂ)) by push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

lemma inv_norm_qParamFun_eq_exp (z : ℍ) :
    (‖Work.Kernels.qParamFun z‖)⁻¹ = Real.exp (2 * Real.pi * z.im) := by
  rw [norm_qParamFun_eq_exp, ← Real.exp_neg]
  congr 1
  ring

lemma one_add_coe_norm_le_two_cuspW (z : ℍ) : 1 + ‖(z : ℂ)‖ ≤ 2 * cuspW z := by
  have h1 : 1 ≤ cuspW z := cuspW_one_le z
  have h2 : ‖(z : ℂ)‖ ≤ cuspW z := coe_norm_le_cuspW z
  linarith

variable {K : Set ℍ} {T : ℝ}

/-- An estimate `‖f z‖ ≤ C ‖E z‖^k` for a function of `z` alone composes to a `CuspBdd`. -/
lemma cuspBdd_of_w {f : ℍ → ℂ} {k : ℕ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, T ≤ z.im → ‖f z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ k) :
    CuspBdd K T (fun _ z => f z) (k : ℤ) 0 := by
  refine ⟨C, hC, fun τ hτ z hz => ?_⟩
  simpa only [cuspG, Real.rpow_zero, one_mul, zpow_natCast] using h z hz

/-- An estimate `‖f z‖ ≤ C (1+‖z‖) ‖E z‖^k` composes to a `CuspBdd` of weight `1`. -/
lemma cuspBdd_of_w_coe {f : ℍ → ℂ} {k : ℕ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, T ≤ z.im → ‖f z‖ ≤ C * (1 + ‖(z : ℂ)‖) * ‖Work.Residues.Ept z‖ ^ k) :
    CuspBdd K T (fun _ z => f z) (k : ℤ) 1 := by
  refine ⟨2 * C, by positivity, fun τ hτ z hz => ?_⟩
  have hb := h z hz
  have h1 := one_add_coe_norm_le_two_cuspW z
  have h2 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ k := by positivity
  have h3 : (0 : ℝ) ≤ C := hC.le
  rw [cuspG, Real.rpow_one, zpow_natCast]
  calc ‖f z‖ ≤ C * (1 + ‖(z : ℂ)‖) * ‖Work.Residues.Ept z‖ ^ k := hb
    _ ≤ C * (2 * cuspW z) * ‖Work.Residues.Ept z‖ ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) h2
    _ = 2 * C * (cuspW z * ‖Work.Residues.Ept z‖ ^ k) := by ring

/-- A bounded function of `z` alone. -/
lemma cuspBdd_of_bdd {f : ℍ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, T ≤ z.im → ‖f z‖ ≤ C) :
    CuspBdd K T (fun _ z => f z) 0 0 := by
  refine ⟨C, hC, fun τ hτ z hz => ?_⟩
  simpa only [cuspG, Real.rpow_zero, zpow_zero, mul_one, one_mul] using h z hz

/-- A function of `τ` bounded on `K` is `O(1)`. -/
lemma cuspBdd_tau {c : ℍ → ℂ} {B : ℝ} (hB : 0 < B) (h : ∀ τ ∈ K, ‖c τ‖ ≤ B) :
    CuspBdd K T (fun τ _ => c τ) 0 0 :=
  CuspBdd.of_bound hB (fun τ hτ _ _ => h τ hτ)

/-- A constant function. -/
lemma cuspBdd_const (a : ℂ) : CuspBdd K T (fun _ _ => a) 0 0 :=
  CuspBdd.of_bound (by positivity : (0 : ℝ) < ‖a‖ + 1)
    (fun _ _ _ _ => by linarith [norm_nonneg a])

/-- Continuity gives a bound on a compact set of `τ`. -/
lemma cuspBdd_tauAtom {c : ℍ → ℂ} (hc : Continuous c) (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ τ ∈ K, ‖c τ‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max B 0 + 1, by positivity,
    fun τ hτ => le_trans (hB τ hτ) (by linarith [le_max_left B 0])⟩

/-! ## §2  Size bounds of the `z`-atoms on `1 ≤ Im z` -/

lemma bdd_E4 : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E4Fun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E4FunSecondOrder
  refine ⟨241 + C, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have h4 : C * ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ C := by
    have hq2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 1 := by
      have hq := norm_qParamFun_le_one z
      nlinarith [norm_nonneg (Work.Kernels.qParamFun z)]
    nlinarith [hC.le]
  have h3 : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z‖ ≤ 1 + 240 * ‖Work.Kernels.qParamFun z‖ := by
    calc ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z‖
        ≤ ‖(1 : ℂ)‖ + ‖(240 : ℂ) * Work.Kernels.qParamFun z‖ := norm_add_le _ _
      _ = 1 + 240 * ‖Work.Kernels.qParamFun z‖ := by
          rw [norm_one, norm_mul, Complex.norm_ofNat]
  have hEq : Work.Kernels.E4Fun z
      = (Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z)
        + (1 + 240 * Work.Kernels.qParamFun z) := by ring
  rw [hEq]
  calc ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z)
        + (1 + 240 * Work.Kernels.qParamFun z)‖
      ≤ ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
        + ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z‖ := norm_add_le _ _
    _ ≤ C + (1 + 240 * ‖Work.Kernels.qParamFun z‖) :=
        add_le_add (le_trans h1 (by linarith)) h3
    _ ≤ 241 + C := by
        have hq := norm_qParamFun_le_one z
        linarith

lemma bdd_E6 : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E6Fun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E6FunSecondOrder
  refine ⟨505 + C, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have h4 : C * ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ C := by
    have hq2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 1 := by
      have hq := norm_qParamFun_le_one z
      nlinarith [norm_nonneg (Work.Kernels.qParamFun z)]
    nlinarith [hC.le]
  have h3 : ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z‖ ≤ 1 + 504 * ‖Work.Kernels.qParamFun z‖ := by
    calc ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z‖
        ≤ ‖(1 : ℂ)‖ + ‖(504 : ℂ) * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
      _ = 1 + 504 * ‖Work.Kernels.qParamFun z‖ := by
          rw [norm_one, norm_mul, Complex.norm_ofNat]
  have hEq : Work.Kernels.E6Fun z
      = (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z)
        + (1 - 504 * Work.Kernels.qParamFun z) := by ring
  rw [hEq]
  calc ‖(Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z)
        + (1 - 504 * Work.Kernels.qParamFun z)‖
      ≤ ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z‖
        + ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z‖ := norm_add_le _ _
    _ ≤ C + (1 + 504 * ‖Work.Kernels.qParamFun z‖) :=
        add_le_add (le_trans h1 (by linarith)) h3
    _ ≤ 505 + C := by
        have hq := norm_qParamFun_le_one z
        linarith

lemma bdd_E8 : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E8Fun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := bdd_E4
  refine ⟨C ^ 2, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have hEq : Work.Kernels.E8Fun z = Work.Kernels.E4Fun z ^ 2 := rfl
  rw [hEq, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

lemma bdd_E10 : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E10Fun z‖ ≤ C := by
  obtain ⟨C4, hC4, h4⟩ := bdd_E4
  obtain ⟨C6, hC6, h6⟩ := bdd_E6
  refine ⟨C4 * C6, by positivity, fun z hz => ?_⟩
  have hEq : Work.Kernels.E10Fun z = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z := rfl
  rw [hEq, norm_mul]
  exact mul_le_mul (h4 z hz) (h6 z hz) (norm_nonneg _) hC4.le

lemma bdd_mE4 : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖mE4 z‖ ≤ C := by
  refine ⟨241, by norm_num, fun z _ => ?_⟩
  have hq := norm_qParamFun_le_one z
  have hEq : mE4 z = (1 : ℂ) + 240 * Work.Kernels.qParamFun z := by simp only [mE4, mq]
  rw [hEq]
  calc ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z‖
      ≤ ‖(1 : ℂ)‖ + ‖(240 : ℂ) * Work.Kernels.qParamFun z‖ := norm_add_le _ _
    _ = 1 + 240 * ‖Work.Kernels.qParamFun z‖ := by
        rw [norm_one, norm_mul, Complex.norm_ofNat]
    _ ≤ 241 := by linarith

lemma bdd_mE6 : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖mE6 z‖ ≤ C := by
  refine ⟨505, by norm_num, fun z _ => ?_⟩
  have hq := norm_qParamFun_le_one z
  have hEq : mE6 z = (1 : ℂ) - 504 * Work.Kernels.qParamFun z := by simp only [mE6, mq]
  rw [hEq]
  calc ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z‖
      ≤ ‖(1 : ℂ)‖ + ‖(504 : ℂ) * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
    _ = 1 + 504 * ‖Work.Kernels.qParamFun z‖ := by
        rw [norm_one, norm_mul, Complex.norm_ofNat]
    _ ≤ 505 := by linarith

lemma bdd_mE8 : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖mE8 z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := bdd_mE4
  refine ⟨C * C, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have hEq : mE8 z = mE4 z * mE4 z := rfl
  rw [hEq, norm_mul]
  exact mul_le_mul h1 h1 (norm_nonneg _) hC.le

lemma bdd_mE10 : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖mE10 z‖ ≤ C := by
  obtain ⟨C4, hC4, h4⟩ := bdd_mE4
  obtain ⟨C6, hC6, h6⟩ := bdd_mE6
  refine ⟨C4 * C6, by positivity, fun z hz => ?_⟩
  have hEq : mE10 z = mE4 z * mE6 z := rfl
  rw [hEq, norm_mul]
  exact mul_le_mul (h4 z hz) (h6 z hz) (norm_nonneg _) hC4.le

lemma bdd_mW_val (z : ℍ) : ‖mW z‖ ≤ 33 := by
  have hq := norm_qParamFun_le_one z
  have hE1 := norm_Ept_le_one' z
  have hEq : mW z = (1 : ℂ) - 8 * Work.Residues.Ept z + 24 * Work.Kernels.qParamFun z := by
    simp only [mW, mq]
  rw [hEq]
  calc ‖(1 : ℂ) - 8 * Work.Residues.Ept z + 24 * Work.Kernels.qParamFun z‖
      ≤ ‖(1 : ℂ) - 8 * Work.Residues.Ept z‖ + ‖(24 : ℂ) * Work.Kernels.qParamFun z‖ :=
        norm_add_le _ _
    _ ≤ (1 + 8) + 24 := by
        refine add_le_add ?_ ?_
        · calc ‖(1 : ℂ) - 8 * Work.Residues.Ept z‖
              ≤ ‖(1 : ℂ)‖ + ‖(8 : ℂ) * Work.Residues.Ept z‖ := norm_sub_le _ _
            _ ≤ 1 + 8 := by
                rw [norm_one, norm_mul, Complex.norm_ofNat]
                linarith
        · rw [norm_mul, Complex.norm_ofNat]
          linarith
    _ = 33 := by norm_num

lemma bdd_mW : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖mW z‖ ≤ C :=
  ⟨33, by norm_num, fun z _ => bdd_mW_val z⟩

lemma bdd_W : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.WFun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := cusp_W_second
  refine ⟨C + 33, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have h1' : ‖Work.Kernels.WFun z - mW z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 3 := by
    have hEq : mW z = (1 : ℂ) - 8 * Work.Residues.Ept z + 24 * Work.Kernels.qParamFun z := by
      simp only [mW, mq]
    rw [hEq, qParamFun_eq_Ept_sq]
    exact h1
  have h2 : ‖mW z‖ ≤ 33 := bdd_mW_val z
  have h3 : C * ‖Work.Residues.Ept z‖ ^ 3 ≤ C := by
    have := norm_Ept_pow_le_one z 3
    nlinarith [hC.le]
  calc ‖Work.Kernels.WFun z‖ = ‖(Work.Kernels.WFun z - mW z) + mW z‖ := by
        congr 1; ring
    _ ≤ ‖Work.Kernels.WFun z - mW z‖ + ‖mW z‖ := norm_add_le _ _
    _ ≤ C + 33 := by linarith

lemma bdd_mD_val (z : ℍ) : ‖mD z‖ ≤ 161 := by
  have hq := norm_qParamFun_le_one z
  have hE1 := norm_Ept_le_one' z
  have hEq : mD z = (1 : ℂ) + 16 * Work.Residues.Ept z - 144 * Work.Kernels.qParamFun z := by
    simp only [mD, mq]
  rw [hEq]
  calc ‖(1 : ℂ) + 16 * Work.Residues.Ept z - 144 * Work.Kernels.qParamFun z‖
      ≤ ‖(1 : ℂ) + 16 * Work.Residues.Ept z‖ + ‖(144 : ℂ) * Work.Kernels.qParamFun z‖ :=
        norm_sub_le _ _
    _ ≤ (1 + 16) + 144 := by
        refine add_le_add ?_ ?_
        · calc ‖(1 : ℂ) + 16 * Work.Residues.Ept z‖
              ≤ ‖(1 : ℂ)‖ + ‖(16 : ℂ) * Work.Residues.Ept z‖ := norm_add_le _ _
            _ ≤ 1 + 16 := by
                rw [norm_one, norm_mul, Complex.norm_ofNat]
                linarith
        · rw [norm_mul, Complex.norm_ofNat]
          linarith
    _ = 161 := by norm_num

lemma bdd_mD : ∃ C : ℝ, 0 < C ∧
    ∀ z : ℍ, 1 ≤ z.im → ‖mD z‖ ≤ C :=
  ⟨161, by norm_num, fun z _ => bdd_mD_val z⟩

lemma bdd_D : ∃ C : ℝ, 0 < C ∧
    ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := cusp_D_second
  refine ⟨161 + C, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have h1' : ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - mD z‖ ≤
      C * ‖Work.Residues.Ept z‖ ^ 3 := by
    have hEq : mD z = (1 : ℂ) + 16 * Work.Residues.Ept z - 144 * Work.Kernels.qParamFun z := by
      simp only [mD, mq]
    rw [hEq, qParamFun_eq_Ept_sq]
    exact h1
  have h2 : ‖mD z‖ ≤ 161 := bdd_mD_val z
  have h3 : C * ‖Work.Residues.Ept z‖ ^ 3 ≤ C := by
    have := norm_Ept_pow_le_one z 3
    nlinarith [hC.le]
  calc ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖
      = ‖(Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - mD z) + mD z‖ := by
        congr 1; ring
    _ ≤ ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - mD z‖ + ‖mD z‖ := norm_add_le _ _
    _ ≤ 161 + C := by linarith


lemma bdd_Gt : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Gt z‖ ≤ C * (1 + ‖(z : ℂ)‖) ∧
    ‖mG z‖ ≤ C * (1 + ‖(z : ℂ)‖) ∧
    ‖Gt z - mG z‖ ≤ C * (1 + ‖(z : ℂ)‖) * ‖Work.Residues.Ept z‖ ^ 4 := by
  obtain ⟨C2, hC2, hE2⟩ := E2Fun_bound
  obtain ⟨C2', hC2', hE2'⟩ := E2Fun_two_term
  refine ⟨C2 + C2' + 100, by positivity, fun z hz => ?_⟩
  have hz0 : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have hq4 : ‖Work.Kernels.qParamFun z‖ ^ 2 = ‖Work.Residues.Ept z‖ ^ 4 := by
    rw [norm_qParamFun_eq_Ept_sq]; ring
  have hE2b := hE2 z hz
  have hE2b' := hE2' z hz
  have h6 : 6 / Real.pi ≤ 6 := by rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  have hGtEq : Gt z = (z : ℂ) * Work.Kernels.E2Fun z - 6 * Complex.I / (Real.pi : ℂ) := rfl
  have hmGEq : mG z = ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
      - 24 * (z : ℂ) * Work.Kernels.qParamFun z := rfl
  have hdiff : Gt z - mG z
      = (z : ℂ) * (Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z) := by
    rw [hGtEq, hmGEq]; ring
  have hGtn : ‖Gt z‖ ≤ ‖(z : ℂ)‖ * C2 + 6 / Real.pi := by
    rw [hGtEq]
    calc ‖(z : ℂ) * Work.Kernels.E2Fun z - 6 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(z : ℂ) * Work.Kernels.E2Fun z‖ + ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ ‖(z : ℂ)‖ * C2 + 6 / Real.pi := by
          have h := mul_le_mul_of_nonneg_left hE2b hz0
          rw [norm_mul, norm_six_I_div_pi]
          linarith
  have hmGn : ‖mG z‖ ≤ (‖(z : ℂ)‖ + 6) + 24 * ‖(z : ℂ)‖ := by
    rw [hmGEq]
    calc ‖((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) - 24 * (z : ℂ) * Work.Kernels.qParamFun z‖
        ≤ ‖(z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)‖
          + ‖(24 : ℂ) * (z : ℂ) * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
      _ ≤ (‖(z : ℂ)‖ + 6) + 24 * ‖(z : ℂ)‖ := by
          refine add_le_add ?_ ?_
          · calc ‖(z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)‖
                ≤ ‖(z : ℂ)‖ + ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
              _ ≤ ‖(z : ℂ)‖ + 6 := by rw [norm_six_I_div_pi]; linarith
          · rw [norm_mul, norm_mul, Complex.norm_ofNat]
            have h1 : ‖(z : ℂ)‖ * ‖Work.Kernels.qParamFun z‖ ≤ ‖(z : ℂ)‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_qParamFun_le_one z) hz0
            nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h2 : 6 / Real.pi ≤ 100 * (1 + ‖(z : ℂ)‖) := by nlinarith [h6, hz0]
    have h3 : ‖(z : ℂ)‖ * C2 ≤ C2 * (1 + ‖(z : ℂ)‖) := by nlinarith [hC2.le, hz0]
    calc ‖Gt z‖ ≤ ‖(z : ℂ)‖ * C2 + 6 / Real.pi := hGtn
      _ ≤ (C2 + C2' + 100) * (1 + ‖(z : ℂ)‖) := by
          nlinarith [h3, h2, hC2.le, hC2'.le, hz0]
  · have h2 : 6 ≤ 100 * (1 + ‖(z : ℂ)‖) := by nlinarith [h6, hz0]
    calc ‖mG z‖ ≤ (‖(z : ℂ)‖ + 6) + 24 * ‖(z : ℂ)‖ := hmGn
      _ ≤ (C2 + C2' + 100) * (1 + ‖(z : ℂ)‖) := by
          nlinarith [h2, hC2.le, hC2'.le, hz0]
  · rw [hdiff, norm_mul]
    calc ‖(z : ℂ)‖ * ‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z‖
        ≤ ‖(z : ℂ)‖ * (C2' * ‖Work.Kernels.qParamFun z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hE2b' hz0
      _ = C2' * ‖(z : ℂ)‖ * ‖Work.Residues.Ept z‖ ^ 4 := by rw [hq4]; ring
      _ ≤ (C2 + C2' + 100) * (1 + ‖(z : ℂ)‖) * ‖Work.Residues.Ept z‖ ^ 4 := by
          have h1 : ‖(z : ℂ)‖ ≤ 1 + ‖(z : ℂ)‖ := by linarith
          have h2 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ 4 := by positivity
          have h3 : C2' * ‖(z : ℂ)‖ ≤ (C2 + C2' + 100) * (1 + ‖(z : ℂ)‖) :=
            mul_le_mul (by linarith [hC2.le]) h1 hz0 (by linarith [hC2.le, hC2'.le])
          exact mul_le_mul_of_nonneg_right h3 h2

lemma bdd_L (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖ℓ.L z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  obtain ⟨C, hC, h⟩ := Classical.choose_spec (cusp_L_second ℓ)
  refine ⟨‖cuspL ℓ‖ + Real.pi + 20 + C, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  have hE3 : ‖Work.Residues.Ept z‖ ^ 3 ≤ 1 := norm_Ept_pow_le_one z 3
  have hCb : C * ‖Work.Residues.Ept z‖ ^ 3 ≤ C := by
    nlinarith [hC.le, hE3, norm_nonneg (Work.Residues.Ept z)]
  have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := norm_Ept_le_one' z
  have hE0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have hA1 : ‖(8 : ℂ) * Work.Residues.Ept z‖ ≤ 8 := by
    rw [norm_mul, Complex.norm_ofNat]; linarith
  have hA2 : ‖(12 : ℂ) * Work.Residues.Ept z ^ 2‖ ≤ 12 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]; nlinarith
  have hA3 : ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ ≤ Real.pi * ‖(z : ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_ofReal_pi]
  have hA : ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ - 8 * Work.Residues.Ept z
      + 12 * Work.Residues.Ept z ^ 2‖ ≤ Real.pi * ‖(z : ℂ)‖ + ‖cuspL ℓ‖ + 20 := by
    calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ - 8 * Work.Residues.Ept z
          + 12 * Work.Residues.Ept z ^ 2‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ - 8 * Work.Residues.Ept z‖
          + ‖(12 : ℂ) * Work.Residues.Ept z ^ 2‖ := norm_add_le _ _
      _ ≤ (Real.pi * ‖(z : ℂ)‖ + ‖cuspL ℓ‖ + 8) + 12 := by
          refine add_le_add ?_ hA2
          calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ - 8 * Work.Residues.Ept z‖
              ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ‖
                + ‖(8 : ℂ) * Work.Residues.Ept z‖ := norm_sub_le _ _
            _ ≤ (Real.pi * ‖(z : ℂ)‖ + ‖cuspL ℓ‖) + 8 := by
                refine add_le_add ?_ hA1
                calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ‖
                    ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖cuspL ℓ‖ := norm_add_le _ _
                  _ ≤ Real.pi * ‖(z : ℂ)‖ + ‖cuspL ℓ‖ := by linarith [hA3]
      _ = Real.pi * ‖(z : ℂ)‖ + ‖cuspL ℓ‖ + 20 := by ring
  have hEq : ℓ.L z = (ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ
      - 8 * Work.Residues.Ept z + 12 * Work.Residues.Ept z ^ 2))
      + ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ
      - 8 * Work.Residues.Ept z + 12 * Work.Residues.Ept z ^ 2) := by ring
  rw [hEq]
  calc ‖(ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ
        - 8 * Work.Residues.Ept z + 12 * Work.Residues.Ept z ^ 2))
        + ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ
        - 8 * Work.Residues.Ept z + 12 * Work.Residues.Ept z ^ 2)‖
      ≤ ‖ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ
          - 8 * Work.Residues.Ept z + 12 * Work.Residues.Ept z ^ 2)‖
        + ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ
          - 8 * Work.Residues.Ept z + 12 * Work.Residues.Ept z ^ 2‖ := norm_add_le _ _
    _ ≤ C + (Real.pi * ‖(z : ℂ)‖ + ‖cuspL ℓ‖ + 20) := add_le_add (le_trans h1 (by linarith)) hA
    _ ≤ (‖cuspL ℓ‖ + Real.pi + 20 + C) * (1 + ‖(z : ℂ)‖) := by
        nlinarith [norm_nonneg (cuspL ℓ), norm_nonneg ((z : ℂ)), Real.pi_pos, hC.le]


/-! ## §3  The `z`-atom `CuspBdd` facts -/

lemma cuspBdd_E4m (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E4Fun z - mE4 z) 4 0 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E4FunSecondOrder
  refine cuspBdd_of_w (k := 4) hC (fun z hz => ?_)
  have h1 := h z (le_trans hT1 hz)
  have h2 : ‖Work.Kernels.qParamFun z‖ ^ 2 = ‖Work.Residues.Ept z‖ ^ 4 := by
    rw [norm_qParamFun_eq_Ept_sq]; ring
  have hEq : Work.Kernels.E4Fun z - mE4 z
      = Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z := by
    rw [show mE4 z = (1 : ℂ) + 240 * Work.Kernels.qParamFun z from rfl]
    ring
  rw [hEq]
  calc ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2 := h1
    _ = C * ‖Work.Residues.Ept z‖ ^ 4 := by rw [h2]

lemma cuspBdd_E6m (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E6Fun z - mE6 z) 4 0 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E6FunSecondOrder
  refine cuspBdd_of_w (k := 4) hC (fun z hz => ?_)
  have h1 := h z (le_trans hT1 hz)
  have h2 : ‖Work.Kernels.qParamFun z‖ ^ 2 = ‖Work.Residues.Ept z‖ ^ 4 := by
    rw [norm_qParamFun_eq_Ept_sq]; ring
  have hEq : Work.Kernels.E6Fun z - mE6 z
      = Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z := by
    rw [show mE6 z = (1 : ℂ) - 504 * Work.Kernels.qParamFun z from rfl]
    ring
  rw [hEq]
  calc ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2 := h1
    _ = C * ‖Work.Residues.Ept z‖ ^ 4 := by rw [h2]

lemma cuspBdd_E4s (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E4Fun z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_E4
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_E6s (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E6Fun z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_E6
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_E8s (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E8Fun z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_E8
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_E10s (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E10Fun z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_E10
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_mE4s (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => mE4 z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_mE4
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_mE6s (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => mE6 z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_mE6
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_mE8s (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => mE8 z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_mE8
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_mE10s (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => mE10 z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_mE10
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_E8m (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E8Fun z - mE8 z) 4 0 := by
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E4Fun z - mE4 z)
      * (Work.Kernels.E4Fun z + mE4 z)) (4 + 0) (0 + 0) :=
    (cuspBdd_E4m hT1).mul ((cuspBdd_E4s hT1).add (cuspBdd_mE4s hT1))
  refine (h1.mono (le_trans zero_le_one hT1) (by norm_num) (by norm_num)).congr (fun τ z => ?_)
  show (Work.Kernels.E4Fun z - mE4 z) * (Work.Kernels.E4Fun z + mE4 z)
      = Work.Kernels.E8Fun z - mE8 z
  rw [show Work.Kernels.E8Fun z = Work.Kernels.E4Fun z ^ 2 from rfl,
    show mE8 z = mE4 z * mE4 z from rfl]
  ring

lemma cuspBdd_E10m (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E10Fun z - mE10 z) 4 0 := by
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E4Fun z - mE4 z) * Work.Kernels.E6Fun z
      + mE4 z * (Work.Kernels.E6Fun z - mE6 z)) (4 + 0) (0 + 0) :=
    ((cuspBdd_E4m hT1).mul (cuspBdd_E6s hT1)).add ((cuspBdd_mE4s hT1).mul (cuspBdd_E6m hT1))
  refine (h1.mono (le_trans zero_le_one hT1) (by norm_num) (by norm_num)).congr (fun τ z => ?_)
  show (Work.Kernels.E4Fun z - mE4 z) * Work.Kernels.E6Fun z
      + mE4 z * (Work.Kernels.E6Fun z - mE6 z) = Work.Kernels.E10Fun z - mE10 z
  rw [show Work.Kernels.E10Fun z = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z from rfl,
    show mE10 z = mE4 z * mE6 z from rfl]
  ring

lemma cuspBdd_Um (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.UFun z - mU z) 3 0 := by
  obtain ⟨C, hC, h⟩ := cusp_U_second
  refine cuspBdd_of_w (k := 3) hC (fun z hz => ?_)
  have h1 := h z (le_trans hT1 hz)
  have hEq : Work.Kernels.UFun z - mU z = Work.Kernels.UFun z
      - (1 + 8 * Work.Residues.Ept z + 24 * Work.Residues.Ept z ^ 2) := by
    rw [show mU z = (1 : ℂ) + 8 * Work.Residues.Ept z + 24 * Work.Kernels.qParamFun z from rfl,
      qParamFun_eq_Ept_sq]
  rw [hEq]
  exact h1

lemma cuspBdd_Wm (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.WFun z - mW z) 3 0 := by
  obtain ⟨C, hC, h⟩ := cusp_W_second
  refine cuspBdd_of_w (k := 3) hC (fun z hz => ?_)
  have h1 := h z (le_trans hT1 hz)
  have hEq : Work.Kernels.WFun z - mW z = Work.Kernels.WFun z
      - (1 - 8 * Work.Residues.Ept z + 24 * Work.Residues.Ept z ^ 2) := by
    rw [show mW z = (1 : ℂ) - 8 * Work.Residues.Ept z + 24 * Work.Kernels.qParamFun z from rfl,
      qParamFun_eq_Ept_sq]
  rw [hEq]
  exact h1

lemma cuspBdd_Dm (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - mD z) 3 0 := by
  obtain ⟨C, hC, h⟩ := cusp_D_second
  refine cuspBdd_of_w (k := 3) hC (fun z hz => ?_)
  have h1 := h z (le_trans hT1 hz)
  have hEq : Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - mD z
      = Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2
        - (1 + 16 * Work.Residues.Ept z - 144 * Work.Residues.Ept z ^ 2) := by
    rw [show mD z = (1 : ℂ) + 16 * Work.Residues.Ept z - 144 * Work.Kernels.qParamFun z from rfl,
      qParamFun_eq_Ept_sq]
  rw [hEq]
  exact h1

lemma cuspBdd_Lm (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ
      - 8 * Work.Residues.Ept z + 12 * mq z)) 3 0 := by
  obtain ⟨C, hC, h⟩ := Classical.choose_spec (cusp_L_second ℓ)
  refine cuspBdd_of_w (k := 3) hC (fun z hz => ?_)
  have h1 := h z (le_trans hT1 hz)
  simpa only [cuspL, mq, qParamFun_eq_Ept_sq] using h1

lemma cuspBdd_Ws (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.WFun z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_W
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_Ds (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_D
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_mWs (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => mW z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_mW
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_mDs (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => mD z) 0 0 := by
  obtain ⟨C, hC, h⟩ := bdd_mD
  exact cuspBdd_of_bdd hC (fun z hz => h z (le_trans hT1 hz))

lemma cuspBdd_Gt (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Gt z) 0 1 := by
  obtain ⟨C, hC, h⟩ := bdd_Gt
  refine cuspBdd_of_w_coe (k := 0) hC (fun z hz => ?_)
  simpa using (h z (le_trans hT1 hz)).1

lemma cuspBdd_mG (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => mG z) 0 1 := by
  obtain ⟨C, hC, h⟩ := bdd_Gt
  refine cuspBdd_of_w_coe (k := 0) hC (fun z hz => ?_)
  simpa using (h z (le_trans hT1 hz)).2.1

lemma cuspBdd_GtmG (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Gt z - mG z) 4 1 := by
  obtain ⟨C, hC, h⟩ := bdd_Gt
  exact cuspBdd_of_w_coe (k := 4) hC (fun z hz => (h z (le_trans hT1 hz)).2.2)

lemma cuspBdd_L (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => ℓ.L z) 0 1 := by
  obtain ⟨C, hC, h⟩ := bdd_L ℓ
  exact cuspBdd_of_w_coe (k := 0) hC
    (fun z hz => by simpa using h z (le_trans hT1 hz))

/-! ## §4  The `τ`-atoms, bounded on the compact `K` -/

lemma cont_fk_two : Continuous (fun τ : ℍ => Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) := by
  have h := continuous_fk_two_ub
  rw [show (fun τ : ℍ => Work.Kernels.fk 2 τ)
      = fun τ : ℍ => Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ from by
    funext τ; exact fk_two_eq τ] at h
  exact h

lemma cuspBdd_phi0E6 (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (MiddleRange.continuous_phiVec_0.mul continuous_E6Fun_ub) hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_phi1E4 (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (MiddleRange.continuous_phiVec_1.mul continuous_E4Fun_ub) hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_phi2E14D (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => Work.Kernels.phiVec τ 2
      * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (MiddleRange.continuous_phiVec_2.mul cont_fk_two) hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_E14D (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom cont_fk_two hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_E4T (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => Work.Kernels.E4Fun τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom continuous_E4Fun_ub hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_psi2 (ℓ : Work.Kernels.LogLambdaData) (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => Work.Kernels.psi2 ℓ τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (continuous_psi2_ub ℓ) hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_psi4 (ℓ : Work.Kernels.LogLambdaData) (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => Work.Kernels.psi4 ℓ τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (continuous_psi4_ub ℓ) hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_j (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => Work.Kernels.jInvariantFun τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom continuous_jInvariantFun_ub hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_c1728sub_j (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (continuous_const.sub continuous_jInvariantFun_ub) hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_tauId (hK : IsCompact K) :
    CuspBdd K T (fun τ _ => (τ : ℂ)) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom continuous_coe hK
  exact cuspBdd_tau hB0 hB

/-! ## §5  The two-variable atoms `S`, `R` -/

/-- `S(τ,z) = (j(τ) - j(z))⁻¹`. -/
def Sz (τ z : ℍ) : ℂ := (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹

/-- `R(τ,z) = (Δ(z)(j(τ) - j(z)))⁻¹`. -/
def Rz (τ z : ℍ) : ℂ :=
  (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))⁻¹

lemma Sz_diff_eq (τ z : ℍ) : Sz τ z - minvJ τ z
    = (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹
      + Work.Residues.Ept z ^ 2 - (744 - Work.Kernels.jInvariantFun τ) * Work.Residues.Ept z ^ 4 := by
  rw [Sz, minvJ]
  show _ = _ + _ - _ * _
  rw [show mq z = Work.Residues.Ept z ^ 2 from qParamFun_eq_Ept_sq z]
  ring

lemma Rz_diff_eq (τ z : ℍ) : Rz τ z - mR τ z
    = (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))⁻¹
      + 1 - (720 - Work.Kernels.jInvariantFun τ) * Work.Residues.Ept z ^ 2 := by
  rw [Rz, mR]
  show _ = _ + _ - _ * _
  rw [show mq z = Work.Residues.Ept z ^ 2 from qParamFun_eq_Ept_sq z]
  ring



/-! ## §6  The two difference identities and the assembly -/

/-- The `z`-side bracket `E₈(z)G(z)² - mE8(z)mG(z)²`, written for the `CuspBdd` calculus. -/
def X8 (z : ℍ) : ℂ := (Work.Kernels.E8Fun z - mE8 z) * Gt z ^ 2
  + mE8 z * ((Gt z - mG z) * (Gt z + mG z))

/-- The `z`-side bracket `E₁₀(z)zG(z) - mE10(z)zmG(z)`. -/
def X10 (z : ℍ) : ℂ := (Work.Kernels.E10Fun z - mE10 z) * ((z : ℂ) * Gt z)
  + mE10 z * ((z : ℂ) * (Gt z - mG z))

lemma X8_eq (z : ℍ) : X8 z = Work.Kernels.E8Fun z * Gt z ^ 2 - mE8 z * (mG z) ^ 2 := by
  rw [X8]; ring

lemma X10_eq (z : ℍ) :
    X10 z = Work.Kernels.E10Fun z * ((z : ℂ) * Gt z) - mE10 z * ((z : ℂ) * mG z) := by
  rw [X10]; ring

/-- The `τ`-side bracket of the `K₊^{(8)}` expansion. -/
def Bf (τ z : ℍ) : ℂ :=
  Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ * Work.Kernels.E8Fun z * Gt z ^ 2
    - 2 * Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z
        * ((z : ℂ) * Gt z)

/-- The model of `Bf`. -/
def Am (τ z : ℍ) : ℂ :=
  Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ * mE8 z * (mG z) ^ 2
    - 2 * Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ * mE10 z * ((z : ℂ) * mG z)

lemma cuspBdd_X8 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => X8 z) 4 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hGt2 : CuspBdd K T (fun _ z => Gt z ^ 2) 0 2 :=
    (((cuspBdd_Gt hT1).mul (cuspBdd_Gt hT1)).mono hT0 (by norm_num) (by norm_num)).congr
      (fun τ z => by show Gt z * Gt z = Gt z ^ 2; ring)
  have hcross : CuspBdd K T (fun _ z => (Gt z - mG z) * (Gt z + mG z)) 4 2 :=
    ((cuspBdd_GtmG hT1).mul ((cuspBdd_Gt hT1).add (cuspBdd_mG hT1))).mono hT0
      (by norm_num) (by norm_num)
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E8Fun z - mE8 z) * Gt z ^ 2) 4 2 :=
    ((cuspBdd_E8m hT1).mul hGt2).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => mE8 z * ((Gt z - mG z) * (Gt z + mG z))) 4 2 :=
    ((cuspBdd_mE8s hT1).mul hcross).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by show _ = X8 z; rw [X8])

lemma cuspBdd_X10 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => X10 z) 4 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hzGt : CuspBdd K T (fun _ z => (z : ℂ) * Gt z) 0 2 :=
    ((CuspBdd.coe K T).mul (cuspBdd_Gt hT1)).mono hT0 (by norm_num) (by norm_num)
  have hzGtm : CuspBdd K T (fun _ z => (z : ℂ) * (Gt z - mG z)) 4 2 :=
    ((CuspBdd.coe K T).mul (cuspBdd_GtmG hT1)).mono hT0 (by norm_num) (by norm_num)
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E10Fun z - mE10 z) * ((z : ℂ) * Gt z)) 4 2 :=
    ((cuspBdd_E10m hT1).mul hzGt).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => mE10 z * ((z : ℂ) * (Gt z - mG z))) 4 2 :=
    ((cuspBdd_mE10s hT1).mul hzGtm).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by show _ = X10 z; rw [X10])

lemma cuspBdd_Am (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) (hK : IsCompact K) :
    CuspBdd K T (fun τ z => Am τ z) 0 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hGt2 : CuspBdd K T (fun _ z => (mG z) ^ 2) 0 2 :=
    (((cuspBdd_mG hT1).mul (cuspBdd_mG hT1)).mono hT0 (by norm_num) (by norm_num)).congr
      (fun τ z => by show mG z * mG z = (mG z) ^ 2; ring)
  have hzmG : CuspBdd K T (fun _ z => (z : ℂ) * mG z) 0 2 :=
    ((CuspBdd.coe K T).mul (cuspBdd_mG hT1)).mono hT0 (by norm_num) (by norm_num)
  have h1 : CuspBdd K T (fun τ z => Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
      * mE8 z * (mG z) ^ 2) 0 2 :=
    (((cuspBdd_phi0E6 hK).mul (cuspBdd_mE8s hT1)).mul hGt2).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun τ z => 2 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ
      * mE10 z * ((z : ℂ) * mG z))) 0 2 :=
    ((cuspBdd_const 2).mul (((cuspBdd_phi1E4 hK).mul (cuspBdd_mE10s hT1)).mul hzmG)).mono hT0
      (by norm_num) (by norm_num)
  exact (h1.sub h2).congr (fun τ z => by show _ = Am τ z; rw [Am]; ring)

lemma cuspBdd_BfsubAm (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) (hK : IsCompact K) :
    CuspBdd K T (fun τ z => Bf τ z - Am τ z) 4 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun τ z => Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ * X8 z) 4 2 :=
    ((cuspBdd_phi0E6 hK).mul (cuspBdd_X8 hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun τ z => 2 * ((Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)
      * X10 z)) 4 2 :=
    ((cuspBdd_const 2).mul ((cuspBdd_phi1E4 hK).mul (cuspBdd_X10 hT1))).mono hT0
      (by norm_num) (by norm_num)
  exact (h1.sub h2).congr (fun τ z => by
    show _ = Bf τ z - Am τ z; rw [Bf, Am, X8_eq, X10_eq]; ring)

/-! ### The `K₊^{(8)}` identity -/

lemma KPlus8_atom (τ z : ℍ)
    (hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.KPlus 8 τ z = cuspC8 *
      ((z : ℂ) ^ 2 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
            - 2 * Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)
        + Work.Kernels.phiVec τ 2 * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)
            * (z : ℂ) ^ 2 * Sz τ z
        + Bf τ z * Rz τ z) := by
  rw [KPlus_eight_decomposition τ z hJ]
  rw [show cuspC8 = ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ from rfl]
  congr 1
  rw [phitVec_zero, phitVec_one, phitVec_two]
  rw [show Work.Kernels.phi0 τ = Work.Kernels.phiVec τ 1 from rfl,
    show Work.Kernels.phi2 τ = Work.Kernels.phiVec τ 2 from rfl,
    show (τ : ℂ) = Work.Kernels.phiVec τ 0 from rfl]
  rw [Sz, Rz, Bf]
  have hΔτ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hΔz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hE : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 := sub_ne_zero.mpr hJ
  field_simp
  ring

lemma KPlus8_diff (τ z : ℍ)
    (hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.KPlus 8 τ z - MP8 τ z = cuspC8 *
      (Work.Kernels.phiVec τ 2 * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)
          * (z : ℂ) ^ 2 * (Sz τ z - minvJ τ z)
        + (Bf τ z - Am τ z) * Rz τ z + Am τ z * (Rz τ z - mR τ z)) := by
  rw [KPlus8_atom τ z hJ]
  simp only [MP8, tphi0, tphi1, tphi2, cuspC8, Bf, Am]
  ring

/-! ### The `K₋^{(8)}` identity -/

/-- The `τ`-side bracket of the `K₋^{(8)}` expansion. -/
def BK (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (-2) * Work.Kernels.c1728 * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L z
    + Work.Kernels.psi2 ℓ τ * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)
        * (Work.Kernels.E8Fun z * Work.Kernels.WFun z
          - Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
    + Work.Kernels.psi4 ℓ τ
        * ((Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * Work.Kernels.E8Fun z
            * Work.Kernels.WFun z
          + Work.Kernels.jInvariantFun τ * Work.Kernels.E6Fun z
            * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))

/-- The model of `BK`. -/
def BM (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (-2) * Work.Kernels.c1728 * Work.Kernels.E4Fun τ * mE10 z
      * ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ - 8 * Work.Residues.Ept z
        + 12 * mq z)
    + Work.Kernels.psi2 ℓ τ * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)
        * (mE8 z * mW z - mE6 z * mD z)
    + Work.Kernels.psi4 ℓ τ
        * ((Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * mE8 z * mW z
          + Work.Kernels.jInvariantFun τ * mE6 z * mD z)

lemma KMinus8_eq_form (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.KMinus ℓ 8 τ z = (Work.Residues.kpre z τ)⁻¹ * BK ℓ τ z := by
  rw [Work.Residues.Loc.KMinus8_eq]
  congr 1

lemma kpre_inv_eq (τ z : ℍ) : (Work.Residues.kpre z τ)⁻¹
    = ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * Rz τ z := by
  have h : Work.Residues.kpre z τ = ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))
      * (Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
    rw [Work.Residues.kpre]; ring
  rw [h, Rz]
  conv_lhs => rw [mul_inv]

lemma MM8_eq_form (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    MM8 ℓ τ z = ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * mR τ z * BM ℓ τ z := by
  simp only [MM8, BM, Work.Kernels.c1728]
  ring

lemma KMinus8_diff (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.KMinus ℓ 8 τ z - MM8 ℓ τ z
      = ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹
        * ((Rz τ z - mR τ z) * BK ℓ τ z + mR τ z * (BK ℓ τ z - BM ℓ τ z)) := by
  rw [KMinus8_eq_form ℓ τ z, kpre_inv_eq τ z, MM8_eq_form ℓ τ z]
  ring


/-! ## §7  The `z`-side and `τ`-side brackets of `K₋` -/

/-- The `z`-side bracket `E₁₀(z)𝓛(z) - mE10(z)(πiz + c_L - 8E + 12q)`. -/
def Y1 (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ :=
  Work.Kernels.E10Fun z * ℓ.L z - mE10 z
    * ((Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ - 8 * Work.Residues.Ept z + 12 * mq z)

/-- The `z`-side bracket `(E₈W - mE8mW) - (E₆D - mE6mD)`. -/
def Y2 (z : ℍ) : ℂ :=
  (Work.Kernels.E8Fun z * Work.Kernels.WFun z - mE8 z * mW z)
    - (Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
      - mE6 z * mD z)

/-- The `τ`-dependent bracket `(1728-j(τ))(E₈W - mE8mW) + j(τ)(E₆D - mE6mD)`. -/
def T3 (τ z : ℍ) : ℂ :=
  (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ)
      * (Work.Kernels.E8Fun z * Work.Kernels.WFun z - mE8 z * mW z)
    + Work.Kernels.jInvariantFun τ
      * (Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
        - mE6 z * mD z)

lemma cuspBdd_Z8 (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E8Fun z * Work.Kernels.WFun z - mE8 z * mW z) 3 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E8Fun z - mE8 z) * Work.Kernels.WFun z) 3 0 :=
    ((cuspBdd_E8m hT1).mul (cuspBdd_Ws hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => mE8 z * (Work.Kernels.WFun z - mW z)) 3 0 :=
    ((cuspBdd_mE8s hT1).mul (cuspBdd_Wm hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by show _ = _; ring)

lemma cuspBdd_Z6 (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
      - mE6 z * mD z) 3 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E6Fun z - mE6 z)
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)) 3 0 :=
    ((cuspBdd_E6m hT1).mul (cuspBdd_Ds hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => mE6 z
      * ((Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2) - mD z)) 3 0 :=
    ((cuspBdd_mE6s hT1).mul (cuspBdd_Dm hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by show _ = _; ring)

lemma cuspBdd_Wterm (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E8Fun z * Work.Kernels.WFun z
      - Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)) 0 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => Work.Kernels.E8Fun z * Work.Kernels.WFun z) 0 0 :=
    ((cuspBdd_E8s hT1).mul (cuspBdd_Ws hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => Work.Kernels.E6Fun z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)) 0 0 :=
    ((cuspBdd_E6s hT1).mul (cuspBdd_Ds hT1)).mono hT0 (by norm_num) (by norm_num)
  exact h1.sub h2

lemma cuspBdd_Wmterm (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => mE8 z * mW z - mE6 z * mD z) 0 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => mE8 z * mW z) 0 0 :=
    ((cuspBdd_mE8s hT1).mul (cuspBdd_mWs hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => mE6 z * mD z) 0 0 :=
    ((cuspBdd_mE6s hT1).mul (cuspBdd_mDs hT1)).mono hT0 (by norm_num) (by norm_num)
  exact h1.sub h2

lemma cuspBdd_T3inner (hT1 : 1 ≤ T) (hK : IsCompact K) :
    CuspBdd K T (fun τ z => (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ)
      * Work.Kernels.E8Fun z * Work.Kernels.WFun z
      + Work.Kernels.jInvariantFun τ * Work.Kernels.E6Fun z
        * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)) 0 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun τ z => (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ)
      * Work.Kernels.E8Fun z * Work.Kernels.WFun z) 0 0 :=
    (((cuspBdd_c1728sub_j hK).mul (cuspBdd_E8s hT1)).mul (cuspBdd_Ws hT1)).mono hT0
      (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun τ z => Work.Kernels.jInvariantFun τ * Work.Kernels.E6Fun z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)) 0 0 :=
    (((cuspBdd_j hK).mul (cuspBdd_E6s hT1)).mul (cuspBdd_Ds hT1)).mono hT0
      (by norm_num) (by norm_num)
  exact h1.add h2

lemma cuspBdd_Y1 (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Y1 ℓ z) 3 1 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E10Fun z - mE10 z) * ℓ.L z) 3 1 :=
    ((cuspBdd_E10m hT1).mul (cuspBdd_L ℓ hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => mE10 z * (ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ)
      + cuspL ℓ - 8 * Work.Residues.Ept z + 12 * mq z))) 3 1 :=
    ((cuspBdd_mE10s hT1).mul (cuspBdd_Lm ℓ hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by show _ = Y1 ℓ z; rw [Y1]; ring)

lemma cuspBdd_Y2 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Y2 z) 3 1 :=
  ((cuspBdd_Z8 hT1).sub (cuspBdd_Z6 hT1)).mono (le_trans zero_le_one hT1)
    (by norm_num) (by norm_num)

lemma cuspBdd_T3 (hT1 : 1 ≤ T) (hK : IsCompact K) :
    CuspBdd K T (fun τ z => T3 τ z) 3 1 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun τ z => (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ)
      * (Work.Kernels.E8Fun z * Work.Kernels.WFun z - mE8 z * mW z)) 3 1 :=
    ((cuspBdd_c1728sub_j hK).mul (cuspBdd_Z8 hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun τ z => Work.Kernels.jInvariantFun τ
      * (Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
        - mE6 z * mD z)) 3 1 :=
    ((cuspBdd_j hK).mul (cuspBdd_Z6 hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by show _ = T3 τ z; rw [T3])

lemma cuspBdd_BK (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) (hK : IsCompact K) :
    CuspBdd K T (fun τ z => BK ℓ τ z) 0 1 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun τ z => (-2 : ℂ) * Work.Kernels.c1728 * Work.Kernels.E4Fun τ
      * Work.Kernels.E10Fun z * ℓ.L z) 0 1 :=
    ((((cuspBdd_const ((-2 : ℂ) * Work.Kernels.c1728)).mul (cuspBdd_E4T hK)).mul
      (cuspBdd_E10s hT1)).mul (cuspBdd_L ℓ hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun τ z => Work.Kernels.psi2 ℓ τ
      * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)
      * (Work.Kernels.E8Fun z * Work.Kernels.WFun z
        - Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))) 0 1 :=
    (((cuspBdd_psi2 ℓ hK).mul (cuspBdd_E14D hK)).mul (cuspBdd_Wterm hT1)).mono hT0
      (by norm_num) (by norm_num)
  have h3 : CuspBdd K T (fun τ z => Work.Kernels.psi4 ℓ τ
      * ((Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * Work.Kernels.E8Fun z
          * Work.Kernels.WFun z
        + Work.Kernels.jInvariantFun τ * Work.Kernels.E6Fun z
          * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))) 0 1 :=
    ((cuspBdd_psi4 ℓ hK).mul (cuspBdd_T3inner hT1 hK)).mono hT0 (by norm_num) (by norm_num)
  exact ((h1.add h2).add h3).congr (fun τ z => by show _ = BK ℓ τ z; rw [BK])

lemma cuspBdd_BKsubBM (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) (hK : IsCompact K) :
    CuspBdd K T (fun τ z => BK ℓ τ z - BM ℓ τ z) 3 1 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun τ z => (-2 : ℂ) * Work.Kernels.c1728 * Work.Kernels.E4Fun τ
      * Y1 ℓ z) 3 1 :=
    (((cuspBdd_const ((-2 : ℂ) * Work.Kernels.c1728)).mul (cuspBdd_E4T hK)).mul
      (cuspBdd_Y1 ℓ hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun τ z => Work.Kernels.psi2 ℓ τ
      * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) * Y2 z) 3 1 :=
    (((cuspBdd_psi2 ℓ hK).mul (cuspBdd_E14D hK)).mul (cuspBdd_Y2 hT1)).mono hT0
      (by norm_num) (by norm_num)
  have h3 : CuspBdd K T (fun τ z => Work.Kernels.psi4 ℓ τ * T3 τ z) 3 1 :=
    ((cuspBdd_psi4 ℓ hK).mul (cuspBdd_T3 hT1 hK)).mono hT0 (by norm_num) (by norm_num)
  exact ((h1.add h2).add h3).congr (fun τ z => by
    show _ = BK ℓ τ z - BM ℓ τ z; rw [BK, BM, Y1, Y2, T3]; ring)


/-! ## §8  The main theorem -/

theorem kernel8_cuspExp (ℓ : Work.Kernels.LogLambdaData) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ T : ℝ, 0 < T ∧ ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ z : UpperHalfPlane, T ≤ z.im →
      ‖Work.Kernels.KPlus 8 τ z - Work.Asymptotics.MP8 τ z‖ ≤ C * Work.Asymptotics.cuspG z 3 1 ∧
      ‖Work.Kernels.KMinus ℓ 8 τ z - Work.Asymptotics.MM8 ℓ τ z‖ ≤ C * Work.Asymptotics.cuspG z 3 1 := by
  obtain ⟨TJ, hTJ0, CJ, hCJ0, hJb⟩ := cusp_invJ_second hK
  obtain ⟨TD, hTD0, CD, hCD0, hDb⟩ := cusp_inv_divisor_second hK
  obtain ⟨T0, M0, hT00, hM00, hExp0⟩ := jInvariantFun_cusp_second
  obtain ⟨Bj, hBj0, hBj⟩ := cuspBdd_tauAtom continuous_jInvariantFun_ub hK
  have hRpos : 0 < Bj + 745 + M0 + 1 := by linarith
  set T : ℝ := max (max (max (max 1 TJ) TD) T0)
    (Real.log (Bj + 745 + M0 + 1) / (2 * Real.pi)) with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hT0' : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hTJle : TJ ≤ T := by
    rw [hTdef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hTDle : TD ≤ T := by
    rw [hTdef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hT0le : T0 ≤ T := by
    rw [hTdef]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hLle : Real.log (Bj + 745 + M0 + 1) / (2 * Real.pi) ≤ T := by
    rw [hTdef]; exact le_max_right _ _
  have hlog : Real.log (Bj + 745 + M0 + 1) ≤ 2 * Real.pi * T := by
    have h := mul_le_mul_of_nonneg_left hLle (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    rwa [mul_div_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at h
  have jne : ∀ τ ∈ K, ∀ z : ℍ, T ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro τ hτ z hz
    have hzT0 : T0 ≤ z.im := le_trans hT0le hz
    have hEr := hExp0 z hzT0
    have hEr' : ‖Work.Kernels.jInvariantFun z
        - ((Work.Residues.Ept z)⁻¹ ^ 2 + 744)‖ ≤ M0 * ‖Work.Residues.Ept z‖ ^ 2 := by
      have hEq : Work.Kernels.jInvariantFun z - (Work.Residues.Ept z)⁻¹ ^ 2 - 744
          = Work.Kernels.jInvariantFun z - ((Work.Residues.Ept z)⁻¹ ^ 2 + 744) := by ring
      rw [← hEq]; exact hEr
    have hnormE : ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ = Real.exp (2 * Real.pi * z.im) := by
      have h1 : ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ = (‖Work.Residues.Ept z‖ ^ 2)⁻¹ := by
        rw [norm_pow, norm_inv, sq, sq, mul_inv]
      rw [h1, ← norm_qParamFun_eq_Ept_sq, inv_norm_qParamFun_eq_exp]
    have hRle : Bj + 745 + M0 + 1 ≤ ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ := by
      rw [hnormE]
      have h1 : Real.exp (Real.log (Bj + 745 + M0 + 1)) ≤ Real.exp (2 * Real.pi * T) :=
        Real.exp_le_exp.mpr hlog
      have h2 : Real.exp (2 * Real.pi * T) ≤ Real.exp (2 * Real.pi * z.im) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      calc Bj + 745 + M0 + 1 = Real.exp (Real.log (Bj + 745 + M0 + 1)) := by
            rw [Real.exp_log hRpos]
        _ ≤ Real.exp (2 * Real.pi * z.im) := le_trans h1 h2
    have hMle : M0 * ‖Work.Residues.Ept z‖ ^ 2 ≤ M0 := by
      have h2 : ‖Work.Residues.Ept z‖ ^ 2 ≤ 1 := norm_Ept_sq_le_one z
      nlinarith [hM00.le]
    have hA : ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖ ≤ ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ + 744 := by
      calc _ ≤ ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ + ‖(744 : ℂ)‖ := norm_add_le _ _
        _ = ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ + 744 := by rw [Complex.norm_ofNat]
    have hb := abs_norm_sub_norm_le (Work.Kernels.jInvariantFun z)
      ((Work.Residues.Ept z)⁻¹ ^ 2 + 744)
    have hb1 : ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖ - ‖Work.Kernels.jInvariantFun z‖
        ≤ |‖Work.Kernels.jInvariantFun z‖ - ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have hA' : ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ - 744
        ≤ ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖ := by
      have h := norm_sub_le ((Work.Residues.Ept z)⁻¹ ^ 2 + 744) (744 : ℂ)
      rw [add_sub_cancel_right, Complex.norm_ofNat] at h
      linarith
    have hjz : Bj + 2 ≤ ‖Work.Kernels.jInvariantFun z‖ := by
      have hb2 : ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖ - ‖Work.Kernels.jInvariantFun z‖
          ≤ M0 * ‖Work.Residues.Ept z‖ ^ 2 := le_trans hb1 (le_trans hb hEr')
      nlinarith [hb2, hA', hRle, hMle]
    intro hcontra
    have hτb := hBj τ hτ
    rw [hcontra] at hτb
    linarith
  have hSzsub : CuspBdd K T (fun τ z => Sz τ z - minvJ τ z) 6 0 := by
    refine ⟨CJ, hCJ0, fun τ hτ z hz => ?_⟩
    change ‖Sz τ z - minvJ τ z‖ ≤ CJ * cuspG z 0 6
    have h1 := hJb τ hτ z (le_trans hTJle hz)
    rw [Sz_diff_eq τ z]
    have h2 : cuspG z 0 6 = ‖Work.Residues.Ept z‖ ^ 6 := by simp [cuspG]
    rw [h2]
    exact h1
  have hRzsub : CuspBdd K T (fun τ z => Rz τ z - mR τ z) 4 0 := by
    refine ⟨CD, hCD0, fun τ hτ z hz => ?_⟩
    change ‖Rz τ z - mR τ z‖ ≤ CD * cuspG z 0 4
    have h1 := hDb τ hτ z (le_trans hTDle hz)
    rw [Rz_diff_eq τ z]
    have h2 : cuspG z 0 4 = ‖Work.Residues.Ept z‖ ^ 4 := by simp [cuspG]
    rw [h2]
    exact h1
  have hmR : CuspBdd K T (fun τ z => mR τ z) 0 0 := by
    refine ⟨721 + Bj, by positivity, fun τ hτ z _ => ?_⟩
    change ‖mR τ z‖ ≤ (721 + Bj) * cuspG z 0 0
    have hq : ‖Work.Kernels.qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z
    have hb := hBj τ hτ
    have hEq : mR τ z = -1 + (720 - Work.Kernels.jInvariantFun τ) * Work.Kernels.qParamFun z := by
      rw [mR, mq]
    rw [hEq]
    have h1 : ‖(720 : ℂ) - Work.Kernels.jInvariantFun τ‖ ≤ 720 + Bj := by
      calc ‖(720 : ℂ) - Work.Kernels.jInvariantFun τ‖
          ≤ ‖(720 : ℂ)‖ + ‖Work.Kernels.jInvariantFun τ‖ := norm_sub_le _ _
        _ ≤ 720 + Bj := by rw [Complex.norm_ofNat]; linarith
    have h2 : ‖(720 - Work.Kernels.jInvariantFun τ) * Work.Kernels.qParamFun z‖ ≤ 720 + Bj := by
      rw [norm_mul]
      refine le_trans (mul_le_mul h1 hq (norm_nonneg _) (by positivity)) ?_
      rw [mul_one]
    simp only [cuspG, Real.rpow_zero, zpow_zero, mul_one]
    calc ‖(-1 : ℂ) + (720 - Work.Kernels.jInvariantFun τ) * Work.Kernels.qParamFun z‖
        ≤ ‖(-1 : ℂ)‖
          + ‖(720 - Work.Kernels.jInvariantFun τ) * Work.Kernels.qParamFun z‖ := norm_add_le _ _
      _ ≤ 1 + (720 + Bj) := by
          rw [norm_neg, norm_one]
          linarith [h2]
      _ = 721 + Bj := by ring
  have hRz : CuspBdd K T (fun τ z => Rz τ z) 0 0 :=
    (hmR.add (hRzsub.mono hT0' (by norm_num) (by norm_num))).congr
      (fun τ z => by show _ = Rz τ z; ring)
  have hSzsq : CuspBdd K T (fun _ z => (z : ℂ) ^ 2) 0 2 :=
    (((CuspBdd.coe K T).mul (CuspBdd.coe K T)).mono hT0' (by norm_num) (by norm_num)).congr
      (fun τ z => by show (z : ℂ) * (z : ℂ) = (z : ℂ) ^ 2; ring)
  have hP1 : CuspBdd K T (fun τ z => Work.Kernels.phiVec τ 2
      * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) * (z : ℂ) ^ 2
      * (Sz τ z - minvJ τ z)) 1 3 :=
    (((cuspBdd_phi2E14D hK).mul hSzsq).mul hSzsub).mono hT0' (by norm_num) (by norm_num)
  have hP2 : CuspBdd K T (fun τ z => (Bf τ z - Am τ z) * Rz τ z) 1 3 :=
    ((cuspBdd_BfsubAm ℓ hT1 hK).mul hRz).mono hT0' (by norm_num) (by norm_num)
  have hP3 : CuspBdd K T (fun τ z => Am τ z * (Rz τ z - mR τ z)) 1 3 :=
    ((cuspBdd_Am ℓ hT1 hK).mul hRzsub).mono hT0' (by norm_num) (by norm_num)
  have hInnerP : CuspBdd K T (fun τ z => Work.Kernels.phiVec τ 2
      * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) * (z : ℂ) ^ 2
      * (Sz τ z - minvJ τ z)
      + (Bf τ z - Am τ z) * Rz τ z + Am τ z * (Rz τ z - mR τ z)) 1 3 :=
    (hP1.add hP2).add hP3
  have hKPlus : CuspBdd K T (fun τ z => Work.Kernels.KPlus 8 τ z - MP8 τ z) 1 3 := by
    obtain ⟨C, hC, hCb⟩ := CuspBdd.const_mul cuspC8 hInnerP
    refine ⟨C, hC, fun τ hτ z hz => ?_⟩
    change ‖Work.Kernels.KPlus 8 τ z - MP8 τ z‖ ≤ C * cuspG z 3 1
    rw [KPlus8_diff τ z (jne τ hτ z hz)]
    exact hCb τ hτ z hz
  have hBK : CuspBdd K T (fun τ z => BK ℓ τ z) 0 1 := cuspBdd_BK ℓ hT1 hK
  have hBKsub : CuspBdd K T (fun τ z => BK ℓ τ z - BM ℓ τ z) 3 1 := cuspBdd_BKsubBM ℓ hT1 hK
  have hInnerM : CuspBdd K T (fun τ z => (Rz τ z - mR τ z) * BK ℓ τ z
      + mR τ z * (BK ℓ τ z - BM ℓ τ z)) 1 3 :=
    ((hRzsub.mul hBK).mono hT0' (by norm_num) (by norm_num)).add
      ((hmR.mul hBKsub).mono hT0' (by norm_num) (by norm_num))
  have hKMinus : CuspBdd K T (fun τ z => Work.Kernels.KMinus ℓ 8 τ z - MM8 ℓ τ z) 1 3 := by
    obtain ⟨C, hC, hCb⟩ :=
      CuspBdd.const_mul (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) hInnerM
    refine ⟨C, hC, fun τ hτ z hz => ?_⟩
    change ‖Work.Kernels.KMinus ℓ 8 τ z - MM8 ℓ τ z‖ ≤ C * cuspG z 3 1
    rw [KMinus8_diff ℓ τ z]
    exact hCb τ hτ z hz
  obtain ⟨C1, hC1, hC1b⟩ := hKPlus
  obtain ⟨C2, hC2, hC2b⟩ := hKMinus
  refine ⟨T, lt_of_lt_of_le one_pos hT1, max C1 C2 + 1, by positivity,
    fun τ hτ z hz => ⟨?_, ?_⟩⟩
  · calc ‖Work.Kernels.KPlus 8 τ z - MP8 τ z‖ ≤ C1 * cuspG z 3 1 := hC1b τ hτ z hz
      _ ≤ (max C1 C2 + 1) * cuspG z 3 1 :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_left C1 C2]) (cuspG_nonneg z 3 1)
  · calc ‖Work.Kernels.KMinus ℓ 8 τ z - MM8 ℓ τ z‖ ≤ C2 * cuspG z 3 1 := hC2b τ hτ z hz
      _ ≤ (max C1 C2 + 1) * cuspG z 3 1 :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_right C1 C2]) (cuspG_nonneg z 3 1)

end


open UpperHalfPlane
open Work.Asymptotics
open Work.Kernels.TildeFacts

noncomputable section

/-! ## §0  The prefactor and the atoms of the difference -/

/-- `c₂₄⁻ = 1/(2·1728·π)`, the prefactor of `Υ_-^{(24)}`. -/
def cuspK24 : ℂ := ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹

/-- The `z`-atom `E₄(z)/Δ(z) - mE4(z)·m(1/Δ)(z)` of the `K₊^{(24)}` difference. -/
def Ez1 (z : ℍ) : ℂ := Work.Kernels.E4Fun z / Work.Kernels.DeltaFun z - mE4 z * minvD z

/-- The `z`-atom `G(z)²/Δ(z) - mG(z)²·m(1/Δ)(z)`. -/
def Ez2 (z : ℍ) : ℂ := Gt z ^ 2 / Work.Kernels.DeltaFun z - (mG z) ^ 2 * minvD z

/-- The `z`-atom `G(z)² - mG(z)²`. -/
def Ez3 (z : ℍ) : ℂ := Gt z ^ 2 - (mG z) ^ 2

/-- The `z`-atom `(E₁₄(z)/Δ(z))·zG(z) - m(E₁₄/Δ)(z)·z·mG(z)`. -/
def Ez4 (z : ℍ) : ℂ := (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ((z : ℂ) * Gt z)
  - mE14D z * ((z : ℂ) * mG z)

/-- The `z`-atom `E₄(z)z² - mE4(z)z²`. -/
def Ez5 (z : ℍ) : ℂ := Work.Kernels.E4Fun z * (z : ℂ) ^ 2 - mE4 z * (z : ℂ) ^ 2

/-- The `z`-atom `(Δ(z)(j(τ)-j(z)))⁻¹ - m(1/Δ)(z)·m(1/(j(τ)-j(z)))`. -/
def Ez6 (τ z : ℍ) : ℂ := Rz τ z - minvD z * minvJ τ z

/-- The `τ`-atom `φ_{-2}(τ)E₁₄(τ)`. -/
def TA0 (τ : ℍ) : ℂ := Work.Kernels.phiVec τ 0 * Work.Kernels.E14Fun τ

/-- The `τ`-atom `φ_0(τ)Δ(τ)`. -/
def TA1 (τ : ℍ) : ℂ := Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ

/-- The `τ`-atom `φ_2(τ)E₁₀(τ)`. -/
def TA2 (τ : ℍ) : ℂ := Work.Kernels.phiVec τ 2 * Work.Kernels.E10Fun τ

/-- The `τ`-bracket multiplying `z²·Ez1` in the `K₊^{(24)}` difference. -/
def TP1 (τ : ℍ) : ℂ := 6 * TA0 τ + (-12 * Work.Kernels.jInvariantFun τ + 5 * 1728) * TA1 τ
  + 6 * TA2 τ

/-- The `τ`-bracket multiplying `Ez2` in the `K₊^{(24)}` difference. -/
def TP2 (τ : ℍ) : ℂ := -6 * TA0 τ + (12 * Work.Kernels.jInvariantFun τ - 7 * 1728) * TA1 τ
  - 6 * TA2 τ

/-- The model of the `τ`-bracket `A₀G² - 2A₁(E₁₄/Δ)zG + A₂E₄z²`. -/
def Ymo (τ z : ℍ) : ℂ := TA0 τ * (mG z) ^ 2 - 2 * TA1 τ * mE14D z * ((z : ℂ) * mG z)
  + TA2 τ * (mE4 z * (z : ℂ) ^ 2)

/-! ## §1  The exact expansion of `K₊^{(24)}` -/

/-- Explicit expansion of `K₊^{(24)}(τ,z)` from its definition as a double sum. -/
theorem KPlus24_expand (τ z : ℍ) :
    Work.Kernels.KPlus 24 τ z =
      ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I *
          Work.Kernels.DeltaFun z)⁻¹ *
      ( Work.Kernels.phiVec τ 0 * Work.Kernels.E14Fun τ
          * (6 * (Work.Kernels.E4Fun z * (z : ℂ) ^ 2)
             + (1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹ - 6)
               * Gt z ^ 2)
        + Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ
          * ((-12 * Work.Kernels.jInvariantFun τ + 5 * 1728) * (Work.Kernels.E4Fun z * (z : ℂ) ^ 2)
             + (-2 * 1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹)
               * ((Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ((z : ℂ) * Gt z))
             + (12 * Work.Kernels.jInvariantFun τ - 7 * 1728) * Gt z ^ 2)
        + Work.Kernels.phiVec τ 2 * Work.Kernels.E10Fun τ
          * ((1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹ + 6)
              * (Work.Kernels.E4Fun z * (z : ℂ) ^ 2)
             + (-6) * Gt z ^ 2) ) := by
  rw [Work.Kernels.KPlus,
    show Work.Kernels.UpsilonPlus 24 τ z =
      ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * Work.Kernels.DeltaFun z)⁻¹ •
        (Work.Kernels.PiMat ![14, 12, 10] τ *
          !![6, 0, Work.Kernels.c1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹ - 6;
             -12 * Work.Kernels.jInvariantFun τ + 5 * Work.Kernels.c1728,
               -2 * Work.Kernels.c1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹,
               12 * Work.Kernels.jInvariantFun τ - 7 * Work.Kernels.c1728;
             Work.Kernels.c1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹ + 6, 0, -6] *
          Work.Kernels.PiMat ![4, 2, 0] z) from rfl]
  simp only [Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  rw [phitVec_zero, phitVec_one, phitVec_two]
  simp only [Work.Kernels.PiMat, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Work.Kernels.phiVec, Work.Kernels.phiNeg2, Work.Kernels.fk, Work.Kernels.c1728,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply]
  norm_num
  ring

/-- **The `K₊^{(24)}` difference identity.** -/
theorem KPlus24_diff (τ z : ℍ) :
    Work.Kernels.KPlus 24 τ z - MP24 τ z =
      cuspC24 * ( TP1 τ * ((z : ℂ) ^ 2 * Ez1 z) + TP2 τ * Ez2 z
        + 1728 * ( Rz τ z * (TA0 τ * Ez3 z - 2 * TA1 τ * Ez4 z + TA2 τ * Ez5 z)
                   + Ez6 τ z * Ymo τ z ) ) := by
  rw [KPlus24_expand,
    show ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * Work.Kernels.DeltaFun z)⁻¹
      = cuspC24 * (Work.Kernels.DeltaFun z)⁻¹ from by
        simp only [Work.Asymptotics.cuspC24, Work.Kernels.c1728, mul_inv]]
  simp only [MP24, tphi0, tphi1, tphi2, cuspC24, Rz, mul_inv,
    Ez1, Ez2, Ez3, Ez4, Ez5, Ez6, TA0, TA1, TA2, TP1, TP2, Ymo]
  ring

/-! ## §2  The `K₋^{(24)}` decomposition and difference identity -/

/-- The model `πiz + c_L - 8E(z) + 12q(z)` of `ℓ.L z`. -/
def Lmod (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspL ℓ - 8 * Work.Residues.Ept z + 12 * mq z

/-- The exact bracket of `K₋^{(24)}` in the decomposition `Work.Residues.KMinus24_eq`. -/
def BK24 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ *
      (((-2 : ℂ) * Work.Kernels.c1728) * (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L z
        + ((-2 : ℂ) * Work.Kernels.c1728)
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) * Work.Kernels.WFun z)
    + Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
        * ((Work.Kernels.jInvariantFun τ
              + 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) * Work.Kernels.WFun z
            - (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
                * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
    + Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
        * ((Work.Kernels.c1728 - 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
              - Work.Kernels.jInvariantFun τ) * Work.Kernels.WFun z
            + (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
                * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))

/-- The `mR`-bracket of the model `MM24`. -/
def U24 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * (((-2 : ℂ) * Work.Kernels.c1728) * mE14D z * Lmod ℓ z)
    + Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ * Work.Kernels.jInvariantFun τ * mW z
    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ * mE10D z * mD z
    + Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
        * (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * mW z
    + Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ * mE10D z * mD z

/-- The `minvD`-bracket of the model `MM24`. -/
def V24 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * ((-2 : ℂ) * Work.Kernels.c1728) * mW z
    + 2 * Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ * mW z
    - 2 * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ * mW z

lemma KMinus24_eq_form (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.KMinus ℓ 24 τ z = (Work.Residues.kpre z τ)⁻¹ * BK24 ℓ τ z := by
  rw [Work.Residues.Loc.KMinus24_eq ℓ τ z]
  rfl

lemma KMinus24_expand (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.KMinus ℓ 24 τ z = cuspK24 * Rz τ z * BK24 ℓ τ z := by
  rw [KMinus24_eq_form ℓ τ z, kpre_inv_eq τ z]
  rfl

lemma MM24_eq_form (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    MM24 ℓ τ z = cuspK24 * (mR τ z * U24 ℓ τ z + minvD z * V24 ℓ τ z) := by
  simp only [MM24, cuspK24, U24, V24, Lmod, Work.Kernels.c1728]
  ring

/-- The `z`-atom `(E₁₄(z)/Δ(z))·ℓ.L z`. -/
def D0 (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ :=
  (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L z

/-- The difference `(E₁₄/Δ)·𝓛 - m(E₁₄/Δ)·m(𝓛)`. -/
def KD0 (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ := D0 ℓ z - mE14D z * Lmod ℓ z

/-- The difference `Rz·(j(τ)-j(z))·W - m(1/Δ)·mW`. -/
def D2 (τ z : ℍ) : ℂ := Rz τ z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
  * Work.Kernels.WFun z - minvD z * mW z

/-- The `z`-atom `(E₁₀(z)/Δ(z))·(U(z)²-V(z)²)`. -/
def D3 (z : ℍ) : ℂ := (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
  * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)

/-- The difference `(E₁₀/Δ)·(U²-V²) - m(E₁₀/Δ)·m(U²-V²)`. -/
def KD3 (z : ℍ) : ℂ := D3 z - mE10D z * mD z

/-- The `(E₁₄/Δ)·𝓛` block of the difference. -/
def G0 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Rz τ z - mR τ z) * D0 ℓ z + mR τ z * KD0 ℓ z

/-- The `(E₁₀/Δ)·(U²-V²)` block of the difference. -/
def G2 (τ z : ℍ) : ℂ := (Rz τ z - mR τ z) * D3 z + mR τ z * KD3 z

/-- **The `K₋^{(24)}` difference identity.** -/
theorem KMinus24_diff (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.KMinus ℓ 24 τ z - MM24 ℓ τ z = cuspK24 *
      ( Work.Kernels.DeltaFun τ * ((-2 : ℂ) * Work.Kernels.c1728) * (G0 ℓ τ z + D2 τ z)
        + Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ *
            ( Work.Kernels.jInvariantFun τ * (Rz τ z - mR τ z) * Work.Kernels.WFun z
              + Work.Kernels.jInvariantFun τ * mR τ z * (Work.Kernels.WFun z - mW z)
              + 2 * D2 τ z - G2 τ z )
        + Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ *
            ( (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * (Rz τ z - mR τ z)
                * Work.Kernels.WFun z
              + (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * mR τ z
                  * (Work.Kernels.WFun z - mW z)
              - 2 * D2 τ z + G2 τ z ) ) := by
  rw [KMinus24_expand ℓ τ z, MM24_eq_form ℓ τ z]
  simp only [BK24, U24, V24, G0, G2, D0, KD0, D2, D3, KD3]
  ring

end



open UpperHalfPlane
open Work.Asymptotics
open Work.Kernels.TildeFacts

noncomputable section

variable {K : Set ℍ} {T : ℝ}

/-! ## §1  Elementary `z`-atoms -/

lemma cuspBdd_mq (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => mq z) 2 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => Work.Residues.Ept z * Work.Residues.Ept z) (1 + 1) (0 + 0) :=
    (CuspBdd.Ept K T).mul (CuspBdd.Ept K T)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr (fun τ z => by
    show Work.Residues.Ept z * Work.Residues.Ept z = mq z
    rw [mq, qParamFun_eq_Ept_sq]; ring)

lemma cuspBdd_minvD (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => minvD z) (-2) 0 := by
  refine ⟨25, by norm_num, fun τ hτ z hz => ?_⟩
  have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := norm_Ept_le_one' z
  have hEp : 0 < ‖Work.Residues.Ept z‖ := norm_pos_iff.mpr (Work.Residues.Ept_ne_zero z)
  have hEq : minvD z = (Work.Residues.Ept z)⁻¹ ^ 2 + 24 := rfl
  have hnorm : ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ = (‖Work.Residues.Ept z‖ ^ 2)⁻¹ := by
    rw [norm_pow, norm_inv, inv_pow]
  have hzp : ‖Work.Residues.Ept z‖ ^ (-2 : ℤ) = (‖Work.Residues.Ept z‖ ^ 2)⁻¹ := by
    rw [zpow_neg]; norm_num
  have h1 : (1 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ (-2 : ℤ) := by
    rw [hzp, one_le_inv₀ (pow_pos hEp 2)]
    exact pow_le_one₀ hEp.le hE1
  have hg : cuspG z 0 (-2) = ‖Work.Residues.Ept z‖ ^ (-2 : ℤ) := by
    simp only [cuspG, Real.rpow_zero, one_mul]
  change ‖minvD z‖ ≤ 25 * cuspG z 0 (-2)
  rw [hg, hEq]
  calc ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 24‖
      ≤ ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ + ‖(24 : ℂ)‖ := norm_add_le _ _
    _ = (‖Work.Residues.Ept z‖ ^ 2)⁻¹ + 24 := by rw [hnorm, Complex.norm_ofNat]
    _ ≤ 25 * ‖Work.Residues.Ept z‖ ^ (-2 : ℤ) := by rw [hzp]; linarith

lemma cuspBdd_invDelta_sub (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => (Work.Kernels.DeltaFun z)⁻¹ - minvD z) 2 0 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_invDelta
  refine cuspBdd_of_w (k := 2) hC (fun z hz => ?_)
  have h1 := h z (le_trans hT1 hz)
  have h2 : minvD z = (Work.Residues.Ept z)⁻¹ ^ 2 + 24 := rfl
  rw [h2]; exact h1

lemma cuspBdd_invDelta (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => (Work.Kernels.DeltaFun z)⁻¹) (-2) 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.DeltaFun z)⁻¹ - minvD z) (-2) 0 :=
    (cuspBdd_invDelta_sub hT1).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => minvD z) (-2) 0 := cuspBdd_minvD hT1
  exact (h1.add h2).congr (fun τ z => by
    show (Work.Kernels.DeltaFun z)⁻¹ - minvD z + minvD z = (Work.Kernels.DeltaFun z)⁻¹; ring)

lemma cuspBdd_E14s (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Work.Kernels.E14Fun z) 0 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => Work.Kernels.E4Fun z * Work.Kernels.E4Fun z
      * Work.Kernels.E6Fun z) (0 + 0 + 0) (0 + 0 + 0) :=
    ((cuspBdd_E4s hT1).mul (cuspBdd_E4s hT1)).mul (cuspBdd_E6s hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr (fun τ z => by
    show Work.Kernels.E4Fun z * Work.Kernels.E4Fun z * Work.Kernels.E6Fun z = Work.Kernels.E14Fun z
    rw [Work.Kernels.E14Fun]; ring)

lemma cuspBdd_mE14s (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => mE14 z) 0 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => mE4 z * mE4 z * mE6 z) (0 + 0 + 0) (0 + 0 + 0) :=
    ((cuspBdd_mE4s hT1).mul (cuspBdd_mE4s hT1)).mul (cuspBdd_mE6s hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr (fun τ z => by
    show mE4 z * mE4 z * mE6 z = mE14 z; rw [mE14])

lemma cuspBdd_E14m (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E14Fun z - mE14 z) 4 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E4Fun z - mE4 z)
      * (Work.Kernels.E4Fun z + mE4 z) * Work.Kernels.E6Fun z) 4 0 :=
    (((cuspBdd_E4m hT1).mul ((cuspBdd_E4s hT1).add (cuspBdd_mE4s hT1))).mul (cuspBdd_E6s hT1)).mono
      hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => (mE4 z * mE4 z) * (Work.Kernels.E6Fun z - mE6 z)) 4 0 :=
    (((cuspBdd_mE4s hT1).mul (cuspBdd_mE4s hT1)).mul (cuspBdd_E6m hT1)).mono
      hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by
    show _ = Work.Kernels.E14Fun z - mE14 z
    rw [mE14, Work.Kernels.E14Fun]; ring)

lemma cuspBdd_E14D_inv (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) (-2) 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => Work.Kernels.E14Fun z * (Work.Kernels.DeltaFun z)⁻¹)
      (0 + (-2)) (0 + 0) := (cuspBdd_E14s hT1).mul (cuspBdd_invDelta hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr (fun τ z => by
    show Work.Kernels.E14Fun z * (Work.Kernels.DeltaFun z)⁻¹
      = Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z
    rw [div_eq_mul_inv])

lemma cuspBdd_mE14D (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => mE14D z) (-2) 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => mE14 z * minvD z) (0 + (-2)) (0 + 0) :=
    (cuspBdd_mE14s hT1).mul (cuspBdd_minvD hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr (fun τ z => by
    show mE14 z * minvD z = mE14D z; rw [mE14D])

lemma cuspBdd_mE14D_sub (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z - mE14D z) 2 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => Work.Kernels.E14Fun z
      * ((Work.Kernels.DeltaFun z)⁻¹ - minvD z)) 2 0 :=
    ((cuspBdd_E14s hT1).mul (cuspBdd_invDelta_sub hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => (Work.Kernels.E14Fun z - mE14 z) * minvD z) 2 0 :=
    ((cuspBdd_E14m hT1).mul (cuspBdd_minvD hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by
    show _ = Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z - mE14D z
    rw [mE14D, div_eq_mul_inv]; ring)

lemma cuspBdd_E10D_inv (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z) (-2) 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => Work.Kernels.E10Fun z * (Work.Kernels.DeltaFun z)⁻¹)
      (0 + (-2)) (0 + 0) := (cuspBdd_E10s hT1).mul (cuspBdd_invDelta hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr (fun τ z => by
    show Work.Kernels.E10Fun z * (Work.Kernels.DeltaFun z)⁻¹
      = Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z
    rw [div_eq_mul_inv])

lemma cuspBdd_mE10D (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => mE10D z) (-2) 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => mE10 z * minvD z) (0 + (-2)) (0 + 0) :=
    (cuspBdd_mE10s hT1).mul (cuspBdd_minvD hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr (fun τ z => by
    show mE10 z * minvD z = mE10D z; rw [mE10D])

lemma cuspBdd_mE10D_sub (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z - mE10D z) 2 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => Work.Kernels.E10Fun z
      * ((Work.Kernels.DeltaFun z)⁻¹ - minvD z)) 2 0 :=
    ((cuspBdd_E10s hT1).mul (cuspBdd_invDelta_sub hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => (Work.Kernels.E10Fun z - mE10 z) * minvD z) 2 0 :=
    ((cuspBdd_E10m hT1).mul (cuspBdd_minvD hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by
    show _ = Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z - mE10D z
    rw [mE10D, div_eq_mul_inv]; ring)

/-! ## §2  The `z`-atoms of the `K₊^{(24)}` difference -/

lemma cuspBdd_Ez1 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Ez1 z) 2 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => Work.Kernels.E4Fun z
      * ((Work.Kernels.DeltaFun z)⁻¹ - minvD z)) 2 0 :=
    ((cuspBdd_E4s hT1).mul (cuspBdd_invDelta_sub hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => (Work.Kernels.E4Fun z - mE4 z) * minvD z) 2 0 :=
    ((cuspBdd_E4m hT1).mul (cuspBdd_minvD hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by
    show _ = Ez1 z; rw [Ez1, div_eq_mul_inv]; ring)

lemma cuspBdd_zsq (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => (z : ℂ) ^ 2) 0 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => (z : ℂ) * (z : ℂ)) (0 + 0) (1 + 1) :=
    (CuspBdd.coe K T).mul (CuspBdd.coe K T)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr
    (fun τ z => by show (z : ℂ) * (z : ℂ) = (z : ℂ) ^ 2; ring)

lemma cuspBdd_Gt2 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Gt z ^ 2) 0 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => Gt z * Gt z) (0 + 0) (1 + 1) :=
    (cuspBdd_Gt hT1).mul (cuspBdd_Gt hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr
    (fun τ z => by show Gt z * Gt z = Gt z ^ 2; ring)

lemma cuspBdd_mG2 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => (mG z) ^ 2) 0 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => mG z * mG z) (0 + 0) (1 + 1) :=
    (cuspBdd_mG hT1).mul (cuspBdd_mG hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr
    (fun τ z => by show mG z * mG z = (mG z) ^ 2; ring)

lemma cuspBdd_z_mG (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => (z : ℂ) * mG z) 0 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => (z : ℂ) * mG z) (0 + 0) (1 + 1) :=
    (CuspBdd.coe K T).mul (cuspBdd_mG hT1)
  exact h.mono hT0 (by norm_num) (by norm_num)

lemma cuspBdd_Ez3 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Ez3 z) 4 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => (Gt z - mG z) * (Gt z + mG z)) (4 + 0) (1 + 1) :=
    (cuspBdd_GtmG hT1).mul ((cuspBdd_Gt hT1).add (cuspBdd_mG hT1))
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr
    (fun τ z => by show _ = Ez3 z; rw [Ez3]; ring)

lemma cuspBdd_Ez5 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Ez5 z) 4 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => (Work.Kernels.E4Fun z - mE4 z) * (z : ℂ) ^ 2) (4 + 0) (0 + 2) :=
    (cuspBdd_E4m hT1).mul (cuspBdd_zsq hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr
    (fun τ z => by show _ = Ez5 z; rw [Ez5]; ring)

lemma cuspBdd_Ez4 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Ez4 z) 2 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z - mE14D z)
      * Gt z) 2 1 :=
    ((cuspBdd_mE14D_sub hT1).mul (cuspBdd_Gt hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => mE14D z * (Gt z - mG z)) 2 1 :=
    ((cuspBdd_mE14D hT1).mul (cuspBdd_GtmG hT1)).mono hT0 (by norm_num) (by norm_num)
  have h3 : CuspBdd K T (fun _ z => (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z - mE14D z)
      * Gt z + mE14D z * (Gt z - mG z)) 2 1 := h1.add h2
  have h : CuspBdd K T (fun _ z => (z : ℂ) * ((Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z
      - mE14D z) * Gt z + mE14D z * (Gt z - mG z))) (0 + 2) (1 + 1) :=
    (CuspBdd.coe K T).mul h3
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr
    (fun τ z => by show _ = Ez4 z; rw [Ez4]; ring)

lemma cuspBdd_Ez2 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => Ez2 z) 2 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => Gt z ^ 2 * ((Work.Kernels.DeltaFun z)⁻¹ - minvD z)) 2 2 :=
    ((cuspBdd_Gt2 hT1).mul (cuspBdd_invDelta_sub hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => Ez3 z * minvD z) 2 2 :=
    ((cuspBdd_Ez3 hT1).mul (cuspBdd_minvD hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by
    show _ = Ez2 z; rw [Ez2, Ez3, div_eq_mul_inv]; ring)

/-! ## §3  The `τ`-atoms (bounded on the compact `K`) -/

lemma cuspBdd_TA0 (hK : IsCompact K) : CuspBdd K T (fun τ _ => TA0 τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (MiddleRange.continuous_phiVec_0.mul
    ((continuous_E4Fun_ub.pow 2).mul continuous_E6Fun_ub)) hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_TA1 (hK : IsCompact K) : CuspBdd K T (fun τ _ => TA1 τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (MiddleRange.continuous_phiVec_1.mul
    continuous_DeltaFun_ub) hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_TA2 (hK : IsCompact K) : CuspBdd K T (fun τ _ => TA2 τ) 0 0 := by
  obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (MiddleRange.continuous_phiVec_2.mul
    (continuous_E4Fun_ub.mul continuous_E6Fun_ub)) hK
  exact cuspBdd_tau hB0 hB

lemma cuspBdd_TP1 (hK : IsCompact K) (hT1 : 1 ≤ T) :
    CuspBdd K T (fun τ _ => TP1 τ) 0 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hA0 := cuspBdd_TA0 (K := K) (T := T) hK
  have hA1 := cuspBdd_TA1 (K := K) (T := T) hK
  have hA2 := cuspBdd_TA2 (K := K) (T := T) hK
  have hj := cuspBdd_j (K := K) (T := T) hK
  have h1 : CuspBdd K T (fun τ _ => 6 * TA0 τ) 0 0 :=
    ((cuspBdd_const (6 : ℂ)).mul hA0).mono hT0 (by norm_num) (by norm_num)
  have hc1 : CuspBdd K T (fun τ _ => -12 * Work.Kernels.jInvariantFun τ) 0 0 :=
    ((cuspBdd_const (-12 : ℂ)).mul hj).mono hT0 (by norm_num) (by norm_num)
  have hcoef : CuspBdd K T (fun τ _ => -12 * Work.Kernels.jInvariantFun τ + 5 * 1728) 0 0 :=
    hc1.add (cuspBdd_const (5 * 1728 : ℂ))
  have h2 : CuspBdd K T (fun τ _ => (-12 * Work.Kernels.jInvariantFun τ + 5 * 1728) * TA1 τ) 0 0 :=
    (hcoef.mul hA1).mono hT0 (by norm_num) (by norm_num)
  have h3 : CuspBdd K T (fun τ _ => 6 * TA2 τ) 0 0 :=
    ((cuspBdd_const (6 : ℂ)).mul hA2).mono hT0 (by norm_num) (by norm_num)
  exact ((h1.add h2).add h3).congr (fun τ z => by show _ = TP1 τ; rw [TP1])

lemma cuspBdd_TP2 (hK : IsCompact K) (hT1 : 1 ≤ T) :
    CuspBdd K T (fun τ _ => TP2 τ) 0 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hA0 := cuspBdd_TA0 (K := K) (T := T) hK
  have hA1 := cuspBdd_TA1 (K := K) (T := T) hK
  have hA2 := cuspBdd_TA2 (K := K) (T := T) hK
  have hj := cuspBdd_j (K := K) (T := T) hK
  have h1 : CuspBdd K T (fun τ _ => -6 * TA0 τ) 0 0 :=
    ((cuspBdd_const (-6 : ℂ)).mul hA0).mono hT0 (by norm_num) (by norm_num)
  have hc1 : CuspBdd K T (fun τ _ => 12 * Work.Kernels.jInvariantFun τ) 0 0 :=
    ((cuspBdd_const (12 : ℂ)).mul hj).mono hT0 (by norm_num) (by norm_num)
  have hcoef : CuspBdd K T (fun τ _ => 12 * Work.Kernels.jInvariantFun τ - 7 * 1728) 0 0 :=
    hc1.sub (cuspBdd_const (7 * 1728 : ℂ))
  have h2 : CuspBdd K T (fun τ _ => (12 * Work.Kernels.jInvariantFun τ - 7 * 1728) * TA1 τ) 0 0 :=
    (hcoef.mul hA1).mono hT0 (by norm_num) (by norm_num)
  have h3 : CuspBdd K T (fun τ _ => -6 * TA2 τ) 0 0 :=
    ((cuspBdd_const (-6 : ℂ)).mul hA2).mono hT0 (by norm_num) (by norm_num)
  exact ((h1.add h2).add h3).congr (fun τ z => by show _ = TP2 τ; rw [TP2]; ring)

lemma cuspBdd_Ymo (hK : IsCompact K) (hT1 : 1 ≤ T) :
    CuspBdd K T (fun τ z => Ymo τ z) (-2) 2 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hA0 := cuspBdd_TA0 (K := K) (T := T) hK
  have hA1 := cuspBdd_TA1 (K := K) (T := T) hK
  have hA2 := cuspBdd_TA2 (K := K) (T := T) hK
  have h1 : CuspBdd K T (fun τ z => TA0 τ * (mG z) ^ 2) (-2) 2 :=
    ((hA0.mul (cuspBdd_mG2 hT1)).mono hT0 (by norm_num) (by norm_num))
  have h2 : CuspBdd K T (fun τ z => TA1 τ * mE14D z * ((z : ℂ) * mG z)) (-2) 2 :=
    (((hA1.mul (cuspBdd_mE14D hT1)).mul (cuspBdd_z_mG hT1)).mono hT0 (by norm_num) (by norm_num))
  have h3 : CuspBdd K T (fun τ z => TA2 τ * (mE4 z * (z : ℂ) ^ 2)) (-2) 2 :=
    (((hA2.mul ((cuspBdd_mE4s hT1).mul (cuspBdd_zsq hT1)))).mono hT0 (by norm_num) (by norm_num))
  exact ((h1.sub (h2.const_mul 2)).add h3).congr (fun τ z => by
    show _ = Ymo τ z; rw [Ymo]; ring)

/-! ## §4  The `z`-atoms of the `K₋^{(24)}` difference -/

lemma cuspBdd_Lmod (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Lmod ℓ z) 0 1 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => (Real.pi : ℂ) * Complex.I * (z : ℂ)) 0 1 :=
    ((cuspBdd_const ((Real.pi : ℂ) * Complex.I)).mul (CuspBdd.coe K T)).mono
      hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => cuspL ℓ) 0 1 :=
    (cuspBdd_const (cuspL ℓ)).mono hT0 (by norm_num) (by norm_num)
  have h3 : CuspBdd K T (fun _ z => (-8 : ℂ) * Work.Residues.Ept z) 0 1 :=
    ((cuspBdd_const (-8 : ℂ)).mul (CuspBdd.Ept K T)).mono hT0 (by norm_num) (by norm_num)
  have h4 : CuspBdd K T (fun _ z => (12 : ℂ) * mq z) 0 1 :=
    ((cuspBdd_const (12 : ℂ)).mul (cuspBdd_mq hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (((h1.add h2).add h3).add h4).congr (fun τ z => by
    show _ = Lmod ℓ z; rw [Lmod]; ring)

lemma cuspBdd_D0 (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => D0 ℓ z) (-2) 1 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z * ℓ.L z)
      ((-2) + 0) (0 + 1) := (cuspBdd_E14D_inv hT1).mul (cuspBdd_L ℓ hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr (fun τ z => by
    show Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z * ℓ.L z = D0 ℓ z
    rw [D0])

lemma cuspBdd_KD0 (ℓ : Work.Kernels.LogLambdaData) (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => KD0 ℓ z) 1 1 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z - mE14D z)
      * ℓ.L z) 1 1 :=
    ((cuspBdd_mE14D_sub hT1).mul (cuspBdd_L ℓ hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => mE14D z * (ℓ.L z - Lmod ℓ z)) 1 1 :=
    ((cuspBdd_mE14D hT1).mul (cuspBdd_Lm ℓ hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by
    show _ = KD0 ℓ z; rw [KD0, D0]; ring)

lemma cuspBdd_D3 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => D3 z) (-2) 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h : CuspBdd K T (fun _ z => Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)) ((-2) + 0) (0 + 0) :=
    (cuspBdd_E10D_inv hT1).mul (cuspBdd_Ds hT1)
  exact (h.mono hT0 (by norm_num) (by norm_num)).congr (fun τ z => by
    show Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2) = D3 z
    rw [D3])

lemma cuspBdd_KD3 (hT1 : 1 ≤ T) : CuspBdd K T (fun _ z => KD3 z) 1 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z - mE10D z)
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)) 1 0 :=
    ((cuspBdd_mE10D_sub hT1).mul (cuspBdd_Ds hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => mE10D z
      * ((Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2) - mD z)) 1 0 :=
    ((cuspBdd_mE10D hT1).mul (cuspBdd_Dm hT1)).mono hT0 (by norm_num) (by norm_num)
  exact (h1.add h2).congr (fun τ z => by
    show _ = KD3 z; rw [KD3, D3]; ring)

lemma cuspBdd_WdivDelta_sub (hT1 : 1 ≤ T) :
    CuspBdd K T (fun _ z => Work.Kernels.WFun z / Work.Kernels.DeltaFun z - minvD z * mW z) 1 0 := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have h1 : CuspBdd K T (fun _ z => Work.Kernels.WFun z
      * ((Work.Kernels.DeltaFun z)⁻¹ - minvD z)) 1 0 :=
    ((cuspBdd_Ws hT1).mul (cuspBdd_invDelta_sub hT1)).mono hT0 (by norm_num) (by norm_num)
  have h2 : CuspBdd K T (fun _ z => minvD z * (Work.Kernels.WFun z - mW z)) 1 0 :=
    ((cuspBdd_minvD hT1).mul (cuspBdd_Wm hT1)).mono hT0 (by norm_num) (by norm_num)
  have hsum : CuspBdd K T (fun _ z => Work.Kernels.WFun z * ((Work.Kernels.DeltaFun z)⁻¹ - minvD z)
      + minvD z * (Work.Kernels.WFun z - mW z)) 1 0 := h1.add h2
  exact hsum.congr (fun τ z => by
    show _ = Work.Kernels.WFun z / Work.Kernels.DeltaFun z - minvD z * mW z
    rw [div_eq_mul_inv]; ring)

lemma cuspBdd_D2 (hT1 : 1 ≤ T)
    (hjne : ∀ τ ∈ K, ∀ z : ℍ, T ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    CuspBdd K T (fun τ z => D2 τ z) 1 0 := by
  obtain ⟨C, hC, hb⟩ := cuspBdd_WdivDelta_sub (K := K) (T := T) hT1
  refine ⟨C, hC, fun τ hτ z hz => ?_⟩
  have hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 :=
    sub_ne_zero.mpr (hjne τ hτ z hz)
  have hRJ : Rz τ z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
      = (Work.Kernels.DeltaFun z)⁻¹ := by
    have h : Rz τ z = (Work.Kernels.DeltaFun z)⁻¹
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹ := by
      rw [Rz, mul_inv]
    rw [h, mul_assoc, inv_mul_cancel₀ hJ, mul_one]
  have heq : D2 τ z = Work.Kernels.WFun z / Work.Kernels.DeltaFun z - minvD z * mW z := by
    rw [D2, hRJ, div_eq_mul_inv]; ring
  change ‖D2 τ z‖ ≤ C * cuspG z 0 1
  rw [heq]; exact hb τ hτ z hz

/-! ## §5  The main theorem -/

theorem kernel24_cuspExp (ℓ : Work.Kernels.LogLambdaData) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ T : ℝ, 0 < T ∧ ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ z : UpperHalfPlane, T ≤ z.im →
      ‖Work.Kernels.KPlus 24 τ z - Work.Asymptotics.MP24 τ z‖ ≤ C * Work.Asymptotics.cuspG z 3 1 ∧
      ‖Work.Kernels.KMinus ℓ 24 τ z - Work.Asymptotics.MM24 ℓ τ z‖ ≤ C * Work.Asymptotics.cuspG z 3 1 := by
  obtain ⟨TR, hTR0, CR, hCR, hRb⟩ := cusp_inv_divisor_second hK
  obtain ⟨T0, M0, hT00, hM00, hExp0⟩ := Work.Asymptotics.jInvariantFun_cusp_second
  obtain ⟨Bj, hBj0, hBj⟩ := cuspBdd_tauAtom continuous_jInvariantFun_ub hK
  have hBpos : 0 < Bj + 745 + M0 + 1 := by linarith
  set T : ℝ := max (max (max 1 TR) T0) (Real.log (Bj + 745 + M0 + 1) / (2 * Real.pi)) with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    exact le_trans (le_trans (le_max_left 1 TR) (le_max_left (max 1 TR) T0))
      (le_max_left (max (max 1 TR) T0) _)
  have hT0' : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hTRle : TR ≤ T := by
    rw [hTdef]
    exact le_trans (le_trans (le_max_right 1 TR) (le_max_left (max 1 TR) T0))
      (le_max_left (max (max 1 TR) T0) _)
  have hT0le : T0 ≤ T := by
    rw [hTdef]
    exact le_trans (le_max_right (max 1 TR) T0) (le_max_left (max (max 1 TR) T0) _)
  have hLle : Real.log (Bj + 745 + M0 + 1) / (2 * Real.pi) ≤ T := by
    rw [hTdef]; exact le_max_right _ _
  have hlog : Real.log (Bj + 745 + M0 + 1) ≤ 2 * Real.pi * T := by
    have h := mul_le_mul_of_nonneg_left hLle (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    rwa [mul_div_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at h
  have jne : ∀ τ ∈ K, ∀ z : ℍ, T ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro τ hτ z hz
    have hzT0 : T0 ≤ z.im := le_trans hT0le hz
    have hEr := hExp0 z hzT0
    have hEr' : ‖Work.Kernels.jInvariantFun z
        - ((Work.Residues.Ept z)⁻¹ ^ 2 + 744)‖ ≤ M0 * ‖Work.Residues.Ept z‖ ^ 2 := by
      have hEq : Work.Kernels.jInvariantFun z - (Work.Residues.Ept z)⁻¹ ^ 2 - 744
          = Work.Kernels.jInvariantFun z - ((Work.Residues.Ept z)⁻¹ ^ 2 + 744) := by ring
      rw [← hEq]; exact hEr
    have hnormE : ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ = Real.exp (2 * Real.pi * z.im) := by
      have h1 : ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ = (‖Work.Residues.Ept z‖ ^ 2)⁻¹ := by
        rw [norm_pow, norm_inv, sq, sq, mul_inv]
      rw [h1, ← norm_qParamFun_eq_Ept_sq, inv_norm_qParamFun_eq_exp]
    have hRle : Bj + 745 + M0 + 1 ≤ ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ := by
      rw [hnormE]
      have h1 : Real.exp (Real.log (Bj + 745 + M0 + 1)) ≤ Real.exp (2 * Real.pi * T) :=
        Real.exp_le_exp.mpr hlog
      have h2 : Real.exp (2 * Real.pi * T) ≤ Real.exp (2 * Real.pi * z.im) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      calc Bj + 745 + M0 + 1 = Real.exp (Real.log (Bj + 745 + M0 + 1)) := by
            rw [Real.exp_log hBpos]
        _ ≤ Real.exp (2 * Real.pi * z.im) := le_trans h1 h2
    have hMle : M0 * ‖Work.Residues.Ept z‖ ^ 2 ≤ M0 := by
      have h2 : ‖Work.Residues.Ept z‖ ^ 2 ≤ 1 := norm_Ept_sq_le_one z
      nlinarith [hM00.le]
    have hA : ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖ ≤ ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ + 744 := by
      calc _ ≤ ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ + ‖(744 : ℂ)‖ := norm_add_le _ _
        _ = ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ + 744 := by rw [Complex.norm_ofNat]
    have hb := abs_norm_sub_norm_le (Work.Kernels.jInvariantFun z)
      ((Work.Residues.Ept z)⁻¹ ^ 2 + 744)
    have hb1 : ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖ - ‖Work.Kernels.jInvariantFun z‖
        ≤ |‖Work.Kernels.jInvariantFun z‖ - ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have hA' : ‖(Work.Residues.Ept z)⁻¹ ^ 2‖ - 744
        ≤ ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖ := by
      have h := norm_sub_le ((Work.Residues.Ept z)⁻¹ ^ 2 + 744) (744 : ℂ)
      rw [add_sub_cancel_right, Complex.norm_ofNat] at h
      linarith
    have hjz : Bj + 2 ≤ ‖Work.Kernels.jInvariantFun z‖ := by
      have hb2 : ‖(Work.Residues.Ept z)⁻¹ ^ 2 + 744‖ - ‖Work.Kernels.jInvariantFun z‖
          ≤ M0 * ‖Work.Residues.Ept z‖ ^ 2 := le_trans hb1 (le_trans hb hEr')
      nlinarith [hb2, hA', hRle, hMle]
    intro hcontra
    have hτb := hBj τ hτ
    rw [hcontra] at hτb
    linarith
  -- the T-dependent atoms
  have hRzsub : CuspBdd K T (fun τ z => Rz τ z - mR τ z) 4 0 := by
    refine ⟨CR, hCR, fun τ hτ z hz => ?_⟩
    have h := hRb τ hτ z (le_trans hTRle hz)
    change ‖Rz τ z - mR τ z‖ ≤ CR * cuspG z 0 4
    have hg : cuspG z 0 4 = ‖Work.Residues.Ept z‖ ^ 4 := by simp [cuspG]
    rw [hg]
    have hthis : Rz τ z - mR τ z
        = (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))⁻¹
          + 1 - (720 - Work.Kernels.jInvariantFun τ) * (Work.Residues.Ept z) ^ 2 := by
      rw [Rz, mR, mq, qParamFun_eq_Ept_sq]; ring
    rw [hthis]; exact h
  have hmR : CuspBdd K T (fun τ z => mR τ z) 0 0 := by
    refine ⟨721 + Bj, by positivity, fun τ hτ z _ => ?_⟩
    change ‖mR τ z‖ ≤ (721 + Bj) * cuspG z 0 0
    have hq : ‖Work.Kernels.qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z
    have hb := hBj τ hτ
    have hEq : mR τ z = -1 + (720 - Work.Kernels.jInvariantFun τ) * Work.Kernels.qParamFun z := by
      rw [mR, mq]
    rw [hEq]
    have h1 : ‖(720 : ℂ) - Work.Kernels.jInvariantFun τ‖ ≤ 720 + Bj := by
      calc ‖(720 : ℂ) - Work.Kernels.jInvariantFun τ‖
          ≤ ‖(720 : ℂ)‖ + ‖Work.Kernels.jInvariantFun τ‖ := norm_sub_le _ _
        _ ≤ 720 + Bj := by rw [Complex.norm_ofNat]; linarith
    have h2 : ‖(720 - Work.Kernels.jInvariantFun τ) * Work.Kernels.qParamFun z‖ ≤ 720 + Bj := by
      rw [norm_mul]
      refine le_trans (mul_le_mul h1 hq (norm_nonneg _) (by positivity)) ?_
      rw [mul_one]
    simp only [cuspG, Real.rpow_zero, zpow_zero, mul_one]
    calc ‖(-1 : ℂ) + (720 - Work.Kernels.jInvariantFun τ) * Work.Kernels.qParamFun z‖
        ≤ ‖(-1 : ℂ)‖
          + ‖(720 - Work.Kernels.jInvariantFun τ) * Work.Kernels.qParamFun z‖ := norm_add_le _ _
      _ ≤ 1 + (720 + Bj) := by rw [norm_neg, norm_one]; linarith [h2]
      _ = 721 + Bj := by ring
  have hRz : CuspBdd K T (fun τ z => Rz τ z) 0 0 :=
    (hmR.add (hRzsub.mono hT0' (by norm_num) (by norm_num))).congr
      (fun τ z => by show mR τ z + (Rz τ z - mR τ z) = Rz τ z; ring)
  have hmRsub : CuspBdd K T (fun τ z => mR τ z - minvD z * minvJ τ z) 4 0 := by
    refine ⟨24 * (744 + Bj) + 1, by positivity, fun τ hτ z _ => ?_⟩
    change ‖mR τ z - minvD z * minvJ τ z‖ ≤ (24 * (744 + Bj) + 1) * cuspG z 0 4
    have hb := hBj τ hτ
    have hEq : mR τ z - minvD z * minvJ τ z
        = -24 * (744 - Work.Kernels.jInvariantFun τ) * (mq z) ^ 2 := by
      have hE : Work.Residues.Ept z ≠ 0 := Work.Residues.Ept_ne_zero z
      rw [mR, minvD, minvJ, mq, qParamFun_eq_Ept_sq]
      field_simp
      ring
    have hg : cuspG z 0 4 = ‖Work.Residues.Ept z‖ ^ 4 := by simp [cuspG]
    have h1 : ‖(744 : ℂ) - Work.Kernels.jInvariantFun τ‖ ≤ 744 + Bj := by
      calc ‖(744 : ℂ) - Work.Kernels.jInvariantFun τ‖
          ≤ ‖(744 : ℂ)‖ + ‖Work.Kernels.jInvariantFun τ‖ := norm_sub_le _ _
        _ ≤ 744 + Bj := by rw [Complex.norm_ofNat]; linarith
    have h2 : ‖(mq z) ^ 2‖ = ‖Work.Residues.Ept z‖ ^ 4 := by
      rw [norm_pow, mq, norm_qParamFun_eq_Ept_sq]; ring
    rw [hEq, hg]
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, h2]
    calc 24 * ‖(744 : ℂ) - Work.Kernels.jInvariantFun τ‖ * ‖Work.Residues.Ept z‖ ^ 4
        ≤ 24 * (744 + Bj) * ‖Work.Residues.Ept z‖ ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) (by positivity)
      _ ≤ (24 * (744 + Bj) + 1) * ‖Work.Residues.Ept z‖ ^ 4 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hEz6 : CuspBdd K T (fun τ z => Ez6 τ z) 4 0 :=
    ((hRzsub.add hmRsub).mono hT0' (by norm_num) (by norm_num)).congr
      (fun τ z => by
        show Rz τ z - mR τ z + (mR τ z - minvD z * minvJ τ z) = Ez6 τ z
        rw [Ez6]
        ring)
  -- the `K₊` inner bracket
  have hzEz1 : CuspBdd K T (fun _ z => (z : ℂ) ^ 2 * Ez1 z) 2 2 :=
    ((cuspBdd_zsq hT1).mul (cuspBdd_Ez1 hT1)).mono hT0' (by norm_num) (by norm_num)
  have hTP1z : CuspBdd K T (fun τ z => TP1 τ * ((z : ℂ) ^ 2 * Ez1 z)) 2 2 :=
    ((cuspBdd_TP1 hK hT1).mul hzEz1).mono hT0' (by norm_num) (by norm_num)
  have hTP2Ez2 : CuspBdd K T (fun τ z => TP2 τ * Ez2 z) 2 2 :=
    ((cuspBdd_TP2 hK hT1).mul (cuspBdd_Ez2 hT1)).mono hT0' (by norm_num) (by norm_num)
  have hbr : CuspBdd K T (fun τ z => TA0 τ * Ez3 z - 2 * TA1 τ * Ez4 z + TA2 τ * Ez5 z) 2 2 := by
    have h1 : CuspBdd K T (fun τ z => TA0 τ * Ez3 z) 2 2 :=
      ((cuspBdd_TA0 hK).mul (cuspBdd_Ez3 hT1)).mono hT0' (by norm_num) (by norm_num)
    have h2 : CuspBdd K T (fun τ z => 2 * (TA1 τ * Ez4 z)) 2 2 :=
      ((cuspBdd_const (2 : ℂ)).mul ((cuspBdd_TA1 hK).mul (cuspBdd_Ez4 hT1))).mono
        hT0' (by norm_num) (by norm_num)
    have h3 : CuspBdd K T (fun τ z => TA2 τ * Ez5 z) 2 2 :=
      ((cuspBdd_TA2 hK).mul (cuspBdd_Ez5 hT1)).mono hT0' (by norm_num) (by norm_num)
    exact ((h1.sub h2).add h3).congr (fun τ z => by ring)
  have hRzbr : CuspBdd K T (fun τ z => Rz τ z
      * (TA0 τ * Ez3 z - 2 * TA1 τ * Ez4 z + TA2 τ * Ez5 z)) 2 2 :=
    (hRz.mul hbr).mono hT0' (by norm_num) (by norm_num)
  have hEz6Ymo : CuspBdd K T (fun τ z => Ez6 τ z * Ymo τ z) 2 2 :=
    (hEz6.mul (cuspBdd_Ymo hK hT1)).mono hT0' (by norm_num) (by norm_num)
  have hInnerP : CuspBdd K T (fun τ z => TP1 τ * ((z : ℂ) ^ 2 * Ez1 z) + TP2 τ * Ez2 z
      + 1728 * (Rz τ z * (TA0 τ * Ez3 z - 2 * TA1 τ * Ez4 z + TA2 τ * Ez5 z)
          + Ez6 τ z * Ymo τ z)) 2 2 := by
    have h3 : CuspBdd K T (fun τ z => (1728 : ℂ) * (Rz τ z
        * (TA0 τ * Ez3 z - 2 * TA1 τ * Ez4 z + TA2 τ * Ez5 z) + Ez6 τ z * Ymo τ z)) 2 2 :=
      ((cuspBdd_const (1728 : ℂ)).mul (hRzbr.add hEz6Ymo)).mono hT0' (by norm_num) (by norm_num)
    exact ((hTP1z.add hTP2Ez2).add h3).congr (fun τ z => by ring)
  have hKPlus : CuspBdd K T (fun τ z => Work.Kernels.KPlus 24 τ z - MP24 τ z) 1 3 :=
    (((CuspBdd.const_mul cuspC24 hInnerP).congr (fun τ z => (KPlus24_diff τ z).symm)).mono
      hT0' (by norm_num) (by norm_num))
  -- the `K₋` inner bracket
  have hD0 := cuspBdd_D0 ℓ (K := K) (T := T) hT1
  have hKD0 := cuspBdd_KD0 ℓ (K := K) (T := T) hT1
  have hD3 := cuspBdd_D3 (K := K) (T := T) hT1
  have hKD3 := cuspBdd_KD3 (K := K) (T := T) hT1
  have hD2 := cuspBdd_D2 (K := K) (T := T) hT1 jne
  have hG0 : CuspBdd K T (fun τ z => G0 ℓ τ z) 1 1 := by
    have h1 : CuspBdd K T (fun τ z => (Rz τ z - mR τ z) * D0 ℓ z) 1 1 :=
      (hRzsub.mul hD0).mono hT0' (by norm_num) (by norm_num)
    have h2 : CuspBdd K T (fun τ z => mR τ z * KD0 ℓ z) 1 1 :=
      (hmR.mul hKD0).mono hT0' (by norm_num) (by norm_num)
    exact (h1.add h2).congr (fun τ z => by show _ = G0 ℓ τ z; rw [G0])
  have hG2 : CuspBdd K T (fun τ z => G2 τ z) 1 0 := by
    have h1 : CuspBdd K T (fun τ z => (Rz τ z - mR τ z) * D3 z) 1 0 :=
      (hRzsub.mul hD3).mono hT0' (by norm_num) (by norm_num)
    have h2 : CuspBdd K T (fun τ z => mR τ z * KD3 z) 1 0 :=
      (hmR.mul hKD3).mono hT0' (by norm_num) (by norm_num)
    exact (h1.add h2).congr (fun τ z => by show _ = G2 τ z; rw [G2])
  have hj := cuspBdd_j (K := K) (T := T) hK
  have hW := cuspBdd_Ws (K := K) (T := T) hT1
  have hWm := cuspBdd_Wm (K := K) (T := T) hT1
  have hc1728subj := cuspBdd_c1728sub_j (K := K) (T := T) hK
  have hpsi2 := cuspBdd_psi2 ℓ (K := K) (T := T) hK
  have hpsi4 := cuspBdd_psi4 ℓ (K := K) (T := T) hK
  have hDeltaT : CuspBdd K T (fun τ _ => Work.Kernels.DeltaFun τ) 0 0 := by
    obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom continuous_DeltaFun_ub hK
    exact cuspBdd_tau hB0 hB
  have hE10tau : CuspBdd K T (fun τ _ => Work.Kernels.E10Fun τ) 0 0 := by
    obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (continuous_E4Fun_ub.mul continuous_E6Fun_ub) hK
    exact cuspBdd_tau hB0 hB
  have hE8tau : CuspBdd K T (fun τ _ => Work.Kernels.E8Fun τ) 0 0 := by
    obtain ⟨B, hB0, hB⟩ := cuspBdd_tauAtom (continuous_E4Fun_ub.pow 2) hK
    exact cuspBdd_tau hB0 hB
  have hW1 : CuspBdd K T (fun τ z => Work.Kernels.jInvariantFun τ * (Rz τ z - mR τ z)
      * Work.Kernels.WFun z) 1 0 := ((hj.mul hRzsub).mul hW).mono hT0' (by norm_num) (by norm_num)
  have hW2 : CuspBdd K T (fun τ z => Work.Kernels.jInvariantFun τ * mR τ z
      * (Work.Kernels.WFun z - mW z)) 1 0 :=
    ((hj.mul hmR).mul hWm).mono hT0' (by norm_num) (by norm_num)
  have hW4 : CuspBdd K T (fun τ z => (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ)
      * (Rz τ z - mR τ z) * Work.Kernels.WFun z) 1 0 :=
    ((hc1728subj.mul hRzsub).mul hW).mono hT0' (by norm_num) (by norm_num)
  have hW5 : CuspBdd K T (fun τ z => (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ)
      * mR τ z * (Work.Kernels.WFun z - mW z)) 1 0 :=
    ((hc1728subj.mul hmR).mul hWm).mono hT0' (by norm_num) (by norm_num)
  have hP2in : CuspBdd K T (fun τ z => Work.Kernels.jInvariantFun τ * (Rz τ z - mR τ z)
      * Work.Kernels.WFun z + Work.Kernels.jInvariantFun τ * mR τ z
        * (Work.Kernels.WFun z - mW z) + 2 * D2 τ z - G2 τ z) 1 0 :=
    ((hW1.add hW2).add ((hD2.const_mul 2).sub hG2)).congr (fun τ z => by ring)
  have hP4in : CuspBdd K T (fun τ z => (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ)
      * (Rz τ z - mR τ z) * Work.Kernels.WFun z
      + (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * mR τ z
        * (Work.Kernels.WFun z - mW z) - 2 * D2 τ z + G2 τ z) 1 0 :=
    ((hW4.add hW5).add (((hD2.const_mul 2).neg).add hG2)).congr (fun τ z => by ring)
  have hP2 : CuspBdd K T (fun τ z => Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
      * ( Work.Kernels.jInvariantFun τ * (Rz τ z - mR τ z) * Work.Kernels.WFun z
          + Work.Kernels.jInvariantFun τ * mR τ z * (Work.Kernels.WFun z - mW z)
          + 2 * D2 τ z - G2 τ z )) 1 0 :=
    ((hpsi2.mul hE10tau).mul hP2in).mono hT0' (by norm_num) (by norm_num)
  have hP4 : CuspBdd K T (fun τ z => Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
      * ( (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * (Rz τ z - mR τ z)
            * Work.Kernels.WFun z
          + (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * mR τ z
              * (Work.Kernels.WFun z - mW z)
          - 2 * D2 τ z + G2 τ z )) 1 0 :=
    ((hpsi4.mul hE8tau).mul hP4in).mono hT0' (by norm_num) (by norm_num)
  have hInnerM : CuspBdd K T (fun τ z => Work.Kernels.DeltaFun τ * ((-2 : ℂ) * Work.Kernels.c1728)
      * (G0 ℓ τ z + D2 τ z)
      + Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
          * ( Work.Kernels.jInvariantFun τ * (Rz τ z - mR τ z) * Work.Kernels.WFun z
              + Work.Kernels.jInvariantFun τ * mR τ z * (Work.Kernels.WFun z - mW z)
              + 2 * D2 τ z - G2 τ z )
      + Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
          * ( (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * (Rz τ z - mR τ z)
                * Work.Kernels.WFun z
              + (Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ) * mR τ z
                  * (Work.Kernels.WFun z - mW z)
              - 2 * D2 τ z + G2 τ z )) 1 1 := by
    have hΔ : CuspBdd K T (fun τ z => Work.Kernels.DeltaFun τ * ((-2 : ℂ) * Work.Kernels.c1728)
        * (G0 ℓ τ z + D2 τ z)) 1 1 :=
      ((hDeltaT.mul (cuspBdd_const ((-2 : ℂ) * Work.Kernels.c1728))).mul
        (hG0.add (hD2.mono hT0' (by norm_num) (by norm_num)))).mono hT0' (by norm_num) (by norm_num)
    exact ((hΔ.add (hP2.mono hT0' (by norm_num) (by norm_num))).add
      (hP4.mono hT0' (by norm_num) (by norm_num))).congr (fun τ z => by ring)
  have hKMinus : CuspBdd K T (fun τ z => Work.Kernels.KMinus ℓ 24 τ z - MM24 ℓ τ z) 1 3 :=
    (((CuspBdd.const_mul cuspK24 hInnerM).congr (fun τ z => (KMinus24_diff ℓ τ z).symm)).mono
      hT0' (by norm_num) (by norm_num))
  obtain ⟨C1, hC1, hC1b⟩ := hKPlus
  obtain ⟨C2, hC2, hC2b⟩ := hKMinus
  refine ⟨T, lt_of_lt_of_le one_pos hT1, max C1 C2 + 1, by positivity,
    fun τ hτ z hz => ⟨?_, ?_⟩⟩
  · calc ‖Work.Kernels.KPlus 24 τ z - MP24 τ z‖ ≤ C1 * cuspG z 3 1 := hC1b τ hτ z hz
      _ ≤ (max C1 C2 + 1) * cuspG z 3 1 :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_left C1 C2]) (cuspG_nonneg z 3 1)
  · calc ‖Work.Kernels.KMinus ℓ 24 τ z - MM24 ℓ τ z‖ ≤ C2 * cuspG z 3 1 := hC2b τ hτ z hz
      _ ≤ (max C1 C2 + 1) * cuspG z 3 1 :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_right C1 C2]) (cuspG_nonneg z 3 1)

end


end Work.Asymptotics.CuspExp.Loc

namespace Work.Asymptotics.CuspExp

/-- **The cusp expansion of the CKMRV kernel `K^{(d)}` in terms of the explicit model `MK`.**
Uniformly for `τ` in a compact `K ⊆ ℍ` and `z` with `T ≤ Im z`,

`K^{(d)}(τ,z) = MK ℓ d τ z + O((1+|Re z|+Im z)³ ‖E(z)‖)`, `E(z) = e^{πiz}`,

for `d = 8` and `d = 24`, where `MK` (`CuspExp/Models.lean`) is the model obtained by replacing
every atom of the explicit kernel by its truncated cusp expansion. -/
theorem kernelKfun_cuspExp (ℓ : Work.Kernels.LogLambdaData) {K : Set UpperHalfPlane}
    (hK : IsCompact K) :
    ∃ T : ℝ, 0 < T ∧ ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ z : UpperHalfPlane, T ≤ z.im →
      ‖Work.Kernels.Kfun ℓ 8 τ z - Work.Asymptotics.MK ℓ 8 τ z‖ ≤ C * Work.Asymptotics.cuspG z 3 1 ∧
      ‖Work.Kernels.Kfun ℓ 24 τ z - Work.Asymptotics.MK ℓ 24 τ z‖ ≤ C * Work.Asymptotics.cuspG z 3 1 := by
  obtain ⟨T8, hT8, C8, hC8, hb8⟩ := Work.Asymptotics.CuspExp.Loc.kernel8_cuspExp ℓ hK
  obtain ⟨T24, hT24, C24, hC24, hb24⟩ := Work.Asymptotics.CuspExp.Loc.kernel24_cuspExp ℓ hK
  refine ⟨max T8 T24, lt_max_of_lt_left hT8, max C8 C24, lt_max_of_lt_left hC8,
    fun τ hτ z hz => ⟨?_, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := hb8 τ hτ z (le_trans (le_max_left _ _) hz)
    have hker : Work.Kernels.Kfun ℓ 8 τ z - Work.Asymptotics.MK ℓ 8 τ z =
        ((Work.Kernels.KPlus 8 τ z - MP8 τ z)
          + (Work.Kernels.KMinus ℓ 8 τ z - MM8 ℓ τ z)) / 2 := by
      unfold Work.Kernels.Kfun Work.Asymptotics.MK
      rw [if_pos rfl]
      ring
    have hmain : ‖Work.Kernels.Kfun ℓ 8 τ z - Work.Asymptotics.MK ℓ 8 τ z‖ ≤
        C8 * Work.Asymptotics.cuspG z 3 1 := by
      rw [hker, norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num,
        div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have h3 : ‖(Work.Kernels.KPlus 8 τ z - MP8 τ z)
          + (Work.Kernels.KMinus ℓ 8 τ z - MM8 ℓ τ z)‖ ≤
          2 * (C8 * Work.Asymptotics.cuspG z 3 1) := by
        calc _ ≤ ‖Work.Kernels.KPlus 8 τ z - MP8 τ z‖
              + ‖Work.Kernels.KMinus ℓ 8 τ z - MM8 ℓ τ z‖ := norm_add_le _ _
          _ ≤ C8 * Work.Asymptotics.cuspG z 3 1 + C8 * Work.Asymptotics.cuspG z 3 1 :=
              add_le_add h1 h2
          _ = 2 * (C8 * Work.Asymptotics.cuspG z 3 1) := by ring
      linarith
    exact le_trans hmain
      (mul_le_mul_of_nonneg_right (le_max_left C8 C24) (Work.Asymptotics.cuspG_nonneg z 3 1))
  · obtain ⟨h1, h2⟩ := hb24 τ hτ z (le_trans (le_max_right _ _) hz)
    have hne : ¬ ((24 : ℕ) = 8) := by norm_num
    have hker : Work.Kernels.Kfun ℓ 24 τ z - Work.Asymptotics.MK ℓ 24 τ z =
        ((Work.Kernels.KPlus 24 τ z - MP24 τ z)
          + (Work.Kernels.KMinus ℓ 24 τ z - MM24 ℓ τ z)) / 2 := by
      unfold Work.Kernels.Kfun Work.Asymptotics.MK
      rw [if_neg hne]
      ring
    have hmain : ‖Work.Kernels.Kfun ℓ 24 τ z - Work.Asymptotics.MK ℓ 24 τ z‖ ≤
        C24 * Work.Asymptotics.cuspG z 3 1 := by
      rw [hker, norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num,
        div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have h3 : ‖(Work.Kernels.KPlus 24 τ z - MP24 τ z)
          + (Work.Kernels.KMinus ℓ 24 τ z - MM24 ℓ τ z)‖ ≤
          2 * (C24 * Work.Asymptotics.cuspG z 3 1) := by
        calc _ ≤ ‖Work.Kernels.KPlus 24 τ z - MP24 τ z‖
              + ‖Work.Kernels.KMinus ℓ 24 τ z - MM24 ℓ τ z‖ := norm_add_le _ _
          _ ≤ C24 * Work.Asymptotics.cuspG z 3 1 + C24 * Work.Asymptotics.cuspG z 3 1 :=
              add_le_add h1 h2
          _ = 2 * (C24 * Work.Asymptotics.cuspG z 3 1) := by ring
      linarith
    exact le_trans hmain
      (mul_le_mul_of_nonneg_right (le_max_right C8 C24) (Work.Asymptotics.cuspG_nonneg z 3 1))

end Work.Asymptotics.CuspExp
