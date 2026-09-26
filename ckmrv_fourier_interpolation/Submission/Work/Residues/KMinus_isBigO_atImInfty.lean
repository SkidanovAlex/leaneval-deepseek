import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Residues.KPlus_isBigO_atImInfty
import Submission.Work.Residues.KMinusCuspDefs

namespace Work.Residues

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold

open Work.Kernels

noncomputable section

/-! ## The algebraic reduction

`Υ_-^{(d)}(τ,z)` is `(2·1728·π·Δ(z)·(jτ−jz))⁻¹` times the product
`Π_{a,b,c}(τ) · B · Π_{e,f,g}(z)` of the paper.  Writing `psiVec ℓ τ = (1, ψ₂, ψ₄)` and
`psitVec ℓ z = (𝓛(z), W(z), U(z)²−V(z)²)`, the kernel is a sum of nine products, which we
collect by the *row* of `Υ_-`; each row gives one of the following three combinations:

* `(d=8)`  `−3456·E₄(τ)E₁₀(z)𝓛(z)`,
  `(E₁₄(τ)/Δ(τ))·(E₈(z)W(z) − E₆(z)(U(z)²−V(z)²))`,
  `(1728−jτ)·E₈(z)W(z) + jτ·E₆(z)(U(z)²−V(z)²)`;
* `(d=24)` `Δ(τ)·(−3456(E₁₄(z)/Δ(z))𝓛(z) − 3456(jτ−jz)W(z))`,
  `E₁₀(τ)·((jτ+2(jτ−jz))W(z) − (E₁₀(z)/Δ(z))(U(z)²−V(z)²))`,
  `E₈(τ)·((1728−2(jτ−jz)−jτ)W(z) + (E₁₀(z)/Δ(z))(U(z)²−V(z)²))`.
-/

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


/-! ## The main theorem

The estimate below is assembled from the two decompositions `KMinus8_eq` and `KMinus24_eq`
together with the analytic bounds gathered in `Work.Residues.ThetaDecay`,
`Work.Residues.ThetaLowerBound`, `Work.Residues.LogLambdaBound`, `Work.Residues.XiSlashS`
and `Work.Residues.ThetaExpansion`.  The residual reduction is described in the `## Plan`
comment at the end of the file. -/

theorem KMinus_isBigO_atImInfty (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im →
      ‖Work.Kernels.KMinus ℓ d τ z‖ ≤ C * ‖(τ : ℂ)‖ *
        Real.exp (-((if d = 8 then (2 : ℝ) else 4) * Real.pi * τ.im)) := by
  rcases hd with rfl | rfl
  · -- `d = 8`
    obtain ⟨Hb, Cb, hCb, hb⟩ := bracket8_cusp ℓ z
    obtain ⟨Hk, Ck, hCk, hk⟩ := kpre_inv_cusp z
    refine ⟨max (max Hk Hb) 1, 2 * Ck * Cb + 1, by positivity, fun τ hτ => ?_⟩
    obtain ⟨hτkh, hτ1⟩ := max_le_iff.mp hτ
    obtain ⟨hτk, hτb⟩ := max_le_iff.mp hτkh
    have h1 := hk τ hτk
    have h2 := hb τ hτb
    simp only [pow_zero, mul_one, pow_one] at h1 h2
    have hif : (if (8 : ℕ) = 8 then (2 : ℝ) else 4) = 2 := by norm_num
    have hK : KMinus ℓ 8 τ z = (kpre z τ)⁻¹ * bracket8 ℓ z τ := by
      rw [KMinus8_eq ℓ τ z]
      congr 1
      rw [bracket8_eq]
      simp only [bracket8e, c1728]
    rw [hK, norm_mul, hif]
    have hnt : (1 : ℝ) ≤ ‖(τ : ℂ)‖ := by
      have habs := Complex.abs_im_le_norm (τ : ℂ)
      have him : (τ : ℂ).im = τ.im := UpperHalfPlane.coe_im τ
      rw [him, abs_of_pos τ.im_pos] at habs
      linarith
    have hbound : ‖(kpre z τ)⁻¹‖ * ‖bracket8 ℓ z τ‖
        ≤ (Ck * tpar τ ^ 2) * (Cb * (1 + ‖(τ : ℂ)‖)) :=
      mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hCk.le (pow_nonneg (tpar_nonneg τ) 2))
    have hfin : (Ck * tpar τ ^ 2) * (Cb * (1 + ‖(τ : ℂ)‖))
        ≤ (2 * Ck * Cb + 1) * ‖(τ : ℂ)‖ * Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [← tpar_pow_two τ]
      have hstep1 : (1 : ℝ) + ‖(τ : ℂ)‖ ≤ 2 * ‖(τ : ℂ)‖ := by linarith
      have hnn : (0 : ℝ) ≤ Ck * Cb * tpar τ ^ 2 :=
        mul_nonneg (mul_nonneg hCk.le hCb.le) (pow_nonneg (tpar_nonneg τ) 2)
      calc (Ck * tpar τ ^ 2) * (Cb * (1 + ‖(τ : ℂ)‖))
          = Ck * Cb * tpar τ ^ 2 * (1 + ‖(τ : ℂ)‖) := by ring
        _ ≤ Ck * Cb * tpar τ ^ 2 * (2 * ‖(τ : ℂ)‖) := mul_le_mul_of_nonneg_left hstep1 hnn
        _ = 2 * Ck * Cb * tpar τ ^ 2 * ‖(τ : ℂ)‖ := by ring
        _ ≤ (2 * Ck * Cb + 1) * ‖(τ : ℂ)‖ * tpar τ ^ 2 := by
            have h2' : (0 : ℝ) ≤ tpar τ ^ 2 := pow_nonneg (tpar_nonneg τ) 2
            have h3' : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
            nlinarith [h2', h3', hCk, hCb]
    exact le_trans hbound hfin
  · -- `d = 24`
    obtain ⟨Hb, Cb, hCb, hb⟩ := bracket24_cusp ℓ z
    obtain ⟨Hk, Ck, hCk, hk⟩ := kpre_inv_cusp z
    refine ⟨max (max Hk Hb) 1, 2 * Ck * Cb + 1, by positivity, fun τ hτ => ?_⟩
    obtain ⟨hτkh, hτ1⟩ := max_le_iff.mp hτ
    obtain ⟨hτk, hτb⟩ := max_le_iff.mp hτkh
    have h1 := hk τ hτk
    have h2 := hb τ hτb
    simp only [pow_zero, mul_one, pow_one] at h1 h2
    have hif : (if (24 : ℕ) = 8 then (2 : ℝ) else 4) = 4 := by norm_num
    have hK : KMinus ℓ 24 τ z = (kpre z τ)⁻¹ * bracket24 ℓ z τ := by
      rw [KMinus24_eq ℓ τ z]
      congr 1
      rw [bracket24_eq]
      simp only [bracket24e, c1728]
    rw [hK, norm_mul, hif, ← tpar_pow_four τ]
    have hnt : (1 : ℝ) ≤ ‖(τ : ℂ)‖ := by
      have habs := Complex.abs_im_le_norm (τ : ℂ)
      have him : (τ : ℂ).im = τ.im := UpperHalfPlane.coe_im τ
      rw [him, abs_of_pos τ.im_pos] at habs
      linarith
    have hbound : ‖(kpre z τ)⁻¹‖ * ‖bracket24 ℓ z τ‖
        ≤ (Ck * tpar τ ^ 2) * (Cb * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2) :=
      mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hCk.le (pow_nonneg (tpar_nonneg τ) 2))
    have hfin : (Ck * tpar τ ^ 2) * (Cb * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2)
        ≤ (2 * Ck * Cb + 1) * ‖(τ : ℂ)‖ * tpar τ ^ 4 := by
      have hstep1 : (1 : ℝ) + ‖(τ : ℂ)‖ ≤ 2 * ‖(τ : ℂ)‖ := by linarith
      have hnn : (0 : ℝ) ≤ Ck * Cb * (tpar τ ^ 2 * tpar τ ^ 2) :=
        mul_nonneg (mul_nonneg hCk.le hCb.le)
          (mul_nonneg (pow_nonneg (tpar_nonneg τ) 2) (pow_nonneg (tpar_nonneg τ) 2))
      have h4 : tpar τ ^ 4 = tpar τ ^ 2 * tpar τ ^ 2 := by ring
      calc (Ck * tpar τ ^ 2) * (Cb * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2)
          = Ck * Cb * (tpar τ ^ 2 * tpar τ ^ 2) * (1 + ‖(τ : ℂ)‖) := by ring
        _ ≤ Ck * Cb * (tpar τ ^ 2 * tpar τ ^ 2) * (2 * ‖(τ : ℂ)‖) :=
            mul_le_mul_of_nonneg_left hstep1 hnn
        _ = 2 * Ck * Cb * (tpar τ ^ 2 * tpar τ ^ 2) * ‖(τ : ℂ)‖ := by ring
        _ ≤ (2 * Ck * Cb + 1) * ‖(τ : ℂ)‖ * tpar τ ^ 4 := by
            rw [h4]
            have h2' : (0 : ℝ) ≤ tpar τ ^ 2 * tpar τ ^ 2 :=
              mul_nonneg (pow_nonneg (tpar_nonneg τ) 2) (pow_nonneg (tpar_nonneg τ) 2)
            have h3' : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
            nlinarith [h2', h3', hCk, hCb]
    exact le_trans hbound hfin

end

end Work.Residues

/-
## Plan of the remaining proof (state as of the current session)

Everything is reduced to the two decompositions above plus explicit estimates at the cusp
`i∞`.  Write `t = tpar τ = e^{-π Im τ}`, `E = Epar τ = e^{πiτ}` (`‖E‖ = t`), `a = UFun τ - 1`,
`b = VFun τ`, `j = jInvariantFun τ`, `az = E8Fun z * WFun z`, `bz = E6Fun z * (UFun z^2 - VFun z^2)`.

**Atoms** (delegated; `Submission/Work/Residues/ThetaDecay` etc.).
* `‖UFun τ - 1‖, ‖WFun τ - 1‖, ‖VFun τ‖ ≤ C t`;  `‖Δ‖, ‖E4Fun - 1‖, ‖E6Fun - 1‖ ≤ C t²`.
* `c t ≤ ‖VFun τ‖`, `c t² ≤ ‖Δ‖`.
* `‖ℓ.L τ - πiτ‖ ≤ C`, `‖ℓ.L_S τ‖ ≤ C t`.
* `‖UFun τ - 1 - 8E‖ ≤ C t²`, `‖VFun τ - 16E‖ ≤ C t³`, `‖Δ - E²‖ ≤ C t⁴`,
  `‖ℓ.L_S τ + 16E‖ ≤ C t³`.
* `(xi2Fun ∣[2] S) = -(U+V)`, `(xi4Fun ∣[4] S) = U² + V² - 2W²` (proved: `XiSlashS`).

**Consequences** (region `Im τ ≥ 1`; `q = t²`).
* `ξ₂ - 2 = 2(U - 1 - 8E) + (16E - V) = O(t²)`.
* `ξ₄ - 2 = 4a - 2b + a² + (a-b)² - 2b²` with `4a - 2b = 4(a - 8E) + 2(16E - b) = O(t²)`.
* `E₁₄ - 1`, `E₁₀ - 1`, `E₈ - 1`, `E₄ - E₆`, `E₄² - E₆`, `E₁₄ - E₆²` all `O(t²)`.
* `(ξ₂|₂S) + 1 = -(a + b) = O(t)`,  `(ξ₄|₄S) + 1 = -2a + 4b + O(t²) = O(t)`.
* `P₁ = ξ₂E₁₄ - ξ₄E₆² = (ξ₂-2)E₁₄ - (ξ₄-2)E₆² + 2(E₁₄ - E₆²) = O(t²)`;
  `P₂ = ξ₄E₄³ - ξ₂E₁₄ = O(t²)`;
  `Q₁ = (ξ₂|₂S)E₁₄ - (ξ₄|₄S)E₆² = O(t)`, `Q₂ = (ξ₄|₄S)E₄³ - (ξ₂|₂S)E₁₄ = O(t)`.

**`d = 8`.**  `KMinus8_eq` gives `K_-^{(8)} = (kpre z τ)⁻¹ * bracket` with
`bracket = -3456 E₄E₁₀(z)𝓛(z) + az·Γ + bz·Λ`, where (`Gamm_eq`, `Lamb_eq`)
`Γ = (ψ₂E₁₄ - ψ₄E₆²)/Δ = (𝓛P₁ + 𝓛_SQ₁)/Δ`, `Λ = (ψ₄E₄³ - ψ₂E₁₄)/Δ = (𝓛P₂ + 𝓛_SQ₂)/Δ`.
Hence `‖Γ‖, ‖Λ‖ ≤ C(1+‖τ‖)`, `‖bracket‖ ≤ C(1+‖τ‖)`, and `‖(kpre z τ)⁻¹‖ ≤ C t²`
(because `‖j - jz‖ ≥ c t^{-2}` from `‖Δ‖ ≤ C t²`, `‖Δ‖ ≥ c t²`, `‖E₄‖ ≥ 1/2`).
So `‖K_-^{(8)}‖ ≤ C(1+‖τ‖) t²`, i.e. the stated bound with `e^{-2π Im τ} = t²`.

**`d = 24`.**  `KMinus24_eq` gives `K_-^{(24)} = (kpre z τ)⁻¹ * (Δ·R₀ + ψ₂E₁₀·R₁ + ψ₄E₈·R₂)`
with `R₀ = -3456(E₁₄(z)/Δ(z))𝓛(z) - 3456(j-jz)W(z)`, `R₁ = (j+2(j-jz))W(z) - (E₁₀(z)/Δ(z))D(z)`,
`R₂ = (1728-2(j-jz)-j)W(z) + (E₁₀(z)/Δ(z))D(z)`, `D(z) = U(z)² - V(z)²`.  Regrouping,
`ΔR₀ + ψ₂E₁₀R₁ + ψ₄E₈R₂ = W(z)·B' - 3456Δ(E₁₄(z)/Δ(z))𝓛(z) + (E₁₀(z)/Δ(z))D(z)·C''`
where `B' = -3456Δ(j-jz) + ψ₂E₁₀(j+2(j-jz)) + ψ₄E₈(1728-2(j-jz)-j)` and
`C'' = ψ₄E₈ - ψ₂E₁₀ = 𝓛X + 𝓛_SY` with `X = ξ₄E₈ - ξ₂E₁₀ = O(t²)`, `Y = (ξ₄|₄S)E₈ - (ξ₂|₂S)E₁₀ = O(t)`.
So `‖C''‖ ≤ C(1+‖τ‖)t²` and the first and third summands are `O(t²)`.

It remains to bound `B'`.  Writing `ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S`, `ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S`,
`B' = 𝓛·B₀ + 𝓛_S·b₂ - 3456Δ(j-jz)` with
`B₀ = ξ₂E₁₀(j+2(j-jz)) + ξ₄E₈(1728-2(j-jz)-j)` and
`b₂ = (ξ₂|₂S)E₁₀(j+2(j-jz)) + (ξ₄|₄S)E₈(1728-2(j-jz)-j)`.
Using `j = E₄³/Δ` and `1728Δ = E₄³ - E₆²`:
* `B₀ = -3jX + 1728ξ₄E₈ + 2jz·X` and `-3jX + 1728ξ₄E₈ = E₄²Ñ/Δ` with
  `Ñ = -2ξ₄E₄³ + 3ξ₂E₄²E₆ - ξ₄E₆²`, which (checked symbolically) is divisible by `V⁴`, so
  `Ñ = V⁴·S₁` and `‖E₄²Ñ/Δ‖ ≤ C t²`; hence `‖B₀‖ ≤ C t²`.
* `𝓛_S·b₂ - 3456Δ(j-jz) = [𝓛_S·E₄²Ñ/Δ - 3456E₄³] + [2jz𝓛_SY + 3456Δ jz]`, where
  `Ñ = -2(ξ₄|₄S)E₄³ + 3(ξ₂|₂S)E₄²E₆ - (ξ₄|₄S)E₆² = V·S` and (symbolically)
  `Ñ = -216 t - (27/2)(V - 16E) + ... `, more precisely `Ñ + 216E = O(t³)`.
  With `‖𝓛_S + 16E‖ ≤ C t³`, `‖Ñ + 216E‖ ≤ C t³`, `‖Δ - E²‖ ≤ C t⁴` one gets
  `𝓛_S·E₄²Ñ/Δ - 3456E₄³ = E₄²Δ⁻¹(𝓛_SÑ - 3456E₄Δ) = O(t²)` from the identity
  `𝓛_SÑ - 3456E₄Δ = (𝓛_S + 16E)Ñ - 16E(Ñ + 216E) + 3456(E² - E₄Δ)`.
  The remaining summand `2jz𝓛_SY + 3456Δ jz` is `O(t²)`.
  Therefore `B' = O(‖τ‖ t²)` and so `‖K_-^{(24)}‖ = C t² · O(‖τ‖ t²) = O(‖τ‖ t⁴)`, which is
  the stated bound with `e^{-4π Im τ} = t⁴`.
-/
