/-
# The vanishing of `φ_+` on the crossed translates `T S T` and `T⁻¹ S T⁻¹`

The functional `φ_+` of CKMRV (3.12) vanishes on the ideal
`𝓘_+ = (S+I)R + (T-I)²R + (z-1)R` and takes the values `φ_+(1) = φ_+(TS) = 0`,
`φ_+(T) = 1`.  It is computed from the six-dimensional representation `σ_R` by

  `φ_+ x = (σ_R x) 0 1 - (σ_R x) 0 4`,

because `x ≡ ∑_j (σ_R x) 0 j • M6_j (mod 𝓘 ⊆ 𝓘_+)` (`Work.Residues.rowDiff_mem_of_idealI`)
and modulo `𝓘_+` the six basis elements reduce to `1, T, TS, -1, -T, -TS`
(`Work.Residues.basis_IdealIp_of_basis_IdealI`).  Hence only the entries `(σ_R x) 0 1` and
`(σ_R x) 0 4` survive, the latter with a minus sign.

For the two crossed translates,

* `σ_R (T S T) = σ(T) σ(S) σ(T)`, whose row `0` is `(2, 0, 0, 0, 0, -1)` — both entries
  `0 1` and `0 4` vanish;
* `σ_R (T⁻¹ S T⁻¹) = σ(T)⁻¹ σ(S) σ(T)⁻¹`, whose row `0` is `(0, 0, 0, 0, 0, 1)` — again
  both entries `0 1` and `0 4` vanish.

This is the group-algebra input to the vanishing of the second-variable residue at the
crossed poles.
-/
import Mathlib
import Submission.Work.Residues.Quotient
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Residues.phi_Tpow_mul_inv_eq_zero

open Work.Kernels

namespace Work.Residues

/-! ## The values of `φ_+` on the six elements `1, T, TS, S, ST, STS` -/

/-- `φ_+ (S) = 0`, from `S + I ∈ 𝓘_+` and `φ_+ (I) = 0`. -/
lemma phiPlus_R_S_eq_zero : phiPlus R_S = 0 := by
  have h := phiPlus_eq_zero_of_mem_idealIp R_S_add_one_mem_idealIp
  rw [map_add, phiPlus_one, add_zero] at h
  exact h

lemma phiPlus_M6_zero : phiPlus (M6 0) = 0 := by
  rw [M6_zero]; exact phiPlus_one

lemma phiPlus_M6_one : phiPlus (M6 1) = 1 := by
  rw [M6_one]; exact phiPlus_R_T

lemma phiPlus_M6_two : phiPlus (M6 2) = 0 := by
  rw [M6_two]; exact phiPlus_TS

lemma phiPlus_M6_three : phiPlus (M6 3) = 0 := by
  rw [M6_three]; exact phiPlus_R_S_eq_zero

/-- `φ_+ (ST) = -1`, from `ST + T ∈ 𝓘_+` and `φ_+ (T) = 1`. -/
lemma phiPlus_M6_four : phiPlus (M6 4) = -1 := by
  have h := phiPlus_eq_zero_of_mem_idealIp M6_four_add_one_mem_idealIp
  rw [map_add, M6_one, phiPlus_R_T] at h
  rw [add_eq_zero_iff_eq_neg] at h
  exact h

/-- `φ_+ (STS) = 0`, from `STS + TS ∈ 𝓘_+` and `φ_+ (TS) = 0`. -/
lemma phiPlus_M6_five : phiPlus (M6 5) = 0 := by
  have h := phiPlus_eq_zero_of_mem_idealIp M6_five_add_two_mem_idealIp
  rw [map_add, phiPlus_M6_two, add_zero] at h
  exact h

/-! ## `φ_+` through the six-dimensional representation -/

/-- The functional `φ_+` is the combination `x ↦ (σ_R x) 0 1 - (σ_R x) 0 4` of two entries
of the six-dimensional representation: reducing `x` modulo `𝓘 ⊆ 𝓘_+` gives
`x ≡ ∑_j (σ_R x) 0 j • M6_j`, and modulo `𝓘_+` the elements `M6_3, M6_4, M6_5` equal
`-1, -T, -TS`. -/
theorem phiPlus_eq_sigmaR (x : R) :
    phiPlus x = (sigmaR x) 0 1 - (sigmaR x) 0 4 := by
  have h := rowDiff_mem_of_idealI x 0
  rw [rowDiff, M6_zero, one_mul] at h
  have hx : x - ∑ j, (sigmaR x) 0 j • M6 j ∈ idealIp := idealI_le_idealIp h
  have hsub : phiPlus (x - ∑ j, (sigmaR x) 0 j • M6 j) = 0 :=
    phiPlus_eq_zero_of_mem_idealIp hx
  rw [map_sub] at hsub
  have key : phiPlus x = phiPlus (∑ j, (sigmaR x) 0 j • M6 j) := sub_eq_zero.mp hsub
  rw [key, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Fin.sum_univ_six, phiPlus_M6_zero, phiPlus_M6_one, phiPlus_M6_two, phiPlus_M6_three,
    phiPlus_M6_four, phiPlus_M6_five]
  ring

/-! ## The statement -/

/-- `T⁻¹ S T⁻¹` as a product of the three monomials `T⁻¹`, `S`, `T⁻¹`. -/
private lemma single_Tinv_S_Tinv :
    MonoidAlgebra.single (ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹) (1 : ℂ)
      = MonoidAlgebra.single (ModularGroup.T)⁻¹ 1 * MonoidAlgebra.single (ModularGroup.S) 1
        * MonoidAlgebra.single (ModularGroup.T)⁻¹ 1 := by
  rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
  norm_num

theorem phiPlus_crossed_translates_eq_zero :
    Work.Residues.phiPlus (Work.Kernels.R_T * Work.Kernels.R_S * Work.Kernels.R_T) = 0
  ∧ Work.Residues.phiPlus (MonoidAlgebra.single (ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹) (1 : ℂ)) = 0 := by
  constructor
  · -- `σ_R (T S T) = σ(T) σ(S) σ(T)` has row `0` equal to `(2, 0, 0, 0, 0, -1)`.
    rw [phiPlus_eq_sigmaR, map_mul, map_mul, sigmaR_R_T, sigmaR_R_S]
    simp [Matrix.mul_apply, Fin.sum_univ_six, Work.Modular.sigmaT, Work.Modular.sigmaS]
  · -- `σ_R (T⁻¹ S T⁻¹) = σ(T)⁻¹ σ(S) σ(T)⁻¹` has row `0` equal to `(0, 0, 0, 0, 0, 1)`.
    rw [single_Tinv_S_Tinv, phiPlus_eq_sigmaR, map_mul, map_mul, sigmaR_single_T_inv,
      sigmaR_R_S]
    simp [Matrix.mul_apply, Fin.sum_univ_six, Work.Modular.sigmaTinv, Work.Modular.sigmaS]

end Work.Residues
