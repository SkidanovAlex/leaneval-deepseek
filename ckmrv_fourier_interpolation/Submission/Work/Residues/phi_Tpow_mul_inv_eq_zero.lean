/-
# The vanishing `φ (T^k · (T S)⁻¹) = 0` and `φ (T^k · (T⁻¹ S)⁻¹) = 0` for all `k : ℤ`

The functional `φ` of CKMRV (3.12) on `R = ℂ[SL(2,ℤ)]` takes the value `1` on `M6 1 = T` and
`0` on the other five basis elements `1, TS, S, ST, STS` of `R/𝓘`, and vanishes on the ideal
`𝓘 = (T-I)²R + S(T-I)²R + (z-1)R`.

Since `M6 · x ≡ σ_R(x) M6 (mod 𝓘)` (`Work.Residues.rowDiff_mem_of_idealI`), the first row
`(σ_R x) 0` of the six-dimensional representation of `x` gives the coordinates of `x` in the
basis `M6` modulo `𝓘`; consequently

  `φ x = (σ_R x) 0 1`

(`Work.Residues.phi_eq_sigmaR`).

The two elements of the statement are, with `σ_R` multiplicative and `σ_R (single γ 1) = σ(γ)`
under the representation `σ` of the paper (so `σ_R (single T 1) = sigmaT`,
`σ_R (single S 1) = sigmaS`, `σ_R (single T⁻¹ 1) = sigmaTinv`):

  `σ_R (single (T^k) 1 * single ((T S)⁻¹) 1) = sigmaT^k * (sigmaS * sigmaTinv)`,
  `σ_R (single (T^k) 1 * single ((T⁻¹ S)⁻¹) 1) = sigmaT^k * (sigmaS * sigmaT)`,

because `(T S)⁻¹ = S⁻¹ T⁻¹` and `(T⁻¹ S)⁻¹ = S⁻¹ T`.  The row
`(sigmaT^k) 0 = (1-k, k, 0, 0, 0, 0)` (`Work.Residues.sigmaR_single_T_zpow_row0`, proved by
induction on `k : ℤ` from the two explicit matrices `sigmaT`, `sigmaTinv`) and the columns
`(sigmaS * sigmaTinv) · 1 = (0,0,0,-1,-2,0)`, `(sigmaS * sigmaT) · 1 = (0,0,2,1,0,0)` then give

  `φ (single (T^k) 1 * single ((T S)⁻¹) 1) = 0`,  `φ (single (T^k) 1 * single ((T⁻¹ S)⁻¹) 1) = 0`.
-/
import Mathlib
import Submission.Work.Residues.Quotient
import Submission.Work.Residues.IdealImRowDiffAll

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Residues

open Work.Kernels

/-! ## `φ` through the six-dimensional representation -/

/-- The functional `φ` of CKMRV (3.12) is the first row of the six-dimensional representation
`σ_R`: `φ x = (σ_R x) 0 1`.  Indeed `x ≡ ∑ j, (σ_R x) 0 j • M6 j (mod 𝓘)` and `φ (M6 j)` is `1`
at `j = 1` and `0` elsewhere. -/
theorem phi_eq_sigmaR (x : R) : phi x = (sigmaR x) 0 1 := by
  have h := rowDiff_mem_of_idealI x 0
  rw [rowDiff, M6_zero, one_mul] at h
  have hdec : x = (x - ∑ j, (sigmaR x) 0 j • M6 j) + ∑ j, (sigmaR x) 0 j • M6 j := by abel
  rw [hdec, map_add, phi_eq_zero_of_mem_idealI h, zero_add, map_sum]
  simp only [map_smul, phi_M6, smul_eq_mul]
  rw [Finset.sum_eq_single (1 : Fin 6)]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ (1 : Fin 6)) h

/-! ## The product of two basis monomials -/

private theorem single_mul_single_one (a b : SL(2,ℤ)) :
    MonoidAlgebra.single (a * b) (1 : ℂ) = (MonoidAlgebra.single a 1) * (MonoidAlgebra.single b 1) := by
  rw [MonoidAlgebra.single_mul_single, mul_one]

/-! ## `σ_R` on the inverse monomials `S⁻¹`, `T⁻¹` -/

/-- `σ_R (S⁻¹) = σ(S)` since `σ(S)` is an involution. -/
theorem sigmaR_single_S_inv :
    sigmaR (MonoidAlgebra.single (ModularGroup.S)⁻¹ (1 : ℂ)) = Work.Modular.sigmaS := by
  have hmul : MonoidAlgebra.single (ModularGroup.S)⁻¹ (1 : ℂ)
      * MonoidAlgebra.single (ModularGroup.S) (1 : ℂ) = 1 := by
    rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, MonoidAlgebra.one_def]
    norm_num
  have h2 : sigmaR (MonoidAlgebra.single (ModularGroup.S)⁻¹ (1 : ℂ))
      * Work.Modular.sigmaS = 1 := by
    have hc := congrArg sigmaR hmul
    rw [map_mul, map_one] at hc
    rwa [show sigmaR (MonoidAlgebra.single (ModularGroup.S) (1 : ℂ))
        = Work.Modular.sigmaS from sigmaR_R_S] at hc
  calc sigmaR (MonoidAlgebra.single (ModularGroup.S)⁻¹ (1 : ℂ))
      = sigmaR (MonoidAlgebra.single (ModularGroup.S)⁻¹ (1 : ℂ)) * 1 := by rw [mul_one]
    _ = sigmaR (MonoidAlgebra.single (ModularGroup.S)⁻¹ (1 : ℂ))
          * (Work.Modular.sigmaS * Work.Modular.sigmaS) := by rw [Work.Modular.sigmaS_mul_self]
    _ = (sigmaR (MonoidAlgebra.single (ModularGroup.S)⁻¹ (1 : ℂ))
          * Work.Modular.sigmaS) * Work.Modular.sigmaS := by rw [mul_assoc]
    _ = 1 * Work.Modular.sigmaS := by rw [h2]
    _ = Work.Modular.sigmaS := by rw [one_mul]

/-- `σ_R (T⁻¹) = σ(T)⁻¹ = sigmaTinv`. -/
theorem sigmaR_single_T_inv :
    sigmaR (MonoidAlgebra.single (ModularGroup.T)⁻¹ (1 : ℂ)) = Work.Modular.sigmaTinv := by
  have hmul : MonoidAlgebra.single (ModularGroup.T)⁻¹ (1 : ℂ)
      * MonoidAlgebra.single (ModularGroup.T) (1 : ℂ) = 1 := by
    rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, MonoidAlgebra.one_def]
    norm_num
  have h2 : sigmaR (MonoidAlgebra.single (ModularGroup.T)⁻¹ (1 : ℂ))
      * Work.Modular.sigmaT = 1 := by
    have hc := congrArg sigmaR hmul
    rw [map_mul, map_one] at hc
    rwa [show sigmaR (MonoidAlgebra.single (ModularGroup.T) (1 : ℂ))
        = Work.Modular.sigmaT from sigmaR_R_T] at hc
  calc sigmaR (MonoidAlgebra.single (ModularGroup.T)⁻¹ (1 : ℂ))
      = sigmaR (MonoidAlgebra.single (ModularGroup.T)⁻¹ (1 : ℂ)) * 1 := by rw [mul_one]
    _ = sigmaR (MonoidAlgebra.single (ModularGroup.T)⁻¹ (1 : ℂ))
          * (Work.Modular.sigmaT * Work.Modular.sigmaTinv) := by rw [Work.Modular.sigmaT_mul_sigmaTinv]
    _ = (sigmaR (MonoidAlgebra.single (ModularGroup.T)⁻¹ (1 : ℂ))
          * Work.Modular.sigmaT) * Work.Modular.sigmaTinv := by rw [mul_assoc]
    _ = 1 * Work.Modular.sigmaTinv := by rw [h2]
    _ = Work.Modular.sigmaTinv := by rw [one_mul]

/-! ## The first row of `σ(T^k)` -/

/-- The first row of `σ(T^k)` is `(1-k, k, 0, 0, 0, 0)` for every `k : ℤ`.  Proved by the
two-directional induction `Int.induction_on`, the two steps being the explicit multiplications
`![1-k, k, 0, 0, 0, 0] * sigmaT = ![1-(k+1), k+1, 0, 0, 0, 0]` and
`![1-k, k, 0, 0, 0, 0] * sigmaTinv = ![1-(k-1), k-1, 0, 0, 0, 0]`. -/
theorem sigmaR_single_T_zpow_row0 (k : ℤ) :
    (sigmaR (MonoidAlgebra.single (ModularGroup.T ^ k) (1 : ℂ))) 0
      = ![1 - (k : ℂ), (k : ℂ), 0, 0, 0, 0] := by
  induction k using Int.induction_on with
  | zero =>
    rw [zpow_zero, ← MonoidAlgebra.one_def, map_one]
    ext j; fin_cases j <;> simp [Matrix.one_apply]
  | succ n ih =>
    rw [_root_.zpow_add_one, single_mul_single_one, map_mul, sigmaR_R_T]
    ext j
    rw [Matrix.mul_apply, Fin.sum_univ_six, ih]
    fin_cases j <;> simp [Work.Modular.sigmaT] <;> push_cast <;> ring
  | pred n ih =>
    rw [show (-(n : ℤ) - 1) = -(n : ℤ) + (-1) by ring, zpow_add ModularGroup.T]
    rw [single_mul_single_one, map_mul, _root_.zpow_neg_one, sigmaR_single_T_inv]
    ext j
    rw [Matrix.mul_apply, Fin.sum_univ_six, ih]
    fin_cases j <;> simp [Work.Modular.sigmaTinv] <;> push_cast <;> ring

/-! ## The two elements `(T S)⁻¹` and `(T⁻¹ S)⁻¹` under `σ_R` -/

/-- `σ_R ((T S)⁻¹) = σ(S) σ(T)⁻¹`. -/
theorem sigmaR_single_TS_inv :
    sigmaR (MonoidAlgebra.single (ModularGroup.T * ModularGroup.S)⁻¹ (1 : ℂ))
      = Work.Modular.sigmaS * Work.Modular.sigmaTinv := by
  rw [show ((ModularGroup.T * ModularGroup.S)⁻¹ : SL(2, ℤ))
      = (ModularGroup.S)⁻¹ * (ModularGroup.T)⁻¹ from _root_.mul_inv_rev _ _]
  rw [single_mul_single_one, map_mul, sigmaR_single_S_inv, sigmaR_single_T_inv]

/-- `σ_R ((T⁻¹ S)⁻¹) = σ(S) σ(T)`. -/
theorem sigmaR_single_TinvS_inv :
    sigmaR (MonoidAlgebra.single (ModularGroup.T⁻¹ * ModularGroup.S)⁻¹ (1 : ℂ))
      = Work.Modular.sigmaS * Work.Modular.sigmaT := by
  rw [show ((ModularGroup.T⁻¹ * ModularGroup.S)⁻¹ : SL(2, ℤ))
      = (ModularGroup.S)⁻¹ * ModularGroup.T from by rw [_root_.mul_inv_rev, inv_inv]]
  rw [single_mul_single_one, map_mul, sigmaR_single_S_inv]
  rw [show sigmaR (MonoidAlgebra.single (ModularGroup.T) (1 : ℂ)) = Work.Modular.sigmaT
      from sigmaR_R_T]

/-! ## The vanishing -/

theorem phi_Tpow_mul_inv_eq_zero (k : ℤ) :
    Work.Residues.phi (MonoidAlgebra.single (ModularGroup.T ^ k) (1 : ℂ)
        * MonoidAlgebra.single (ModularGroup.T * ModularGroup.S)⁻¹ (1 : ℂ)) = 0
      ∧ Work.Residues.phi (MonoidAlgebra.single (ModularGroup.T ^ k) (1 : ℂ)
        * MonoidAlgebra.single (ModularGroup.T⁻¹ * ModularGroup.S)⁻¹ (1 : ℂ)) = 0 := by
  have hrow := sigmaR_single_T_zpow_row0 k
  constructor
  · rw [phi_eq_sigmaR, map_mul, sigmaR_single_TS_inv]
    rw [Matrix.mul_apply, Fin.sum_univ_six, hrow]
    simp [Work.Modular.sigmaS, Work.Modular.sigmaTinv]
  · rw [phi_eq_sigmaR, map_mul, sigmaR_single_TinvS_inv]
    rw [Matrix.mul_apply, Fin.sum_univ_six, hrow]
    simp [Work.Modular.sigmaS, Work.Modular.sigmaT]

end Work.Residues
