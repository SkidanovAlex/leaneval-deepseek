import Mathlib
import Submission.Work.Residues.IdealImDefs

set_option maxHeartbeats 1000000

open scoped MonoidAlgebra MatrixGroups

namespace Work.Residues

open Work.Kernels

/-! ## Two elementary rewrites used in the computation

`sm` is `MonoidAlgebra.single_mul_single` for coefficients `1`, and `two_smul_one_eq` says that
the scalar `2` of `ℂ` acting on `1 ∈ R` is the natural number `2` of `R` (the two occur in
different normal forms, one from the matrix entries of `σ(T)` and one from the statement). -/

private lemma sm (g h : SL(2,ℤ)) :
    (MonoidAlgebra.single g (1 : ℂ) : R) * MonoidAlgebra.single h (1 : ℂ)
      = MonoidAlgebra.single (g * h) (1 : ℂ) := by
  rw [MonoidAlgebra.single_mul_single]; simp

private lemma two_smul_one_eq : (2 : ℂ) • (1 : R) = (2 : R) :=
  (Algebra.algebraMap_eq_smul_one (2 : ℂ)).symm

/-! ## The `i = 2` computation

`TST - 2 + STS = z·(S(T-I)²(STST)) - STS·(z-I)`: the second summand is a multiple of the
inclusion of `TSTST = S` and the first uses `S² = z`.  We write it in the equivalent form
`TST - 2 + STS = S(T-I)²(z·STST) + (z-I)(-STS)`, in which the two summands are visibly
elements of the two pieces `(T-I)²R + S(T-I)²R` and `(z-I)R` of `𝓘`. -/

private lemma smul_two_one (A B X : R) : Rneg * (A * B * X) = A * B * (Rneg * X) := by
  rw [Rneg_comm (A * B * X), mul_assoc, Rneg_comm X]

private lemma rowDiff_aux2a :
    R_S * (R_T - 1)^2 * (R_S * R_T * R_S * R_T)
      = R_S * R_T * R_S - 2 * Rneg + Rneg * (R_T * R_S * R_T) := by
  rw [show (R_T - 1)^2 = R_T * R_T - 2 * R_T + 1 by noncomm_ring]
  rw [show R_S * (R_T * R_T - 2 * R_T + 1) * (R_S * R_T * R_S * R_T)
      = R_S * (R_T * (R_T * R_S * R_T * R_S * R_T))
        - 2 * (R_S * (R_T * R_S * R_T * R_S * R_T))
        + (R_S * R_S) * (R_T * R_S * R_T) by noncomm_ring]
  rw [R_TSTST, R_S_mul_R_S_eq]
  noncomm_ring

private lemma rowDiff_aux2b :
    R_S * (R_T - 1)^2 * (Rneg * (R_S * R_T * R_S * R_T))
      = Rneg * (R_S * R_T * R_S) - 2 + R_T * R_S * R_T := by
  rw [← smul_two_one R_S ((R_T - 1)^2) (R_S * R_T * R_S * R_T)]
  rw [rowDiff_aux2a]
  rw [show Rneg * (R_S * R_T * R_S - 2 * Rneg + Rneg * (R_T * R_S * R_T))
      = Rneg * (R_S * R_T * R_S) - 2 * (Rneg * Rneg) + (Rneg * Rneg) * (R_T * R_S * R_T)
      by noncomm_ring]
  rw [Rneg_mul_Rneg]
  simp

/-! ## The `i = 5` computation -/

private lemma rowDiff_aux5 :
    R_S * R_T * R_S * R_T + R_T * R_S - 2 * R_S
      = (R_T - 1)^2 * (R_S * R_T * R_S * R_T) := by
  rw [show (R_T - 1)^2 = R_T * R_T - 2 * R_T + 1 by noncomm_ring]
  rw [show (R_T * R_T - 2 * R_T + 1) * (R_S * R_T * R_S * R_T)
      = R_T * (R_T * R_S * R_T * R_S * R_T) - 2 * (R_T * R_S * R_T * R_S * R_T)
        + (R_S * R_T * R_S * R_T) by noncomm_ring]
  rw [R_TSTST]
  noncomm_ring

/-- The `T`-base case of the reduction of the six elements `1, T, TS, S, ST, STS` modulo
`𝓘 = (T-I)²R + S(T-I)²R + (z-1)R` (`z = Rneg = -I`): multiplying the `i`-th of them on the
right by `T` and subtracting its reduction `∑ j, (σ_R R_T) i j • M6 j = ∑ j, sigmaT i j • M6 j`
lands in `𝓘`.

Only `i = 1, 2, 4, 5` are non-trivial: `rowDiff R_T 1 = (T-1)²`,
`rowDiff R_T 4 = S(T-1)²`, `rowDiff R_T 5 = (T-1)² * (S*T*S*T)`, and `rowDiff R_T 2` needs the
group-algebra relations `(S*T)^3 = z` (`Work.Residues.R_ST_cube`) and `T*S*T*S*T = S`
(`Work.Residues.R_TSTST`): `T*S*T - 2 + S*T*S = z * (S*(T-1)^2*(S*T*S*T)) - S*T*S*(z-1)`. -/
theorem rowDiff_R_T_mem (i : Fin 6) :
    Work.Residues.rowDiff Work.Kernels.R_T i ∈ Work.Residues.idealI := by
  fin_cases i
  · change Work.Residues.rowDiff Work.Kernels.R_T 0 ∈ idealI
    rw [show Work.Residues.rowDiff Work.Kernels.R_T 0 = 0 by
      rw [rowDiff, sigmaR_R_T]
      simp [M6, Modular.sigmaT, Fin.sum_univ_six]]
    exact Submodule.zero_mem _
  · change Work.Residues.rowDiff Work.Kernels.R_T 1 ∈ idealI
    rw [show Work.Residues.rowDiff Work.Kernels.R_T 1 = (R_T - 1)^2 by
      rw [rowDiff, sigmaR_R_T]
      show M6 1 * R_T - ∑ j, Modular.sigmaT 1 j • M6 j = _
      simp [M6, Modular.sigmaT, Fin.sum_univ_six, two_smul]
      rw [← sm ModularGroup.T ModularGroup.T]
      noncomm_ring]
    simpa using IdealI_le_idealI (gen_T2_mem_IdealI (1 : R))
  · change Work.Residues.rowDiff Work.Kernels.R_T 2 ∈ idealI
    rw [show Work.Residues.rowDiff Work.Kernels.R_T 2 =
        R_S * (R_T - 1)^2 * (Rneg * (R_S * R_T * R_S * R_T))
          + (Rneg - 1) * (-(R_S * R_T * R_S)) by
      rw [rowDiff, sigmaR_R_T]
      have hL : M6 2 * R_T - ∑ j, Modular.sigmaT 2 j • M6 j
          = R_T * R_S * R_T - 2 + R_S * R_T * R_S := by
        simp [M6, Modular.sigmaT, Fin.sum_univ_six]
        rw [two_smul_one_eq]
        noncomm_ring
      rw [hL, rowDiff_aux2b]
      noncomm_ring]
    exact Submodule.add_mem _
      (IdealI_le_idealI (gen_S_T2_mem_IdealI (Rneg * (R_S * R_T * R_S * R_T))))
      (augIdeal_le_idealI (Rneg_sub_one_mul_mem (-(R_S * R_T * R_S))))
  · change Work.Residues.rowDiff Work.Kernels.R_T 3 ∈ idealI
    rw [show Work.Residues.rowDiff Work.Kernels.R_T 3 = 0 by
      rw [rowDiff, sigmaR_R_T]
      simp [M6, Modular.sigmaT, Fin.sum_univ_six]]
    exact Submodule.zero_mem _
  · change Work.Residues.rowDiff Work.Kernels.R_T 4 ∈ idealI
    rw [show Work.Residues.rowDiff Work.Kernels.R_T 4 = R_S * (R_T - 1)^2 by
      rw [rowDiff, sigmaR_R_T]
      show M6 4 * R_T - ∑ j, Modular.sigmaT 4 j • M6 j = _
      simp [M6, Modular.sigmaT, Fin.sum_univ_six, two_smul]
      rw [← sm (ModularGroup.S * ModularGroup.T) ModularGroup.T, ← sm ModularGroup.S ModularGroup.T]
      noncomm_ring]
    simpa using IdealI_le_idealI (gen_S_T2_mem_IdealI (1 : R))
  · change Work.Residues.rowDiff Work.Kernels.R_T 5 ∈ idealI
    rw [show Work.Residues.rowDiff Work.Kernels.R_T 5
        = (R_T - 1)^2 * (R_S * R_T * R_S * R_T) by
      rw [rowDiff, sigmaR_R_T]
      have hL : M6 5 * R_T - ∑ j, Modular.sigmaT 5 j • M6 j
          = R_S * R_T * R_S * R_T + R_T * R_S - 2 * R_S := by
        simp [M6, Modular.sigmaT, Fin.sum_univ_six, two_smul]
        noncomm_ring
      rw [hL, rowDiff_aux5]]
    exact IdealI_le_idealI (gen_T2_mem_IdealI (R_S * R_T * R_S * R_T))

end Work.Residues
