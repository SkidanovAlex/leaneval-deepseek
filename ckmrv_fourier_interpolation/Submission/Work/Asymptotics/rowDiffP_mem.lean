/-
# The error vector of the second basis `M'` lands in `𝓘`

The companion of `Work.Residues.rowDiff_mem_of_idealI` for the second basis

  `M' = (I, T⁻¹, STS, S, ST⁻¹, TS)`

of CKMRV (proof of Prop. 3.2(1)): for every `x ∈ R` and every `i : Fin 6` the error vector

  `rowDiffP x i = M'_i x - ∑ j, σ'(x)_{ij} M'_j`

of the reduction modulo `𝓘 = (T-I)²R + S(T-I)²R + (z-1)R` lies in `𝓘`.

The proof reduces to the first basis: writing `G = MpChangeC` one has
`M'_i ≡ ∑_j G_{ij} M_j (mod 𝓘)` (`MpR_sub_sum_row_mem`), `G` is an involution and
`σ' = G σ G`, whence

  `rowDiffP x i = ∑ j, G_{ij} · rowDiff x j + (M'_i - ∑_j G_{ij} M_j) x`
                    - ∑ j, (G σ G)_{ij} · (M'_j - ∑_j G_{jk} M_k)`,

both error terms on the right lying in the right ideal `𝓘` and `∑ j, G_{ij} · rowDiff x j`
lying in `𝓘` by `Work.Residues.rowDiff_mem_of_idealI`.
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Residues.IdealImRowDiffAll

noncomputable section

open Work.Kernels Work.Residues
open scoped MatrixGroups

namespace Work.Asymptotics

set_option maxHeartbeats 2000000

/-! ## The change of basis `M' ≡ G M (mod 𝓘)` -/

/-- `T · T⁻¹ = 1` in `R`. -/
private lemma R_T_mul_R_Tinv_aux : R_T * R_Tinv = (1 : R) := by
  rw [R_T, R_Tinv, MonoidAlgebra.single_mul_single, mul_one, mul_inv_cancel,
    MonoidAlgebra.one_def]

private lemma MpR_sub_sum_row_mem_zero :
    MpR (0 : Fin 6) - ∑ j : Fin 6, MpChangeC (0 : Fin 6) j • (M6 j : R) ∈ idealI := by
  rw [MpR_zero]
  have hsum : (∑ j : Fin 6, MpChangeC (0 : Fin 6) j • (M6 j : R)) = 1 := by
    simp [MpChangeC, M6, Fin.sum_univ_six]
  rw [hsum, sub_self]
  exact Submodule.zero_mem _

private lemma MpR_sub_sum_row_mem_one :
    MpR (1 : Fin 6) - ∑ j : Fin 6, MpChangeC (1 : Fin 6) j • (M6 j : R) ∈ idealI := by
  have hsum : (∑ j : Fin 6, MpChangeC (1 : Fin 6) j • (M6 j : R))
      = (2 : ℂ) • (1 : R) + (-1 : ℂ) • R_T := by
    simp [MpChangeC, M6, Fin.sum_univ_six]
  rw [hsum, MpR_one]
  rw [show (2 : ℂ) • (1 : R) = (2 : R) by rw [Algebra.smul_def, map_ofNat, mul_one]]
  rw [show (-1 : ℂ) • R_T = -R_T by
    rw [Algebra.smul_def, map_neg, map_one, neg_mul, one_mul]]
  have key : R_Tinv - (2 + -R_T) = (R_T - 1) ^ 2 * R_Tinv := by
    have e : (R_T - 1) ^ 2 * R_Tinv = R_Tinv - (2 + -R_T) := by
      rw [show (R_T - 1) ^ 2 = R_T * R_T - 2 * R_T + 1 by noncomm_ring]
      rw [show (R_T * R_T - 2 * R_T + 1) * R_Tinv
          = R_T * (R_T * R_Tinv) - 2 * (R_T * R_Tinv) + R_Tinv by noncomm_ring]
      rw [R_T_mul_R_Tinv_aux]
      simp only [mul_one]
      noncomm_ring
    exact e.symm
  rw [key]
  exact IdealI_le_idealI (gen_T2_mem_IdealI R_Tinv)

private lemma MpR_sub_sum_row_mem_two :
    MpR (2 : Fin 6) - ∑ j : Fin 6, MpChangeC (2 : Fin 6) j • (M6 j : R) ∈ idealI := by
  have hsum : (∑ j : Fin 6, MpChangeC (2 : Fin 6) j • (M6 j : R)) = R_S * R_T * R_S := by
    simp [MpChangeC, M6, Fin.sum_univ_six]
  rw [hsum, MpR_two, sub_self]
  exact Submodule.zero_mem _

private lemma MpR_sub_sum_row_mem_three :
    MpR (3 : Fin 6) - ∑ j : Fin 6, MpChangeC (3 : Fin 6) j • (M6 j : R) ∈ idealI := by
  have hsum : (∑ j : Fin 6, MpChangeC (3 : Fin 6) j • (M6 j : R)) = R_S := by
    simp [MpChangeC, M6, Fin.sum_univ_six]
  rw [hsum, MpR_three, sub_self]
  exact Submodule.zero_mem _

private lemma MpR_sub_sum_row_mem_four :
    MpR (4 : Fin 6) - ∑ j : Fin 6, MpChangeC (4 : Fin 6) j • (M6 j : R) ∈ idealI := by
  have hsum : (∑ j : Fin 6, MpChangeC (4 : Fin 6) j • (M6 j : R))
      = (2 : ℂ) • R_S + (-1 : ℂ) • (R_S * R_T) := by
    simp [MpChangeC, M6, Fin.sum_univ_six]
  rw [hsum, MpR_four]
  rw [show (2 : ℂ) • R_S = 2 * R_S by rw [Algebra.smul_def, map_ofNat]]
  rw [show (-1 : ℂ) • (R_S * R_T) = -(R_S * R_T) by
    rw [Algebra.smul_def, map_neg, map_one, neg_mul, one_mul]]
  have key : R_S * R_Tinv - (2 * R_S + -(R_S * R_T)) = R_S * (R_T - 1) ^ 2 * R_Tinv := by
    have e : R_S * (R_T - 1) ^ 2 * R_Tinv = R_S * R_Tinv - (2 * R_S + -(R_S * R_T)) := by
      rw [show (R_T - 1) ^ 2 = R_T * R_T - 2 * R_T + 1 by noncomm_ring]
      rw [show R_S * (R_T * R_T - 2 * R_T + 1) * R_Tinv
          = R_S * (R_T * (R_T * R_Tinv)) - 2 * (R_S * (R_T * R_Tinv)) + R_S * R_Tinv
          by noncomm_ring]
      rw [R_T_mul_R_Tinv_aux]
      simp only [mul_one]
      noncomm_ring
    exact e.symm
  rw [key]
  exact IdealI_le_idealI (gen_S_T2_mem_IdealI R_Tinv)

private lemma MpR_sub_sum_row_mem_five :
    MpR (5 : Fin 6) - ∑ j : Fin 6, MpChangeC (5 : Fin 6) j • (M6 j : R) ∈ idealI := by
  have hsum : (∑ j : Fin 6, MpChangeC (5 : Fin 6) j • (M6 j : R)) = R_T * R_S := by
    simp [MpChangeC, M6, Fin.sum_univ_six]
  rw [hsum, MpR_five, sub_self]
  exact Submodule.zero_mem _

/-- The change of basis `M' ≡ G · M (mod 𝓘)`: for each of the six elements `M'_i` of the
second basis there is an integral `ℂ`-linear combination `∑_j G_{ij} M_j` of the elements
`M6_j` of the first basis congruent to it modulo `𝓘`. -/
private lemma MpR_sub_sum_row_mem (i : Fin 6) :
    MpR i - ∑ j : Fin 6, MpChangeC i j • (M6 j : R) ∈ idealI := by
  fin_cases i
  · exact MpR_sub_sum_row_mem_zero
  · exact MpR_sub_sum_row_mem_one
  · exact MpR_sub_sum_row_mem_two
  · exact MpR_sub_sum_row_mem_three
  · exact MpR_sub_sum_row_mem_four
  · exact MpR_sub_sum_row_mem_five

/-! ## The reduction -/

/-- **The error vector of the second basis lands in `𝓘`.**  This is the analogue of
`Work.Residues.rowDiff_mem_of_idealI` for the basis `M' = (1, T⁻¹, STS, S, ST⁻¹, TS)` in
which the propagation argument of CKMRV (proof of Proposition 3.2(1)) is run. -/
theorem rowDiffP_mem (x : Work.Kernels.R) (i : Fin 6) :
    rowDiffP x i ∈ Work.Residues.idealI := by
  have hG2 : MpChangeC * MpChangeC = (1 : Matrix (Fin 6) (Fin 6) ℂ) := MpChangeC_mul_self
  -- `∑_j G_{ij} · rowDiff x j`, expanded
  have hK1 : (∑ j, MpChangeC i j • rowDiff x j)
      = (∑ j, MpChangeC i j • M6 j) * x - ∑ j, (MpChangeC * sigmaR x) i j • M6 j := by
    simp only [rowDiff, smul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_mul_assoc]
    · exact matRow_smul_sum MpChangeC (sigmaR x) M6 i
  -- `(G σ G) · (G M) = (G σ) · M`
  have hK2 : (∑ j, (MpChangeC * sigmaR x * MpChangeC) i j • (∑ k, MpChangeC j k • M6 k))
      = ∑ j, (MpChangeC * sigmaR x) i j • M6 j := by
    rw [matRow_smul_sum (MpChangeC * sigmaR x * MpChangeC) MpChangeC M6 i]
    rw [show (MpChangeC * sigmaR x * MpChangeC) * MpChangeC = MpChangeC * sigmaR x by
      rw [mul_assoc, hG2, mul_one]]
  -- the second error term, decomposed along `M' - G M`
  have hR : (∑ j, (MpChangeC * sigmaR x * MpChangeC) i j
        • (MpR j - ∑ k, MpChangeC j k • M6 k))
      = ∑ j, (MpChangeC * sigmaR x * MpChangeC) i j • MpR j
        - ∑ j, (MpChangeC * sigmaR x) i j • M6 j := by
    simp only [smul_sub, Finset.sum_sub_distrib, hK2]
  -- the exact identity expressing `rowDiffP` in terms of `rowDiff` and the change of basis
  have hid : rowDiffP x i - ∑ j, MpChangeC i j • rowDiff x j
      = (MpR i - ∑ j, MpChangeC i j • M6 j) * x
        - ∑ j, (MpChangeC * sigmaR x * MpChangeC) i j
            • (MpR j - ∑ k, MpChangeC j k • M6 k) := by
    rw [hK1, hR, rowDiffP, sigmaP, sub_mul]
    abel
  have hh : (MpR i - ∑ j, MpChangeC i j • M6 j) * x ∈ idealI :=
    idealI_mul_mem (MpR_sub_sum_row_mem i) x
  have hs : (∑ j, (MpChangeC * sigmaR x * MpChangeC) i j
      • (MpR j - ∑ k, MpChangeC j k • M6 k)) ∈ idealI :=
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (MpR_sub_sum_row_mem j))
  have hmain : rowDiffP x i - ∑ j, MpChangeC i j • rowDiff x j ∈ idealI := by
    rw [hid]
    exact Submodule.sub_mem _ hh hs
  have h3 : (∑ j, MpChangeC i j • rowDiff x j) ∈ idealI :=
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (rowDiff_mem_of_idealI x j))
  have hsplit : rowDiffP x i
      = (∑ j, MpChangeC i j • rowDiff x j)
        + (rowDiffP x i - ∑ j, MpChangeC i j • rowDiff x j) := by abel
  rw [hsplit]
  exact Submodule.add_mem _ h3 hmain

end Work.Asymptotics
