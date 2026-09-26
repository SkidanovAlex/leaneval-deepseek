import Submission.Work.Asymptotics.ExtensionEvenDefs

/-! # The finite check of CKMRV Proposition 3.2(1) for the neighbour `ModularGroup.S * ModularGroup.T⁻¹`

For each of the six rows `i` the error vector `rowDiffP (of ν) i` of the second
basis equals `(T-I)² a + S(T-I)² b` modulo the collapse ideal `(z-1)R`, with the
carries `a`, `b` given by `Work.Asymptotics.CarryOk` (see
`Submission/Work/Asymptotics/ExtensionEvenDefs.lean`).  The row residue is
computed from the explicit matrix `σ'(ν) = MpChangeC * σ_R(ν) * MpChangeC`.
-/

set_option maxHeartbeats 2000000

noncomputable section

open Work.Kernels Work.Residues
open scoped MatrixGroups

namespace Work.Asymptotics

lemma sigmaP_ofSTinv_row0 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 0 j =
      (![0, 0, 0, 0, 1, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_STinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_STinv_0 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 0 j • MpR j)
      = (1:ℂ) • MpR 4 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofSTinv_row0 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofSTinv_row1 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 1 j =
      (![0, 0, 1, 0, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_STinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_STinv_1 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 1 j • MpR j)
      = (1:ℂ) • MpR 2 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofSTinv_row1 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofSTinv_row2 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 2 j =
      (![0, 0, 0, 1, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_STinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_STinv_2 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 2 j • MpR j)
      = (1:ℂ) • MpR 3 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofSTinv_row2 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofSTinv_row3 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 3 j =
      (![0, 1, 0, 0, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_STinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_STinv_3 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 3 j • MpR j)
      = (1:ℂ) • MpR 1 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofSTinv_row3 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofSTinv_row4 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 4 j =
      (![0, 0, 0, 0, 0, 1] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_STinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_STinv_4 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 4 j • MpR j)
      = (1:ℂ) • MpR 5 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofSTinv_row4 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofSTinv_row5 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 5 j =
      (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_STinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_STinv_5 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹))) 5 j • MpR j)
      = (1:ℂ) • MpR 0 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofSTinv_row5 j])]
  simp [Fin.sum_univ_six]

theorem carry_STinv_0 : CarryOk (ModularGroup.S * ModularGroup.T⁻¹) 0 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹)) 0
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_STinv_0]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 0) * (ModularGroup.S * ModularGroup.T⁻¹) : X) = ModularGroup.S * ModularGroup.T⁻¹ from by decide,
      show ((Mp 4) : X) = ModularGroup.S * ModularGroup.T⁻¹ from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem carry_STinv_1 : CarryOk (ModularGroup.S * ModularGroup.T⁻¹) 1 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹)) 1
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_STinv_1]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 1) * (ModularGroup.S * ModularGroup.T⁻¹) : X) = ModularGroup.S * ModularGroup.T * ModularGroup.S from by decide,
      show ((Mp 2) : X) = ModularGroup.S * ModularGroup.T * ModularGroup.S from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem carry_STinv_2 : CarryOk (ModularGroup.S * ModularGroup.T⁻¹) 2 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹)) 2
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = (MonoidAlgebra.single (-(ModularGroup.S)) (1:ℂ) - MonoidAlgebra.single (-(-(ModularGroup.S))) (1:ℂ)) := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_STinv_2]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 2) * (ModularGroup.S * ModularGroup.T⁻¹) : X) = -(ModularGroup.S) from by decide,
      show ((Mp 3) : X) = -(-(ModularGroup.S)) from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact single_sub_single_neg_mem (-(ModularGroup.S)) (1:ℂ)

theorem carry_STinv_3 : CarryOk (ModularGroup.S * ModularGroup.T⁻¹) 3 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹)) 3
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = (MonoidAlgebra.single (-(ModularGroup.T⁻¹)) (1:ℂ) - MonoidAlgebra.single (-(-(ModularGroup.T⁻¹))) (1:ℂ)) := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_STinv_3]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 3) * (ModularGroup.S * ModularGroup.T⁻¹) : X) = -(ModularGroup.T⁻¹) from by decide,
      show ((Mp 1) : X) = -(-(ModularGroup.T⁻¹)) from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact single_sub_single_neg_mem (-(ModularGroup.T⁻¹)) (1:ℂ)

theorem carry_STinv_4 : CarryOk (ModularGroup.S * ModularGroup.T⁻¹) 4 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹)) 4
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = (MonoidAlgebra.single (ModularGroup.S * ModularGroup.S * ModularGroup.T * ModularGroup.S) (1:ℂ) - MonoidAlgebra.single (-(ModularGroup.S * ModularGroup.S * ModularGroup.T * ModularGroup.S)) (1:ℂ)) := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_STinv_4]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 4) * (ModularGroup.S * ModularGroup.T⁻¹) : X) = ModularGroup.S * ModularGroup.S * ModularGroup.T * ModularGroup.S from by decide,
      show ((Mp 5) : X) = -(ModularGroup.S * ModularGroup.S * ModularGroup.T * ModularGroup.S) from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact single_sub_single_neg_mem (ModularGroup.S * ModularGroup.S * ModularGroup.T * ModularGroup.S) (1:ℂ)

theorem carry_STinv_5 : CarryOk (ModularGroup.S * ModularGroup.T⁻¹) 5 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T⁻¹)) 5
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = (MonoidAlgebra.single (-(1)) (1:ℂ) - MonoidAlgebra.single (-(-(1))) (1:ℂ)) := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_STinv_5]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 5) * (ModularGroup.S * ModularGroup.T⁻¹) : X) = -(1) from by decide,
      show ((Mp 0) : X) = -(-(1)) from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact single_sub_single_neg_mem (-(1)) (1:ℂ)

theorem hold_STinv_0 : SafePair (ModularGroup.S * ModularGroup.T⁻¹) 0 none := by
  intro γ h
  simp at h

theorem holdS_STinv_0 : SafePairS (ModularGroup.S * ModularGroup.T⁻¹) 0 none := by
  intro γ h
  simp at h

theorem hold_STinv_1 : SafePair (ModularGroup.S * ModularGroup.T⁻¹) 1 none := by
  intro γ h
  simp at h

theorem holdS_STinv_1 : SafePairS (ModularGroup.S * ModularGroup.T⁻¹) 1 none := by
  intro γ h
  simp at h

theorem hold_STinv_2 : SafePair (ModularGroup.S * ModularGroup.T⁻¹) 2 none := by
  intro γ h
  simp at h

theorem holdS_STinv_2 : SafePairS (ModularGroup.S * ModularGroup.T⁻¹) 2 none := by
  intro γ h
  simp at h

theorem hold_STinv_3 : SafePair (ModularGroup.S * ModularGroup.T⁻¹) 3 none := by
  intro γ h
  simp at h

theorem holdS_STinv_3 : SafePairS (ModularGroup.S * ModularGroup.T⁻¹) 3 none := by
  intro γ h
  simp at h

theorem hold_STinv_4 : SafePair (ModularGroup.S * ModularGroup.T⁻¹) 4 none := by
  intro γ h
  simp at h

theorem holdS_STinv_4 : SafePairS (ModularGroup.S * ModularGroup.T⁻¹) 4 none := by
  intro γ h
  simp at h

theorem hold_STinv_5 : SafePair (ModularGroup.S * ModularGroup.T⁻¹) 5 none := by
  intro γ h
  simp at h

theorem holdS_STinv_5 : SafePairS (ModularGroup.S * ModularGroup.T⁻¹) 5 none := by
  intro γ h
  simp at h

end Work.Asymptotics
