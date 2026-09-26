import Submission.Work.Asymptotics.ExtensionEvenDefs

/-! # The finite check of CKMRV Proposition 3.2(1) for the neighbour `ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹`

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

lemma sigmaP_ofTSTinv_row0 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 0 j =
      (![0, 0, -1, 0, 2, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_TSTinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaT, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_TSTinv_0 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 0 j • MpR j)
      = (-1:ℂ) • MpR 2 + (2:ℂ) • MpR 4 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofTSTinv_row0 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofTSTinv_row1 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 1 j =
      (![0, 0, 0, 0, 1, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_TSTinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaT, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_TSTinv_1 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 1 j • MpR j)
      = (1:ℂ) • MpR 4 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofTSTinv_row1 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofTSTinv_row2 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 2 j =
      (![-1, 2, 0, 0, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_TSTinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaT, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_TSTinv_2 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 2 j • MpR j)
      = (-1:ℂ) • MpR 0 + (2:ℂ) • MpR 1 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofTSTinv_row2 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofTSTinv_row3 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 3 j =
      (![0, 2, 0, 0, 0, -1] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_TSTinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaT, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_TSTinv_3 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 3 j • MpR j)
      = (2:ℂ) • MpR 1 + (-1:ℂ) • MpR 5 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofTSTinv_row3 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofTSTinv_row4 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 4 j =
      (![0, 1, 0, 0, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_TSTinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaT, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_TSTinv_4 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 4 j • MpR j)
      = (1:ℂ) • MpR 1 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofTSTinv_row4 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofTSTinv_row5 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 5 j =
      (![0, 0, 0, -1, 2, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [sigmaR_of_TSTinv]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC, Work.Modular.sigmaT, Work.Modular.sigmaS, Work.Modular.sigmaTinv] <;> norm_num

lemma rowSum_TSTinv_5 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))) 5 j • MpR j)
      = (-1:ℂ) • MpR 3 + (2:ℂ) • MpR 4 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofTSTinv_row5 j])]
  simp [Fin.sum_univ_six]

theorem carry_TSTinv_0 : CarryOk (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 0 (some (ModularGroup.S * ModularGroup.T * ModularGroup.S)) none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) 0
      - ((R_T - 1)^2 * ofOpt (some (ModularGroup.S * ModularGroup.T * ModularGroup.S)) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_TSTinv_0]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [T2_mul_single]
    rw [show ((Mp 0) * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) : X) = ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹ from by decide,
      show ((Mp 2) : X) = ModularGroup.S * ModularGroup.T * ModularGroup.S from by decide,
      show ((Mp 4) : X) = ModularGroup.S * ModularGroup.T⁻¹ from by decide,
      show (((ModularGroup.T) * (ModularGroup.T)) * (ModularGroup.S * ModularGroup.T * ModularGroup.S) : X) = ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹ from by decide,
      show ((ModularGroup.T) * (ModularGroup.S * ModularGroup.T * ModularGroup.S) : X) = ModularGroup.S * ModularGroup.T⁻¹ from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem carry_TSTinv_1 : CarryOk (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 1 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) 1
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_TSTinv_1]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 1) * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) : X) = ModularGroup.S * ModularGroup.T⁻¹ from by decide,
      show ((Mp 4) : X) = ModularGroup.S * ModularGroup.T⁻¹ from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem carry_TSTinv_2 : CarryOk (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 2 (some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) 2
      - ((R_T - 1)^2 * ofOpt (some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) + R_S * (R_T - 1)^2 * ofOpt (none))
      = (MonoidAlgebra.single (1) (1:ℂ) - MonoidAlgebra.single (-(1)) (1:ℂ)) + (MonoidAlgebra.single (-(ModularGroup.T⁻¹)) (1:ℂ) - MonoidAlgebra.single (-(-(ModularGroup.T⁻¹))) (1:ℂ)) + (MonoidAlgebra.single (-(ModularGroup.T⁻¹)) (1:ℂ) - MonoidAlgebra.single (-(-(ModularGroup.T⁻¹))) (1:ℂ)) := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_TSTinv_2]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [T2_mul_single]
    rw [show ((Mp 2) * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) : X) = ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹ from by decide,
      show ((Mp 0) : X) = 1 from by decide,
      show ((Mp 1) : X) = -(-(ModularGroup.T⁻¹)) from by decide,
      show (((ModularGroup.T) * (ModularGroup.T)) * (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹) : X) = -(1) from by decide,
      show ((ModularGroup.T) * (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹) : X) = -(ModularGroup.T⁻¹) from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.add_mem _ (Submodule.add_mem _ (single_sub_single_neg_mem (1) (1:ℂ)) (single_sub_single_neg_mem (-(ModularGroup.T⁻¹)) (1:ℂ))) (single_sub_single_neg_mem (-(ModularGroup.T⁻¹)) (1:ℂ))

theorem carry_TSTinv_3 : CarryOk (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 3 none (some (ModularGroup.S * ModularGroup.T * ModularGroup.S)) := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) 3
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (some (ModularGroup.S * ModularGroup.T * ModularGroup.S)))
      = (MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) - MonoidAlgebra.single (-(ModularGroup.T * ModularGroup.S)) (1:ℂ)) + (MonoidAlgebra.single (-(ModularGroup.T⁻¹)) (1:ℂ) - MonoidAlgebra.single (-(-(ModularGroup.T⁻¹))) (1:ℂ)) + (MonoidAlgebra.single (-(ModularGroup.T⁻¹)) (1:ℂ) - MonoidAlgebra.single (-(-(ModularGroup.T⁻¹))) (1:ℂ)) := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_TSTinv_3]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [RS_T2_mul_single]
    rw [show ((Mp 3) * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) : X) = ModularGroup.S * ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹ from by decide,
      show ((Mp 1) : X) = -(-(ModularGroup.T⁻¹)) from by decide,
      show ((Mp 5) : X) = ModularGroup.T * ModularGroup.S from by decide,
      show ((ModularGroup.S) * (((ModularGroup.T) * (ModularGroup.T)) * (ModularGroup.S * ModularGroup.T * ModularGroup.S)) : X) = ModularGroup.S * ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹ from by decide,
      show ((ModularGroup.S) * ((ModularGroup.T) * (ModularGroup.S * ModularGroup.T * ModularGroup.S)) : X) = -(ModularGroup.T⁻¹) from by decide,
      show ((ModularGroup.S) * (ModularGroup.S * ModularGroup.T * ModularGroup.S) : X) = -(ModularGroup.T * ModularGroup.S) from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.add_mem _ (Submodule.add_mem _ (single_sub_single_neg_mem (ModularGroup.T * ModularGroup.S) (1:ℂ)) (single_sub_single_neg_mem (-(ModularGroup.T⁻¹)) (1:ℂ))) (single_sub_single_neg_mem (-(ModularGroup.T⁻¹)) (1:ℂ))

theorem carry_TSTinv_4 : CarryOk (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 4 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) 4
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = (MonoidAlgebra.single (-(ModularGroup.T⁻¹)) (1:ℂ) - MonoidAlgebra.single (-(-(ModularGroup.T⁻¹))) (1:ℂ)) := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_TSTinv_4]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 4) * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) : X) = -(ModularGroup.T⁻¹) from by decide,
      show ((Mp 1) : X) = -(-(ModularGroup.T⁻¹)) from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact single_sub_single_neg_mem (-(ModularGroup.T⁻¹)) (1:ℂ)

theorem carry_TSTinv_5 : CarryOk (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 5 none (some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) 5
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)))
      = (MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹) (1:ℂ) - MonoidAlgebra.single (-(ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) (1:ℂ)) + (MonoidAlgebra.single (ModularGroup.S) (1:ℂ) - MonoidAlgebra.single (-(ModularGroup.S)) (1:ℂ)) + (MonoidAlgebra.single (ModularGroup.S * ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) - MonoidAlgebra.single (-(ModularGroup.S * ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ)) + (MonoidAlgebra.single (ModularGroup.S * ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) - MonoidAlgebra.single (-(ModularGroup.S * ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ)) := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_TSTinv_5]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [RS_T2_mul_single]
    rw [show ((Mp 5) * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) : X) = ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹ from by decide,
      show ((Mp 3) : X) = ModularGroup.S from by decide,
      show ((Mp 4) : X) = -(ModularGroup.S * ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹) from by decide,
      show ((ModularGroup.S) * (((ModularGroup.T) * (ModularGroup.T)) * (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) : X) = -(ModularGroup.S) from by decide,
      show ((ModularGroup.S) * ((ModularGroup.T) * (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) : X) = ModularGroup.S * ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ from by decide,
      show ((ModularGroup.S) * (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹) : X) = -(ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹) from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (single_sub_single_neg_mem (ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹) (1:ℂ)) (single_sub_single_neg_mem (ModularGroup.S) (1:ℂ))) (single_sub_single_neg_mem (ModularGroup.S * ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ))) (single_sub_single_neg_mem (ModularGroup.S * ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ))

theorem hold_TSTinv_0 : SafePair (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 0 (some (ModularGroup.S * ModularGroup.T * ModularGroup.S)) := by
  intro γ h
  rw [Option.some.injEq] at h
  subst h
  decide

theorem holdS_TSTinv_0 : SafePairS (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 0 none := by
  intro γ h
  simp at h

theorem hold_TSTinv_1 : SafePair (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 1 none := by
  intro γ h
  simp at h

theorem holdS_TSTinv_1 : SafePairS (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 1 none := by
  intro γ h
  simp at h

theorem hold_TSTinv_2 : SafePair (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 2 (some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) := by
  intro γ h
  rw [Option.some.injEq] at h
  subst h
  decide

theorem holdS_TSTinv_2 : SafePairS (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 2 none := by
  intro γ h
  simp at h

theorem hold_TSTinv_3 : SafePair (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 3 none := by
  intro γ h
  simp at h

theorem holdS_TSTinv_3 : SafePairS (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 3 (some (ModularGroup.S * ModularGroup.T * ModularGroup.S)) := by
  intro γ h
  rw [Option.some.injEq] at h
  subst h
  decide

theorem hold_TSTinv_4 : SafePair (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 4 none := by
  intro γ h
  simp at h

theorem holdS_TSTinv_4 : SafePairS (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 4 none := by
  intro γ h
  simp at h

theorem hold_TSTinv_5 : SafePair (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 5 none := by
  intro γ h
  simp at h

theorem holdS_TSTinv_5 : SafePairS (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 5 (some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) := by
  intro γ h
  rw [Option.some.injEq] at h
  subst h
  decide

end Work.Asymptotics
