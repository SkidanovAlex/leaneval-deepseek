import Submission.Work.Asymptotics.ExtensionEvenDefs

/-! # The finite check of CKMRV Proposition 3.2(1) for the neighbour `(1 : X)`

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

lemma sigmaP_ofone_row0 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 0 j =
      (![1, 0, 0, 0, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [show (MonoidAlgebra.of ℂ X (1 : X) : R) = 1 from map_one _]
  rw [map_one, mul_one, MpChangeC_mul_self]
  fin_cases j <;> simp [Matrix.one_apply]

lemma rowSum_one_0 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 0 j • MpR j)
      = (1:ℂ) • MpR 0 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofone_row0 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofone_row1 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 1 j =
      (![0, 1, 0, 0, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [show (MonoidAlgebra.of ℂ X (1 : X) : R) = 1 from map_one _]
  rw [map_one, mul_one, MpChangeC_mul_self]
  fin_cases j <;> simp [Matrix.one_apply]

lemma rowSum_one_1 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 1 j • MpR j)
      = (1:ℂ) • MpR 1 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofone_row1 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofone_row2 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 2 j =
      (![0, 0, 1, 0, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [show (MonoidAlgebra.of ℂ X (1 : X) : R) = 1 from map_one _]
  rw [map_one, mul_one, MpChangeC_mul_self]
  fin_cases j <;> simp [Matrix.one_apply]

lemma rowSum_one_2 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 2 j • MpR j)
      = (1:ℂ) • MpR 2 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofone_row2 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofone_row3 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 3 j =
      (![0, 0, 0, 1, 0, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [show (MonoidAlgebra.of ℂ X (1 : X) : R) = 1 from map_one _]
  rw [map_one, mul_one, MpChangeC_mul_self]
  fin_cases j <;> simp [Matrix.one_apply]

lemma rowSum_one_3 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 3 j • MpR j)
      = (1:ℂ) • MpR 3 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofone_row3 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofone_row4 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 4 j =
      (![0, 0, 0, 0, 1, 0] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [show (MonoidAlgebra.of ℂ X (1 : X) : R) = 1 from map_one _]
  rw [map_one, mul_one, MpChangeC_mul_self]
  fin_cases j <;> simp [Matrix.one_apply]

lemma rowSum_one_4 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 4 j • MpR j)
      = (1:ℂ) • MpR 4 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofone_row4 j])]
  simp [Fin.sum_univ_six]

lemma sigmaP_ofone_row5 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 5 j =
      (![0, 0, 0, 0, 0, 1] : Fin 6 → ℂ) j := by
  rw [sigmaP]
  rw [show (MonoidAlgebra.of ℂ X (1 : X) : R) = 1 from map_one _]
  rw [map_one, mul_one, MpChangeC_mul_self]
  fin_cases j <;> simp [Matrix.one_apply]

lemma rowSum_one_5 :
    (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X ((1 : X)))) 5 j • MpR j)
      = (1:ℂ) • MpR 5 := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_ofone_row5 j])]
  simp [Fin.sum_univ_six]

theorem carry_one_0 : CarryOk ((1 : X)) 0 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X ((1 : X))) 0
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_one_0]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 0) * ((1 : X)) : X) = 1 from by decide,
      show ((Mp 0) : X) = 1 from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem carry_one_1 : CarryOk ((1 : X)) 1 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X ((1 : X))) 1
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_one_1]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 1) * ((1 : X)) : X) = ModularGroup.T⁻¹ from by decide,
      show ((Mp 1) : X) = ModularGroup.T⁻¹ from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem carry_one_2 : CarryOk ((1 : X)) 2 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X ((1 : X))) 2
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_one_2]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 2) * ((1 : X)) : X) = ModularGroup.S * ModularGroup.T * ModularGroup.S from by decide,
      show ((Mp 2) : X) = ModularGroup.S * ModularGroup.T * ModularGroup.S from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem carry_one_3 : CarryOk ((1 : X)) 3 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X ((1 : X))) 3
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_one_3]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 3) * ((1 : X)) : X) = ModularGroup.S from by decide,
      show ((Mp 3) : X) = ModularGroup.S from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem carry_one_4 : CarryOk ((1 : X)) 4 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X ((1 : X))) 4
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_one_4]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 4) * ((1 : X)) : X) = ModularGroup.S * ModularGroup.T⁻¹ from by decide,
      show ((Mp 4) : X) = ModularGroup.S * ModularGroup.T⁻¹ from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem carry_one_5 : CarryOk ((1 : X)) 5 none none := by
  have h : rowDiffP (MonoidAlgebra.of ℂ X ((1 : X))) 5
      - ((R_T - 1)^2 * ofOpt (none) + R_S * (R_T - 1)^2 * ofOpt (none))
      = 0 := by
    simp only [ofOpt_none, ofOpt_some, mul_zero, add_zero, zero_add]
    rw [rowDiffP, rowSum_one_5]
    simp only [MpR_eq_of, MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_single]
    rw [show ((Mp 5) * ((1 : X)) : X) = ModularGroup.T * ModularGroup.S from by decide,
      show ((Mp 5) : X) = ModularGroup.T * ModularGroup.S from by decide]
    simp only [two_smulC, neg_one_smulC, neg_two_smulC, one_smul, one_mul]
    abel
  simp only [CarryOk]
  rw [h]
  exact Submodule.zero_mem _

theorem hold_one_0 : SafePair ((1 : X)) 0 none := by
  intro γ h
  simp at h

theorem holdS_one_0 : SafePairS ((1 : X)) 0 none := by
  intro γ h
  simp at h

theorem hold_one_1 : SafePair ((1 : X)) 1 none := by
  intro γ h
  simp at h

theorem holdS_one_1 : SafePairS ((1 : X)) 1 none := by
  intro γ h
  simp at h

theorem hold_one_2 : SafePair ((1 : X)) 2 none := by
  intro γ h
  simp at h

theorem holdS_one_2 : SafePairS ((1 : X)) 2 none := by
  intro γ h
  simp at h

theorem hold_one_3 : SafePair ((1 : X)) 3 none := by
  intro γ h
  simp at h

theorem holdS_one_3 : SafePairS ((1 : X)) 3 none := by
  intro γ h
  simp at h

theorem hold_one_4 : SafePair ((1 : X)) 4 none := by
  intro γ h
  simp at h

theorem holdS_one_4 : SafePairS ((1 : X)) 4 none := by
  intro γ h
  simp at h

theorem hold_one_5 : SafePair ((1 : X)) 5 none := by
  intro γ h
  simp at h

theorem holdS_one_5 : SafePairS ((1 : X)) 5 none := by
  intro γ h
  simp at h

end Work.Asymptotics
