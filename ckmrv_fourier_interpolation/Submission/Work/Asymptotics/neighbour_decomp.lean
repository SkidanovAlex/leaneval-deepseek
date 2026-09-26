import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.spanning_Mp_idealIOdd
import Submission.Work.Asymptotics.PropagateCarriesOdd

noncomputable section
open Work.Kernels Work.Asymptotics
open scoped MatrixGroups MonoidAlgebra
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Work.Asymptotics

theorem T2_mul_smul_single (c : ℂ) (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (R_T - 1)^2 * (c • (MonoidAlgebra.single α (1:ℂ) : R))
      = c • ((MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * α)) (1:ℂ) : R)
             - (2:ℂ) • MonoidAlgebra.single (ModularGroup.T * α) (1:ℂ)
             + MonoidAlgebra.single α (1:ℂ)) := by
  rw [show (R_T - 1)^2 = R_T * R_T - 2 * R_T + 1 from by noncomm_ring]
  simp only [sub_mul, add_mul, one_mul]
  rw [show R_T = MonoidAlgebra.single ModularGroup.T (1:ℂ) from rfl]
  simp only [mul_smul_comm, smul_sub, smul_add, smul_smul, MonoidAlgebra.single_mul_single,
    mul_one, mul_assoc]
  rw [show ((2:R) * (MonoidAlgebra.single (ModularGroup.T * α) (1:ℂ) : R)) = (2:ℂ) • MonoidAlgebra.single (ModularGroup.T * α) (1:ℂ) from by
    rw [show (2:R) = algebraMap ℂ R (2:ℂ) from (map_ofNat (algebraMap ℂ R) 2).symm, Algebra.smul_def]]
  module

theorem ST2_mul_smul_single (c : ℂ) (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    R_S * (R_T - 1)^2 * (c • (MonoidAlgebra.single β (1:ℂ) : R))
      = c • ((MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * β))) (1:ℂ) : R)
             - (2:ℂ) • MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * β)) (1:ℂ)
             + MonoidAlgebra.single (ModularGroup.S * β) (1:ℂ)) := by
  rw [show R_S * (R_T - 1)^2 * (c • (MonoidAlgebra.single β (1:ℂ) : R))
       = R_S * ((R_T - 1)^2 * (c • (MonoidAlgebra.single β (1:ℂ) : R))) from by noncomm_ring]
  rw [T2_mul_smul_single]
  simp only [mul_sub, mul_add, smul_sub, smul_add, smul_smul, mul_smul_comm, R_S,
    MonoidAlgebra.single_mul_single, mul_one]

theorem aug_mul_smul_single (c : ℂ) (ρ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (Rneg + 1) * (c • (MonoidAlgebra.single ρ (1:ℂ) : R))
      = c • ((MonoidAlgebra.single (-ρ) (1:ℂ) : R) + MonoidAlgebra.single ρ (1:ℂ)) := by
  rw [show Rneg + 1 = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) + 1 from rfl]
  rw [add_mul, one_mul]
  simp only [mul_smul_comm, MonoidAlgebra.single_mul_single, mul_one, smul_add]
  rw [show ((-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) * ρ) = -ρ from by
    ext i j; fin_cases i <;> fin_cases j <;> simp]


private lemma case_0_0 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 0))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 0) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_0_1 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * ModularGroup.S) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show (((Mp 0) * ModularGroup.S) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1]
    module

private lemma case_0_2 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.T))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL ModularGroup.T⁻¹, (0 : R), (2 : ℂ) • MpElem 0 + (-1 : ℂ) • MpElem 1, ?_, Or.inr ⟨(1 : ℂ), ModularGroup.T⁻¹, rfl⟩, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 1)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * ModularGroup.T) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T (1:ℂ) := by
      rw [show (((Mp 0) * ModularGroup.T) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.T * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_0_3 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 1))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show (((Mp 0) * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1]
    module

private lemma case_0_4 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 5))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 0) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_0_5 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 0) * (ModularGroup.S * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_0_6 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S), (0 : R), (-1 : ℂ) • MpElem 2 + (2 : ℂ) • MpElem 4, ?_, Or.inr ⟨(1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S), rfl⟩, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 2))) ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 4)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 0) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_0_7 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (-((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 0))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 0) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_0_8 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (-(ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 3))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (-ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 0) * (-ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_0_9 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (-(ModularGroup.T)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (0 : R), (-2 : ℂ) • MpElem 0 + (1 : ℂ) • MpElem 1, ?_, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, Or.inl rfl, (Rneg + 1) * ((2 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) + (-1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 1)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (-ModularGroup.T)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 0) * (-ModularGroup.T)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_5 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_0_10 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (-(ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 1))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (-ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 0) * (-ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_0_11 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (-(ModularGroup.T * ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 5))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (-(ModularGroup.T * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 0) * (-(ModularGroup.T * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_0_12 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (-(ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 4))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (-(ModularGroup.S * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 0) * (-(ModularGroup.S * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_2 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_0_13 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (-(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (0 : R), (1 : ℂ) • MpElem 2 + (-2 : ℂ) • MpElem 4, ?_, Or.inr ⟨(1 : ℂ), (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, Or.inl rfl, (Rneg + 1) * ((2 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (-1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2))) ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 4)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 0) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_6 : (MonoidAlgebra.single (-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_1_0 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 1))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show (((Mp 1) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1]
    module

private lemma case_1_1 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S), (0 : R), (2 : ℂ) • MpElem 3 + (-1 : ℂ) • MpElem 5, ?_, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S), rfl⟩, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 5)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * ModularGroup.S) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 1) * ModularGroup.S) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_1_2 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.T))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 0))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * ModularGroup.T) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 1) * ModularGroup.T) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_1_3 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹), (0 : R), (-1 : ℂ) • MpElem 0 + (2 : ℂ) • MpElem 1, ?_, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹), rfl⟩, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 1)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 1) * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_1_4 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show (((Mp 1) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1]
    module

private lemma case_1_5 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 1) * (ModularGroup.S * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_1_6 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 1) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_1_7 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (-((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 1))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 1) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_1_8 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (-(ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (0 : R), (-2 : ℂ) • MpElem 3 + (1 : ℂ) • MpElem 5, ?_, Or.inr ⟨(1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, Or.inl rfl, (Rneg + 1) * ((-1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (2 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 5)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (-ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 1) * (-ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_1_9 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (-(ModularGroup.T)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 0))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (-ModularGroup.T)) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 1) * (-ModularGroup.T)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_1_10 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (-(ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (0 : R), (1 : ℂ) • MpElem 0 + (-2 : ℂ) • MpElem 1, ?_, Or.inr ⟨(1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, Or.inl rfl, (Rneg + 1) * ((-1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) + (2 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 1)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (-ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 1) * (-ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_1_11 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (-(ModularGroup.T * ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 3))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (-(ModularGroup.T * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 1) * (-(ModularGroup.T * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_1_12 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (-(ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 2))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (-(ModularGroup.S * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 1) * (-(ModularGroup.S * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_1_13 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (-(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 4))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 1) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_2 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_2_0 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 2) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_2_1 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (-2 : ℂ) • MpElem 3 + (1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, (Rneg + 1) * ((2 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (-1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * ModularGroup.S) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 2) * ModularGroup.S) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_7 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6, h_7]
    module

private lemma case_2_2 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.T))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S), (0 : R), (2 : ℂ) • MpElem 3 + (-1 : ℂ) • MpElem 5, ?_, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S), rfl⟩, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 5)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * ModularGroup.T) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 2) * ModularGroup.T) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_2_3 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S), (-2 : ℂ) • MpElem 1 + (1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S), rfl⟩, (Rneg + 1) * ((2 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (-1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 1))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 5)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 2) * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_7 : (MonoidAlgebra.single (-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6, h_7]
    module

private lemma case_2_4 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 1))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 2) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_2_5 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 3))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 2) * (ModularGroup.S * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_2_6 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (0 : R), (1 : ℂ) • MpElem 0 + (-2 : ℂ) • MpElem 1, ?_, Or.inr ⟨(1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, Or.inl rfl, (Rneg + 1) * ((-1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) + (2 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 1)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 2) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_2_7 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (-((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 2))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 2) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_2_8 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (-(ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL ModularGroup.T⁻¹, (2 : ℂ) • MpElem 3 + (-1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), ModularGroup.T⁻¹, rfl⟩, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 4)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (-ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T) (1:ℂ) := by
      rw [show (((Mp 2) * (-ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_2_9 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (-(ModularGroup.T)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (0 : R), (-2 : ℂ) • MpElem 3 + (1 : ℂ) • MpElem 5, ?_, Or.inr ⟨(1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, Or.inl rfl, (Rneg + 1) * ((-1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (2 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 5)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (-ModularGroup.T)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 2) * (-ModularGroup.T)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_2_10 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (-(ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (2 : ℂ) • MpElem 1 + (-1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 1))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 5)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (-ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 2) * (-ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) (1:ℂ) : R) = MonoidAlgebra.single ((((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((ModularGroup.S * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5]
    module

private lemma case_2_11 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (-(ModularGroup.T * ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 1))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (-(ModularGroup.T * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show (((Mp 2) * (-(ModularGroup.T * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1]
    module

private lemma case_2_12 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (-(ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (-(ModularGroup.S * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show (((Mp 2) * (-(ModularGroup.S * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1]
    module

private lemma case_2_13 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (-(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹), (0 : R), (-1 : ℂ) • MpElem 0 + (2 : ℂ) • MpElem 1, ?_, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹), rfl⟩, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 1)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 2) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_3_0 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show (((Mp 3) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1]
    module

private lemma case_3_1 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 0))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * ModularGroup.S) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 3) * ModularGroup.S) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_3_2 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.T))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL ModularGroup.T⁻¹, (2 : ℂ) • MpElem 3 + (-1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), ModularGroup.T⁻¹, rfl⟩, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 4)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * ModularGroup.T) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T) (1:ℂ) := by
      rw [show (((Mp 3) * ModularGroup.T) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_3_3 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 3) * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_3_4 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 3) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_3_5 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 1))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 3) * (ModularGroup.S * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_3_6 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S), (-2 : ℂ) • MpElem 1 + (1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S), rfl⟩, (Rneg + 1) * ((2 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (-1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 1))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 5)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 3) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_7 : (MonoidAlgebra.single (-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6, h_7]
    module

private lemma case_3_7 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (-((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 3))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 3) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_3_8 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (-(ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 0))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (-ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 3) * (-ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_3_9 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (-(ModularGroup.T)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (-2 : ℂ) • MpElem 3 + (1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, (Rneg + 1) * ((2 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (-1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (-ModularGroup.T)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 3) * (-ModularGroup.T)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_7 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6, h_7]
    module

private lemma case_3_10 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (-(ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 4))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (-ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 3) * (-ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_2 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_3_11 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (-(ModularGroup.T * ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 2))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (-(ModularGroup.T * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 3) * (-(ModularGroup.T * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_3_12 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (-(ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 1))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (-(ModularGroup.S * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show (((Mp 3) * (-(ModularGroup.S * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1]
    module

private lemma case_3_13 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (-(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (2 : ℂ) • MpElem 1 + (-1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 1))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 5)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single ((((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 3) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) (1:ℂ) : R) = MonoidAlgebra.single ((((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((ModularGroup.S * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5]
    module

private lemma case_4_0 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 4) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_4_1 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S), (-2 : ℂ) • MpElem 0 + (-1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S), rfl⟩, (Rneg + 1) * ((2 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 2)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * ModularGroup.S) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 4) * ModularGroup.S) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S)))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.S) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.S) from by decide]
    have h_6 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_4_2 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.T))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * ModularGroup.T) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show (((Mp 4) * ModularGroup.T) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1]
    module

private lemma case_4_3 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹), (-1 : ℂ) • MpElem 3 + (2 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹), rfl⟩, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 4)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 4) * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5]
    module

private lemma case_4_4 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 0))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 4) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_4_5 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 5))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 4) * (ModularGroup.S * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_4_6 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 1))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 4) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_4_7 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (-((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 4))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 4) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_2 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_4_8 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (-(ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (2 : ℂ) • MpElem 0 + (1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, (Rneg + 1) * ((-1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (-ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * ModularGroup.T) (1:ℂ) := by
      rw [show (((Mp 4) * (-ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * ModularGroup.T) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * ModularGroup.T) (1:ℂ) := by
      rw [show ((ModularGroup.S * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * ModularGroup.T) from by decide]
    have h_6 : (MonoidAlgebra.single (-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_4_9 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (-(ModularGroup.T)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 3, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 3))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (-ModularGroup.T)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 4) * (-ModularGroup.T)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_4_10 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (-(ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (1 : ℂ) • MpElem 3 + (-2 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, (Rneg + 1) * ((-1 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (2 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 4)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (-ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 4) * (-ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_7 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6, h_7]
    module

private lemma case_4_11 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (-(ModularGroup.T * ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 0))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (-(ModularGroup.T * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 4) * (-(ModularGroup.T * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_4_12 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (-(ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 5))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (-(ModularGroup.S * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 4) * (-(ModularGroup.S * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_4_13 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (-(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 1, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 1))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show (((Mp 4) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1]
    module

private lemma case_5_0 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 5))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 5) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_5_1 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (0 : R), (-2 : ℂ) • MpElem 0 + (1 : ℂ) • MpElem 1, ?_, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, Or.inl rfl, (Rneg + 1) * ((2 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) + (-1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 1)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * ModularGroup.S) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 5) * ModularGroup.S) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_5 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((-(ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_5_2 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.T))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (2 : ℂ) • MpElem 0 + (1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, (Rneg + 1) * ((-1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * ModularGroup.T) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * ModularGroup.T) (1:ℂ) := by
      rw [show (((Mp 5) * ModularGroup.T) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * ModularGroup.T) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * ModularGroup.T) (1:ℂ) := by
      rw [show ((ModularGroup.S * ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * ModularGroup.T) from by decide]
    have h_6 : (MonoidAlgebra.single (-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_5_3 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S), (0 : R), (-1 : ℂ) • MpElem 2 + (2 : ℂ) • MpElem 4, ?_, Or.inr ⟨(1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S), rfl⟩, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 2))) ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 4)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 5) * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.T * ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_5_4 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 5) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_5_5 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 0))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 5) * (ModularGroup.S * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_5_6 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹), (-1 : ℂ) • MpElem 3 + (2 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹), rfl⟩, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 4)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 5) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5]
    module

private lemma case_5_7 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (-((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 5, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 5))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 5) * (-(1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((-((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_5_8 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (-(ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL ModularGroup.T⁻¹, (0 : R), (2 : ℂ) • MpElem 0 + (-1 : ℂ) • MpElem 1, ?_, Or.inr ⟨(1 : ℂ), ModularGroup.T⁻¹, rfl⟩, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (2:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 1)))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (-ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T (1:ℂ) := by
      rw [show (((Mp 5) * (-ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.T * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4]
    module

private lemma case_5_9 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (-(ModularGroup.T)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S), (-2 : ℂ) • MpElem 0 + (-1 : ℂ) • MpElem 2, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S), rfl⟩, (Rneg + 1) * ((2 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 0))) ((Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 2)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (-ModularGroup.T)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 5) * (-ModularGroup.T)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S)))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T⁻¹ * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.S) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.S) from by decide]
    have h_6 : (MonoidAlgebra.single (-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((-(-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_5_10 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (-(ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (0 : R), (1 : ℂ) • MpElem 2 + (-2 : ℂ) • MpElem 4, ?_, Or.inr ⟨(1 : ℂ), (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, Or.inl rfl, (Rneg + 1) * ((2 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (-1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2))) ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 4)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [T2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (-ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 5) * (-ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.T * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.T * (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_6 : (MonoidAlgebra.single (-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((-(((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6]
    module

private lemma case_5_11 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (-(ModularGroup.T * ModularGroup.S)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (-1 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inl rfl, (Rneg + 1) * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (-1:ℂ) (spMp_mem_spMpSpan 4))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (-(ModularGroup.T * ModularGroup.S))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 5) * (-(ModularGroup.T * ModularGroup.S))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_2 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2]
    module

private lemma case_5_12 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (-(ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (0 : R), (1 : ℂ) • MpElem 0, ?_, Or.inl rfl, Or.inl rfl, (0 : R), ?_, ?_⟩
  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 0))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (-(ModularGroup.S * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 5) * (-(ModularGroup.S * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1]
    module

private lemma case_5_13 : ∃ (A B u : R), u ∈ spMpSpan ∧
    (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • ofSL γ) ∧
    (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • ofSL γ) ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (-(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)))
      = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by
  refine ⟨(0 : R), (1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), (1 : ℂ) • MpElem 3 + (-2 : ℂ) • MpElem 4, ?_, Or.inl rfl, Or.inr ⟨(1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), rfl⟩, (Rneg + 1) * ((-1 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (2 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩
  · exact Submodule.add_mem _ ((Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))) ((Submodule.smul_mem _ (-2:ℂ) (spMp_mem_spMpSpan 4)))
  · exact augIdealOdd_mul_mem Rneg_add_one_mem_augIdealOdd _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    rw [ST2_mul_smul_single]
    rw [mul_add, aug_mul_smul_single, aug_mul_smul_single]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show (((Mp 5) * (-((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_2 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_3 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_4 : (MonoidAlgebra.single (ModularGroup.S * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * (ModularGroup.T * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_5 : (MonoidAlgebra.single (ModularGroup.S * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) := by
      rw [show ((ModularGroup.S * ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (((ModularGroup.S * ModularGroup.T⁻¹) * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) from by decide]
    have h_6 : (MonoidAlgebra.single (-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((-(ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_7 : (MonoidAlgebra.single (-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((-((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1, h_2, h_3, h_4, h_5, h_6, h_7]
    module

theorem neighbour_decomp (ν : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hν : ν ∈ Work.Asymptotics.NeighborsP) (i : Fin 6) :
    ∃ (A B u : Work.Kernels.R), u ∈ Work.Asymptotics.spMpSpan ∧
      (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), A = c • Work.Asymptotics.ofSL γ) ∧
      (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), B = c • Work.Asymptotics.ofSL γ) ∧
      ∃ w ∈ Work.Asymptotics.augIdealOdd, Work.Asymptotics.ofSL (Work.Asymptotics.Mp i * ν)
        = u + (Work.Kernels.R_T - 1)^2 * A + Work.Kernels.R_S * (Work.Kernels.R_T - 1)^2 * B + w := by

  unfold Work.Asymptotics.NeighborsP at hν
  simp only [Set.mem_ofPred_eq] at hν
  rcases hν with h | h
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · fin_cases i
      · exact case_0_0
      · exact case_1_0
      · exact case_2_0
      · exact case_3_0
      · exact case_4_0
      · exact case_5_0
    · fin_cases i
      · exact case_0_1
      · exact case_1_1
      · exact case_2_1
      · exact case_3_1
      · exact case_4_1
      · exact case_5_1
    · fin_cases i
      · exact case_0_2
      · exact case_1_2
      · exact case_2_2
      · exact case_3_2
      · exact case_4_2
      · exact case_5_2
    · fin_cases i
      · exact case_0_3
      · exact case_1_3
      · exact case_2_3
      · exact case_3_3
      · exact case_4_3
      · exact case_5_3
    · fin_cases i
      · exact case_0_4
      · exact case_1_4
      · exact case_2_4
      · exact case_3_4
      · exact case_4_4
      · exact case_5_4
    · fin_cases i
      · exact case_0_5
      · exact case_1_5
      · exact case_2_5
      · exact case_3_5
      · exact case_4_5
      · exact case_5_5
    · fin_cases i
      · exact case_0_6
      · exact case_1_6
      · exact case_2_6
      · exact case_3_6
      · exact case_4_6
      · exact case_5_6
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h | h | h
    · have hν' : ν = -((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by rw [← h]; simp
      rw [hν']
      fin_cases i
      · exact case_0_7
      · exact case_1_7
      · exact case_2_7
      · exact case_3_7
      · exact case_4_7
      · exact case_5_7
    · have hν' : ν = -(ModularGroup.S) := by rw [← h]; simp
      rw [hν']
      fin_cases i
      · exact case_0_8
      · exact case_1_8
      · exact case_2_8
      · exact case_3_8
      · exact case_4_8
      · exact case_5_8
    · have hν' : ν = -(ModularGroup.T) := by rw [← h]; simp
      rw [hν']
      fin_cases i
      · exact case_0_9
      · exact case_1_9
      · exact case_2_9
      · exact case_3_9
      · exact case_4_9
      · exact case_5_9
    · have hν' : ν = -(ModularGroup.T⁻¹) := by rw [← h]; simp
      rw [hν']
      fin_cases i
      · exact case_0_10
      · exact case_1_10
      · exact case_2_10
      · exact case_3_10
      · exact case_4_10
      · exact case_5_10
    · have hν' : ν = -(ModularGroup.T * ModularGroup.S) := by rw [← h]; simp
      rw [hν']
      fin_cases i
      · exact case_0_11
      · exact case_1_11
      · exact case_2_11
      · exact case_3_11
      · exact case_4_11
      · exact case_5_11
    · have hν' : ν = -(ModularGroup.S * ModularGroup.T⁻¹) := by rw [← h]; simp
      rw [hν']
      fin_cases i
      · exact case_0_12
      · exact case_1_12
      · exact case_2_12
      · exact case_3_12
      · exact case_4_12
      · exact case_5_12
    · have hν' : ν = -(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) := by rw [← h]; simp
      rw [hν']
      fin_cases i
      · exact case_0_13
      · exact case_1_13
      · exact case_2_13
      · exact case_3_13
      · exact case_4_13
      · exact case_5_13

end Work.Asymptotics

