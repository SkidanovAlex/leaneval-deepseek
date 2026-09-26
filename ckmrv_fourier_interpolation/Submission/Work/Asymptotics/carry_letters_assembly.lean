import Submission.Work.Asymptotics.carry_letters_one
import Submission.Work.Asymptotics.carry_letters_S
import Submission.Work.Asymptotics.carry_letters_T
import Submission.Work.Asymptotics.carry_letters_Tinv
import Submission.Work.Asymptotics.carry_letters_TS
import Submission.Work.Asymptotics.carry_letters_STinv
import Submission.Work.Asymptotics.carry_letters_TSTinv

/-!
# The finite check of CKMRV Proposition 3.2(1) for all neighbours `ν ∈ NeighborsP`

Assembles the per-letter checks of `Submission/Work/Asymptotics/carry_letters_*.lean`
into the single interface used by the small extension claim:
`∀ ν ∈ NeighborsP, ∃ a b, CarryOk ν i a b ∧ SafePair ν i a ∧ SafePairS ν i b`.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Work.Kernels Work.Residues
open scoped MatrixGroups

namespace Work.Asymptotics

/-- The error vector of the second basis is insensitive to `γ ↦ -γ` modulo `(z-1)R`. -/
lemma rowDiffP_neg_sub (μ : X) (i : Fin 6) :
    (rowDiffP (MonoidAlgebra.of ℂ X (-μ)) i - rowDiffP (MonoidAlgebra.of ℂ X μ) i) ∈ augIdeal := by
  have hσ : sigmaP (MonoidAlgebra.of ℂ X (-μ)) = sigmaP (MonoidAlgebra.of ℂ X μ) := by
    rw [of_neg_of, sigmaP_mul, sigmaP_Rneg, one_mul]
  have h1 : rowDiffP (MonoidAlgebra.of ℂ X (-μ)) i - rowDiffP (MonoidAlgebra.of ℂ X μ) i
      = MpR i * ((MonoidAlgebra.of ℂ X (-μ) : R) - MonoidAlgebra.of ℂ X μ) := by
    simp only [rowDiffP, hσ]
    noncomm_ring
  rw [h1, show (MonoidAlgebra.of ℂ X (-μ) : R) - MonoidAlgebra.of ℂ X μ
      = (Rneg - 1) * MonoidAlgebra.of ℂ X μ from by rw [of_neg_of]; noncomm_ring]
  exact mul_mem_augIdeal_left (Rneg_sub_one_mul_mem _) _

/-- The checks for `μ` descend to `-μ`. -/
theorem neg_carry (μ : X) (i : Fin 6) (a b : Option X) (h : CarryOk μ i a b)
    (ha : SafePair μ i a) (hb : SafePairS μ i b) :
    CarryOk (-μ) i a b ∧ SafePair (-μ) i a ∧ SafePairS (-μ) i b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOk] at h ⊢
    have h1 := rowDiffP_neg_sub μ i
    rw [show rowDiffP (MonoidAlgebra.of ℂ X (-μ)) i
        - ((R_T - 1)^2 * ofOpt a + R_S * (R_T - 1)^2 * ofOpt b)
        = (rowDiffP (MonoidAlgebra.of ℂ X (-μ)) i - rowDiffP (MonoidAlgebra.of ℂ X μ) i)
          + (rowDiffP (MonoidAlgebra.of ℂ X μ) i
              - ((R_T - 1)^2 * ofOpt a + R_S * (R_T - 1)^2 * ofOpt b)) from by abel]
    exact Submodule.add_mem _ h1 h
  · simpa only [SafePair, SafeThick_neg] using ha
  · simpa only [SafePairS, SafeThick_neg] using hb

/-- The checks for the seven representatives. -/
theorem exists_carry_pos {ν : X} (hν : ν ∈ ({(1 : X), ModularGroup.S, ModularGroup.T,
    ModularGroup.T⁻¹, ModularGroup.T * ModularGroup.S,
    ModularGroup.S * ModularGroup.T⁻¹,
    ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹} : Set X)) (i : Fin 6) :
    ∃ a b : Option X, CarryOk ν i a b ∧ SafePair ν i a ∧ SafePairS ν i b := by
  fin_cases i
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, carry_one_0, hold_one_0, holdS_one_0⟩
    · exact ⟨none, none, carry_S_0, hold_S_0, holdS_S_0⟩
    · exact ⟨(some (-(ModularGroup.T⁻¹))), none, carry_T_0, hold_T_0, holdS_T_0⟩
    · exact ⟨none, none, carry_Tinv_0, hold_Tinv_0, holdS_Tinv_0⟩
    · exact ⟨none, none, carry_TS_0, hold_TS_0, holdS_TS_0⟩
    · exact ⟨none, none, carry_STinv_0, hold_STinv_0, holdS_STinv_0⟩
    · exact ⟨(some (ModularGroup.S * ModularGroup.T * ModularGroup.S)), none, carry_TSTinv_0, hold_TSTinv_0, holdS_TSTinv_0⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, carry_one_1, hold_one_1, holdS_one_1⟩
    · exact ⟨(some (ModularGroup.T⁻¹ * ModularGroup.S)), none, carry_S_1, hold_S_1, holdS_S_1⟩
    · exact ⟨none, none, carry_T_1, hold_T_1, holdS_T_1⟩
    · exact ⟨(some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)), none, carry_Tinv_1, hold_Tinv_1, holdS_Tinv_1⟩
    · exact ⟨none, none, carry_TS_1, hold_TS_1, holdS_TS_1⟩
    · exact ⟨none, none, carry_STinv_1, hold_STinv_1, holdS_STinv_1⟩
    · exact ⟨none, none, carry_TSTinv_1, hold_TSTinv_1, holdS_TSTinv_1⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, carry_one_2, hold_one_2, holdS_one_2⟩
    · exact ⟨none, (some (-(ModularGroup.T⁻¹))), carry_S_2, hold_S_2, holdS_S_2⟩
    · exact ⟨(some (ModularGroup.T⁻¹ * ModularGroup.S)), none, carry_T_2, hold_T_2, holdS_T_2⟩
    · exact ⟨none, (some (ModularGroup.S * ModularGroup.T * ModularGroup.S)), carry_Tinv_2, hold_Tinv_2, holdS_Tinv_2⟩
    · exact ⟨none, none, carry_TS_2, hold_TS_2, holdS_TS_2⟩
    · exact ⟨none, none, carry_STinv_2, hold_STinv_2, holdS_STinv_2⟩
    · exact ⟨(some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)), none, carry_TSTinv_2, hold_TSTinv_2, holdS_TSTinv_2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, carry_one_3, hold_one_3, holdS_one_3⟩
    · exact ⟨none, none, carry_S_3, hold_S_3, holdS_S_3⟩
    · exact ⟨none, (some (-(ModularGroup.T⁻¹))), carry_T_3, hold_T_3, holdS_T_3⟩
    · exact ⟨none, none, carry_Tinv_3, hold_Tinv_3, holdS_Tinv_3⟩
    · exact ⟨none, none, carry_TS_3, hold_TS_3, holdS_TS_3⟩
    · exact ⟨none, none, carry_STinv_3, hold_STinv_3, holdS_STinv_3⟩
    · exact ⟨none, (some (ModularGroup.S * ModularGroup.T * ModularGroup.S)), carry_TSTinv_3, hold_TSTinv_3, holdS_TSTinv_3⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, carry_one_4, hold_one_4, holdS_one_4⟩
    · exact ⟨none, (some (ModularGroup.T⁻¹ * ModularGroup.S)), carry_S_4, hold_S_4, holdS_S_4⟩
    · exact ⟨none, none, carry_T_4, hold_T_4, holdS_T_4⟩
    · exact ⟨none, (some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)), carry_Tinv_4, hold_Tinv_4, holdS_Tinv_4⟩
    · exact ⟨none, none, carry_TS_4, hold_TS_4, holdS_TS_4⟩
    · exact ⟨none, none, carry_STinv_4, hold_STinv_4, holdS_STinv_4⟩
    · exact ⟨none, none, carry_TSTinv_4, hold_TSTinv_4, holdS_TSTinv_4⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, carry_one_5, hold_one_5, holdS_one_5⟩
    · exact ⟨(some (-(ModularGroup.T⁻¹))), none, carry_S_5, hold_S_5, holdS_S_5⟩
    · exact ⟨none, (some (ModularGroup.T⁻¹ * ModularGroup.S)), carry_T_5, hold_T_5, holdS_T_5⟩
    · exact ⟨(some (ModularGroup.S * ModularGroup.T * ModularGroup.S)), none, carry_Tinv_5, hold_Tinv_5, holdS_Tinv_5⟩
    · exact ⟨none, none, carry_TS_5, hold_TS_5, holdS_TS_5⟩
    · exact ⟨none, none, carry_STinv_5, hold_STinv_5, holdS_STinv_5⟩
    · exact ⟨none, (some (ModularGroup.S * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹)), carry_TSTinv_5, hold_TSTinv_5, holdS_TSTinv_5⟩

theorem exists_carry_neighborsP (ν : X) (hν : ν ∈ NeighborsP) (i : Fin 6) :
    ∃ a b : Option X, CarryOk ν i a b ∧ SafePair ν i a ∧ SafePairS ν i b := by
  rcases hν with h | h
  · exact exists_carry_pos h i
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h1 | h1 | h1 | h1 | h1 | h1 | h1
    · rw [show ν = -((1 : X)) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos (ν := ((1 : X))) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry ((1 : X)) i a b hc ha hb
      exact ⟨a, b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.S) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos (ν := (ModularGroup.S)) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry (ModularGroup.S) i a b hc ha hb
      exact ⟨a, b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.T) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos (ν := (ModularGroup.T)) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry (ModularGroup.T) i a b hc ha hb
      exact ⟨a, b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.T⁻¹) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos (ν := (ModularGroup.T⁻¹)) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry (ModularGroup.T⁻¹) i a b hc ha hb
      exact ⟨a, b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.T * ModularGroup.S) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos (ν := (ModularGroup.T * ModularGroup.S)) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry (ModularGroup.T * ModularGroup.S) i a b hc ha hb
      exact ⟨a, b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.S * ModularGroup.T⁻¹) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos (ν := (ModularGroup.S * ModularGroup.T⁻¹)) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry (ModularGroup.S * ModularGroup.T⁻¹) i a b hc ha hb
      exact ⟨a, b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos (ν := (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) i a b hc ha hb
      exact ⟨a, b, k1, k2, k3⟩

end Work.Asymptotics
