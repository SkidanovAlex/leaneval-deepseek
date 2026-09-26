/-
# The finite check of CKMRV Proposition 3.2(1) at odd weight

For a neighbour `ν` of the standard fundamental domain `𝓕̄` and a row `i`, the error vector

  `rowDiffOdd ν i = MpElem i * ofSL ν - ∑_j σ(ν)_{ij} MpElem j ∈ 𝓘_odd`

of the reduction of `R = ℂ[SL(2,ℤ)]` modulo the odd-weight defect ideal
`𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R` (`Work.Asymptotics.idealIOdd`) admits carries:

  `rowDiffOdd ν i - ((T-I)² a + S(T-I)² b) ∈ augIdealOdd = (1+z)R`,

with `a`, `b` each `0` (i.e. `none`) or a scalar multiple of a *single* group element
(`Work.Asymptotics.CarryOkOdd`), and with the group elements *safe* in the sense that their
`T`- (resp. `S T`-) translates again land in the safe set
(`Work.Asymptotics.SafePairOdd`, `Work.Asymptotics.SafePairSOdd`).

This is the finite check of CKMRV Proposition 3.2(1) at odd weight; it is the odd-weight
analogue of `Work.Asymptotics.exists_carry_neighborsP` (`carry_letters_*`).  The group algebra
computations are those of `Work.Asymptotics.neighbour_decomp`, repackaged against the interface
`Work.Asymptotics.CarryOkOdd`; the neighbours are reduced to the seven positive representatives
by the observation that `rowDiffOdd (-ν) i + rowDiffOdd ν i ∈ augIdealOdd` (so `ν ↦ -ν` acts
by negating the *scalars* of the carries, keeping the group elements, hence the safety).
-/
import Mathlib
import Submission.Work.Asymptotics.SmallExtensionOddDefs
import Submission.Work.Asymptotics.small_decomp_neighbor_odd
import Submission.Work.Asymptotics.ExtensionEvenDefs
import Submission.Work.Asymptotics.PropagateCarriesOdd
import Submission.Work.Asymptotics.neighbour_decomp

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

noncomputable section

open Work.Kernels Work.Asymptotics
open scoped MatrixGroups MonoidAlgebra

namespace Work.Asymptotics

/-! ## The involution `ν ↦ -ν` on carries -/

/-- Negate the scalar of a carry, keeping its group element: this is the effect of replacing a
neighbour `ν` by `-ν` on the carries (see `neg_carry_odd`). -/
def negOpt : Option (ℂ × X) → Option (ℂ × X)
  | none => none
  | some (c, γ) => some (-c, γ)

@[simp] lemma negOpt_none : negOpt (none : Option (ℂ × X)) = none := rfl
@[simp] lemma negOpt_some (c : ℂ) (γ : X) : negOpt (some (c, γ)) = some (-c, γ) := rfl

lemma ofOptC_negOpt (a : Option (ℂ × X)) : ofOptC (negOpt a) = -ofOptC a := by
  rcases a with _ | ⟨c, γ⟩
  · simp
  · simp only [negOpt_some, ofOptC_some, neg_smul]

/-- `ofSL (-ν) = z * ofSL ν` in the group algebra. -/
lemma ofSL_neg_eq (ν : X) : ofSL (-ν) = Rneg * ofSL ν := by
  rw [show (-ν : X) = (-1) * ν from by simp, ofSL_mul]

/-- **`ν` and `-ν` carry the same error, up to sign.**  Since `z` acts as `-1` on the quotient
`R ⧸ (1+z)R`, one has `rowDiffOdd (-ν) i + rowDiffOdd ν i ∈ (1+z)R`. -/
lemma rowDiffOdd_neg_add_mem_augIdealOdd (ν : X) (i : Fin 6) :
    rowDiffOdd (-ν) i + rowDiffOdd ν i ∈ augIdealOdd := by
  have hbase : MpElem i * ofSL (-ν) + MpElem i * ofSL ν ∈ augIdealOdd := by
    rw [ofSL_neg_eq ν]
    have h : MpElem i * (Rneg * ofSL ν) + MpElem i * ofSL ν
        = MpElem i * (Rneg + 1) * ofSL ν := by noncomm_ring
    rw [h]
    exact Submodule.subset_span ⟨MpElem i, ofSL ν, rfl⟩
  have hsp : (rowDiffOdd (-ν) i + rowDiffOdd ν i) - (MpElem i * ofSL (-ν) + MpElem i * ofSL ν)
      ∈ spMpSpan := by
    have h1 : (∑ j : Fin 6, (sigmaHom (-ν)) i j • MpElem j) ∈ spMpSpan :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (spMp_mem_spMpSpan j)
    have h2 : (∑ j : Fin 6, (sigmaHom ν) i j • MpElem j) ∈ spMpSpan :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (spMp_mem_spMpSpan j)
    rw [rowDiffOdd, rowDiffOdd]
    rw [show MpElem i * ofSL (-ν) - (∑ j, (sigmaHom (-ν)) i j • MpElem j)
          + (MpElem i * ofSL ν - ∑ j, (sigmaHom ν) i j • MpElem j)
          - (MpElem i * ofSL (-ν) + MpElem i * ofSL ν)
        = - (∑ j, (sigmaHom (-ν)) i j • MpElem j)
          - (∑ j, (sigmaHom ν) i j • MpElem j) from by abel]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ h1) h2
  have hmem : (rowDiffOdd (-ν) i + rowDiffOdd ν i) - (MpElem i * ofSL (-ν) + MpElem i * ofSL ν)
      ∈ idealIOdd :=
    Submodule.sub_mem _
      (Submodule.add_mem _ (rowDiffOdd_mem_idealIOdd (-ν) i) (rowDiffOdd_mem_idealIOdd ν i))
      (augIdealOdd_le_idealIOdd hbase)
  have hzero : (rowDiffOdd (-ν) i + rowDiffOdd ν i)
      - (MpElem i * ofSL (-ν) + MpElem i * ofSL ν) = 0 := by
    have := Submodule.mem_inf.mpr ⟨hsp, hmem⟩
    rw [spMpSpan_inf_idealIOdd] at this
    simpa using this
  rw [sub_eq_zero.mp hzero]
  exact hbase

/-- **Descent of the carries to `-ν`.**  The carries of `ν` also work for `-ν` after negating
their scalars; the group elements — hence `SafePairOdd`/`SafePairSOdd`, which only see
`SafeThick ν i = SafeThick (-ν) i` — are unchanged. -/
theorem neg_carry_odd (μ : X) (i : Fin 6) (a b : Option (ℂ × X))
    (h : CarryOkOdd μ i a b) (ha : SafePairOdd μ i a) (hb : SafePairSOdd μ i b) :
    CarryOkOdd (-μ) i (negOpt a) (negOpt b) ∧ SafePairOdd (-μ) i (negOpt a)
      ∧ SafePairSOdd (-μ) i (negOpt b) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd] at h ⊢
    rw [ofOptC_negOpt a, ofOptC_negOpt b]
    have h2 := rowDiffOdd_neg_add_mem_augIdealOdd μ i
    have hkey : rowDiffOdd (-μ) i - ((R_T - 1) ^ 2 * -ofOptC a + R_S * (R_T - 1) ^ 2 * -ofOptC b)
        = (rowDiffOdd (-μ) i + rowDiffOdd μ i)
          - (rowDiffOdd μ i - ((R_T - 1) ^ 2 * ofOptC a + R_S * (R_T - 1) ^ 2 * ofOptC b)) := by
      noncomm_ring
    rw [hkey]
    simpa only [sub_eq_add_neg] using Submodule.add_mem _ h2 (Submodule.neg_mem _ h)
  · intro c γ hc
    rw [SafeThick_neg]
    rcases a with _ | ⟨c₀, γ₀⟩
    · simp [negOpt] at hc
    · simp only [negOpt_some, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨-, rfl⟩ := hc
      exact ha c₀ γ₀ rfl
  · intro c γ hc
    rw [SafeThick_neg]
    rcases b with _ | ⟨c₀, γ₀⟩
    · simp [negOpt] at hc
    · simp only [negOpt_some, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨-, rfl⟩ := hc
      exact hb c₀ γ₀ rfl

/-! ## The finite checks for the seven positive neighbours -/

-- ======================================================================
private lemma casePos_0_0 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 0, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 0))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 0) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_1_0 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 1, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 1))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show (((Mp 1) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_2_0 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 2, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 2) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 2) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_3_0 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 3, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show (((Mp 3) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_4_0 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 4) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_5_0 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 5, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 5))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 5) * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_0_1 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 3, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * ModularGroup.S) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show (((Mp 0) * ModularGroup.S) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_1_1 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.S))
      = u + (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(2 : ℂ) • MpElem 3 + (-1 : ℂ) • MpElem 5, ?_, (0 : R), ?_, ?_⟩

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

private lemma casePos_2_1 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) + w := by
  refine ⟨(-2 : ℂ) • MpElem 3 + (1 : ℂ) • MpElem 4, ?_, (Rneg + 1) * ((2 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (-1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_3_1 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 0, ?_, (Rneg + 1) * ((1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩

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

private lemma casePos_4_1 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S)) + w := by
  refine ⟨(-2 : ℂ) • MpElem 0 + (-1 : ℂ) • MpElem 2, ?_, (Rneg + 1) * ((2 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩

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

private lemma casePos_5_1 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.S))
      = u + (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-2 : ℂ) • MpElem 0 + (1 : ℂ) • MpElem 1, ?_, (Rneg + 1) * ((2 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) + (-1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_0_2 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.T))
      = u + (R_T - 1)^2 * ((1 : ℂ) • ofSL ModularGroup.T⁻¹) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(2 : ℂ) • MpElem 0 + (-1 : ℂ) • MpElem 1, ?_, (0 : R), ?_, ?_⟩

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

private lemma casePos_1_2 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.T))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 0, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 0))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * ModularGroup.T) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show (((Mp 1) * ModularGroup.T) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 0) (1:ℂ) : R) = MonoidAlgebra.single (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (1:ℂ) := by
      rw [show ((Mp 0) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_2_2 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.T))
      = u + (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(2 : ℂ) • MpElem 3 + (-1 : ℂ) • MpElem 5, ?_, (0 : R), ?_, ?_⟩

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

private lemma casePos_3_2 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.T))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL ModularGroup.T⁻¹) + w := by
  refine ⟨(2 : ℂ) • MpElem 3 + (-1 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

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

private lemma casePos_4_2 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.T))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 3, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 4) * ModularGroup.T) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show (((Mp 4) * ModularGroup.T) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_5_2 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.T))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) + w := by
  refine ⟨(2 : ℂ) • MpElem 0 + (1 : ℂ) • MpElem 2, ?_, (Rneg + 1) * ((-1 : ℂ) • ofSL (((ModularGroup.S * ModularGroup.T) * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_0_3 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 1, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 1))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show (((Mp 0) * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 1) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.T⁻¹ (1:ℂ) := by
      rw [show ((Mp 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T⁻¹ from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_1_3 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 0 + (2 : ℂ) • MpElem 1, ?_, (0 : R), ?_, ?_⟩

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

private lemma casePos_2_3 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) + w := by
  refine ⟨(-2 : ℂ) • MpElem 1 + (1 : ℂ) • MpElem 5, ?_, (Rneg + 1) * ((2 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (-1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_3_3 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * ModularGroup.T⁻¹) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 3) * ModularGroup.T⁻¹) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_4_3 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 3 + (2 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

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

private lemma casePos_5_3 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 2 + (2 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

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

private lemma casePos_0_4 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 5, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 5))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 0) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 5) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 5) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.T * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_1_4 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 3, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 3))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show (((Mp 1) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 3) (1:ℂ) : R) = MonoidAlgebra.single ModularGroup.S (1:ℂ) := by
      rw [show ((Mp 3) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_2_4 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 1, ?_, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_3_4 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 2, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 3) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 3) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_4_4 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 0, ?_, (Rneg + 1) * ((1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩

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

private lemma casePos_5_4 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.T * ModularGroup.S))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 5) * (ModularGroup.T * ModularGroup.S)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 5) * (ModularGroup.T * ModularGroup.S)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_0_5 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 0) * (ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 0) * (ModularGroup.S * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_1_5 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 2, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 2))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * (ModularGroup.S * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show (((Mp 1) * (ModularGroup.S * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 2) (1:ℂ) : R) = MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) (1:ℂ) := by
      rw [show ((Mp 2) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ((ModularGroup.S * ModularGroup.T) * ModularGroup.S) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_2_5 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 3, ?_, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.S * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_3_5 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 1, ?_, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_4_5 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 5, ?_, (Rneg + 1) * ((1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_5_5 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 0, ?_, (Rneg + 1) * ((1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)), ?_, ?_⟩

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

private lemma casePos_0_6 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 0 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 2 + (2 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

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

private lemma casePos_1_6 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 1 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

  · exact (Submodule.smul_mem _ (1:ℂ) (spMp_mem_spMpSpan 4))
  · exact Submodule.zero_mem _
  · simp only [ofSL, MpElem, mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
    have h_0 : (MonoidAlgebra.single ((Mp 1) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show (((Mp 1) * ((ModularGroup.T * ModularGroup.S) * ModularGroup.T⁻¹)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    have h_1 : (MonoidAlgebra.single (Mp 4) (1:ℂ) : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T⁻¹) (1:ℂ) := by
      rw [show ((Mp 4) : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (ModularGroup.S * ModularGroup.T⁻¹) from by decide]
    simp only [h_0, h_1]
    module

private lemma casePos_2_6 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 2 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(1 : ℂ) • MpElem 0 + (-2 : ℂ) • MpElem 1, ?_, (Rneg + 1) * ((-1 : ℂ) • ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) + (2 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_3_6 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 3 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) + w := by
  refine ⟨(-2 : ℂ) • MpElem 1 + (1 : ℂ) • MpElem 5, ?_, (Rneg + 1) * ((2 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) + (-1 : ℂ) • ofSL ((ModularGroup.T * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_4_6 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 4 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 1, ?_, (Rneg + 1) * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), ?_, ?_⟩

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

private lemma casePos_5_6 : ∃ (u : R), u ∈ spMpSpan ∧
    ∃ w ∈ augIdealOdd, ofSL (Mp 5 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹))
      = u + (R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) + w := by
  refine ⟨(-1 : ℂ) • MpElem 3 + (2 : ℂ) • MpElem 4, ?_, (0 : R), ?_, ?_⟩

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

private lemma carryOdd_0_0 :
    CarryOkOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 (none) (none) ∧ SafePairOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 (none)
      ∧ SafePairSOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_0_0
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 0 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 0 * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_1_0 :
    CarryOkOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 (none) (none) ∧ SafePairOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 (none)
      ∧ SafePairSOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_1_0
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 1 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 1 * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_2_0 :
    CarryOkOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 2 (none) (none) ∧ SafePairOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 2 (none)
      ∧ SafePairSOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 2 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_2_0
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 2 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 2 * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_3_0 :
    CarryOkOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 3 (none) (none) ∧ SafePairOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 3 (none)
      ∧ SafePairSOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 3 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_3_0
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 3 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 3 * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_4_0 :
    CarryOkOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 4 (none) (none) ∧ SafePairOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 4 (none)
      ∧ SafePairSOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 4 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_4_0
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 4 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 4 * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_5_0 :
    CarryOkOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 5 (none) (none) ∧ SafePairOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 5 (none)
      ∧ SafePairSOdd (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 5 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_5_0
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 5 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 5 * (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_0_1 :
    CarryOkOdd (ModularGroup.S) 0 (none) (none) ∧ SafePairOdd (ModularGroup.S) 0 (none)
      ∧ SafePairSOdd (ModularGroup.S) 0 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_0_1
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 0 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 0 * (ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_1_1 :
    CarryOkOdd (ModularGroup.S) 1 (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S))) (none) ∧ SafePairOdd (ModularGroup.S) 1 (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S)))
      ∧ SafePairSOdd (ModularGroup.S) 1 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_1_1
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 1 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 1 * (ModularGroup.S)) - u - ((R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide
  · intro c γ h
    simp at h

private lemma carryOdd_2_1 :
    CarryOkOdd (ModularGroup.S) 2 (none) (some ((1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) ∧ SafePairOdd (ModularGroup.S) 2 (none)
      ∧ SafePairSOdd (ModularGroup.S) 2 (some ((1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_2_1
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 2 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 2 * (ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide

private lemma carryOdd_3_1 :
    CarryOkOdd (ModularGroup.S) 3 (none) (none) ∧ SafePairOdd (ModularGroup.S) 3 (none)
      ∧ SafePairSOdd (ModularGroup.S) 3 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_3_1
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 3 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 3 * (ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_4_1 :
    CarryOkOdd (ModularGroup.S) 4 (none) (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S))) ∧ SafePairOdd (ModularGroup.S) 4 (none)
      ∧ SafePairSOdd (ModularGroup.S) 4 (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S))) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_4_1
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 4 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 4 * (ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide

private lemma carryOdd_5_1 :
    CarryOkOdd (ModularGroup.S) 5 (some ((1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (none) ∧ SafePairOdd (ModularGroup.S) 5 (some ((1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))
      ∧ SafePairSOdd (ModularGroup.S) 5 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_5_1
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 5 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 5 * (ModularGroup.S)) - u - ((R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide
  · intro c γ h
    simp at h

private lemma carryOdd_0_2 :
    CarryOkOdd (ModularGroup.T) 0 (some ((1 : ℂ), ModularGroup.T⁻¹)) (none) ∧ SafePairOdd (ModularGroup.T) 0 (some ((1 : ℂ), ModularGroup.T⁻¹))
      ∧ SafePairSOdd (ModularGroup.T) 0 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_0_2
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 0 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 0 * (ModularGroup.T)) - u - ((R_T - 1)^2 * ((1 : ℂ) • ofSL ModularGroup.T⁻¹) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide
  · intro c γ h
    simp at h

private lemma carryOdd_1_2 :
    CarryOkOdd (ModularGroup.T) 1 (none) (none) ∧ SafePairOdd (ModularGroup.T) 1 (none)
      ∧ SafePairSOdd (ModularGroup.T) 1 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_1_2
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 1 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 1 * (ModularGroup.T)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_2_2 :
    CarryOkOdd (ModularGroup.T) 2 (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S))) (none) ∧ SafePairOdd (ModularGroup.T) 2 (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S)))
      ∧ SafePairSOdd (ModularGroup.T) 2 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_2_2
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 2 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 2 * (ModularGroup.T)) - u - ((R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.S)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide
  · intro c γ h
    simp at h

private lemma carryOdd_3_2 :
    CarryOkOdd (ModularGroup.T) 3 (none) (some ((1 : ℂ), ModularGroup.T⁻¹)) ∧ SafePairOdd (ModularGroup.T) 3 (none)
      ∧ SafePairSOdd (ModularGroup.T) 3 (some ((1 : ℂ), ModularGroup.T⁻¹)) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_3_2
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 3 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 3 * (ModularGroup.T)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL ModularGroup.T⁻¹)) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide

private lemma carryOdd_4_2 :
    CarryOkOdd (ModularGroup.T) 4 (none) (none) ∧ SafePairOdd (ModularGroup.T) 4 (none)
      ∧ SafePairSOdd (ModularGroup.T) 4 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_4_2
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 4 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 4 * (ModularGroup.T)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_5_2 :
    CarryOkOdd (ModularGroup.T) 5 (none) (some ((1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) ∧ SafePairOdd (ModularGroup.T) 5 (none)
      ∧ SafePairSOdd (ModularGroup.T) 5 (some ((1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_5_2
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 5 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 5 * (ModularGroup.T)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide

private lemma carryOdd_0_3 :
    CarryOkOdd (ModularGroup.T⁻¹) 0 (none) (none) ∧ SafePairOdd (ModularGroup.T⁻¹) 0 (none)
      ∧ SafePairSOdd (ModularGroup.T⁻¹) 0 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_0_3
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 0 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 0 * (ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_1_3 :
    CarryOkOdd (ModularGroup.T⁻¹) 1 (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) (none) ∧ SafePairOdd (ModularGroup.T⁻¹) 1 (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)))
      ∧ SafePairSOdd (ModularGroup.T⁻¹) 1 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_1_3
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 1 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 1 * (ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide
  · intro c γ h
    simp at h

private lemma carryOdd_2_3 :
    CarryOkOdd (ModularGroup.T⁻¹) 2 (none) (some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) ∧ SafePairOdd (ModularGroup.T⁻¹) 2 (none)
      ∧ SafePairSOdd (ModularGroup.T⁻¹) 2 (some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_2_3
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 2 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 2 * (ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide

private lemma carryOdd_3_3 :
    CarryOkOdd (ModularGroup.T⁻¹) 3 (none) (none) ∧ SafePairOdd (ModularGroup.T⁻¹) 3 (none)
      ∧ SafePairSOdd (ModularGroup.T⁻¹) 3 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_3_3
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 3 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 3 * (ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_4_3 :
    CarryOkOdd (ModularGroup.T⁻¹) 4 (none) (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) ∧ SafePairOdd (ModularGroup.T⁻¹) 4 (none)
      ∧ SafePairSOdd (ModularGroup.T⁻¹) 4 (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_4_3
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 4 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 4 * (ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide

private lemma carryOdd_5_3 :
    CarryOkOdd (ModularGroup.T⁻¹) 5 (some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) (none) ∧ SafePairOdd (ModularGroup.T⁻¹) 5 (some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)))
      ∧ SafePairSOdd (ModularGroup.T⁻¹) 5 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_5_3
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 5 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 5 * (ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide
  · intro c γ h
    simp at h

private lemma carryOdd_0_4 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S) 0 (none) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S) 0 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S) 0 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_0_4
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 0 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 0 * (ModularGroup.T * ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_1_4 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S) 1 (none) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S) 1 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S) 1 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_1_4
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 1 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 1 * (ModularGroup.T * ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_2_4 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S) 2 (none) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S) 2 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S) 2 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_2_4
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 2 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 2 * (ModularGroup.T * ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_3_4 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S) 3 (none) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S) 3 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S) 3 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_3_4
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 3 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 3 * (ModularGroup.T * ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_4_4 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S) 4 (none) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S) 4 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S) 4 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_4_4
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 4 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 4 * (ModularGroup.T * ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_5_4 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S) 5 (none) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S) 5 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S) 5 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_5_4
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 5 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 5 * (ModularGroup.T * ModularGroup.S)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_0_5 :
    CarryOkOdd (ModularGroup.S * ModularGroup.T⁻¹) 0 (none) (none) ∧ SafePairOdd (ModularGroup.S * ModularGroup.T⁻¹) 0 (none)
      ∧ SafePairSOdd (ModularGroup.S * ModularGroup.T⁻¹) 0 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_0_5
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 0 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 0 * (ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_1_5 :
    CarryOkOdd (ModularGroup.S * ModularGroup.T⁻¹) 1 (none) (none) ∧ SafePairOdd (ModularGroup.S * ModularGroup.T⁻¹) 1 (none)
      ∧ SafePairSOdd (ModularGroup.S * ModularGroup.T⁻¹) 1 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_1_5
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 1 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 1 * (ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_2_5 :
    CarryOkOdd (ModularGroup.S * ModularGroup.T⁻¹) 2 (none) (none) ∧ SafePairOdd (ModularGroup.S * ModularGroup.T⁻¹) 2 (none)
      ∧ SafePairSOdd (ModularGroup.S * ModularGroup.T⁻¹) 2 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_2_5
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 2 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 2 * (ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_3_5 :
    CarryOkOdd (ModularGroup.S * ModularGroup.T⁻¹) 3 (none) (none) ∧ SafePairOdd (ModularGroup.S * ModularGroup.T⁻¹) 3 (none)
      ∧ SafePairSOdd (ModularGroup.S * ModularGroup.T⁻¹) 3 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_3_5
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 3 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 3 * (ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_4_5 :
    CarryOkOdd (ModularGroup.S * ModularGroup.T⁻¹) 4 (none) (none) ∧ SafePairOdd (ModularGroup.S * ModularGroup.T⁻¹) 4 (none)
      ∧ SafePairSOdd (ModularGroup.S * ModularGroup.T⁻¹) 4 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_4_5
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 4 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 4 * (ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_5_5 :
    CarryOkOdd (ModularGroup.S * ModularGroup.T⁻¹) 5 (none) (none) ∧ SafePairOdd (ModularGroup.S * ModularGroup.T⁻¹) 5 (none)
      ∧ SafePairSOdd (ModularGroup.S * ModularGroup.T⁻¹) 5 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_5_5
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 5 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 5 * (ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_0_6 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 0 (some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 0 (some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)))
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 0 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_0_6
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 0 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 0 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide
  · intro c γ h
    simp at h

private lemma carryOdd_1_6 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 1 (none) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 1 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 1 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_1_6
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 1 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 1 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_2_6 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 2 (some ((1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)))) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 2 (some ((1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))))
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 2 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_2_6
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 2 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 2 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide
  · intro c γ h
    simp at h

private lemma carryOdd_3_6 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 3 (none) (some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 3 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 3 (some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_3_6
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 3 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 3 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL ((ModularGroup.S * ModularGroup.T) * ModularGroup.S))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide

private lemma carryOdd_4_6 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 4 (none) (none) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 4 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 4 (none) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_4_6
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 4 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 4 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((0 : R))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    simp at h

private lemma carryOdd_5_6 :
    CarryOkOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 5 (none) (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) ∧ SafePairOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 5 (none)
      ∧ SafePairSOdd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) 5 (some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) := by
  obtain ⟨u, hu, w, hw, heq⟩ := casePos_5_6
  refine ⟨?_, ?_, ?_⟩
  · rw [CarryOkOdd]
    simp only [ofOptC_some, ofOptC_none]
    rw [rowDiffOdd_eq_of_decomp 5 hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
    have h : ofSL (Mp 5 * (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹)) - u - ((R_T - 1)^2 * ((0 : R)) + R_S * (R_T - 1)^2 * ((1 : ℂ) • ofSL (ModularGroup.T⁻¹ * ModularGroup.T⁻¹))) = w := by
      rw [heq]; abel
    rw [h]; exact hw
  · intro c γ h
    simp at h
  · intro c γ h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    decide

theorem exists_carry_pos_odd {ν : X} (hν : ν ∈ ({(1 : X), ModularGroup.S, ModularGroup.T,
    ModularGroup.T⁻¹, ModularGroup.T * ModularGroup.S,
    ModularGroup.S * ModularGroup.T⁻¹,
    ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹} : Set X)) (i : Fin 6) :
    ∃ a b : Option (ℂ × X), CarryOkOdd ν i a b ∧ SafePairOdd ν i a ∧ SafePairSOdd ν i b := by
  fin_cases i
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, (carryOdd_0_0).1, (carryOdd_0_0).2.1, (carryOdd_0_0).2.2⟩
    · exact ⟨none, none, (carryOdd_0_1).1, (carryOdd_0_1).2.1, (carryOdd_0_1).2.2⟩
    · exact ⟨some ((1 : ℂ), ModularGroup.T⁻¹), none, (carryOdd_0_2).1, (carryOdd_0_2).2.1, (carryOdd_0_2).2.2⟩
    · exact ⟨none, none, (carryOdd_0_3).1, (carryOdd_0_3).2.1, (carryOdd_0_3).2.2⟩
    · exact ⟨none, none, (carryOdd_0_4).1, (carryOdd_0_4).2.1, (carryOdd_0_4).2.2⟩
    · exact ⟨none, none, (carryOdd_0_5).1, (carryOdd_0_5).2.1, (carryOdd_0_5).2.2⟩
    · exact ⟨some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)), none, (carryOdd_0_6).1, (carryOdd_0_6).2.1, (carryOdd_0_6).2.2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, (carryOdd_1_0).1, (carryOdd_1_0).2.1, (carryOdd_1_0).2.2⟩
    · exact ⟨some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S)), none, (carryOdd_1_1).1, (carryOdd_1_1).2.1, (carryOdd_1_1).2.2⟩
    · exact ⟨none, none, (carryOdd_1_2).1, (carryOdd_1_2).2.1, (carryOdd_1_2).2.2⟩
    · exact ⟨some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)), none, (carryOdd_1_3).1, (carryOdd_1_3).2.1, (carryOdd_1_3).2.2⟩
    · exact ⟨none, none, (carryOdd_1_4).1, (carryOdd_1_4).2.1, (carryOdd_1_4).2.2⟩
    · exact ⟨none, none, (carryOdd_1_5).1, (carryOdd_1_5).2.1, (carryOdd_1_5).2.2⟩
    · exact ⟨none, none, (carryOdd_1_6).1, (carryOdd_1_6).2.1, (carryOdd_1_6).2.2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, (carryOdd_2_0).1, (carryOdd_2_0).2.1, (carryOdd_2_0).2.2⟩
    · exact ⟨none, some ((1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), (carryOdd_2_1).1, (carryOdd_2_1).2.1, (carryOdd_2_1).2.2⟩
    · exact ⟨some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S)), none, (carryOdd_2_2).1, (carryOdd_2_2).2.1, (carryOdd_2_2).2.2⟩
    · exact ⟨none, some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)), (carryOdd_2_3).1, (carryOdd_2_3).2.1, (carryOdd_2_3).2.2⟩
    · exact ⟨none, none, (carryOdd_2_4).1, (carryOdd_2_4).2.1, (carryOdd_2_4).2.2⟩
    · exact ⟨none, none, (carryOdd_2_5).1, (carryOdd_2_5).2.1, (carryOdd_2_5).2.2⟩
    · exact ⟨some ((1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), none, (carryOdd_2_6).1, (carryOdd_2_6).2.1, (carryOdd_2_6).2.2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, (carryOdd_3_0).1, (carryOdd_3_0).2.1, (carryOdd_3_0).2.2⟩
    · exact ⟨none, none, (carryOdd_3_1).1, (carryOdd_3_1).2.1, (carryOdd_3_1).2.2⟩
    · exact ⟨none, some ((1 : ℂ), ModularGroup.T⁻¹), (carryOdd_3_2).1, (carryOdd_3_2).2.1, (carryOdd_3_2).2.2⟩
    · exact ⟨none, none, (carryOdd_3_3).1, (carryOdd_3_3).2.1, (carryOdd_3_3).2.2⟩
    · exact ⟨none, none, (carryOdd_3_4).1, (carryOdd_3_4).2.1, (carryOdd_3_4).2.2⟩
    · exact ⟨none, none, (carryOdd_3_5).1, (carryOdd_3_5).2.1, (carryOdd_3_5).2.2⟩
    · exact ⟨none, some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)), (carryOdd_3_6).1, (carryOdd_3_6).2.1, (carryOdd_3_6).2.2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, (carryOdd_4_0).1, (carryOdd_4_0).2.1, (carryOdd_4_0).2.2⟩
    · exact ⟨none, some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.S)), (carryOdd_4_1).1, (carryOdd_4_1).2.1, (carryOdd_4_1).2.2⟩
    · exact ⟨none, none, (carryOdd_4_2).1, (carryOdd_4_2).2.1, (carryOdd_4_2).2.2⟩
    · exact ⟨none, some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)), (carryOdd_4_3).1, (carryOdd_4_3).2.1, (carryOdd_4_3).2.2⟩
    · exact ⟨none, none, (carryOdd_4_4).1, (carryOdd_4_4).2.1, (carryOdd_4_4).2.2⟩
    · exact ⟨none, none, (carryOdd_4_5).1, (carryOdd_4_5).2.1, (carryOdd_4_5).2.2⟩
    · exact ⟨none, none, (carryOdd_4_6).1, (carryOdd_4_6).2.1, (carryOdd_4_6).2.2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨none, none, (carryOdd_5_0).1, (carryOdd_5_0).2.1, (carryOdd_5_0).2.2⟩
    · exact ⟨some ((1 : ℂ), (ModularGroup.T⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), none, (carryOdd_5_1).1, (carryOdd_5_1).2.1, (carryOdd_5_1).2.2⟩
    · exact ⟨none, some ((1 : ℂ), ((ModularGroup.T⁻¹ * ModularGroup.S) * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))), (carryOdd_5_2).1, (carryOdd_5_2).2.1, (carryOdd_5_2).2.2⟩
    · exact ⟨some ((1 : ℂ), ((ModularGroup.S * ModularGroup.T) * ModularGroup.S)), none, (carryOdd_5_3).1, (carryOdd_5_3).2.1, (carryOdd_5_3).2.2⟩
    · exact ⟨none, none, (carryOdd_5_4).1, (carryOdd_5_4).2.1, (carryOdd_5_4).2.2⟩
    · exact ⟨none, none, (carryOdd_5_5).1, (carryOdd_5_5).2.1, (carryOdd_5_5).2.2⟩
    · exact ⟨none, some ((1 : ℂ), (ModularGroup.T⁻¹ * ModularGroup.T⁻¹)), (carryOdd_5_6).1, (carryOdd_5_6).2.1, (carryOdd_5_6).2.2⟩

theorem exists_carry_neighborsP_odd {ν : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hν : ν ∈ Work.Asymptotics.NeighborsP) (i : Fin 6) :
    ∃ (a b : Option (ℂ × Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      Work.Asymptotics.CarryOkOdd ν i a b ∧ Work.Asymptotics.SafePairOdd ν i a
        ∧ Work.Asymptotics.SafePairSOdd ν i b := by
  rcases hν with h | h
  · exact exists_carry_pos_odd h i
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h1 | h1 | h1 | h1 | h1 | h1 | h1
    · rw [show ν = -((1 : X)) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos_odd (ν := ((1 : X))) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry_odd ((1 : X)) i a b hc ha hb
      exact ⟨negOpt a, negOpt b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.S) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos_odd (ν := ModularGroup.S) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry_odd ModularGroup.S i a b hc ha hb
      exact ⟨negOpt a, negOpt b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.T) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos_odd (ν := ModularGroup.T) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry_odd ModularGroup.T i a b hc ha hb
      exact ⟨negOpt a, negOpt b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.T⁻¹) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ := exists_carry_pos_odd (ν := ModularGroup.T⁻¹) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry_odd ModularGroup.T⁻¹ i a b hc ha hb
      exact ⟨negOpt a, negOpt b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.T * ModularGroup.S) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ :=
        exists_carry_pos_odd (ν := ModularGroup.T * ModularGroup.S) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry_odd (ModularGroup.T * ModularGroup.S) i a b hc ha hb
      exact ⟨negOpt a, negOpt b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.S * ModularGroup.T⁻¹) from by rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ :=
        exists_carry_pos_odd (ν := ModularGroup.S * ModularGroup.T⁻¹) (by simp) i
      obtain ⟨k1, k2, k3⟩ := neg_carry_odd (ModularGroup.S * ModularGroup.T⁻¹) i a b hc ha hb
      exact ⟨negOpt a, negOpt b, k1, k2, k3⟩
    · rw [show ν = -(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) from by
        rw [← h1, neg_neg]]
      obtain ⟨a, b, hc, ha, hb⟩ :=
        exists_carry_pos_odd (ν := ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) (by simp) i
      obtain ⟨k1, k2, k3⟩ :=
        neg_carry_odd (ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) i a b hc ha hb
      exact ⟨negOpt a, negOpt b, k1, k2, k3⟩

end Work.Asymptotics
