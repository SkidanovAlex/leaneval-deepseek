import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.flatPieceRTList_factor
import Submission.Work.BoseFixB1.flatPiece_eigen
import Submission.Work.BoseFixB1.tFold_eigen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem flatPieceRT_eigen {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (S T : Finset (Fin N)) (hST : Disjoint S T) (i : Fin N) :
    (Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.flatPieceRT V A S T Φ)
        = if i ∈ S then Work.BoseFixB1.flatPieceRT V A S T Φ else 0)
    ∧ (Work.UBBInputs8.boxQInd V A i (Work.BoseFixB1.flatPieceRT V A S T Φ)
        = if i ∈ T then Work.BoseFixB1.flatPieceRT V A S T Φ else 0)
    ∧ (Work.BoseFixB1.rInd A i (Work.BoseFixB1.flatPieceRT V A S T Φ)
        = if i ∈ S ∨ i ∈ T then 0 else Work.BoseFixB1.flatPieceRT V A S T Φ) := by
  -- the eigen-data of the mean fold
  have heig := tFold_eigen hℓ hV hA hVeq hAc hST (List.finRange N) (List.nodup_finRange N) hΦc
  -- the factorisation of the piece
  have hfact := flatPieceRTList_factor V A S T (List.finRange N) (List.nodup_finRange N) Φ
  set G : Submission.BoseGases.X N → ℝ := tFold V A S T (List.finRange N) Φ with hGdef
  set Cp : Submission.BoseGases.X N → ℝ := cFold A S T (eraseSlot (List.finRange N) i)
    with hCpdef
  have hfac : flatPieceRT V A S T Φ = cFold A S T (List.finRange N) * G := by
    rw [hGdef]
    exact hfact
  -- the extraction of the slot factor at `i`
  have hsplit : cFold A S T (List.finRange N) = cOf A S T i * Cp := by
    rw [hCpdef]
    funext y
    exact cFold_eq_cOf_mul_eraseSlot A S T (List.finRange N) i (List.mem_finRange i) y
  have hinv : ∀ y z, Cp (Function.update y i z) = Cp y := by
    intro y z
    rw [hCpdef]
    exact cFold_invariant A S T (eraseSlot (List.finRange N) i) (not_mem_eraseSlot _ i) y z
  have hΘ : flatPieceRT V A S T Φ = cOf A S T i * (Cp * G) := by
    rw [hfac, hsplit, mul_assoc]
  have hGS : i ∈ S → Work.BoseFixB1S.oneMean V A i G = G := by
    intro hS
    rw [hGdef]
    exact heig.2.1 i (List.mem_finRange i) hS
  have hGT : i ∈ T → Work.BoseFixB1S.oneMean V A i G = 0 := by
    intro hT
    rw [hGdef]
    exact heig.2.2 i (List.mem_finRange i) hT
  -- the slot mean of the piece, on the whole configuration space
  have hM : Work.BoseFixB1S.oneMean V A i (flatPieceRT V A S T Φ)
      = if i ∈ S ∪ T then Cp * Work.BoseFixB1S.oneMean V A i G else 0 := by
    rw [hfac, hsplit, mul_assoc]
    by_cases h : i ∈ S ∪ T
    · rw [if_pos h, cOf_of_mem h]
      exact oneMean_indSlot_mul_invariant hA i hinv G
    · rw [if_neg h, cOf_of_notMem h]
      exact oneMean_one_sub_indSlot_mul_invariant hA i hinv G
  refine ⟨?_, ?_, ?_⟩
  · -- `Pᵢ Θ = [i ∈ S]·Θ`
    rw [boxPInd_eq_fun, hM]
    by_cases hS : i ∈ S
    · rw [if_pos (Finset.mem_union_left T hS), if_pos hS, hGS hS, hΘ,
        cOf_of_mem (Finset.mem_union_left T hS)]
    · rw [if_neg hS]
      by_cases hT : i ∈ T
      · rw [if_pos (Finset.mem_union_right S hT), hGT hT]
        funext x
        simp only [Pi.mul_apply, Pi.zero_apply, indSlot_apply]
        ring
      · rw [if_neg (by simp [hS, hT])]
        funext x
        simp only [Pi.mul_apply, Pi.zero_apply, indSlot_apply]
        ring

  · -- `Qᵢ Θ = [i ∈ T]·Θ`
    rw [boxQInd_eq_fun, boxPInd_eq_fun, hM]
    by_cases hT : i ∈ T
    · rw [if_pos hT, if_pos (Finset.mem_union_right S hT), hGT hT, hΘ,
        cOf_of_mem (Finset.mem_union_right S hT)]
      funext x
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, Pi.one_apply, indSlot_apply]
      have hidem := Work.BoseFixB1S.Aind_mul_self A (x i)
      linear_combination (Cp x * G x) * hidem
    · rw [if_neg hT]
      by_cases hS : i ∈ S
      · rw [if_pos (Finset.mem_union_left T hS), hGS hS, hΘ,
          cOf_of_mem (Finset.mem_union_left T hS)]
        funext x
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, Pi.one_apply, indSlot_apply]
        have hidem := Work.BoseFixB1S.Aind_mul_self A (x i)
        linear_combination (Cp x * G x) * hidem
      · rw [if_neg (by simp [hS, hT]), hΘ, cOf_of_notMem (by simp [hS, hT])]
        funext x
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, Pi.one_apply, indSlot_apply]
        have hidem := Work.BoseFixB1S.Aind_mul_self A (x i)
        linear_combination (-(Cp x * G x)) * hidem

  · -- `Rᵢ Θ = [i ∈ S ∨ i ∈ T]·0`
    rw [rInd_eq_fun]
    by_cases h : i ∈ S ∨ i ∈ T
    · rw [if_pos h, hΘ, cOf_of_mem (Finset.mem_union.mpr h)]
      funext x
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, Pi.one_apply, indSlot_apply]
      have hidem := Work.BoseFixB1S.Aind_mul_self A (x i)
      linear_combination (-(Cp x * G x)) * hidem
    · rw [if_neg h, hΘ, cOf_of_notMem (by simpa [Finset.mem_union] using h)]
      funext x
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, Pi.one_apply, indSlot_apply]
      have hidem := Work.BoseFixB1S.Aind_mul_self A (x i)
      linear_combination (Cp x * G x) * hidem

end Work.BoseFixB1
