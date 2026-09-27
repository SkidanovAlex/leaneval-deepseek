import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open MeasureTheory
open scoped ENNReal

/-- Finite subadditivity of `vol`: the measure of a finite union is at most the sum of the
measures, whenever each piece has finite measure. -/
private theorem vol_iUnion_fin_le {n : ℕ} (f : Fin n → Set ℝ) (h : ∀ i, volume (f i) ≠ ⊤) :
    vol (⋃ i, f i) ≤ ∑ i, vol (f i) := by
  have hsum : (∑ i : Fin n, volume (f i)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i _
    exact h i
  calc vol (⋃ i, f i) = (volume (⋃ i, f i)).toReal := rfl
    _ ≤ (∑ i : Fin n, volume (f i)).toReal := by
        refine ENNReal.toReal_mono hsum ?_
        have hb := measure_biUnion_finset_le (μ := (volume : Measure ℝ))
          (Finset.univ : Finset (Fin n)) f
        simpa using hb
    _ = ∑ i : Fin n, vol (f i) := ENNReal.toReal_sum (fun i _ => h i)

/-- Pigeonhole (EKL Step 8): if each of eight measurable sets `P i` covers all but `9εT` of
the interval `[0,T]`, and `72ε < 1`, then the eight sets have a common point in `[0,T]`.

Indeed each complement `[0,T] \ (P i ∩ [0,T])` has `vol` at most `9εT`, their union is all
of `[0,T]` when the sets have no common point, and `8 · 9εT = 72εT < T`. -/
theorem step8_nonempty {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) (hε7 : 72 * ε < 1)
    {P : Fin 8 → Set ℝ} (hPm : ∀ i, MeasurableSet (P i))
    (hP : ∀ i, (1 - 9 * ε) * T ≤ vol (P i ∩ Set.Icc 0 T)) :
    ∃ τ ∈ Set.Icc 0 T, ∀ i : Fin 8, τ ∈ P i := by
  by_contra hcon
  -- no point of `[0,T]` lies in all the `P i`
  have hcon' : ∀ τ, τ ∈ Set.Icc 0 T → ∃ i : Fin 8, τ ∉ P i := by
    intro τ hτ
    by_contra h
    simp only [not_exists, not_not] at h
    exact hcon ⟨τ, hτ, h⟩
  have hAfin : volume (Set.Icc 0 T) ≠ ⊤ := volume_ne_top_of_subset_Icc subset_rfl
  -- measure of each complement slice
  have hEi : ∀ i : Fin 8,
      vol (Set.Icc 0 T \ (P i ∩ Set.Icc 0 T)) = T - vol (P i ∩ Set.Icc 0 T) := by
    intro i
    rw [vol_sdiff Set.inter_subset_right ((hPm i).inter measurableSet_Icc) hAfin,
        vol_Icc (le_of_lt hT)]
    ring
  have hEbound : ∀ i : Fin 8, vol (Set.Icc 0 T \ (P i ∩ Set.Icc 0 T)) ≤ 9 * ε * T := by
    intro i
    rw [hEi i]
    linarith [hP i]
  -- the complement slices cover `[0,T]`
  have hunion : Set.Icc 0 T = ⋃ i : Fin 8, (Set.Icc 0 T \ (P i ∩ Set.Icc 0 T)) := by
    ext τ; constructor
    · intro hτ
      obtain ⟨i, hi⟩ := hcon' τ hτ
      exact Set.mem_iUnion.mpr ⟨i, ⟨hτ, fun hq => hi hq.1⟩⟩
    · intro hτ
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hτ
      exact hi.1
  have hbound : vol (⋃ i : Fin 8, (Set.Icc 0 T \ (P i ∩ Set.Icc 0 T))) ≤ 72 * ε * T := by
    calc vol (⋃ i : Fin 8, (Set.Icc 0 T \ (P i ∩ Set.Icc 0 T)))
        ≤ ∑ i : Fin 8, vol (Set.Icc 0 T \ (P i ∩ Set.Icc 0 T)) := by
          refine vol_iUnion_fin_le _ ?_
          intro i
          exact volume_ne_top_of_subset_Icc Set.sdiff_subset
        _ ≤ ∑ i : Fin 8, (9 * ε * T) := Finset.sum_le_sum (fun i _ => hEbound i)
        _ = 72 * ε * T := by simp [Finset.sum_const, Finset.card_univ]; ring
  have h1 : vol (Set.Icc 0 T) ≤ 72 * ε * T := by rw [hunion]; exact hbound
  have h2 : vol (Set.Icc 0 T) = T := by rw [vol_Icc (le_of_lt hT)]; ring
  have h3 : (72 * ε) * T < T := by
    have h := mul_lt_mul_of_pos_right hε7 hT
    linarith
  linarith [h1, h2, h3]

end Work.EKLC8Core
