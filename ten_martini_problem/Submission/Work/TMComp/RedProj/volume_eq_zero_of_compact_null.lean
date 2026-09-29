import Mathlib

namespace Work.TMComp.RedProj

/-- If a set of reals meets every compact subinterval `[c,d]` (with
`a < c ≤ d < b`) in measure zero, then it meets the whole open interval
`(a,b)` in measure zero. -/
theorem volume_eq_zero_of_compact_null (s : Set ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ c d : ℝ, a < c → c ≤ d → d < b → MeasureTheory.volume (s ∩ Set.Icc c d) = 0) :
    MeasureTheory.volume (s ∩ Set.Ioo a b) = 0 := by
  have hbda : (0 : ℝ) < b - a := by linarith
  let F : ℕ → Set ℝ :=
    fun n => s ∩ Set.Icc (a + (b - a) / ((n : ℝ) + 2)) (b - (b - a) / ((n : ℝ) + 2))
  have hFnull : ∀ n, MeasureTheory.volume (F n) = 0 := by
    intro n
    have hk : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have htk : (0 : ℝ) < (b - a) / ((n : ℝ) + 2) := div_pos hbda hk
    have hc : a < a + (b - a) / ((n : ℝ) + 2) := by linarith
    have hd : b - (b - a) / ((n : ℝ) + 2) < b := by linarith
    have hcd : a + (b - a) / ((n : ℝ) + 2) ≤ b - (b - a) / ((n : ℝ) + 2) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hk2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith
      have h2 : 2 * ((b - a) / ((n : ℝ) + 2)) ≤ b - a := by
        rw [← mul_div_assoc, div_le_iff₀ hk]
        nlinarith [hbda, hk2]
      linarith
    show MeasureTheory.volume
        (s ∩ Set.Icc (a + (b - a) / ((n : ℝ) + 2)) (b - (b - a) / ((n : ℝ) + 2))) = 0
    exact h _ _ hc hcd hd
  have hcover : s ∩ Set.Ioo a b ⊆ ⋃ n, F n := by
    rintro x ⟨hxs, hx⟩
    rw [Set.mem_Ioo] at hx
    obtain ⟨hax, hxb⟩ := hx
    have hδ : (0 : ℝ) < min (x - a) (b - x) := lt_min (by linarith) (by linarith)
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / min (x - a) (b - x))
    have h' : (b - a) < (N : ℝ) * min (x - a) (b - x) := by
      rwa [div_lt_iff₀ hδ] at hN
    have hNk : (b - a) < ((N : ℝ) + 2) * min (x - a) (b - x) := by
      nlinarith [h', hδ]
    have hlt : (b - a) / ((N : ℝ) + 2) < min (x - a) (b - x) := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 2)]
      nlinarith [hNk]
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    refine ⟨hxs, Set.mem_Icc.2 ⟨?_, ?_⟩⟩
    · have := lt_of_lt_of_le hlt (min_le_left (x - a) (b - x)); linarith
    · have := lt_of_lt_of_le hlt (min_le_right (x - a) (b - x)); linarith
  have hle : MeasureTheory.volume (s ∩ Set.Ioo a b) ≤ 0 :=
    calc MeasureTheory.volume (s ∩ Set.Ioo a b)
        ≤ MeasureTheory.volume (⋃ n, F n) := MeasureTheory.measure_mono hcover
      _ ≤ ∑' n, MeasureTheory.volume (F n) := MeasureTheory.measure_iUnion_le _
      _ = 0 := by simp [hFnull]
  exact le_antisymm hle (by simp)

end Work.TMComp.RedProj
