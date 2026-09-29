import Mathlib

namespace Work.TMComp.RedProj

theorem exists_pos_forall_lt {f : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ m : ℕ, 1 ≤ m → m < N → 0 < f m) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m → m < N → c ≤ f m := by
  by_cases hN : N ≤ 1
  · refine ⟨1, one_pos, ?_⟩
    intro m hm1 hmN
    exfalso
    omega
  · have hN1 : 1 < N := not_le.mp hN
    let s : Finset ℕ := (Finset.range N).filter (fun m => 1 ≤ m)
    have hs : s.Nonempty := by
      refine ⟨1, ?_⟩
      simp only [s, Finset.mem_filter, Finset.mem_range]
      omega
    refine ⟨s.inf' hs f, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro i hi
      simp only [s, Finset.mem_filter, Finset.mem_range] at hi
      exact hpos i hi.2 hi.1
    · intro m hm1 hmN
      exact Finset.inf'_le f (by
        simp only [s, Finset.mem_filter, Finset.mem_range]
        exact ⟨hmN, hm1⟩)

end Work.TMComp.RedProj
