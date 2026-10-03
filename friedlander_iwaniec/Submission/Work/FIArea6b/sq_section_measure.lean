import Mathlib

namespace Work.FIArea6b

open MeasureTheory

theorem sq_section_measure {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    (MeasureTheory.volume {x : ℝ | c ≤ x ^ 2 ∧ x ^ 2 ≤ d})
      = ENNReal.ofReal (2 * (Real.sqrt d - Real.sqrt c)) := by
  have hd : 0 ≤ d := le_trans hc hcd
  have hsc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hscd : Real.sqrt c ≤ Real.sqrt d := Real.sqrt_le_sqrt hcd
  -- If `√c ≤ |y| ≤ √d` then `c ≤ y ^ 2 ≤ d`.
  have key : ∀ y : ℝ, Real.sqrt c ≤ |y| → |y| ≤ Real.sqrt d →
      c ≤ y ^ 2 ∧ y ^ 2 ≤ d := by
    intro y hge hle
    constructor
    · calc c = (Real.sqrt c) ^ 2 := (Real.sq_sqrt hc).symm
        _ ≤ |y| ^ 2 := pow_le_pow_left₀ hsc hge 2
        _ = y ^ 2 := sq_abs y
    · calc y ^ 2 = |y| ^ 2 := (sq_abs y).symm
        _ ≤ (Real.sqrt d) ^ 2 := pow_le_pow_left₀ (abs_nonneg y) hle 2
        _ = d := Real.sq_sqrt hd
  have hset : {x : ℝ | c ≤ x ^ 2 ∧ x ^ 2 ≤ d}
      = Set.Icc (-Real.sqrt d) (-Real.sqrt c) ∪ Set.Icc (Real.sqrt c) (Real.sqrt d) := by
    ext x
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := hx
      have hle : |x| ≤ Real.sqrt d := Real.abs_le_sqrt h2
      have hge : Real.sqrt c ≤ |x| := by
        rw [← Real.sqrt_sq_eq_abs x]
        exact (Real.le_sqrt hsc (sq_nonneg x)).2 (by rw [Real.sq_sqrt hc]; exact h1)
      by_cases hx0 : 0 ≤ x
      · right
        exact ⟨by simpa [abs_of_nonneg hx0] using hge,
          by simpa [abs_of_nonneg hx0] using hle⟩
      · left
        have hx0' : x < 0 := lt_of_not_ge hx0
        rw [abs_of_neg hx0'] at hge hle
        exact ⟨by linarith, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have hx0 : x ≤ 0 := le_trans h2 (by linarith)
        refine key x ?_ ?_
        · rw [abs_of_nonpos hx0]; linarith
        · rw [abs_of_nonpos hx0]; linarith
      · have hx0 : 0 ≤ x := le_trans hsc h1
        refine key x ?_ ?_
        · rwa [abs_of_nonneg hx0]
        · rwa [abs_of_nonneg hx0]
  rw [hset]
  have hA : volume (Set.Icc (-Real.sqrt d) (-Real.sqrt c))
      = ENNReal.ofReal (Real.sqrt d - Real.sqrt c) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hB : volume (Set.Icc (Real.sqrt c) (Real.sqrt d))
      = ENNReal.ofReal (Real.sqrt d - Real.sqrt c) :=
    Real.volume_Icc
  have hint : volume (Set.Icc (-Real.sqrt d) (-Real.sqrt c)
      ∩ Set.Icc (Real.sqrt c) (Real.sqrt d)) = 0 := by
    have hsub : Set.Icc (-Real.sqrt d) (-Real.sqrt c) ∩ Set.Icc (Real.sqrt c) (Real.sqrt d)
        ⊆ ({0} : Set ℝ) := by
      intro x hx
      obtain ⟨⟨-, h2a⟩, ⟨h1b, -⟩⟩ := hx
      have hsqrt : Real.sqrt c = 0 := le_antisymm (by linarith) hsc
      simp only [Set.mem_singleton_iff]
      linarith
    exact le_bot_iff.mp (le_trans (measure_mono hsub) (le_of_eq Real.volume_singleton))
  have hunion : volume (Set.Icc (-Real.sqrt d) (-Real.sqrt c) ∪ Set.Icc (Real.sqrt c) (Real.sqrt d))
      = volume (Set.Icc (-Real.sqrt d) (-Real.sqrt c))
        + volume (Set.Icc (Real.sqrt c) (Real.sqrt d)) := by
    have h := measure_union_add_inter (μ := volume) (Set.Icc (-Real.sqrt d) (-Real.sqrt c))
      (measurableSet_Icc (a := Real.sqrt c) (b := Real.sqrt d))
    rw [hint, add_zero] at h
    exact h
  rw [hunion, hA, hB]
  have hs : 0 ≤ Real.sqrt d - Real.sqrt c := sub_nonneg.2 hscd
  rw [two_mul, ENNReal.ofReal_add hs hs]

end Work.FIArea6b
