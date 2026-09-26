import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Calculus

theorem strictMonoOn_surj_Ioo_tendsto_right {s u : ℝ} {f : ℝ → ℝ} (hu : 0 < u)
    (hmono : StrictMonoOn f (Set.Ioo 0 u))
    (hsurj : f '' Set.Ioo 0 u = Set.Ioo s 1) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, x ∈ Set.Ioo 0 u → u - δ < x → 1 - ε < f x := by
  intro ε hε
  -- The domain (0,u) is nonempty (u/2 ∈ (0,u)), so the image interval (s,1)
  -- is nonempty, in particular s < 1.
  have hu2 : u / 2 ∈ Set.Ioo (0 : ℝ) u := by
    constructor <;> linarith
  have hfs : f (u / 2) ∈ Set.Ioo s 1 := by
    rw [← hsurj]
    exact Set.mem_image_of_mem f hu2
  have hs1 : s < 1 := lt_trans hfs.1 hfs.2
  -- Pick y strictly between max s (1 - ε) and 1; then y > 1 - ε and y > s.
  have hmax1 : max s (1 - ε) < 1 := by
    exact max_lt hs1 (by linarith)
  rcases exists_between hmax1 with ⟨y, hmy, hy1⟩
  have hys : s < y := lt_of_le_of_lt (le_max_left s (1 - ε)) hmy
  have hyε : 1 - ε < y := lt_of_le_of_lt (le_max_right s (1 - ε)) hmy
  -- y is attained: y = f x0 for some x0 ∈ (0,u).
  have hymem : y ∈ f '' Set.Ioo (0 : ℝ) u := by
    rw [hsurj]
    exact ⟨hys, hy1⟩
  rcases hymem with ⟨x0, hx0, hfx0⟩
  -- δ = u - x0 > 0 works: points to its right have f x > y > 1 - ε.
  refine ⟨u - x0, ?_, ?_⟩
  · linarith [hx0.2]
  · intro x hx hgt
    have hx0x : x0 < x := by linarith
    have hfx : f x0 < f x := hmono hx0 hx hx0x
    have hyfx : y < f x := by
      simpa [hfx0] using hfx
    exact lt_trans hyε hyfx

end Commons.Analysis.Calculus