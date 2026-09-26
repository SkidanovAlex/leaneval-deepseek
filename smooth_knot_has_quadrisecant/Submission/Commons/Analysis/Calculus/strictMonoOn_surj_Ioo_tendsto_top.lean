import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Calculus

theorem strictMonoOn_surj_Ioo_tendsto_top {s u : ℝ} {f : ℝ → ℝ} (hs : s < 1)
    (hmono : StrictMonoOn f (Set.Ioo s 1))
    (hsurj : f '' Set.Ioo s 1 = Set.Ioo 0 u) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, x ∈ Set.Ioo s 1 → 1 - δ < x → u - ε < f x := by
  intro ε hε
  -- The domain (s,1) is nonempty (its midpoint lies in it), so the image
  -- interval (0,u) is nonempty; in particular 0 < u.
  have hm : (s + 1) / 2 ∈ Set.Ioo s 1 := by
    constructor <;> linarith
  have hfm : f ((s + 1) / 2) ∈ Set.Ioo (0 : ℝ) u := by
    rw [← hsurj]
    exact Set.mem_image_of_mem f hm
  have hu : 0 < u := lt_trans hfm.1 hfm.2
  -- Pick y strictly between max 0 (u - ε) and u; then 0 < y and u - ε < y.
  have hmaxu : max (0 : ℝ) (u - ε) < u := by
    exact max_lt hu (by linarith)
  rcases exists_between hmaxu with ⟨y, hmaxy, hyu⟩
  have hy0 : 0 < y := lt_of_le_of_lt (le_max_left (0 : ℝ) (u - ε)) hmaxy
  have hyε : u - ε < y := lt_of_le_of_lt (le_max_right (0 : ℝ) (u - ε)) hmaxy
  -- y is attained: y = f x0 for some x0 ∈ (s,1).
  have hymem : y ∈ f '' Set.Ioo s 1 := by
    rw [hsurj]
    exact ⟨hy0, hyu⟩
  rcases hymem with ⟨x0, hx0, hfx0⟩
  -- δ = 1 - x0 > 0 works: points to its right have f x > y > u - ε.
  refine ⟨1 - x0, ?_, ?_⟩
  · linarith [hx0.2]
  · intro x hx hgt
    have hx0x : x0 < x := by linarith
    have hfx : f x0 < f x := hmono hx0 hx hx0x
    have hyfx : y < f x := by
      simpa [hfx0] using hfx
    exact lt_trans hyε hyfx

end Commons.Analysis.Calculus