import Mathlib
import Submission.Work.WilG4a.NoStripDefs
import Submission.Work.WilG4a.UB1_mem

namespace Work.WilG4a

theorem unbAbove1_mem (S : WilkiesDesign.SOMin) (p F : ℕ) :
    ∃ (A c c' : ℕ), ∀ (D : ℕ) (Z : Set (Fin (p + 1) → ℝ)), Z ∈ S.Ω F D (p + 1) →
      Work.WilG4a.unbAbove1 p Z ∈ S.Ω (A + F) (c * D + c') (p + 1) := by
  obtain ⟨A₀, c₀, c₀', hUB⟩ := UB1_mem S p F
  refine ⟨A₀ + 3, c₀, c₀', ?_⟩
  intro D Z hZ
  -- `UB1 p Z` is `Ω`-definable with format `A₀ + F` and degree `c₀ * D + c₀'`.
  have h1 := hUB D Z hZ
  -- The fibre is bounded above iff some `y` is an upper bound: project out `y`,
  have h2 := S.proj h1
  -- then take the complement,
  have h3 := S.compl h2
  -- then reindex `Fin p → ℝ` into `Fin (p+1) → ℝ` by `Fin.init`.
  have h4 := S.prod_right h3
  have hfmt : (A₀ + 3) + F = ((A₀ + F + 1) + 1) + 1 := by omega
  rw [hfmt]
  exact h4

end Work.WilG4a
