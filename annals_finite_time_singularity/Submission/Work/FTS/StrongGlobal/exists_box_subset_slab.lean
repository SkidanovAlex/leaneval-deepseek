import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

/-- **A small cube around an interior point of a slab is contained in the slab.**

`slab a b = (0,∞) × (0,π/2) × (a,b)` is open, so at any point `(z,θ,τ₀)` with `z > 0`,
`0 < θ < π/2` and `a < τ₀ < b` there is a genuine cube `Ioo (z-ε) (z+ε) ×ˢ Ioo (θ-ε) (θ+ε) ×ˢ
Ioo (τ₀-ε) (τ₀+ε)` (with the *same* radius `ε` in all three coordinates, as the consumers of the
joint `C¹`-clause need) contained in the slab. -/
theorem exists_box_subset_slab {z θ τ₀ a b : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) (ha : a < τ₀) (hb : τ₀ < b) :
    ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (z - ε) (z + ε) ×ˢ Set.Ioo (θ - ε) (θ + ε) ×ˢ
      Set.Ioo (τ₀ - ε) (τ₀ + ε) ⊆ Work.FTS.StrongGlobal.slab a b := by
  -- the margins to the five "walls" of the slab
  have hπ : 0 < Real.pi / 2 - θ := by linarith
  have ha' : 0 < τ₀ - a := by linarith
  have hb' : 0 < b - τ₀ := by linarith
  set m : ℝ := min (min z θ) (min (Real.pi / 2 - θ) (min (τ₀ - a) (b - τ₀))) with hm
  have hmz : m ≤ z := by
    rw [hm]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hmθ : m ≤ θ := by
    rw [hm]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hmπ : m ≤ Real.pi / 2 - θ := by
    rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hma : m ≤ τ₀ - a := by
    rw [hm]
    exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _)
  have hmb : m ≤ b - τ₀ := by
    rw [hm]
    exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_right _ _)
  have hmpos : 0 < m := by
    rw [hm]
    exact lt_min (lt_min hz hθ0) (lt_min hπ (lt_min ha' hb'))
  refine ⟨m / 2, by linarith, ?_⟩
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  rw [Set.mem_Ioo] at h1 h2 h3
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  obtain ⟨h3a, h3b⟩ := h3
  refine mem_slab.mpr ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

end Work.FTS.StrongGlobal
