import Mathlib
import Submission.Work.ELNest.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE.Nest

theorem exists_nest_level_window {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n < δ ∧
      (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ n < δ := by
  have hA : 0 < Work.ELNest.alpha1 - Work.ELNest.beta0 := by
    unfold Work.ELNest.alpha1 Work.ELNest.beta0; norm_num
  have hB : 0 < Work.ELNest.beta0' - Work.ELNest.alpha2 := by
    unfold Work.ELNest.beta0' Work.ELNest.alpha2; norm_num
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (max (Work.ELNest.alpha1 - Work.ELNest.beta0)
      (Work.ELNest.beta0' - Work.ELNest.alpha2) / δ)
    (by norm_num : (1 : ℝ) < 1024)
  refine ⟨n, ?_, ?_⟩
  · have hpos : (0 : ℝ) < (1024 : ℝ) ^ n := pow_pos (by norm_num) n
    have hC : max (Work.ELNest.alpha1 - Work.ELNest.beta0)
        (Work.ELNest.beta0' - Work.ELNest.alpha2) < δ * (1024 : ℝ) ^ n := by
      have h := (div_lt_iff₀ hδ).mp hn
      rw [mul_comm]; exact h
    rw [div_lt_iff₀ hpos]
    have hAC : Work.ELNest.alpha1 - Work.ELNest.beta0 ≤
        max (Work.ELNest.alpha1 - Work.ELNest.beta0)
          (Work.ELNest.beta0' - Work.ELNest.alpha2) := le_max_left _ _
    linarith
  · have hpos : (0 : ℝ) < (1024 : ℝ) ^ n := pow_pos (by norm_num) n
    have hC : max (Work.ELNest.alpha1 - Work.ELNest.beta0)
        (Work.ELNest.beta0' - Work.ELNest.alpha2) < δ * (1024 : ℝ) ^ n := by
      have h := (div_lt_iff₀ hδ).mp hn
      rw [mul_comm]; exact h
    rw [div_lt_iff₀ hpos]
    have hBC : Work.ELNest.beta0' - Work.ELNest.alpha2 ≤
        max (Work.ELNest.alpha1 - Work.ELNest.beta0)
          (Work.ELNest.beta0' - Work.ELNest.alpha2) := le_max_right _ _
    linarith

end Work.GATE.Nest
