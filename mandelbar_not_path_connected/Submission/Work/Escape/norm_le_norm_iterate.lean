import Mathlib
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Escape

/-- One step of the monotonicity of the norm along the orbit, valid as soon as the orbit stays
outside the closed disk of radius `max 2 A`: the norm does not decrease, and the point stays
outside that disk.  This is the single-step form of `norm_le_norm_iterate`. -/
theorem norm_le_norm_step (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d)
    {z : ℂ} (hz : max 2 A ≤ ‖z‖) : ‖z‖ ≤ ‖f z‖ ∧ max 2 A ≤ ‖f z‖ := by
  have h2 : (2 : ℝ) ≤ ‖z‖ := (le_max_left _ _).trans hz
  have hA : A ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hz1 : (1 : ℝ) ≤ ‖z‖ := by linarith
  have hpow : ‖z‖ ^ 2 ≤ ‖z‖ ^ d := pow_le_pow_right₀ hz1 hd
  have hge : ‖z‖ ≤ ‖z‖ ^ d - A := by
    nlinarith [norm_nonneg z, h2, hA, hpow]
  exact ⟨le_trans hge (h.le_norm z), le_trans hz (le_trans hge (h.le_norm z))⟩

theorem norm_le_norm_iterate (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d)
    {z : ℂ} (hz : z ∈ escapeRegion A) (n : ℕ) : ‖z‖ ≤ ‖(f^[n]) z‖ := by
  have hz' : max 2 A ≤ ‖z‖ := le_of_lt hz
  have key : ∀ n : ℕ, ‖z‖ ≤ ‖(f^[n]) z‖ ∧ max 2 A ≤ ‖(f^[n]) z‖ := by
    intro n
    induction n with
    | zero => rw [Function.iterate_zero_apply]; exact ⟨le_refl ‖z‖, hz'⟩
    | succ n ih =>
        obtain ⟨hle, hmax⟩ := ih
        rw [Function.iterate_succ_apply']
        exact ⟨le_trans hle (norm_le_norm_step f d A h hd hmax).1,
          (norm_le_norm_step f d A h hd hmax).2⟩
  exact (key n).1

end Work.Escape
