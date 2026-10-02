/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — `Int.fract (· - α₁)` is injective on `[0,1)`

The arithmetic fact used by item `angleMono` (step `L9` of `NOTES_LEAD_mandelbar_rn0.md` §2):
two distinct angles of `[0,1)` have distinct `α₁`-shifted fractional parts.  It is the
justification of the strictness of the angle ordering `wₙ < wₙ₊₁`.
-/
import Mathlib
import Submission.Work.SeedSimple2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedSimple2.Mono

/-- Two *distinct* angles of `[0,1)` have distinct `α₁`-shifted fractional parts. -/
theorem fract_sub_alpha1_ne {a e : ℝ} (ha : a ∈ Set.Ico 0 1) (he : e ∈ Set.Ico 0 1)
    (hae : a ≠ e) : Int.fract (e - Work.EL.alpha1) ≠ Int.fract (a - Work.EL.alpha1) := by
  intro h
  have h1 : (e - Work.EL.alpha1) - Int.fract (a - Work.EL.alpha1)
      = (⌊e - Work.EL.alpha1⌋ : ℝ) := by
    have := Int.floor_add_fract (e - Work.EL.alpha1)
    rw [h] at this
    linarith
  have h2 : (a - Work.EL.alpha1) - Int.fract (a - Work.EL.alpha1)
      = (⌊a - Work.EL.alpha1⌋ : ℝ) := by
    have := Int.floor_add_fract (a - Work.EL.alpha1); linarith
  have h3 : (e - a : ℝ) = ((⌊e - Work.EL.alpha1⌋ - ⌊a - Work.EL.alpha1⌋ : ℤ) : ℝ) := by
    push_cast; linarith
  have habs : |(e - a : ℝ)| < 1 := by
    rw [abs_lt]; constructor <;> linarith [ha.1, ha.2, he.1, he.2]
  have h4 : |((⌊e - Work.EL.alpha1⌋ - ⌊a - Work.EL.alpha1⌋ : ℤ) : ℝ)| < 1 := by
    rw [← h3]; exact habs
  rw [abs_lt] at h4
  have h5 : (⌊e - Work.EL.alpha1⌋ - ⌊a - Work.EL.alpha1⌋ : ℤ) = 0 := by
    have h1' : (-1 : ℤ) < ⌊e - Work.EL.alpha1⌋ - ⌊a - Work.EL.alpha1⌋ := by exact_mod_cast h4.1
    have h2' : (⌊e - Work.EL.alpha1⌋ - ⌊a - Work.EL.alpha1⌋ : ℤ) < 1 := by exact_mod_cast h4.2
    omega
  have h6 : e - a = 0 := by rw [h3, h5]; norm_num
  exact hae (by linarith)

end Work.SeedSimple2.Mono
