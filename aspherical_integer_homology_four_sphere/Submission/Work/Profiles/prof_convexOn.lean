/-
Copyright: area `Profiles` of the aspherical 4-manifold project.

# Convexity of the smoothing `prof F η`

The smoothing `prof F η x = ∫ t, F (x - t) η t` of a model function `F` against a
nonnegative bump `η` is convex whenever `F` is convex and continuous and `η` is
nonnegative, continuous and compactly supported.  This is the pointwise convexity
inequality for `F` integrated against the nonnegative kernel `η`:

`F (a (x - t) + b (y - t)) ≤ a F (x - t) + b F (y - t)`,  `a, b ≥ 0`, `a + b = 1`.
-/
import Mathlib
import Submission.Work.Profiles.Basic
import Submission.Work.Profiles.Eta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory
open scoped ContDiff

namespace Work.Profiles

theorem prof_convexOn {F η : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) (hFc : Continuous F)
    (hη : ∀ t, 0 ≤ η t) (hηcont : Continuous η) (hηc : HasCompactSupport η) :
    ConvexOn ℝ Set.univ (prof F η) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- Integrability of `t ↦ F (c - t) * η t` for every `c`, from continuity and compact support.
  have hInt : ∀ c : ℝ, Integrable (fun t : ℝ => F (c - t) * η t) volume := by
    intro c
    have hcont : Continuous fun t : ℝ => F (c - t) * η t :=
      (hFc.comp (continuous_const.sub continuous_id)).mul hηcont
    exact hcont.integrable_of_hasCompactSupport (hηc.mul_left)
  -- Linearity of the integral in the combination of the two shifted integrands.
  have hA : ∫ t, a * (F (x - t) * η t) = a * ∫ t, F (x - t) * η t := integral_const_mul a _
  have hB : ∫ t, b * (F (y - t) * η t) = b * ∫ t, F (y - t) * η t := integral_const_mul b _
  have heq : (fun t : ℝ => (a * F (x - t) + b * F (y - t)) * η t)
      = fun t => a * (F (x - t) * η t) + b * (F (y - t) * η t) := by
    funext t; ring
  -- The integral of the pointwise convexity inequality.
  have h2 : ∫ t, (a * F (x - t) + b * F (y - t)) * η t
      = a • prof F η x + b • prof F η y := by
    rw [heq, integral_add ((hInt x).const_mul a) ((hInt y).const_mul b), hA, hB]
    simp only [prof, smul_eq_mul]
  -- `a • x + b • y - t = a • (x - t) + b • (y - t)`.
  have hkey : ∀ t : ℝ, a • x + b • y - t = a • (x - t) + b • (y - t) := by
    intro t
    simp only [smul_eq_mul]
    have h : a * (x - t) + b * (y - t) = a * x + b * y - t := by
      rw [show a * (x - t) + b * (y - t) = a * x + b * y - (a + b) * t by ring, hab]
      ring
    exact h.symm
  -- Pointwise convexity inequality, multiplied by the nonnegative weight `η t`.
  have hpt : ∀ t : ℝ, F (a • x + b • y - t) * η t
      ≤ (a * F (x - t) + b * F (y - t)) * η t := by
    intro t
    rw [hkey t]
    have hconv := hF.2 (Set.mem_univ (x - t)) (Set.mem_univ (y - t)) ha hb hab
    have hconv' : F (a • (x - t) + b • (y - t)) ≤ a * F (x - t) + b * F (y - t) := by
      simpa only [smul_eq_mul] using hconv
    exact mul_le_mul_of_nonneg_right hconv' (hη t)
  have hL : Integrable (fun t : ℝ => F (a • x + b • y - t) * η t) volume := hInt (a • x + b • y)
  have hR : Integrable (fun t : ℝ => (a * F (x - t) + b * F (y - t)) * η t) volume := by
    rw [heq]
    exact ((hInt x).const_mul a).add ((hInt y).const_mul b)
  have h1 : prof F η (a • x + b • y) ≤ ∫ t, (a * F (x - t) + b * F (y - t)) * η t := by
    simp only [prof]
    exact integral_mono hL hR (fun t => hpt t)
  exact h1.trans h2.le

end Work.Profiles
