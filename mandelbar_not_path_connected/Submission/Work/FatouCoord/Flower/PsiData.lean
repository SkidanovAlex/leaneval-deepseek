/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Flower.entire_repelling
import Submission.Work.FatouCoord.Petal.repelling_coord

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The entire repelling coordinate and the chart conjugacy

Given a chart conjugacy `V` on a left half-plane `{Re w < -R}` (`V (w+1) = wMap f (V w)`,
`V w ≈ w`), we extend it to an `rV f V R : ℂ → ℂ` by the standard representative trick, and
record that the entire repelling coordinate `Ψ = rΨ f Ψ₀ R` (with `Ψ₀ w = -1/V w` on the half
plane) satisfies `Ψ w = -1 / rV f V R w` for **every** `w`.  This identity is what transfers the
estimates for `V` to `Ψ`.
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.FatouCoord.Flower

open Work.FatouCoord

noncomputable section

variable {f V Ψ₀ : ℂ → ℂ} {R : ℝ} {w : ℂ}

theorem iterate_neg_one_div (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    f^[n] (-1 / z) = -1 / ((wMap f)^[n] z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      congr 1
      rw [wMap_apply]
      by_cases h : f (-1 / z) = 0
      · simp [h]
      · field_simp

/-- The chart conjugacy `V`, extended to all of `ℂ` by the standard representative trick. -/
def rV (f V : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  (wMap f)^[EntireRepelling.rIdx R w] (V (w - ((EntireRepelling.rIdx R w : ℕ) : ℂ)))

theorem rV_defeq (f V : ℂ → ℂ) (R : ℝ) (w : ℂ) :
    rV f V R w = EntireRepelling.rΨ (wMap f) V R w := rfl

theorem rV_eq_of_re_lt (hVshift : ∀ u : ℂ, u.re < -R → V (u+1) = wMap f (V u))
    (hw : w.re < -R) : rV f V R w = V w := by
  rw [rV_defeq, EntireRepelling.rΨ_eq_Ψ₀ hVshift hw]

theorem rV_shift (hVshift : ∀ u : ℂ, u.re < -R → V (u+1) = wMap f (V u)) :
    rV f V R (w+1) = wMap f (rV f V R w) :=
  EntireRepelling.rΨ_shift (F := wMap f) (Ψ₀ := V) (R := R) hVshift

/-- The entire repelling coordinate is `-1` over the extended conjugacy. -/
theorem rΨ_eq_neg_inv_rV (hVshift : ∀ u : ℂ, u.re < -R → V (u+1) = wMap f (V u))
    (hΨ₀ : ∀ u : ℂ, u.re < -R → Ψ₀ u = -1 / V u) :
    ∀ w : ℂ, EntireRepelling.rΨ f Ψ₀ R w = -1 / rV f V R w := by
  intro w
  have hn : (w - ((EntireRepelling.rIdx R w : ℕ) : ℂ)).re < -R := EntireRepelling.rIdx_spec R w
  show EntireRepelling.rA f Ψ₀ R w (EntireRepelling.rIdx R w) = _
  simp only [EntireRepelling.rA, rV]
  rw [hΨ₀ _ hn, iterate_neg_one_div]

end

end Work.FatouCoord.Flower
