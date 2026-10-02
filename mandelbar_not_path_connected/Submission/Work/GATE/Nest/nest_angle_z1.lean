import Mathlib
import Submission.Work.GATE.Defs
import Submission.Work.GATE.Nest.nest_angle_window
import Submission.Work.ELNest.bAng_range
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A1 with the `z₁`-nest angles: `nest_angle_z1`

The nest-angle lemma `Work.GATE.Nest.nest_angle_window` (A1 in the `δ`-window form of §2.2 of
the residuals note) applied to the *certificate's* angle data: the level-`n` pair of the `z₁`-nest
has angles `βₙ = bAng n = α₁ − (α₁ − β₀)/1024ⁿ` and `βₙ' = bAng' n = α₂ + (β₀' − α₂)/1024ⁿ`
(`Work.ELNest`), so

* `α₁ − δ < βₙ` is *exactly* the hypothesis `(α₁ − β₀)/1024ⁿ < δ` (because
  `α₁ − βₙ = (α₁ − β₀)/1024ⁿ`), and
* `βₙ' < α₂ + δ` is *exactly* the hypothesis `(β₀' − α₂)/1024ⁿ < δ` (because
  `βₙ' − α₂ = (β₀' − α₂)/1024ⁿ`),

while the remaining sharp bounds `0 < βₙ`, `βₙ < α₁`, `α₂ < βₙ'`, `βₙ' < 1` and `α₁ < α₂` are
supplied by `Work.ELNest.bAng_range` and the angle arithmetic.
-/

namespace Work.GATE.Nest

theorem nest_angle_z1 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P0 Q : Work.EL.CoPair hN) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hP0a : P0.a = Work.EL.alpha1) (hP0b : P0.b = Work.EL.alpha2)
    (hQa : Q.a = Work.ELNest.bAng' n) (hQb : Q.b = Work.ELNest.bAng n + 1)
    (hPs : Work.EL.PairSides hN P0) (hQs : Work.EL.PairSides hN Q)
    (hcover : ∀ z ∉ Work.EL.K c, ∃ ϑ : ℝ, z ∈ Work.EL.paramRay hN ϑ)
    {z : ℂ} (hzK : z ∉ Work.EL.K c)
    (hzP : z ∈ Work.EL.pairSideNear P0) (hzQ : z ∈ Work.EL.pairSideNear Q)
    (hn1 : (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n < δ)
    (hn2 : (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ n < δ) :
    ∃ ϑ : ℝ, z ∈ Work.EL.paramRay hN ϑ ∧
      ((Work.EL.alpha1 - δ < ϑ ∧ ϑ ≤ Work.EL.alpha1) ∨
        (Work.EL.alpha2 ≤ ϑ ∧ ϑ < Work.EL.alpha2 + δ)) := by
  have hα1 : Work.EL.alpha1 = Work.ELNest.alpha1 := rfl
  have hα2 : Work.EL.alpha2 = Work.ELNest.alpha2 := rfl
  have h12 : Work.EL.alpha1 < Work.EL.alpha2 := by
    rw [hα1, hα2]
    norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  have hβ : 0 < Work.ELNest.bAng n := Work.ELNest.bAng_pos n
  have hβ₁ : Work.ELNest.bAng n < Work.EL.alpha1 := by
    rw [hα1]; exact (Work.ELNest.bAng_range n).1.2
  have h₂β' : Work.EL.alpha2 < Work.ELNest.bAng' n := by
    rw [hα2]; exact (Work.ELNest.bAng_range n).2.1
  have hβ'1 : Work.ELNest.bAng' n < 1 := Work.ELNest.bAng'_lt_one n
  have hδ₁ : Work.EL.alpha1 - δ < Work.ELNest.bAng n := by
    have h1 : Work.ELNest.bAng n =
        Work.ELNest.alpha1 - (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n := rfl
    rw [hα1, h1]; linarith
  have hδ₂ : Work.ELNest.bAng' n < Work.EL.alpha2 + δ := by
    have h2 : Work.ELNest.bAng' n =
        Work.ELNest.alpha2 + (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ n := rfl
    rw [hα2, h2]; linarith
  exact nest_angle_window (hN := hN) (P0 := P0) (Q := Q)
    hP0a hP0b hQa hQb hβ hβ₁ h12 h₂β' hβ'1 hPs hQs hcover hzK hzP hzQ hδ₁ hδ₂

end Work.GATE.Nest
