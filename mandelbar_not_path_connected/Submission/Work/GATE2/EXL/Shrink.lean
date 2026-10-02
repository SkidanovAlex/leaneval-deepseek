/-
# GATE2 / EXL — shrinking the leak disc, and the independence of `v`

The two constructions `Work.GATE2.EXL.exitLoop_exists` and `…_iota` produce
`∃ r₀ > 0, ∃ v, Nonempty (ExitLoop c₀ Ψ x₀ r₀ v α)`.  The consumers (D1, which fixes the radius to
PARIMPL's `LeakData.r₀` and the height `v` to the real Écalle height of the entry point) need the
two easy flexibilities recorded here:

* **the disc can be shrunk**: `ExitLoop … r₀ …` implies `ExitLoop … r₀' …` for `r₀' ≤ r₀`
  (every `∀ u ∈ closedBall x₀ r₀`-field only weakens);
* **`v` is irrelevant**: the only field mentioning `v` is the offset-avoidance, and
  `(v : ℂ) + (λt − (u−1)) ∈ slitAt v` is *equivalent* to `offset.im = 0 → offset.re > −1/2`,
  which is independent of `v`.
-/
import Submission.Work.GATE2.ExitPathInputs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

/-- **The radius of the leak disc can be decreased.**  Every field of `ExitLoop` except the
`∀ u ∈ closedBall x₀ r₀` ones is independent of `r₀`, and those only weaken. -/
def ExitLoop.mono_r₀ {c₀ : ℂ} {Ψ : ℂ → ℂ} {x₀ r₀ v α : ℝ}
    (h : Work.GATE2.ExitLoop c₀ Ψ x₀ r₀ v α) {r₀' : ℝ}
    (hr : r₀' ≤ r₀) : Work.GATE2.ExitLoop c₀ Ψ x₀ r₀' v α where
  𝒦 := h.𝒦
  isCompact := h.isCompact
  offK := h.offK
  win := h.win
  discs := fun u hu => h.discs u (Metric.closedBall_subset_closedBall hr hu)
  K₀ := h.K₀
  isCompact_K₀ := h.isCompact_K₀
  K₀_re := h.K₀_re
  K₀_sub := h.K₀_sub
  loop := fun u hu => h.loop u (Metric.closedBall_subset_closedBall hr hu)

/-- The offset-avoidance `(W)` does not depend on `v`: `(v : ℂ) + w ∈ slitAt v` is
`¬ (w.im = 0 ∧ w.re ≤ −1/2)`. -/
theorem slitAt_add_iff {v : ℝ} {w : ℂ} :
    (v : ℂ) + w ∈ Work.GATE2.slitAt v ↔ ¬ (w.im = 0 ∧ w.re ≤ -(1 / 2 : ℝ)) := by
  rw [Work.GATE2.slitAt, Set.mem_ofPred_eq]
  constructor
  · rintro h ⟨him, hre⟩
    exact h ⟨by simp [Complex.add_im, Complex.ofReal_im, him],
      by simp only [Complex.add_re, Complex.ofReal_re]; linarith⟩
  · rintro h ⟨him, hre⟩
    exact h ⟨by simpa using him,
      by simp only [Complex.add_re, Complex.ofReal_re] at hre; linarith⟩

/-- **The height `v` is irrelevant** to `ExitLoop`. -/
def ExitLoop.congr_v {c₀ : ℂ} {Ψ : ℂ → ℂ} {x₀ r₀ v α : ℝ}
    (h : Work.GATE2.ExitLoop c₀ Ψ x₀ r₀ v α) (v' : ℝ) :
    Work.GATE2.ExitLoop c₀ Ψ x₀ r₀ v' α where
  𝒦 := h.𝒦
  isCompact := h.isCompact
  offK := h.offK
  win := h.win
  discs := h.discs
  K₀ := h.K₀
  isCompact_K₀ := h.isCompact_K₀
  K₀_re := h.K₀_re
  K₀_sub := h.K₀_sub
  loop := fun u hu => by
    obtain ⟨lam, h0, h1, hK, hg, hW⟩ := h.loop u hu
    refine ⟨lam, h0, h1, hK, hg, fun t => ?_⟩
    exact slitAt_add_iff.mpr (slitAt_add_iff.mp (hW t))

end Work.GATE2.EXL
