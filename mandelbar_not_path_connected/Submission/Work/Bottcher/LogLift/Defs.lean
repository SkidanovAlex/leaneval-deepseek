import Mathlib
import Submission.Work.Bottcher.Contraction.LiftCoreDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Path concatenation helpers for the logarithmic lift of `normFactor`

Elementary path operations on `C(unitInterval, ℂ)` used in
`Work.Bottcher.Contraction.exists_continuous_log_of_monodromy`:

* `concatC δ₁ δ₂ h` is the concatenation of `δ₁` and `δ₂` (traverse `δ₁` on `[0,1/2]`, then
  `δ₂` on `[1/2,1]`), defined through `Path.trans`;
* `revC δ` is the reversal `t ↦ δ (1-t)` of `δ`.

The accompanying lemmas record the pointwise descriptions of these maps.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.LogLift

noncomputable section

open Work.Bottcher.Contraction (liftChange liftOf)

/-- Concatenation of two paths in `ℂ` with matching endpoints. -/
def concatC (δ₁ δ₂ : C(unitInterval, ℂ)) (h : δ₁ 1 = δ₂ 0) : C(unitInterval, ℂ) :=
  ((⟨δ₁, rfl, rfl⟩ : Path (δ₁ 0) (δ₁ 1)).trans
    (⟨δ₂, h.symm, rfl⟩ : Path (δ₁ 1) (δ₂ 1))).toContinuousMap

/-- Reversal `t ↦ δ (1 - t)` of a path in `ℂ`. -/
def revC (δ : C(unitInterval, ℂ)) : C(unitInterval, ℂ) :=
  δ.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩

@[simp] theorem revC_apply (δ : C(unitInterval, ℂ)) (t : unitInterval) :
    revC δ t = δ (unitInterval.symm t) := rfl

theorem concatC_apply_le (δ₁ δ₂ : C(unitInterval, ℂ)) (h : δ₁ 1 = δ₂ 0) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    concatC δ₁ δ₂ h t
      = δ₁ ⟨2 * (t : ℝ), Set.mem_Icc.mpr ⟨by linarith [t.2.1], by linarith [ht]⟩⟩ := by
  rw [concatC, Path.coe_toContinuousMap, Path.trans_apply, dif_pos ht]
  rfl

theorem concatC_apply_gt (δ₁ δ₂ : C(unitInterval, ℂ)) (h : δ₁ 1 = δ₂ 0) (t : unitInterval)
    (ht : ¬ (t : ℝ) ≤ 1 / 2) :
    concatC δ₁ δ₂ h t
      = δ₂ ⟨2 * (t : ℝ) - 1, Set.mem_Icc.mpr ⟨by linarith [t.2.2], by linarith [t.2.2]⟩⟩ := by
  rw [concatC, Path.coe_toContinuousMap, Path.trans_apply, dif_neg ht]
  rfl

theorem concatC_zero (δ₁ δ₂ : C(unitInterval, ℂ)) (h : δ₁ 1 = δ₂ 0) :
    concatC δ₁ δ₂ h 0 = δ₁ 0 := by
  have := concatC_apply_le δ₁ δ₂ h 0 (by norm_num)
  simpa using this

theorem concatC_one (δ₁ δ₂ : C(unitInterval, ℂ)) (h : δ₁ 1 = δ₂ 0) :
    concatC δ₁ δ₂ h 1 = δ₂ 1 := by
  have h1 := concatC_apply_gt δ₁ δ₂ h 1 (by norm_num)
  rw [h1]
  congr 1
  ext
  norm_num

theorem revC_zero (δ : C(unitInterval, ℂ)) : revC δ 0 = δ 1 := by
  simp [revC]

theorem revC_one (δ : C(unitInterval, ℂ)) : revC δ 1 = δ 0 := by
  simp [revC]

theorem revC_ne_zero (δ : C(unitInterval, ℂ)) (h : ∀ t, δ t ≠ 0) :
    ∀ t, revC δ t ≠ 0 := fun t => h _

theorem concatC_ne_zero (δ₁ δ₂ : C(unitInterval, ℂ)) (h : δ₁ 1 = δ₂ 0)
    (h₁ : ∀ t, δ₁ t ≠ 0) (h₂ : ∀ t, δ₂ t ≠ 0) : ∀ t, concatC δ₁ δ₂ h t ≠ 0 := by
  intro t
  by_cases ht : (t : ℝ) ≤ 1/2
  · rw [concatC_apply_le _ _ _ _ ht]; exact h₁ _
  · rw [concatC_apply_gt _ _ _ _ ht]; exact h₂ _

/-- The lift change is unchanged when the path is replaced by an equal one. -/
theorem liftChange_congr {δ₁ δ₂ : C(unitInterval, ℂ)} (hδ : δ₁ = δ₂)
    (h₁ : ∀ t, δ₁ t ≠ 0) (h₂ : ∀ t, δ₂ t ≠ 0) :
    liftChange δ₁ h₁ = liftChange δ₂ h₂ := by
  subst hδ; rfl

end

end Work.Bottcher.LogLift
