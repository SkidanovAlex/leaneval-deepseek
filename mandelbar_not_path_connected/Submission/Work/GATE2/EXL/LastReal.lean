/-
# GATE2 / EXL — the initial segment of the arc after its last real point

The exit loop of case (ii) (`NOTES_LEAD_mandelbar_gaps3.md` §2.2 (b)) is built from the lifted
equipotential arc `A` from the deep real leak point `x*` to `γ₁ s₁`, but the segment used is the
part **after the last real point** of `A`: this is exactly what makes the offset-avoidance (W) hold
(the offset `λ t − λ 0` is real only at the two ends of the loop, where it is `0` resp. `1`, both
off the slit `(−∞, −1/2]`).

This module extracts that segment: for a continuous `A : C(I, ℂ)` with `(A 0).im = 0` and
`(A 1).im ≠ 0`, the set of real parameters is compact and nonempty, it has a largest element `r₀`,
`r₀ < 1`, and the reparametrised terminal segment

    B t := A (r₀ + t (1 - r₀))

starts at the **last real point** (a real number `x₀`, `B 0 = (x₀ : ℂ)`), ends at `A 1`, has
`Im ≠ 0` at every positive parameter, and has range contained in that of `A` (so all the
`Re`/off-`K`/window/floor data transfer).
-/
import Submission.Work.GATE2.Inputs

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

/-- **The last real point of a continuous arc.** -/
theorem lastReal_of_arc {A : C(unitInterval, ℂ)} (h0 : (A 0).im = 0) (hs : (A 1).im ≠ 0) :
    ∃ x₀ : ℝ, ∃ B : C(unitInterval, ℂ),
      B 0 = ((x₀ : ℝ) : ℂ) ∧ B 1 = A 1 ∧
      (∀ t : unitInterval, 0 < (t : ℝ) → (B t).im ≠ 0) ∧
      (∀ t : unitInterval, ∃ t' : unitInterval, B t = A t') := by
  have hmem : ∀ r : ℝ, min (max r 0) 1 ∈ Set.Icc (0 : ℝ) 1 := fun r =>
    ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  set g : ℝ → ℂ := fun r => A ⟨min (max r 0) 1, hmem r⟩ with hg
  have hgcont : Continuous g := by
    rw [hg]
    exact A.continuous.comp (Continuous.subtype_mk
      ((continuous_id.max continuous_const).min continuous_const) hmem)
  have hg0 : g 0 = A 0 := by
    rw [hg]
    show A ⟨min (max (0 : ℝ) 0) 1, hmem 0⟩ = A 0
    exact congrArg A (Subtype.ext (by norm_num))
  have hg1 : g 1 = A 1 := by
    rw [hg]
    show A ⟨min (max (1 : ℝ) 0) 1, hmem 1⟩ = A 1
    exact congrArg A (Subtype.ext (by norm_num))
  have hge : ∀ (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1), g r = A ⟨r, hr⟩ := by
    intro r hr
    rw [hg]
    show A ⟨min (max r 0) 1, hmem r⟩ = A ⟨r, hr⟩
    have hxy : min (max r 0) 1 = r := by rw [max_eq_left hr.1, min_eq_left hr.2]
    exact congrArg A (Subtype.ext hxy)
  set S : Set ℝ := {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ (g r).im = 0} with hS
  have hSne : S.Nonempty := ⟨0, ⟨⟨le_refl 0, zero_le_one⟩, by rw [hg0]; exact h0⟩⟩
  have hSclosed : IsClosed S := by
    rw [hS]
    exact isClosed_Icc.inter (isClosed_eq (Complex.continuous_im.comp hgcont) continuous_const)
  have hScomp : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed (fun r hr => hr.1)
  obtain ⟨r₀, hr₀S, hmax⟩ := hScomp.exists_isMaxOn hSne continuousOn_id
  have hr₀lt1 : r₀ < 1 := by
    rcases lt_or_eq_of_le hr₀S.1.2 with h | h
    · exact h
    · exfalso
      have hcon : (g r₀).im = 0 := hr₀S.2
      rw [h, hg1] at hcon
      exact hs hcon
  have hr₀ge0 : 0 ≤ r₀ := hr₀S.1.1
  refine ⟨(g r₀).re, ⟨fun t : unitInterval => g (r₀ + (t : ℝ) * (1 - r₀)),
    hgcont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩,
    ?_, ?_, ?_, ?_⟩
  · show g (r₀ + ((0 : unitInterval) : ℝ) * (1 - r₀)) = (((g r₀).re : ℝ) : ℂ)
    have harg : r₀ + ((0 : unitInterval) : ℝ) * (1 - r₀) = r₀ := by
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]; ring
    rw [harg]
    exact (Complex.ext (by simp) (by simpa using hr₀S.2.symm)).symm
  · show g (r₀ + ((1 : unitInterval) : ℝ) * (1 - r₀)) = A 1
    have harg : r₀ + ((1 : unitInterval) : ℝ) * (1 - r₀) = 1 := by
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]; ring
    rw [harg, hg1]
  · intro t ht
    have hσmem : r₀ + (t : ℝ) * (1 - r₀) ∈ Set.Icc (0 : ℝ) 1 := by
      have h3 : 0 ≤ 1 - r₀ := sub_nonneg.mpr hr₀lt1.le
      constructor
      · nlinarith [t.2.1, ht, hr₀ge0, h3]
      · nlinarith [t.2.2, h3]
    intro hcon
    have hmemS : r₀ + (t : ℝ) * (1 - r₀) ∈ S := ⟨hσmem, hcon⟩
    have hle := hmax hmemS
    have hgt : r₀ < r₀ + (t : ℝ) * (1 - r₀) := by
      have : 0 < (t : ℝ) * (1 - r₀) := mul_pos ht (sub_pos.mpr hr₀lt1)
      linarith
    exact absurd hle (not_le.mpr hgt)
  · intro t
    have hσmem : r₀ + (t : ℝ) * (1 - r₀) ∈ Set.Icc (0 : ℝ) 1 := by
      have h3 : 0 ≤ 1 - r₀ := sub_nonneg.mpr hr₀lt1.le
      constructor
      · nlinarith [t.2.1, hr₀ge0, h3]
      · nlinarith [t.2.2, h3]
    exact ⟨⟨r₀ + (t : ℝ) * (1 - r₀), hσmem⟩, hge _ hσmem⟩

end Work.GATE2.EXL
