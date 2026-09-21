import Mathlib
import Submission.Work.OddRadon.radialMap_injOn

/-!
# The radial system has at most one positive solution

`RadialSystem n Φ Ψ R r` says, on `[0, π/2]`,

    (R^{2n+2} + r^{2n+2}) · cos²α = Φ α,    (R^{2n+1} - r^{2n+1}) · cos α = Ψ α.

On `[0, π/2)` the factor `cos α` does not vanish, so both `(R, r)` and `(R', r')` are
solutions of the *same* two-power system at every point of `[0, π/2)`.  Injectivity of the
two-power map on the positive quadrant (`radialMap_injOn`) then forces `R = R'` and
`r = r'` wherever both pairs are positive.  This is the uniqueness of the radial graph that
Step 3 of the paper relies on.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

theorem radialSystem_determined (n : ℕ) {Φ Ψ : ℝ → ℝ} {R r R' r' : ℝ → ℝ}
    (h : RadialSystem n Φ Ψ R r) (h' : RadialSystem n Φ Ψ R' r')
    (hpos : ∀ α ∈ Set.Ico 0 (Real.pi / 2), 0 < R α ∧ 0 < r α)
    (hpos' : ∀ α ∈ Set.Ico 0 (Real.pi / 2), 0 < R' α ∧ 0 < r' α) :
    Set.EqOn R R' (Set.Ico 0 (Real.pi / 2)) ∧
      Set.EqOn r r' (Set.Ico 0 (Real.pi / 2)) := by
  have hsub : Set.Ico (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    Set.Ico_subset_Icc_self
  have key : ∀ α ∈ Set.Ico 0 (Real.pi / 2), R α = R' α ∧ r α = r' α := by
    intro α hα
    have hαIcc : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hsub hα
    -- `cos α ≠ 0` on `[0, π/2)`, so the cleared system may be divided through by it.
    have hcos : Real.cos α ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩)
    obtain ⟨hA, hB⟩ := h α hαIcc
    obtain ⟨hA', hB'⟩ := h' α hαIcc
    -- The two power sums agree, and so do the two power differences.
    have hS : R α ^ (2 * n + 2) + r α ^ (2 * n + 2)
        = R' α ^ (2 * n + 2) + r' α ^ (2 * n + 2) :=
      mul_right_cancel₀ (pow_ne_zero 2 hcos) (by rw [hA, hA'])
    have hD : R α ^ (2 * n + 1) - r α ^ (2 * n + 1)
        = R' α ^ (2 * n + 1) - r' α ^ (2 * n + 1) :=
      mul_right_cancel₀ hcos (by rw [hB, hB'])
    have hmap : radialMap n (R α, r α) = radialMap n (R' α, r' α) := by
      simp only [radialMap, Prod.mk.injEq]
      exact ⟨hS, hD⟩
    have hp := radialMap_injOn n (hpos α hα) (hpos' α hα) hmap
    exact ⟨by simpa using congrArg Prod.fst hp, by simpa using congrArg Prod.snd hp⟩
  exact ⟨fun α hα => (key α hα).1, fun α hα => (key α hα).2⟩

end Work.OddRadon
