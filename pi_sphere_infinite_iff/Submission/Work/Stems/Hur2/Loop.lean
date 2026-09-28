import Submission.Work.Stems.Hur2.ConeLift

/-!
# The boundary loop of a square, parametrised in quarters

Given three composable paths `γ₀ : x₀ → a`, `e : a → b`, `γ₁ : x₀ → b`, the loop
`γ₀ · e · γ₁⁻¹ · (const)` traversed with weights `1/4, 1/4, 1/4, 1/4` is
`(γ₀.trans e).trans (γ₁.symm.trans (refl x₀))`; continuity is then automatic.  Its values at the
four "quarter points" are `γ₀`, `e`, `γ₁`, `x₀`, matching the parametrisation `bd` used for the
square's boundary.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

/-- The boundary loop of the square, in the parametrisation matching `bd`. -/
def loopPath {X : Type} [TopologicalSpace X] {x₀ a b : X}
    (γ₀ : Path x₀ a) (e : Path a b) (γ₁ : Path x₀ b) : Path x₀ x₀ :=
  (γ₀.trans e).trans (γ₁.symm.trans (Path.refl x₀))

/-- `loopPath` at the parametrisation of the bottom edge is `γ₀`. -/
theorem loopPath_quarter {X : Type} [TopologicalSpace X] {x₀ a b : X}
    (γ₀ : Path x₀ a) (e : Path a b) (γ₁ : Path x₀ b) (t : unitInterval) :
    loopPath γ₀ e γ₁ (quarter t) = γ₀ t := by
  have hq : ((quarter t : unitInterval) : ℝ) = (t : ℝ) / 4 := quarter_val t
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rw [← Path.extend_extends' (loopPath γ₀ e γ₁) (quarter t)]
  unfold loopPath
  rw [Path.extend_trans_of_le_half _ _ (by rw [hq]; linarith)]
  rw [Path.extend_trans_of_le_half _ _ (by rw [hq]; linarith)]
  rw [show (2 : ℝ) * (2 * ((quarter t : unitInterval) : ℝ)) = (t : ℝ) by rw [hq]; ring]
  rw [Path.extend_extends' γ₀ t]

/-- `loopPath` at the parametrisation of the right edge is `e`. -/
theorem loopPath_rightPt {X : Type} [TopologicalSpace X] {x₀ a b : X}
    (γ₀ : Path x₀ a) (e : Path a b) (γ₁ : Path x₀ b) (t : unitInterval) :
    loopPath γ₀ e γ₁ (rightPt t) = e t := by
  have hq : ((rightPt t : unitInterval) : ℝ) = (t : ℝ) / 4 + 1 / 4 := rightPt_val t
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rw [← Path.extend_extends' (loopPath γ₀ e γ₁) (rightPt t)]
  unfold loopPath
  rw [Path.extend_trans_of_le_half _ _ (t := ((rightPt t : unitInterval) : ℝ)) (by rw [hq]; linarith)]
  rw [Path.extend_trans_of_half_le _ _ (t := 2 * ((rightPt t : unitInterval) : ℝ))
    (by rw [hq]; linarith)]
  rw [show (2 : ℝ) * (2 * ((rightPt t : unitInterval) : ℝ)) - 1 = (t : ℝ) by rw [hq]; ring]
  rw [Path.extend_extends' e t]

/-- `loopPath` at the parametrisation of the top edge is `γ₁`. -/
theorem loopPath_topPt {X : Type} [TopologicalSpace X] {x₀ a b : X}
    (γ₀ : Path x₀ a) (e : Path a b) (γ₁ : Path x₀ b) (t : unitInterval) :
    loopPath γ₀ e γ₁ (topPt t) = γ₁ t := by
  have hq : ((topPt t : unitInterval) : ℝ) = (3 - (t : ℝ)) / 4 := topPt_val t
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rw [← Path.extend_extends' (loopPath γ₀ e γ₁) (topPt t)]
  unfold loopPath
  rw [Path.extend_trans_of_half_le _ _ (t := ((topPt t : unitInterval) : ℝ)) (by rw [hq]; linarith)]
  rw [Path.extend_trans_of_le_half _ _ (t := 2 * ((topPt t : unitInterval) : ℝ) - 1)
    (by rw [hq]; linarith)]
  rw [show (2 : ℝ) * (2 * ((topPt t : unitInterval) : ℝ) - 1) = 1 - (t : ℝ) by rw [hq]; ring]
  rw [Path.extend_symm_apply]
  rw [show (1 : ℝ) - (1 - (t : ℝ)) = (t : ℝ) by ring]
  rw [Path.extend_extends' γ₁ t]

/-- `loopPath` at the parametrisation of the left edge is the base point. -/
theorem loopPath_leftPt {X : Type} [TopologicalSpace X] {x₀ a b : X}
    (γ₀ : Path x₀ a) (e : Path a b) (γ₁ : Path x₀ b) (t : unitInterval) :
    loopPath γ₀ e γ₁ (leftPt t) = x₀ := by
  have hq : ((leftPt t : unitInterval) : ℝ) = 1 - (t : ℝ) / 4 := leftPt_val t
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rw [← Path.extend_extends' (loopPath γ₀ e γ₁) (leftPt t)]
  unfold loopPath
  rw [Path.extend_trans_of_half_le _ _ (t := ((leftPt t : unitInterval) : ℝ)) (by rw [hq]; linarith)]
  rw [show (2 : ℝ) * ((leftPt t : unitInterval) : ℝ) - 1 = 1 - (t : ℝ) / 2 by rw [hq]; ring]
  rcases le_total (t : ℝ) 1 with h | h
  · rw [Path.extend_trans_of_half_le _ _ (t := 1 - (t : ℝ) / 2) (by linarith)]
    rw [show (2 : ℝ) * (1 - (t : ℝ) / 2) - 1 = (1 : ℝ) - (t : ℝ) by ring]
    rw [show (1 : ℝ) - (t : ℝ) = ↑(⟨1 - (t : ℝ), by constructor <;> linarith⟩ : unitInterval)
      from rfl]
    rw [Path.extend_extends' (Path.refl x₀) ⟨1 - (t : ℝ), by constructor <;> linarith⟩]
    rfl
  · rw [Path.extend_trans_of_le_half _ _ (t := 1 - (t : ℝ) / 2) (by linarith)]
    rw [show (2 : ℝ) * (1 - (t : ℝ) / 2) = 1 by linarith]
    rw [Path.extend_symm_apply]
    rw [show (1 : ℝ) - 1 = 0 by ring]
    exact Path.extend_zero γ₁

-- The four value lemmas `loopPath_quarter`, `loopPath_rightPt`, `loopPath_topPt`,
-- `loopPath_leftPt` above are proved.  Technique, for the record: rewrite with
-- `← Path.extend_extends' (loopPath …) (quarter t)` to replace the value by the extension at the
-- real parameter, `unfold loopPath`, then chain `Path.extend_trans_of_le_half` /
-- `Path.extend_trans_of_half_le` (naming the parameter explicitly via `t := …`, since the implicit
-- argument is otherwise taken from the wrong occurrence), `Path.extend_symm_apply`, and finally
-- `Path.extend_extends'` to come back.  In `loopPath_leftPt` the two cases `t ≤ 1` / `1 ≤ t`
-- split as `rcases le_total (t : ℝ) 1`, and the second ends with `Path.extend_zero`.
--
-- **Trap (cost one build round):** the interval bounds of `t : unitInterval` must be introduced as
-- `have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1` / `have ht1 : (t : ℝ) ≤ 1 := t.2.2` before `linarith`
-- can use them — `t.2.1`/`t.2.2` are *projections*, not hypotheses, so `linarith` never sees them.

end

end Work.Stems.Hur2
