import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `boxState_sq_bound` — a `BoxState` is bounded on its box

A `Work.BoseKinLoc.BoxState n ℓ` is a globally smooth (`ContDiff ℝ ∞`) real
function on the `n`-particle configuration space `X n = (ℝ³)^n`, together with
symmetry and non-vanishing.  Nothing about its growth at infinity is recorded,
but the centred box `abox n ℓ` is compact, so on it the state is bounded:

  `∃ P ≥ 0, ∀ x ∈ abox n ℓ, (Φ x)² ≤ P`.

The three helper lemmas are the two monotonicity/elementarity facts needed for
compactness of `abox n ℓ` at an *arbitrary* side length `ℓ` (the corpus lemma
`Submission.BoseGases.abox_compact` requires `0 < ℓ`), and that compactness.
For `ℓ ≤ 0` the box `abox n ℓ` is empty (or, when `n = 0`, all of the
one-point space `X 0`), and the inclusion `abox n ℓ ⊆ abox n (max ℓ 1)` plus
closedness handles both cases uniformly.
-/

noncomputable section

namespace Work.BoseFixB1.WB

open scoped BigOperators

/-- The centred cube is monotone in its side length. -/
lemma acube_subset_of_le {ℓ L : ℝ} (h : ℓ ≤ L) :
    Submission.BoseGases.acube ℓ ⊆ Submission.BoseGases.acube L := by
  intro y hy m
  exact Set.Icc_subset_Icc (by linarith) (by linarith) (hy m)

/-- The `n`-particle centred box is monotone in the side length. -/
lemma abox_subset_of_le {n : ℕ} {ℓ L : ℝ} (h : ℓ ≤ L) :
    Submission.BoseGases.abox n ℓ ⊆ Submission.BoseGases.abox n L := by
  intro x hx i
  exact acube_subset_of_le h (hx i)

/-- The `n`-particle centred box is compact for **every** side length `ℓ`
(not merely for `0 < ℓ`): it is closed, and it sits inside the compact box of
side length `max ℓ 1`. -/
lemma isCompact_abox (n : ℕ) (ℓ : ℝ) : IsCompact (Submission.BoseGases.abox n ℓ) := by
  refine IsCompact.of_isClosed_subset ?_ (Submission.BoseGases.abox_isClosed n ℓ)
    (abox_subset_of_le (le_max_left ℓ 1))
  exact Submission.BoseGases.abox_compact n (lt_of_lt_of_le zero_lt_one (le_max_right ℓ 1))

/-- **A smooth box state is bounded on its box**, hence so is its square. -/
theorem boxState_sq_bound {n : ℕ} {ℓ : ℝ} (Φ : Work.BoseKinLoc.BoxState n ℓ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ x : Submission.BoseGases.X n,
      x ∈ Submission.BoseGases.abox n ℓ → (Φ x) ^ 2 ≤ P := by
  obtain ⟨B, hB⟩ := (isCompact_abox n ℓ).exists_bound_of_continuousOn
    ((Φ.contDiff.continuous).continuousOn)
  refine ⟨max 0 (B ^ 2), le_max_left _ _, fun x hx => ?_⟩
  have h1 : (Φ x) ^ 2 = ‖Φ x‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖Φ x‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg (Φ x), hB x hx]
  calc (Φ x) ^ 2 = ‖Φ x‖ ^ 2 := h1
    _ ≤ B ^ 2 := h2
    _ ≤ max 0 (B ^ 2) := le_max_right _ _

end Work.BoseFixB1.WB
