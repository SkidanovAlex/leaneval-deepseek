import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.pinchingSet_component_bound_v2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A bound on the norm of an algebraic curvature tensor from its sectional curvatures

For a fixed `Λ : ℝ` there is a constant `C` such that every algebraic curvature tensor `R` on `ℝⁿ`
all of whose sectional curvatures `secK R u v` on *orthonormal* pairs satisfy `|secK R u v| ≤ Λ`
has `‖R‖ ≤ C`.

This is the classical statement that the sectional curvature determines the curvature tensor and
that on the finite-dimensional space of algebraic curvature tensors the supremum of `|secK|` over
orthonormal pairs is a norm; quantitatively it is the chain

  `|secK R u v| ≤ dot u u * dot v v * S`  (polarisation of the quartic form, `S = max Λ 0`),
  `|R i j k l| ≤ 8 * S`                   (the explicit polarisation identity),

and then `‖R‖ ≤ 8 * S` because the norm on `Fin n → … → ℝ` is the supremum norm.

The two ingredients are proved (sorry-free) in
`Submission.Work.Diff.L.pinchingSet_component_bound_v2`:
`Work.Diff.L.abs_secK_le_of_isONPair_abs_le` and
`Work.Diff.L.abs_R4_stdB_le_of_secK_bound`.
-/

namespace Work.Diff.L

open Submission.Diff.Alg

theorem exists_curv4_norm_bound_v2 {n : ℕ} (Λ : ℝ) :
    ∃ C : ℝ, ∀ R : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv R →
      (∀ u v : Fin n → ℝ, Submission.Diff.Alg.IsONPair u v →
        |Submission.Diff.Alg.secK R u v| ≤ Λ) → ‖R‖ ≤ C := by
  refine ⟨8 * max Λ 0, fun R hR hsec => ?_⟩
  have hS : (0 : ℝ) ≤ max Λ 0 := le_max_right _ _
  have hΛS : Λ ≤ max Λ 0 := le_max_left _ _
  have hbm : (0 : ℝ) ≤ 8 * max Λ 0 := mul_nonneg (by norm_num) hS
  -- the sectional curvatures are bounded by `max Λ 0`
  have h1 : ∀ u v : Fin n → ℝ, IsONPair u v → |secK R u v| ≤ max Λ 0 :=
    fun u v huv => le_trans (hsec u v huv) hΛS
  -- polarise the quartic form, then read off the components
  have h2 := abs_secK_le_of_isONPair_abs_le hR hS h1
  have h3 := abs_R4_stdB_le_of_secK_bound hR hS h2
  -- the norm on `Fin n → Fin n → Fin n → Fin n → ℝ` is the supremum norm
  rw [pi_norm_le_iff_of_nonneg hbm]
  intro i
  rw [pi_norm_le_iff_of_nonneg hbm]
  intro j
  rw [pi_norm_le_iff_of_nonneg hbm]
  intro k
  rw [pi_norm_le_iff_of_nonneg hbm]
  intro l
  simpa using h3 i j k l

end Work.Diff.L
