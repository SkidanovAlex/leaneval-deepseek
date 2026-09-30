/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Decoupling

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary norm/coordinate lemmas

Three elementary facts about the Euclidean space `E k = EuclideanSpace ℝ (Fin k)` and the
complex norm, factored into a module that depends only on `Decoupling.lean` (and hence not on
`Discretisation.lean`/`DecouplingThm12.lean`).

They are used by `Nikolskii.lean` (and formerly lived in `Discretisation.lean`), which imports
them from here so that the localisation machinery (`Nikolskii.lean`, `NikolskiiGlobal.lean`,
`Localise.lean`, `Ne89.lean`, `FromDecLin.lean`, `DecouplesBridge.lean`) does **not** depend on
`DecouplingThm12.lean`.  This is what makes it possible for `DecouplingThm12.lean` to obtain
`bdg_thm_ntmain` from the enlarged GLYZ decoupling theorem via `DecouplesBridge.lean`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace

set_option autoImplicit false

namespace Submission.Vinogradov

/-- The norm of a nonnegative real, as a complex number. -/
lemma complex_norm_ofReal_nonneg (y : ℝ) (hy : 0 ≤ y) : ‖(y : ℂ)‖ = y := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]

/-- The inner product on `E k` in coordinates. -/
lemma inner_coord (k : ℕ) (x w : E k) :
    ⟪x, w⟫ = ∑ j : Fin k, x j * w j := by
  simp [PiLp.inner_apply, mul_comm]

/-- The squared norm on `E k` in coordinates. -/
lemma norm_sq_coord_sum (k : ℕ) (w : E k) : ‖w‖ ^ 2 = ∑ j : Fin k, (w j) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  have hnonneg : 0 ≤ ∑ j : Fin k, ‖(w.ofLp j : ℝ)‖ ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg ‖(w.ofLp j : ℝ)‖)
  rw [Real.sq_sqrt hnonneg]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (w.ofLp j : ℝ) = w j by rfl]
  rw [Real.norm_eq_abs, sq_abs]

end Submission.Vinogradov
