import Mathlib
import Submission.Work.Drive.normalFrame
import Submission.Work.Drive.framePathDefs

/-!
# The expansion of a vector in the frame `(e, v, e × v)`

If `e` and `v` are orthonormal vectors of `Space = ℝ³`, then `(e, v, e × v)` is an orthonormal
basis of `Space`, so every vector expands in it with its inner-product coordinates:

`x = ⟪x, e⟫ • e + ⟪x, v⟫ • v + ⟪x, e × v⟫ • (e × v)`.

The proof is the standard one: the family is orthonormal (`norm_crossv_of_orthonormal` and the
orthogonality of the cross product to its factors), and a vector orthogonal to all three members
of an orthonormal family of full cardinality is zero
(`Work.Drive.eq_zero_of_inner_eq_zero_of_orthonormal`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

theorem crossv_expansion {e v x : LeanEval.KnotTheory.Quadrisecant.Space}
    (he : ‖e‖ = 1) (hv : ‖v‖ = 1) (hev : inner ℝ e v = 0) :
    x = inner ℝ x e • e + inner ℝ x v • v
        + inner ℝ x (Work.Drive.crossv e v) • Work.Drive.crossv e v := by
  have hc : ‖crossv e v‖ = 1 := norm_crossv_of_orthonormal he hv hev
  have hev' : inner ℝ v e = 0 := by rw [real_inner_comm]; exact hev
  have hce : inner ℝ (crossv e v) e = 0 := inner_crossv_self e v
  have hec : inner ℝ e (crossv e v) = 0 := inner_self_crossv e v
  have hcv : inner ℝ (crossv e v) v = 0 := inner_crossv_right e v
  have hvc : inner ℝ v (crossv e v) = 0 := by rw [real_inner_comm]; exact hcv
  have horth : Orthonormal ℝ ![e, v, crossv e v] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hev, hev', hce, hec, hcv, hvc, he, hv, hc]
  have hz : x - (inner ℝ x e • e + inner ℝ x v • v + inner ℝ x (crossv e v) • crossv e v)
      = 0 := by
    refine eq_zero_of_inner_eq_zero_of_orthonormal horth (fun i => ?_)
    fin_cases i <;>
      simp [inner_sub_left, inner_add_left, real_inner_smul_left, hev, hev', hce, hec, hcv,
        hvc, he, hv, hc]
  exact sub_eq_zero.mp hz

end Work.Drive
