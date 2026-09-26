import Mathlib
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.Systole
import Submission.Work.TorusCover.Circles
import Submission.Work.TorusCover.Standard
import Submission.Work.TorusCover.curveLength_le_integral_deriv

/-!
# The length of the meridian circle of the standard torus

The meridian circle `φ ↦ torusMap θ φ` is the level set `{θ = const}` of the standard
parametrisation of the torus of revolution (major radius `2`, minor radius `1`).  Its
derivative in the meridian parameter has norm exactly `1` (it is the unit circle
`(cos φ, sin φ)` in the `(cos θ, sin θ)`-plane times the `z`-axis), so its extrinsic
length over one period is `2π`.

Here we prove this without any calculus: `φ ↦ meridianCircle θ φ` is `1`-Lipschitz because

  `‖meridianCircle θ s - meridianCircle θ t‖ ^ 2
      = ((2 + cos s) - (2 + cos t)) ^ 2 (cos θ ^ 2 + sin θ ^ 2) + (sin s - sin t) ^ 2
      = (cos s - cos t) ^ 2 + (sin s - sin t) ^ 2
      = 2 - 2 cos (s - t) ≤ (s - t) ^ 2`,

using `1 - x ^ 2 / 2 ≤ cos x`.  The variation of a Lipschitz function is bounded by the
length of the interval (`LipschitzOnWith.comp_eVariationOn_le`, `eVariationOn_id_Icc`),
which gives the upper bound `curveLength ≤ ofReal (2π)`; the matching lower bound is the
extrinsic systole bound `TorusParam.systole_bound` applied to the winding vector `(0, 1)`
of the meridian circle (`hasWinding_meridian`), since `torusParamModel.c = 1`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

namespace Work.TorusCover

noncomputable section

/-- The squared norm of the difference of two points of the meridian circle `{θ = const}` is
at most the square of the difference of the meridian parameters: the meridian circle is a
reparametrisation of the unit circle. -/
lemma norm_sq_meridianCircle_sub_le (θ s t : ℝ) :
    ‖Work.Core.meridianCircle θ s - Work.Core.meridianCircle θ t‖ ^ 2 ≤ (s - t) ^ 2 := by
  have h1 : ‖Work.Core.meridianCircle θ s - Work.Core.meridianCircle θ t‖ ^ 2
      = (Real.cos s - Real.cos t) ^ 2 + (Real.sin s - Real.sin t) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ)]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    rw [Fin.sum_univ_three]
    simp only [Work.Core.meridianCircle, Work.Core.torusMap_apply_zero,
      Work.Core.torusMap_apply_one, Work.Core.torusMap_apply_two]
    have e1 : (2 + Real.cos s) * Real.cos θ - (2 + Real.cos t) * Real.cos θ
        = (Real.cos s - Real.cos t) * Real.cos θ := by ring
    have e2 : (2 + Real.cos s) * Real.sin θ - (2 + Real.cos t) * Real.sin θ
        = (Real.cos s - Real.cos t) * Real.sin θ := by ring
    rw [e1, e2, mul_pow, mul_pow, ← mul_add, add_comm (Real.cos θ ^ 2),
      Real.sin_sq_add_cos_sq, mul_one]
  rw [h1]
  have h2 : (Real.cos s - Real.cos t) ^ 2 + (Real.sin s - Real.sin t) ^ 2
      = 2 - 2 * Real.cos (s - t) := by
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq s, Real.sin_sq_add_cos_sq t]
  rw [h2]
  have h3 := Real.one_sub_sq_div_two_le_cos (x := s - t)
  nlinarith [h3]

/-- The meridian circle `{θ = const}` is `1`-Lipschitz as a function of the meridian
parameter. -/
lemma lipschitzWith_meridianCircle (θ : ℝ) :
    LipschitzWith 1 (fun φ => Work.Core.meridianCircle θ φ) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, Real.dist_eq]
  have hab : ‖Work.Core.meridianCircle θ s - Work.Core.meridianCircle θ t‖ ^ 2 ≤ |s - t| ^ 2 := by
    rw [sq_abs]; exact norm_sq_meridianCircle_sub_le θ s t
  have := sq_le_sq.mp hab
  simpa [abs_of_nonneg (norm_nonneg _)] using this

theorem curveLength_meridianCircle_eq (θ : ℝ) :
    Work.TorusCover.curveLength (fun φ => Work.Core.meridianCircle θ φ) 0 (2 * Real.pi) =
      ENNReal.ofReal (2 * Real.pi) := by
  have hupper : curveLength (fun φ => Work.Core.meridianCircle θ φ) 0 (2 * Real.pi) ≤
      ENNReal.ofReal (2 * Real.pi) := by
    rw [curveLength_def]
    have h := (lipschitzWith_meridianCircle θ).lipschitzOnWith.comp_eVariationOn_le
      (g := id) (s := Set.Icc 0 (2 * Real.pi)) (Set.mapsTo_univ _ _)
    rw [eVariationOn_id_Icc] at h
    simpa using h
  have hlower : ENNReal.ofReal (2 * Real.pi) ≤
      curveLength (fun φ => Work.Core.meridianCircle θ φ) 0 (2 * Real.pi) := by
    obtain ⟨Λ, hΛ⟩ := hasWinding_meridian torusParamModel θ
    have h := TorusParam.systole_bound torusParamModel hΛ (by decide : ((0, 1) : ℤ × ℤ) ≠ 0)
    simpa [Work.TorusCover.torusParamModel, Work.Core.meridianCircle] using h
  exact le_antisymm hupper hlower

end

end Work.TorusCover
