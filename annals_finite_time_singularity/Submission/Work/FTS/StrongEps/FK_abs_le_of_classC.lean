import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKAbsLeSqrtEta
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FK_abs_le_of_classC` — the angular moment of a `ClassC` profile

`FK f z = ∫_θ f(z,θ) K(θ) dθ` with `K(θ) = 3 sinθ cos²θ`.  On the class `ClassC α` the
angular moment is dominated, **uniformly in `α ∈ (0,1]` and in `z > 0`**, by the level-`6`
`ℋ`-size:

  `|FK f z| ≤ 7 · Xn6 α f`   whenever `ClassC α f`.

The two inputs are

* `FKAbsLeSqrtEta` — the weighted angular Cauchy–Schwarz
  `|FK Y z| ≤ 4 √(∫_θ sin(2θ)^{-η} Y(z,θ)²)`;
* `fkSliceSup_sliceSupGraded` — the uniform-in-`z` slice bound
  `∫_θ sin(2θ)^{-η} (D_z^jD_θ^i f z θ)² ≤ 3 HkSq α k f` for `i + j + 1 ≤ k`
  (the window form of the radial Hardy inequality, which is what removes the
  degeneracy of the angular Hardy constant `1/√(γ-1)` as `α → 0`).

Taking `(j,i) = (0,0)`, `k = 6` turns the angular moment into `√48 · Xn6 α f`, and `√48 ≤ 7`.
-/

namespace Work.FTS.StrongEps

open MeasureTheory

theorem FK_abs_le_of_classC :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α Ce : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α f → Work.FTS.StrongGlobal.Xn6 α f ≤ Ce →
      ∀ z ∈ Set.Ioi 0, |Work.Construction.FK f z| ≤ C * Ce := by
  refine ⟨7, by norm_num, ?_⟩
  intro α Ce hα f hf hXn z hz
  have hα0 : 0 < α := hα.1
  -- `ClassC` is `ℋ⁷`-honest; descend to `ℋ⁶`
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 6 (by norm_num) hf.mem
  -- integrability of the weighted squared slice of `f` at the fixed `z > 0`
  have hint : MeasureTheory.IntegrableOn
      (fun θ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_slice_integrable
      (α := α) hα0 hf.reg hmem6 (j := 0) (i := 0) (by norm_num) hz
  -- the weighted angular Cauchy–Schwarz
  have hFK := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKAbsLeSqrtEta
    (z := z) (Y := f) hint
  -- the uniform-in-`z` slice bound, at the top slot `(j,i) = (0,0)`
  have hslice := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_sliceSupGraded
    (α := α) hα0 hf.reg hmem6 0 0 (by norm_num) z hz
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
  have hCe0 : 0 ≤ Ce := le_trans hXnn hXn
  have hstep : Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2)
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hslice
  have hsqrt48 : Real.sqrt 48 = 4 * Real.sqrt 3 := by
    rw [show (48 : ℝ) = (4 * Real.sqrt 3) ^ 2 from by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have h48 : Real.sqrt 48 ≤ 7 := by
    rw [show (7 : ℝ) = Real.sqrt 49 from by
      rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc |Work.Construction.FK f z|
      ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2) := hFK
    _ ≤ 4 * Real.sqrt (3 * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = Real.sqrt 48 * Work.FTS.StrongGlobal.Xn6 α f := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        rw [show Work.FTS.StrongGlobal.Xn6 α f
            = Real.sqrt (Work.Spaces.HkSq α 6 f) from rfl]
        rw [hsqrt48]
        ring
    _ ≤ 7 * Ce := by
        calc Real.sqrt 48 * Work.FTS.StrongGlobal.Xn6 α f
            ≤ Real.sqrt 48 * Ce := mul_le_mul_of_nonneg_left hXn (Real.sqrt_nonneg _)
          _ ≤ 7 * Ce := mul_le_mul_of_nonneg_right h48 hCe0

end Work.FTS.StrongEps
