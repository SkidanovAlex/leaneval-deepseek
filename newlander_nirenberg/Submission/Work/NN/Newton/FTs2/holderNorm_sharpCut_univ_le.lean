import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Core.sharpCut
import Submission.Work.NN.Core.Lev.sharpCut_fderiv_bounds
import Submission.Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds

/-!
# The `C^{1,α}` norm of the parametric cutoff `sharpCut a b` on all of `ℂ`

For `1/2 ≤ a < b ≤ 1` the cutoff `φ = sharpCut a b` (equal to `1` on `‖ζ‖ ≤ a` and to `0` for
`b ≤ ‖ζ‖`) satisfies

  `holderNorm 1 α (sharpCut a b) univ ≤ ofReal (D / (b - a) ^ 2)`

with a constant `D` depending only on `α` (not on `a`, `b`).

The proof is an assembly of two inputs already available in the workspace:

* `Work.NN.Core.Lev.sharpCut_fderiv_bounds`: `‖φ‖ ≤ 1`, `‖∇φ‖ ≤ C/(b-a)` and
  `‖∇φ x - ∇φ y‖ ≤ C (1/(a(b-a)) + 1/(b-a)²) ‖x - y‖` with `C > 0` independent of `a, b`;
* `Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds`: these data bound the `C^{1,α}` norm on a
  convex open set by `3 M₀ + 4 M₁ + M₂`.

It remains to compare `3 + 4C/(b-a) + C(1/(a(b-a)) + 1/(b-a)²)` with `D/(b-a)²` under the
hypotheses `1/2 ≤ a < b ≤ 1`: since `0 < b - a ≤ 1` we have `3 ≤ 3/(b-a)²`,
`C/(b-a) ≤ C/(b-a)²` and `1/(a(b-a)) ≤ 2/(b-a) ≤ 2/(b-a)²`, so that `D = 3 + 7C` suffices.
-/

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Newton.FTs2

/-- Elementary arithmetic: for `C > 0`, `1/2 ≤ a < b ≤ 1` the first- and second-order data of
`sharpCut a b` is dominated by `(3 + 7 C) / (b - a) ^ 2`. -/
lemma sharpCut_univ_arith {C a b : ℝ} (hC : 0 < C) (ha : 1 / 2 ≤ a) (hab : a < b)
    (hb : b ≤ 1) :
    3 * 1 + 4 * (C * (1 / (b - a))) + C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2)
      ≤ (3 + 7 * C) * (1 / (b - a) ^ 2) := by
  have hapos : 0 < a := by linarith
  have hdpos : 0 < b - a := by linarith
  have hdle1 : b - a ≤ 1 := by linarith
  have hd2pos : 0 < (b - a) ^ 2 := by positivity
  rw [show (3 + 7 * C) * (1 / (b - a) ^ 2) = (3 + 7 * C) / (b - a) ^ 2 by ring]
  rw [le_div_iff₀ hd2pos]
  have h1 : (b - a) ^ 2 ≤ 1 := by nlinarith
  have h2 : (b - a) ^ 2 ≤ b - a := by nlinarith
  have h3 : C * (b - a) ≤ C := by nlinarith
  have h4 : C ≤ 2 * C * a := by nlinarith
  have key : (3 * 1 + 4 * (C * (1 / (b - a)))
        + C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2)) * (b - a) ^ 2 ≤ 3 + 7 * C := by
    field_simp
    nlinarith [h1, h2, h3, h4]
  exact key

theorem holderNorm_sharpCut_univ_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ a b : ℝ, 1 / 2 ≤ a → a < b → b ≤ 1 →
      Work.CR.Flat.holderNorm 1 α (Work.NN.Core.sharpCut a b) Set.univ
        ≤ ENNReal.ofReal (D * (1 / (b - a) ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := Work.NN.Core.Lev.sharpCut_fderiv_bounds
  refine ⟨3 + 7 * C, by linarith, ?_⟩
  intro a b ha hab hb
  have hapos : 0 < a := by linarith
  have hM1 : 0 ≤ C * (1 / (b - a)) := by
    have : 0 < b - a := by linarith
    positivity
  have hM2 : 0 ≤ C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) := by
    have h1 : 0 < b - a := by linarith
    have h2 : 0 < a * (b - a) := by positivity
    positivity
  have hbd := Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds (Ω := Set.univ)
    isOpen_univ convex_univ hα0 hα1
    (g := Work.NN.Core.sharpCut a b)
    ((Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).of_le (by simp))
    (M₀ := 1) (M₁ := C * (1 / (b - a))) (M₂ := C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2))
    zero_le_one hM1 hM2
    (fun x _ => Work.NN.Core.norm_sharpCut_le_one a b x)
    (fun x _ => (hC a b hapos hab).1 x)
    (fun x _ y _ => (hC a b hapos hab).2.2 x y)
  refine le_trans hbd (ENNReal.ofReal_le_ofReal ?_)
  exact sharpCut_univ_arith hC0 ha hab hb

end Work.NN.Newton.FTs2
