import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.NN.Core.sharpCut
import Submission.Work.NN.Ratio.Cut

namespace Work.NN.Core.TelTwoDF

open scoped NNReal ENNReal
-- NOTE: the `ContDiff` scope is opened so that the `∞` in `ContDiff ℝ ∞` below is the
-- `C^∞` of the `ContDiff` hierarchy (`(⊤ : ℕ∞) : WithTop ℕ∞`) and not the `⊤` of `ℝ≥0∞`
-- introduced by the `ENNReal` scope.  Without it the statement does not even elaborate.
open scoped ContDiff
open Set

/-- From `x ≠ ⊤` in `ℝ≥0∞` one extracts a *positive* real upper bound `x ≤ ofReal C`. -/
lemma exists_pos_ofReal_le_of_ne_top {x : ℝ≥0∞} (h : x ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ x ≤ ENNReal.ofReal C := by
  refine ⟨max x.toReal 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  calc x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal h).symm
    _ ≤ ENNReal.ofReal (max x.toReal 1) := ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- `Work.NN.Core.sharpCut a b` and the (definitionally identical) flexible cutoff
`Work.NN.Ratio.rCut a b` of `Submission/Work/NN/Ratio/Cut.lean` are the same function. -/
lemma sharpCut_eq_rCut (a b : ℝ) : Work.NN.Core.sharpCut a b = Work.NN.Ratio.rCut a b := by
  funext ζ
  simp only [Work.NN.Core.sharpCut, Work.NN.Core.sharpCutReal, Work.NN.Ratio.rCut,
    Work.NN.Ratio.rCutR]

variable {a b α : ℝ}

/-- The `∂̄`-derivative of the sharp cutoff, written through the flexible cutoff. -/
lemma dbarC_sharpCut_eq (a b : ℝ) :
    Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b)
      = fun ζ => Work.CR.Flat.dbarC (Work.NN.Ratio.rCut a b) ζ := by
  funext ζ
  rw [sharpCut_eq_rCut]

/-- `∂̄ (sharpCut a b)` is smooth away from the two circles `‖ζ‖ = a`, `‖ζ‖ = b`; it is
smooth everywhere since `sharpCut` is. -/
lemma contDiff_dbarC_sharpCut (a b : ℝ) :
    ContDiff ℝ ∞ (Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b)) := by
  rw [dbarC_sharpCut_eq]
  exact Work.NN.Ratio.contDiff_dbarC_rCut a b

/-- `sharpCut a b` is `C^{k+1}` for every `k`. -/
lemma contDiff_succ_sharpCut (a b : ℝ) (k : ℕ) : ContDiff ℝ (k + 1) (Work.NN.Core.sharpCut a b) := by
  rw [sharpCut_eq_rCut]
  exact (Work.NN.Ratio.contDiff_rCut a b).of_le (by simp)

/-- `∂̄ (sharpCut a b)` is `C^{k+1}` for every `k`. -/
lemma contDiff_succ_dbarC_sharpCut (a b : ℝ) (k : ℕ) :
    ContDiff ℝ (k + 1) (Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b)) := by
  rw [dbarC_sharpCut_eq]
  exact (Work.NN.Ratio.contDiff_dbarC_rCut a b).of_le (by simp)

/-- **The properties of the `∂̄`-derivative of the parametric cutoff `sharpCut a b`.**

`Work.NN.Core.sharpCut a b : ℂ → ℂ` is the smooth cutoff of `Submission/Work/NN/Core/sharpCut.lean`,
equal to `1` on `‖ζ‖ ≤ a` and to `0` for `b ≤ ‖ζ‖` (see `sharpCut_eq_one`, `sharpCut_eq_zero`,
`contDiff_sharpCut`, `norm_sharpCut_le_one` there).  It is the radial function
`sharpCut a b ζ = g (‖ζ‖²)` with `g = Real.smoothTransition ∘ ((b² - ·)/(b² - a²))`.

This assertion collects what the `(0,2)`-telescoping needs about its `∂̄`-derivative
`Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b)`, where
`dbarC u z = (1/2)(fderiv ℝ u z 1 + i · fderiv ℝ u z i)` is the one-variable `∂̄`-operator of
`Submission/Work/CR/Flat/Cauchy.lean` (namespace `Work.CR.Flat`):

* it is smooth (`ContDiff ℝ ∞`, NOT `⊤`: `⊤` would be real analyticity, which fails for a
  compactly supported nonzero function on the connected space `ℂ`; compare
  `Work.CR.Flat.Cauchy.openCut_props_infty`);
* it vanishes where the cutoff is `1` and where it is `0`: for `dbarC` this is
  `(g' (‖ζ‖²) : ℂ) · ζ` with `g' = smoothTransition' (·) · (-(b² - a²)⁻¹)` and
  `smoothTransition'` vanishing at `0` and `1`, so the chain rule gives `0` on both closed regions
  (this also covers the boundary circles `‖ζ‖ = a` and `‖ζ‖ = b`, where the cutoff is *not*
  locally constant);
* its `C^{k,α}`-norm over all of `ℂ` is finite, and so is the one of the cutoff itself.  The
  hypothesis `α ≤ 1` is needed: for `α > 1` the ratio `‖f x - f y‖ / ‖x - y‖^α` diverges as
  `y → x` at points where `f = dbarC (sharpCut a b)` is smooth and nonzero (this happens on the
  open annulus `a < ‖ζ‖ < b`).

The norm bounds follow because both functions are smooth and compactly supported (supported in
`‖ζ‖ ≤ b` and in `a ≤ ‖ζ‖ ≤ b` respectively).  A convenient route is
`Work.CR.Flat.Holder.holderNorm_mono_set` together with a bound on a large ball, or the
`HasCompactSupport` machinery. -/
theorem sharpCut_dbar_props {a b α : ℝ} (ha : 0 < a) (hab : a < b) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ContDiff ℝ ∞ (Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b)) ∧
    (∀ ζ : ℂ, ‖ζ‖ ≤ a → Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) ζ = 0) ∧
    (∀ ζ : ℂ, b ≤ ‖ζ‖ → Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) ζ = 0) ∧
    (∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      Work.CR.Flat.holderNorm k α (Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b)) Set.univ
        ≤ ENNReal.ofReal C) ∧
    (∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      Work.CR.Flat.holderNorm k α (Work.NN.Core.sharpCut a b) Set.univ ≤ ENNReal.ofReal C) := by
  have hHa : (0 : ℝ) ≤ a := ha.le
  have hd : Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b)
      = fun ζ => Work.CR.Flat.dbarC (Work.NN.Ratio.rCut a b) ζ := dbarC_sharpCut_eq a b
  have hc : Work.NN.Core.sharpCut a b = Work.NN.Ratio.rCut a b := sharpCut_eq_rCut a b
  refine ⟨contDiff_dbarC_sharpCut a b, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    rw [hd]
    exact Work.NN.Ratio.dbarC_rCut_eq_zero_of_norm_le hHa hab hζ
  · intro ζ hζ
    rw [hd]
    exact Work.NN.Ratio.dbarC_rCut_eq_zero_of_le_norm hHa hab hζ
  · intro k
    refine exists_pos_ofReal_le_of_ne_top ?_
    rw [hd]
    exact Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport' hα hα1
      ((Work.NN.Ratio.contDiff_dbarC_rCut a b).of_le (by simp))
      (Work.NN.Ratio.hasCompactSupport_dbarC_rCut hHa hab)
  · intro k
    refine exists_pos_ofReal_le_of_ne_top ?_
    rw [hc]
    exact Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport' hα hα1
      ((Work.NN.Ratio.contDiff_rCut a b).of_le (by simp))
      (Work.NN.Ratio.hasCompactSupport_rCut hHa hab)

end Work.NN.Core.TelTwoDF

