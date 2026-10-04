import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarDef
import Submission.Work.Diff.STE.B3.VarCoef.mulOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.pdOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.commMulPd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The difference of `varLap A B` and its formal adjoint `varLapStar A B`

`varLap A B g = -(Σ_{ab} A_ab · ∂_a∂_b g + Σ_a B_a · ∂_a g)` and
`varLapStar A B g = -(Σ_{ab} ∂_a∂_b (A_ab · g) + Σ_a ∂_a (B_a · g))` differ by an operator of
order one: expanding the two-step Leibniz rule

`∂_a∂_b (A_ab · g) = A_ab · ∂_a∂_b g + (∂_a A_ab)·∂_b g + (∂_b A_ab)·∂_a g + (∂_a∂_b A_ab)·g`

and the one-step rule `∂_a (B_a · g) = B_a · ∂_a g + (∂_a B_a)·g` the leading second-order terms
cancel and one is left with

`varLap A B g - varLapStar A B g
   = Σ_{ab} [ (∂_a A_ab)·∂_b g + (∂_b A_ab)·∂_a g + (∂_a∂_b A_ab)·g ] + Σ_a (∂_a B_a)·g`.

This file holds the *vocabulary* of that computation:

* `cm` — the complexification of a real-valued function, and the two Leibniz rules for `∂ᵢ` in the
  presence of the complexification (`pd_cm`, `pd_cm_mul`, `pd_pd_cm_mul`);
* `crossFun`, `lowFun`, `varLapDiffFun` — the pointwise right-hand side above;
* `varLapDiffModel` — the same right-hand side assembled as an operator in the `Op` calculus of
  `VarCoef/OpOrder.lean`, together with the (definitional) identification
  `varLapDiffModel_apply` with `varLapDiffFun`.

The order estimate `IsOrd 1 C (varLapDiffModel A B)` and the pointwise identity with
`varLapOp A B - varLapStarOp A B` are proved in the files that import this one.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The complexification of a real-valued function -/

/-- The complexification of a real-valued function. -/
def cm (m : (ι → ℝ) → ℝ) : (ι → ℝ) → ℂ := fun x => ((m x : ℝ) : ℂ)

theorem cm_apply (m : (ι → ℝ) → ℝ) (x : ι → ℝ) : cm m x = ((m x : ℝ) : ℂ) := rfl

theorem contDiff_cm {m : (ι → ℝ) → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) :
    ContDiff ℝ (⊤ : ℕ∞) (cm m) := Complex.ofRealCLM.contDiff.comp hm

theorem differentiable_cm {m : (ι → ℝ) → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) :
    Differentiable ℝ (cm m) := (contDiff_cm hm).differentiable (by simp)

/-- **The partial derivative commutes with complexification** (no differentiability hypothesis:
both sides are the junk value `0` where `m` is not differentiable). -/
theorem pd_cm (i : ι) (m : (ι → ℝ) → ℝ) :
    Work.Diff.STE.pd i (cm m) = cm (Work.Diff.STE.pdR i m) := by
  funext x
  show (fderiv ℝ (fun y : ι → ℝ => ((m y : ℝ) : ℂ)) x) (Pi.single i 1)
      = ((fderiv ℝ m x) (Pi.single i 1) : ℂ)
  have hcomp : (fun y : ι → ℝ => ((m y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ m := by
    funext y
    exact (Complex.ofRealCLM_apply (m y)).symm
  by_cases hm : DifferentiableAt ℝ m x
  · rw [hcomp]
    have h := (Complex.ofRealCLM.hasFDerivAt (x := m x)).comp x hm.hasFDerivAt
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  · have hm' : ¬ DifferentiableAt ℝ (fun y : ι → ℝ => ((m y : ℝ) : ℂ)) x := by
      intro h
      refine hm ?_
      have h2 := Complex.reCLM.differentiableAt.comp x h
      simpa [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using h2
    rw [fderiv_zero_of_not_differentiableAt hm, fderiv_zero_of_not_differentiableAt hm']
    simp

/-! ## 2. The Leibniz rules, at the level of functions -/

/-- Additivity of `∂ᵢ` on differentiable functions (function level). -/
theorem pd_add (i : ι) {f g : (ι → ℝ) → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    Work.Diff.STE.pd i (f + g) = Work.Diff.STE.pd i f + Work.Diff.STE.pd i g := by
  funext x
  have h := fderiv_add (hf x) (hg x)
  have h2 : (fderiv ℝ (f + g) x) (Pi.single i 1)
      = (fderiv ℝ f x) (Pi.single i 1) + (fderiv ℝ g x) (Pi.single i 1) := by
    rw [h]; simp
  simpa [Work.Diff.STE.pd] using h2

/-- The Leibniz rule for `∂ᵢ` on differentiable functions (function level). -/
theorem pd_mul (i : ι) {f g : (ι → ℝ) → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    Work.Diff.STE.pd i (f * g) = f * Work.Diff.STE.pd i g + g * Work.Diff.STE.pd i f := by
  funext x
  have h := fderiv_mul (hf x) (hg x)
  have h2 : (fderiv ℝ (f * g) x) (Pi.single i 1)
      = f x * ((fderiv ℝ g x) (Pi.single i 1))
        + g x * ((fderiv ℝ f x) (Pi.single i 1)) := by
    rw [h]; simp [smul_eq_mul]
  simpa [Work.Diff.STE.pd] using h2

/-- **The Leibniz rule for a complexified multiplier.** -/
theorem pd_cm_mul (i : ι) {m : (ι → ℝ) → ℝ} {f : (ι → ℝ) → ℂ}
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Work.Diff.STE.pd i (cm m * f)
      = cm m * Work.Diff.STE.pd i f + cm (Work.Diff.STE.pdR i m) * f := by
  rw [pd_mul i (differentiable_cm hm) (hf.differentiable (by simp)), pd_cm i m]
  funext x
  simp only [Pi.mul_apply, Pi.add_apply, cm]
  ring

/-- **The two-step Leibniz rule**: the second derivative of `cm m · f` split into the "leading"
term and the three remaining ones. -/
theorem pd_pd_cm_mul (a b : ι) {m : (ι → ℝ) → ℝ} {f : (ι → ℝ) → ℂ}
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Work.Diff.STE.pd a (Work.Diff.STE.pd b (cm m * f))
      = cm m * Work.Diff.STE.pd a (Work.Diff.STE.pd b f)
        + ((cm (Work.Diff.STE.pdR a m) * Work.Diff.STE.pd b f
              + cm (Work.Diff.STE.pdR b m) * Work.Diff.STE.pd a f)
            + cm (Work.Diff.STE.pdR a (Work.Diff.STE.pdR b m)) * f) := by
  have hb : Work.Diff.STE.pd b (cm m * f)
      = cm m * Work.Diff.STE.pd b f + cm (Work.Diff.STE.pdR b m) * f :=
    pd_cm_mul b hm hf
  rw [hb]
  have hd1 : Differentiable ℝ (cm m * Work.Diff.STE.pd b f) :=
    ((contDiff_cm hm).mul (pd_contDiff_top hf b)).differentiable (by simp)
  have hd2 : Differentiable ℝ (cm (Work.Diff.STE.pdR b m) * f) :=
    ((contDiff_cm (pdR_contDiff hm b)).mul hf).differentiable (by simp)
  rw [pd_add a hd1 hd2,
    pd_cm_mul a hm (pd_contDiff_top hf b),
    pd_cm_mul a (pdR_contDiff hm b) hf]
  funext x
  simp only [Pi.mul_apply, Pi.add_apply, cm]
  ring

/-! ## 3. The pointwise model of the difference -/

/-- The "cross" part of `varLap A B - varLapStar A B`: the terms in which at least one derivative
falls on the coefficient. -/
def crossFun (A : ι → ι → (ι → ℝ) → ℝ) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  ∑ a, ∑ b, ((cm (Work.Diff.STE.pdR a (A a b)) * Work.Diff.STE.pd b f
        + cm (Work.Diff.STE.pdR b (A a b)) * Work.Diff.STE.pd a f)
      + cm (Work.Diff.STE.pdR a (Work.Diff.STE.pdR b (A a b))) * f)

/-- The first-order part of `varLap A B - varLapStar A B` coming from `B`. -/
def lowFun (B : ι → (ι → ℝ) → ℝ) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  ∑ a, cm (Work.Diff.STE.pdR a (B a)) * f

/-- The pointwise model of `varLap A B - varLapStar A B`. -/
def varLapDiffFun (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ := crossFun A f + lowFun B f

/-- The operator model of `varLap A B - varLapStar A B` in the order calculus. -/
def varLapDiffModel (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) : Op ι :=
  (∑ a, ∑ b, ((compOp (mulOp (Work.Diff.STE.pdR a (A a b))) (pdOp b)
          + compOp (mulOp (Work.Diff.STE.pdR b (A a b))) (pdOp a))
        + mulOp (Work.Diff.STE.pdR a (Work.Diff.STE.pdR b (A a b)))))
    + ∑ a, mulOp (Work.Diff.STE.pdR a (B a))

/-- The operator model evaluated at a function is the pointwise model. -/
theorem varLapDiffModel_apply (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (f : (ι → ℝ) → ℂ) :
    varLapDiffModel A B f = varLapDiffFun A B f := by
  funext x
  simp only [varLapDiffModel, varLapDiffFun, crossFun, lowFun, compOp_apply, mulOp, pdOp,
    finset_sumOp_apply, Finset.sum_apply, Pi.add_apply, Pi.mul_apply, cm]

end Work.Diff.STE.B3.VarCoef
