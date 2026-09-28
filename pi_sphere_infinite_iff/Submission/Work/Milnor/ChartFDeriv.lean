import Mathlib
import Submission.Work.Milnor.ChartDefs

/-!
# General second-order `fderiv` lemmas used for the Hessian of `morseChart2`
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace
open TopologicalSpace Set Metric
open Submission.Milnor

namespace Work.Milnor
noncomputable section

/-- **Second-order product rule at a point where both factors vanish to first order.**
If the first derivatives of `f` and `g` vanish at `0`, then the Hessian of `f * g`
at `0` is `f 0 • (Hessian of g) + g 0 • (Hessian of f)`. -/
lemma hasFDerivAt_fderiv_mul_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {Lf Lg : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasFDerivAt f (0 : E →L[ℝ] ℝ) 0) (hg : HasFDerivAt g (0 : E →L[ℝ] ℝ) 0)
    (hf' : HasFDerivAt (fderiv ℝ f) Lf 0) (hg' : HasFDerivAt (fderiv ℝ g) Lg 0)
    (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g) :
    HasFDerivAt (fderiv ℝ (fun x => f x * g x)) (f 0 • Lg + g 0 • Lf) 0 := by
  have hmul : fderiv ℝ (fun x => f x * g x)
      = fun x => f x • fderiv ℝ g x + g x • fderiv ℝ f x := by
    funext x
    exact fderiv_fun_mul (hfd x) (hgd x)
  rw [hmul]
  have h1 : HasFDerivAt (fun x : E => f x • fderiv ℝ g x) (f 0 • Lg) 0 := by
    have h := hf.smul (𝕜' := ℝ) (F := E →L[ℝ] ℝ) hg'
    have hz : (0 : E →L[ℝ] ℝ).smulRight (fderiv ℝ g 0) = 0 :=
      ContinuousLinearMap.zero_smulRight
    rw [hz] at h
    convert h using 1
    · ext x y; simp
    all_goals try rfl
    all_goals simp
  have h2 : HasFDerivAt (fun x : E => g x • fderiv ℝ f x) (g 0 • Lf) 0 := by
    have h := hg.smul (𝕜' := ℝ) (F := E →L[ℝ] ℝ) hf'
    have hz : (0 : E →L[ℝ] ℝ).smulRight (fderiv ℝ f 0) = 0 :=
      ContinuousLinearMap.zero_smulRight
    rw [hz] at h
    convert h using 1
    · ext x y; simp
    all_goals try rfl
    all_goals simp
  convert h1.add h2 using 1
  all_goals try (ext x; rfl)
  all_goals try rfl

/-- The first `fderiv` of `x ↦ f x.1` is `(fderiv f x.1) ∘L fst`. -/
lemma fderiv_comp_fst {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {f : E₁ → ℝ} (hfd : Differentiable ℝ f)
    (x : E₁ × E₂) :
    fderiv ℝ (fun x : E₁ × E₂ => f x.1) x
      = (fderiv ℝ f x.1) ∘L (ContinuousLinearMap.fst ℝ E₁ E₂) := by
  have h2 : HasFDerivAt (f ∘ Prod.fst)
      ((fderiv ℝ f x.1) ∘L (ContinuousLinearMap.fst ℝ E₁ E₂)) x :=
    (hfd x.1).hasFDerivAt.comp x
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ E₁ E₂))
  have h : (fun x : E₁ × E₂ => f x.1) = f ∘ Prod.fst := rfl
  rw [h]
  exact h2.fderiv

/-- The second `fderiv` of `x ↦ f x.1` at `0` is the Hessian of `f` at `0` pulled back by `fst`
in both variables. -/
lemma hasFDerivAt_fderiv_comp_fst {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {f : E₁ → ℝ} {L : E₁ →L[ℝ] E₁ →L[ℝ] ℝ}
    (hf : HasFDerivAt (fderiv ℝ f) L 0) (hfd : Differentiable ℝ f) :
    HasFDerivAt (fderiv ℝ (fun x : E₁ × E₂ => f x.1))
      ((ContinuousLinearMap.compL ℝ (E₁ × E₂) E₁ ℝ).flip (ContinuousLinearMap.fst ℝ E₁ E₂)
          ∘L (L ∘L (ContinuousLinearMap.fst ℝ E₁ E₂))) 0 := by
  have hΦ : fderiv ℝ (fun x : E₁ × E₂ => f x.1)
      = fun x => (fderiv ℝ f x.1) ∘L (ContinuousLinearMap.fst ℝ E₁ E₂) :=
    funext (fderiv_comp_fst hfd)
  rw [hΦ]
  have hΨ : HasFDerivAt (fun L' : E₁ →L[ℝ] ℝ => L' ∘L (ContinuousLinearMap.fst ℝ E₁ E₂))
      ((ContinuousLinearMap.compL ℝ (E₁ × E₂) E₁ ℝ).flip (ContinuousLinearMap.fst ℝ E₁ E₂))
      (fderiv ℝ f 0) :=
    ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.compL ℝ (E₁ × E₂) E₁ ℝ).flip (ContinuousLinearMap.fst ℝ E₁ E₂))
  have h1 : HasFDerivAt (fun x : E₁ × E₂ => fderiv ℝ f x.1)
      (L ∘L (ContinuousLinearMap.fst ℝ E₁ E₂)) 0 :=
    hf.comp (0 : E₁ × E₂)
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ E₁ E₂))
  exact hΨ.comp (0 : E₁ × E₂) h1

/-- The first `fderiv` of `x ↦ f x.2` is `(fderiv f x.2) ∘L snd`. -/
lemma fderiv_comp_snd {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {f : E₂ → ℝ} (hfd : Differentiable ℝ f)
    (x : E₁ × E₂) :
    fderiv ℝ (fun x : E₁ × E₂ => f x.2) x
      = (fderiv ℝ f x.2) ∘L (ContinuousLinearMap.snd ℝ E₁ E₂) := by
  have h2 : HasFDerivAt (f ∘ Prod.snd)
      ((fderiv ℝ f x.2) ∘L (ContinuousLinearMap.snd ℝ E₁ E₂)) x :=
    (hfd x.2).hasFDerivAt.comp x
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ E₁ E₂))
  have h : (fun x : E₁ × E₂ => f x.2) = f ∘ Prod.snd := rfl
  rw [h]
  exact h2.fderiv

/-- The second `fderiv` of `x ↦ f x.2` at `0` is the Hessian of `f` at `0` pulled back by `snd`
in both variables. -/
lemma hasFDerivAt_fderiv_comp_snd {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {f : E₂ → ℝ} {L : E₂ →L[ℝ] E₂ →L[ℝ] ℝ}
    (hf : HasFDerivAt (fderiv ℝ f) L 0) (hfd : Differentiable ℝ f) :
    HasFDerivAt (fderiv ℝ (fun x : E₁ × E₂ => f x.2))
      ((ContinuousLinearMap.compL ℝ (E₁ × E₂) E₂ ℝ).flip (ContinuousLinearMap.snd ℝ E₁ E₂)
          ∘L (L ∘L (ContinuousLinearMap.snd ℝ E₁ E₂))) 0 := by
  have hΦ : fderiv ℝ (fun x : E₁ × E₂ => f x.2)
      = fun x => (fderiv ℝ f x.2) ∘L (ContinuousLinearMap.snd ℝ E₁ E₂) :=
    funext (fderiv_comp_snd hfd)
  rw [hΦ]
  have hΨ : HasFDerivAt (fun L' : E₂ →L[ℝ] ℝ => L' ∘L (ContinuousLinearMap.snd ℝ E₁ E₂))
      ((ContinuousLinearMap.compL ℝ (E₁ × E₂) E₂ ℝ).flip (ContinuousLinearMap.snd ℝ E₁ E₂))
      (fderiv ℝ f 0) :=
    ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.compL ℝ (E₁ × E₂) E₂ ℝ).flip (ContinuousLinearMap.snd ℝ E₁ E₂))
  have h1 : HasFDerivAt (fun x : E₁ × E₂ => fderiv ℝ f x.2)
      (L ∘L (ContinuousLinearMap.snd ℝ E₁ E₂)) 0 :=
    hf.comp (0 : E₁ × E₂)
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ E₁ E₂))
  exact hΨ.comp (0 : E₁ × E₂) h1

end
end Work.Milnor
