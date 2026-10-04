import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The first-order chain rule for `pd` (VarCoef layer)

`Work.Diff.STE.pd i f = fun x ↦ fderiv ℝ f x (Pi.single i 1)` is the `i`-th partial derivative
(directional derivative along `eᵢ`).  This file proves the chain rule

`∂ᵢ (g ∘ σ) = ∑_a (∂ᵢ σ_a) · (∂_a g) ∘ σ`,

i.e.

`pd i (fun z => g (σ z)) = fun z => ∑ a, ((pdR i (fun z => σ z a) z : ℝ) : ℂ) * pd a g (σ z)`

for smooth `g : (ι → ℝ) → ℂ` and smooth `σ : (ι → ℝ) → (ι → ℝ)`.

The proof is the usual one: `fderiv_comp` writes the derivative of the composite as a composition
of continuous linear maps, and the derivative of `g` at a point is expanded in the standard basis
`Pi.single a 1` of `ι → ℝ`.
-/

namespace Work.Diff.STE.B3.VarCoef

/-- Evaluation of a continuous linear map `F : (ι → ℝ) →L[ℝ] ℂ` on a vector `v` in the standard
basis `Pi.single a 1` of `ι → ℝ`. -/
private lemma pd_comp_chain_apply_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) →L[ℝ] ℂ) (v : ι → ℝ) :
    F v = ∑ a, ((v a : ℝ) : ℂ) * F (Pi.single a 1) := by
  conv_lhs => rw [show v = ∑ a, v a • Pi.single a 1 from by
    funext b
    rw [Finset.sum_apply, Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp only [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hx), smul_zero]
    · intro hb; exact absurd (Finset.mem_univ b) hb]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, Complex.real_smul]

/-- The `a`-th coordinate of the directional derivative of `σ` along `eᵢ` is the `i`-th partial
derivative of the `a`-th component of `σ`. -/
private lemma pd_comp_chain_pdR {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : (ι → ℝ) → (ι → ℝ)) (z : ι → ℝ) (hσ : DifferentiableAt ℝ σ z) (i a : ι) :
    Work.Diff.STE.pdR i (fun z => σ z a) z = (fderiv ℝ σ z (Pi.single i 1)) a := by
  have h : fderiv ℝ (fun z => σ z a) z = ContinuousLinearMap.proj a ∘SL fderiv ℝ σ z :=
    fderiv_apply hσ a
  simp only [Work.Diff.STE.pdR]
  rw [h, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem pd_comp_chain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (σ : (ι → ℝ) → (ι → ℝ)) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (i : ι) :
    Work.Diff.STE.pd i (fun z => g (σ z))
      = fun z => ∑ a, ((Work.Diff.STE.pdR i (fun z => σ z a) z : ℝ) : ℂ)
          * Work.Diff.STE.pd a g (σ z) := by
  funext z
  have hdg : DifferentiableAt ℝ g (σ z) := (ContDiff.contDiffAt hg).differentiableAt (by simp)
  have hdσ : DifferentiableAt ℝ σ z := (ContDiff.contDiffAt hσ).differentiableAt (by simp)
  have hcomp : fderiv ℝ (fun z => g (σ z)) z
      = (fderiv ℝ g (σ z)).comp (fderiv ℝ σ z) := fderiv_comp z hdg hdσ
  simp only [Work.Diff.STE.pd]
  rw [hcomp, ContinuousLinearMap.comp_apply]
  rw [pd_comp_chain_apply_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [pd_comp_chain_pdR σ z hdσ]

end Work.Diff.STE.B3.VarCoef
