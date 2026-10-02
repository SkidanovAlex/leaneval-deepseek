import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Sobolev.dzbar_mul
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `∂̄` of the Cauchy-type kernel `w ↦ w̄ / (‖w‖² + ε²)`

The subproject computes the `∂̄`-derivative of the standard mollifying kernel
`w ↦ w̄ / (‖w‖² + ε²)` used in the Cauchy-transform argument of the Mandelbar
development.  In `Submission/Work/MRMT/Basic.lean` the Wirtinger derivative `∂̄` is
read off from the real Fréchet derivative, so the relevant general facts are the
quotient rule for `∂̄` (proved here on top of the pointwise Leibniz rule
`Work.MRMT.Sobolev.dzbar_mul`) and the derivative of the pointwise inverse.
-/

namespace Work.MRMT.Cauchy

open Complex

/-- `∂̄` does not see additive constants. -/
lemma dzbar_add_const (f : ℂ → ℂ) (c : ℂ) (z : ℂ) :
    Work.MRMT.dzbar (fun w => f w + c) z = Work.MRMT.dzbar f z := by
  simp only [Work.MRMT.dzbar, fderiv_add_const]

/-- `∂̄` of a pointwise inverse: `∂̄ (w ↦ (g w)⁻¹) z = -(g z)⁻² · ∂̄ g z`.

This is the composite of the Fréchet derivative of inversion
(`hasFDerivAt_inv'`, whose derivative at `x` is `-mulLeftRight ℝ ℂ x⁻¹ x⁻¹`) with the
chain rule, transported back through the definition of `∂̄`. -/
lemma dzbar_inv_comp (g : ℂ → ℂ) (z : ℂ) (hg : DifferentiableAt ℝ g z) (hz : g z ≠ 0) :
    Work.MRMT.dzbar (fun w => (g w)⁻¹) z = -((g z)⁻¹) ^ 2 * Work.MRMT.dzbar g z := by
  have hfde : fderiv ℝ (fun w => (g w)⁻¹) z
      = (-ContinuousLinearMap.mulLeftRight ℝ ℂ (g z)⁻¹ (g z)⁻¹).comp (fderiv ℝ g z) :=
    ((hasFDerivAt_inv' (𝕜 := ℝ) (R := ℂ) hz).comp z hg.hasFDerivAt).fderiv
  simp only [Work.MRMT.dzbar, hfde, ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  ring

/-- The `∂̄`-quotient rule: `∂̄(f/g) = (∂̄f · g - f · ∂̄g) / g²` away from the zeros of `g`. -/
lemma dzbar_div {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hz : g z ≠ 0) :
    Work.MRMT.dzbar (fun w => f w / g w) z
      = (Work.MRMT.dzbar f z * g z - f z * Work.MRMT.dzbar g z) / (g z) ^ 2 := by
  have hgi : DifferentiableAt ℝ (fun w => (g w)⁻¹) z := hg.inv hz
  have hmul : Work.MRMT.dzbar (fun w => f w * (g w)⁻¹) z
      = f z * Work.MRMT.dzbar (fun w => (g w)⁻¹) z + (g z)⁻¹ * Work.MRMT.dzbar f z :=
    Work.MRMT.Sobolev.dzbar_mul hf hgi
  have hdiv : (fun w => f w / g w) = (fun w => f w * (g w)⁻¹) := by
    funext w; rw [div_eq_mul_inv]
  rw [hdiv, hmul, dzbar_inv_comp g z hg hz]
  field_simp
  ring

/-- `∂̄` of `w ↦ w̄ w`: since `w̄ w = ‖w‖²` is real-valued, `∂̄(w̄w) = w`. -/
lemma dzbar_star_mul_self (w : ℂ) : Work.MRMT.dzbar (fun u : ℂ => star u * u) w = w := by
  change Work.MRMT.dzbar (fun u : ℂ => star u * id u) w = w
  rw [Work.MRMT.Sobolev.dzbar_mul (f := fun u : ℂ => star u) (g := id)
      (Work.MRMT.Wirtinger.differentiableAt_star w) differentiableAt_id,
      Work.MRMT.Wirtinger.dzbar_star, Work.MRMT.dzbar_id]
  simp

/-- `w ↦ w⁻¹` is not real differentiable at `0` (it is not even continuous there). -/
lemma not_differentiableAt_inv_zero : ¬ DifferentiableAt ℝ (fun w : ℂ => w⁻¹) 0 := by
  intro hd
  have h1 : DifferentiableAt ℝ (fun t : ℝ => ((t : ℂ))⁻¹) 0 :=
    DifferentiableAt.comp (0 : ℝ) hd Complex.ofRealCLM.differentiableAt
  have heq : (fun t : ℝ => ((t : ℂ))⁻¹) = (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) := by
    funext t; exact (Complex.ofReal_inv t).symm
  rw [heq] at h1
  have h := Complex.reCLM.differentiableAt.comp (0 : ℝ) h1
  have hfun : (⇑Complex.reCLM ∘ fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) = fun t : ℝ => t⁻¹ := by
    funext t; simp [Complex.reCLM_apply]
  rw [hfun] at h
  exact (differentiableAt_inv_iff (𝕜 := ℝ) (x := 0)).mp h rfl

theorem dzbar_star_div_normSq_add (ε : ℝ) (z : ℂ) :
    Work.MRMT.dzbar (fun w : ℂ => star w / ((‖w‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) z
      = (ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2 := by
  -- Rewrite the real-valued denominator `‖w‖² + ε²` as the complex polynomial `w̄ w + ε²`.
  have hden : ∀ w : ℂ, ((‖w‖ ^ 2 + ε ^ 2 : ℝ) : ℂ) = star w * w + (ε : ℂ) ^ 2 := by
    intro w
    rw [Complex.ofReal_add, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_pow, Complex.star_def]
  by_cases hC : star z * z + (ε : ℂ) ^ 2 = 0
  · -- Exceptional case: the denominator vanishes, which forces `z = 0` and `ε = 0`.
    -- There the function is `w ↦ w⁻¹`, which is not differentiable at `0`, so `∂̄` takes
    -- its junk value `0`, and the right-hand side is `0 / 0 = 0`.
    have hcast : ((Complex.normSq z + ε ^ 2 : ℝ) : ℂ) = star z * z + (ε : ℂ) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact hden z
    have hsum : Complex.normSq z + ε ^ 2 = 0 := by
      have : ((Complex.normSq z + ε ^ 2 : ℝ) : ℂ) = 0 := by rw [hcast, hC]
      exact Complex.ofReal_eq_zero.mp this
    have hz : z = 0 :=
      Complex.normSq_eq_zero.mp (by linarith [Complex.normSq_nonneg z, sq_nonneg ε])
    have hε : ε = 0 := by
      have h2 : ε ^ 2 = 0 := by linarith [Complex.normSq_nonneg z, sq_nonneg ε]
      exact sq_eq_zero_iff.mp h2
    subst hz
    subst hε
    have hG : (fun w : ℂ => star w / ((‖w‖ ^ 2 + (0 : ℝ) ^ 2 : ℝ) : ℂ))
        = (fun w : ℂ => w⁻¹) := by
      funext w
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
      rw [Complex.inv_def, Complex.star_def, ← Complex.normSq_eq_norm_sq, div_eq_mul_inv,
        Complex.ofReal_inv]
    rw [hG, Work.MRMT.dzbar,
      fderiv_zero_of_not_differentiableAt not_differentiableAt_inv_zero]
    simp
  · -- Generic case: apply the quotient rule to `w̄ / (w̄ w + ε²)`.
    have hfun : (fun w : ℂ => star w / ((‖w‖ ^ 2 + ε ^ 2 : ℝ) : ℂ))
        = fun w : ℂ => star w / (star w * w + (ε : ℂ) ^ 2) := by
      funext w; rw [hden w]
    rw [hfun, hden z]
    have hD : DifferentiableAt ℝ (fun w : ℂ => star w * w + (ε : ℂ) ^ 2) z :=
      ((Work.MRMT.Wirtinger.differentiableAt_star z).mul differentiableAt_id).add_const _
    have hstar : DifferentiableAt ℝ (star : ℂ → ℂ) z :=
      Work.MRMT.Wirtinger.differentiableAt_star z
    rw [dzbar_div hstar hD hC]
    have hCz : Work.MRMT.dzbar (fun w : ℂ => star w * w + (ε : ℂ) ^ 2) z = z := by
      rw [dzbar_add_const, dzbar_star_mul_self]
    rw [hCz, Work.MRMT.Wirtinger.dzbar_star]
    ring

end Work.MRMT.Cauchy
