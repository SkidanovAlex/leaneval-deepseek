import Mathlib
import Submission.Work.Mostow.BCGDefs

/-!
# Derivatives of the Busemann function and of its gradient (hyperboloid chart)

In the chart `E n = EuclideanSpace ℝ (Fin n)` of ℍⁿ (upper sheet of `x₁² + ⋯ + xₙ² - x_{n+1}² = -1`),
the Busemann function normalised at the origin is

  `busemann ξ y = log (tpart y - ⟪y, ξ⟫)`,   `tpart y = √(1 + ‖y‖²)`,

and its Euclidean gradient is the vector field

  `gradB n ξ y = (tpart y - ⟪y,ξ⟫)⁻¹ • ((tpart y)⁻¹ • y - ξ)`

(this is `gradB` from `Submission.Work.Mostow.BCGDefs`). This file proves that `busemann ξ ·` is
differentiable on all of `E n` with derivative `innerSL ℝ (gradB n ξ y)`, that `gradB n ξ ·` is
differentiable with derivative `hessB n ξ y`, and computes the values of `gradB` and `hessB` at the
origin. Here `ξ` ranges over the boundary sphere `Sph n = {‖ξ‖ = 1}`; the hypothesis `ξ ∈ Sph n`
is exactly what makes the denominators non-zero:

  `tpart y - ⟪y, ξ⟫ ≥ tpart y - ‖y‖ > 0`.

The proof is a straightforward chain-rule computation. The only two facts needed are the
derivative of `tpart` and the chain rule for the inverse of a (nowhere vanishing) scalar function;
both are isolated below as reusable lemmas.
-/

namespace Work.Mostow

open Submission.Mostow
open scoped Real

noncomputable section

/-- `innerSL ℝ` is linear in its first argument (used to reassociate scalar multiples). -/
private theorem innerSL_smul_aux (n : ℕ) (c : ℝ) (v : Submission.Mostow.E n) :
    innerSL ℝ (c • v) = c • innerSL ℝ v := by
  ext h
  simp [innerSL_apply_apply]

/-- The derivative of the chart time coordinate `tpart y = √(1 + ‖y‖²)`: it is `⟪y, ·⟫ / tpart y`. -/
theorem hasFDerivAt_tpart (n : ℕ) (y : Submission.Mostow.E n) :
    HasFDerivAt (fun y : Submission.Mostow.E n => Submission.Mostow.tpart y)
      (innerSL ℝ ((Submission.Mostow.tpart y)⁻¹ • y)) y := by
  have h1 : HasFDerivAt (fun y : E n => 1 + ‖y‖ ^ 2) ((2 : ℝ) • innerSL ℝ y) y := by
    have h := (hasFDerivAt_id (𝕜 := ℝ) y).norm_sq.const_add (1 : ℝ)
    have h2 : (2 • (innerSL ℝ) (id y) ∘SL ContinuousLinearMap.id ℝ (E n)) =
        ((2 : ℝ) • innerSL ℝ y) := by
      ext v
      simp
    rw [h2] at h
    simpa using h
  have h3 := h1.sqrt (by positivity : (1 + ‖y‖ ^ 2) ≠ 0)
  have hderiv : (1 / (2 * √(1 + ‖y‖ ^ 2))) • ((2 : ℝ) • innerSL ℝ y) =
      innerSL ℝ ((tpart y)⁻¹ • y) := by
    rw [innerSL_smul_aux n, smul_smul]
    congr 1
    rw [show √(1 + ‖y‖ ^ 2) = tpart y from rfl]
    field_simp
  rw [hderiv] at h3
  simpa [tpart] using h3

/-- Chain rule for the inverse of a scalar function: `(y ↦ (f y)⁻¹)` has derivative
`-f(x)⁻² • f'`. This is the commutative case of `hasFDerivAt_inv` composed with `hf`. -/
theorem hasFDerivAt_inv_of_ne_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {f' : F →L[ℝ] ℝ} {x : F} (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => (f y)⁻¹) ((-(f x) ^ 2)⁻¹ • f') x := by
  have h0 := hasFDerivAt_inv (𝕜 := ℝ) (x := f x) hx
  have hcomp := h0.comp x hf
  have h1 : (ContinuousLinearMap.toSpanSingleton ℝ (-(f x ^ 2)⁻¹)) ∘SL f' =
      (-(f x ^ 2)⁻¹) • f' := by
    ext v
    simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  rw [h1] at hcomp
  have hfun : ((fun x : ℝ => x⁻¹) ∘ f) = fun y => (f y)⁻¹ := rfl
  have hder : (-(f x ^ 2)⁻¹) • f' = ((-(f x) ^ 2)⁻¹) • f' := by rw [inv_neg]
  rw [hfun, hder] at hcomp
  exact hcomp

/-- `tpart y - ⟪y, ξ⟫ > 0` for `ξ` on the boundary sphere: Cauchy–Schwarz plus
`‖y‖ < √(1+‖y‖²)`. -/
private theorem tpart_sub_inner_pos (n : ℕ) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n) (y : Submission.Mostow.E n) :
    0 < Submission.Mostow.tpart y - inner ℝ y ξ := by
  have hξn : ‖ξ‖ = 1 := by
    rw [Sph, Metric.mem_sphere, dist_eq_norm, sub_zero] at hξ
    exact hξ
  have h1 : inner ℝ y ξ ≤ ‖y‖ * ‖ξ‖ := real_inner_le_norm y ξ
  rw [hξn, mul_one] at h1
  have hts : ‖y‖ < tpart y := by
    rw [tpart, Real.lt_sqrt (norm_nonneg y)]
    linarith [sq_nonneg ‖y‖]
  linarith

/-- `y ↦ ⟪y, ξ⟫` has derivative `innerSL ℝ ξ` (the inner product is symmetric). -/
private theorem hasFDerivAt_inner_right (n : ℕ) (ξ : Submission.Mostow.E n)
    (y : Submission.Mostow.E n) :
    HasFDerivAt (fun y : Submission.Mostow.E n => inner ℝ y ξ) (innerSL ℝ ξ) y := by
  simpa [innerSL_apply_apply, real_inner_comm] using (innerSL ℝ ξ).hasFDerivAt (x := y)

theorem BusemannDeriv (n : ℕ) :
    (∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n → ∀ y : Submission.Mostow.E n,
      HasFDerivAt (fun y => Submission.Mostow.busemann ξ y)
        (innerSL ℝ (Work.Mostow.gradB n ξ y)) y) ∧
    (∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n → ∀ y : Submission.Mostow.E n,
      HasFDerivAt (fun y => Work.Mostow.gradB n ξ y) (Work.Mostow.hessB n ξ y) y) ∧
    (∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n → Work.Mostow.gradB n ξ 0 = -ξ) ∧
    (∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n → ∀ v : Submission.Mostow.E n,
      Work.Mostow.hessB n ξ 0 v = v - (inner ℝ ξ v) • ξ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- derivative of the Busemann function
    intro ξ hξ y
    have hpos := tpart_sub_inner_pos n ξ hξ y
    have hlin : HasFDerivAt (fun y : E n => inner ℝ y ξ) (innerSL ℝ ξ) y :=
      hasFDerivAt_inner_right n ξ y
    have hF := (hasFDerivAt_tpart n y).sub hlin
    have hlog := hF.log (ne_of_gt hpos)
    have hfun : (fun y : E n => busemann ξ y) =
        fun x => Real.log (((fun y : E n => tpart y) - fun y : E n => inner ℝ y ξ) x) := by
      ext x
      simp [busemann]
    have hder : (innerSL ℝ (gradB n ξ y)) =
        (((fun y : E n => tpart y) - fun y : E n => inner ℝ y ξ) y)⁻¹ •
          (innerSL ℝ ((tpart y)⁻¹ • y) - innerSL ℝ ξ) := by
      show innerSL ℝ (gradB n ξ y) = (tpart y - inner ℝ y ξ)⁻¹ •
          (innerSL ℝ ((tpart y)⁻¹ • y) - innerSL ℝ ξ)
      ext h
      simp [gradB, innerSL_apply_apply]
    rw [hfun, hder]
    exact hlog
  · -- derivative of the gradient field `gradB`
    intro ξ hξ y
    obtain ⟨hpos, htpos⟩ : 0 < tpart y - inner ℝ y ξ ∧ 0 < tpart y :=
      ⟨tpart_sub_inner_pos n ξ hξ y, by rw [tpart]; positivity⟩
    have htpart := hasFDerivAt_tpart n y
    have hlin : HasFDerivAt (fun y : E n => inner ℝ y ξ) (innerSL ℝ ξ) y :=
      hasFDerivAt_inner_right n ξ y
    have htp_inv := hasFDerivAt_inv_of_ne_zero (F := E n)
      (f := fun y : E n => tpart y) (f' := innerSL ℝ ((tpart y)⁻¹ • y)) (x := y) htpart (ne_of_gt htpos)
    have h1 := htp_inv.smul (hasFDerivAt_id (𝕜 := ℝ) y)
    have h2 := h1.sub (hasFDerivAt_const ξ y)
    have hg := htpart.sub hlin
    have hginv := hasFDerivAt_inv_of_ne_zero (F := E n)
      (f := fun y : E n => tpart y - inner ℝ y ξ)
      (f' := innerSL ℝ ((tpart y)⁻¹ • y) - innerSL ℝ ξ) (x := y) hg (ne_of_gt hpos)
    have h3 := hginv.smul h2
    convert h3 using 1
    · ext z
      simp [gradB]
    · apply ContinuousLinearMap.ext
      intro v
      simp only [hessB, gradB, ContinuousLinearMap.smulRight_apply, add_apply, sub_apply,
        smul_apply, innerSL_apply_apply, zero_apply, id_eq, Pi.sub_apply, Pi.smul_apply',
        ContinuousLinearMap.id_apply, one_apply_eq_self, real_inner_smul_left, inner_sub_left,
        inv_neg, ← inv_pow]
      module
  · intro ξ hξ
    simp [gradB, tpart, inner_zero_left]
  · intro ξ hξ v
    simp [hessB, gradB, tpart, inner_zero_left, innerSL_apply_apply]

end

end Work.Mostow
