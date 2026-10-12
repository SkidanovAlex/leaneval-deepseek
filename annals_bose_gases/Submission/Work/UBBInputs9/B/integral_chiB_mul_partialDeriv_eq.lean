import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.integral_chiB_mul_partialDeriv_eq`

The exact `u`-averaged "first-moment" identity for the sliding window

    `chiB ℓ d u x = χ(x/ℓ)·χ(x/(ℓd) − u) = chiScale ℓ x · chiScale (ℓd) (x − (ℓd)•u)`

of the `dℓ`-infra layer (`Submission.Work.DLInfra`), FS `eq:chiBdefinition`:

    `∫_u chiB ℓ d u x · ∂_k chiB ℓ d u (x) du = chiScale ℓ x · ∂_k chiScale ℓ (x)`.

## Why it is true

Write `s := ℓ·d`, `w := s⁻¹ • x`.  Since `chiScale s y = χ(s⁻¹ • y)` and `χ` is even, the
second factor of `chiB` is a *pure translation* in `u`:

    `chiScale s (x − s•u) = χ(w − u)`   and   `∂_k chiScale s (x − s•u) = s⁻¹ (∂_k χ)(w − u)`.

The product rule for `chiB` therefore gives, with `A := chiScale ℓ x`,
`A' := ∂_k chiScale ℓ (x)`, `B(u) := χ(w−u)`, `∂B(u) := (∂_k χ)(w − u)`,

    `chiB · ∂_k chiB = A·A'·B(u)² + (A²/s)·B(u)·∂B(u)`,

so the `u`-integral splits (translation invariance `∫_u G(w−u) du = ∫_v G(v) dv`) into

    `A·A'·∫_v χ(v)² dv + (A²/s)·∫_v χ(v)(∂_k χ)(v) dv = A·A'·1 + (A²/s)·0`,

using the `L²`-normalisation `∫χ² = 1` (`CubicChi.chi_L2`) and the **oddness** of
`v ↦ χ(v)(∂_k χ)(v)` (the derivative of an even function is odd, `chi_even`), whose integral
vanishes (`MeasureTheory.integral_neg_eq_self`).

## Contents

* `ChiDeriv` — the small calculus package: the rescaling rule for `fderiv chiScale`, the
  translation rule `y ↦ chiScale s (y − c)`, the product rule for `chiB`, the oddness of
  `∂_k χ` and the vanishing integral of an odd function;
* `integral_chiB_mul_partialDeriv_eq` — the target identity.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real

namespace Work.UBBInputs9.B

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! ## The calculus package `ChiDeriv` -/

namespace ChiDeriv

/-- `chiScale s = χ(s⁻¹ • ·)` is `C^∞` for **every** real `s` (no `s ≠ 0` needed: the
rescaling is a continuous linear map, and `χ` is smooth; at `s = 0` the map is the constant
`χ 0`). -/
lemma chiScale_contDiff_any (s : ℝ) : ContDiff ℝ ∞ (chiScale s) := by
  unfold chiScale
  exact chi_contDiff.comp (ContinuousLinearMap.contDiff ((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³))

/-- **Rescaling rule for the gradient of the cutoff**: `d(χ_s)_x(v) = s⁻¹ · dχ_{s⁻¹•x}(v)`. -/
lemma fderiv_chiScale_apply (s : ℝ) (x v : ℝ³) :
    fderiv ℝ (chiScale s) x v = s⁻¹ * fderiv ℝ chi (s⁻¹ • x) v := by
  have hchi : DifferentiableAt ℝ chi (s⁻¹ • x) := chi_contDiff.differentiable (by norm_num) _
  have hlin : HasFDerivAt (fun y : ℝ³ => s⁻¹ • y) (s⁻¹ • ContinuousLinearMap.id ℝ ℝ³) x :=
    (hasFDerivAt_id x).const_smul (s⁻¹)
  have hcomp : HasFDerivAt (chi ∘ fun y : ℝ³ => s⁻¹ • y)
      ((fderiv ℝ chi (s⁻¹ • x)) ∘SL (s⁻¹ • ContinuousLinearMap.id ℝ ℝ³)) x :=
    hchi.hasFDerivAt.comp x hlin
  have hfun : chiScale s = (chi ∘ fun y : ℝ³ => s⁻¹ • y) := rfl
  rw [hfun, hcomp.fderiv, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- **Translation rule**: the derivative of the translated cutoff `y ↦ chiScale s (y − c)` is
the derivative of `chiScale s` at the translated point (the shift has derivative the identity). -/
lemma fderiv_chiScale_comp_sub_const (s : ℝ) (c x v : ℝ³) :
    fderiv ℝ (fun y : ℝ³ => chiScale s (y - c)) x v = fderiv ℝ (chiScale s) (x - c) v := by
  have hlin : HasFDerivAt (fun y : ℝ³ => y - c) (ContinuousLinearMap.id ℝ ℝ³) x :=
    hasFDerivAt_sub_const c
  have hcomp : HasFDerivAt (chiScale s ∘ fun y : ℝ³ => y - c)
      ((fderiv ℝ (chiScale s) (x - c)) ∘SL (ContinuousLinearMap.id ℝ ℝ³)) x :=
    ((chiScale_contDiff_any s).differentiable (by norm_num) (x - c)).hasFDerivAt.comp x hlin
  have hfun : (fun y : ℝ³ => chiScale s (y - c)) = (chiScale s ∘ fun y : ℝ³ => y - c) := rfl
  rw [hfun, hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]

/-- **The product rule for the sliding window**: with `s := ℓ·d` (written out as `ℓ * d`),
`chiB ℓ d u = chiScale ℓ · chiScale (ℓd)(· − (ℓd)•u)`, so

    `∂_k chiB ℓ d u (x) = chiScale ℓ x · ∂_k chiScale (ℓd) (x − (ℓd)•u)
        + chiScale (ℓd) (x − (ℓd)•u) · ∂_k chiScale ℓ (x)`. -/
lemma fderiv_chiB_apply (ℓ d : ℝ) (u x v : ℝ³) :
    fderiv ℝ (fun y : ℝ³ => chiB ℓ d u y) x v
      = chiScale ℓ x * fderiv ℝ (chiScale (ℓ * d)) (x - (ℓ * d) • u) v
        + chiScale (ℓ * d) (x - (ℓ * d) • u) * fderiv ℝ (chiScale ℓ) x v := by
  have hdiff1 : DifferentiableAt ℝ (chiScale ℓ) x :=
    (chiScale_contDiff_any ℓ).differentiable (by norm_num) x
  have hdiff2 : DifferentiableAt ℝ (fun y : ℝ³ => chiScale (ℓ * d) (y - (ℓ * d) • u)) x := by
    have h1 : (fun y : ℝ³ => chiScale (ℓ * d) (y - (ℓ * d) • u))
        = chiScale (ℓ*d) ∘ (fun y : ℝ³ => y - (ℓ*d) • u) := rfl
    rw [h1]
    exact ((chiScale_contDiff_any (ℓ*d)).differentiable (by norm_num) _).comp x (by fun_prop)
  have hfd : fderiv ℝ (fun y : ℝ³ => chiB ℓ d u y) x
      = chiScale ℓ x • fderiv ℝ (fun y : ℝ³ => chiScale (ℓ * d) (y - (ℓ * d) • u)) x
        + (fun y : ℝ³ => chiScale (ℓ * d) (y - (ℓ * d) • u)) x • fderiv ℝ (chiScale ℓ) x := by
    show fderiv ℝ (chiScale ℓ * fun y : ℝ³ => chiScale (ℓ * d) (y - (ℓ * d) • u)) x = _
    exact fderiv_mul hdiff1 hdiff2
  rw [hfd, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
    fderiv_chiScale_comp_sub_const]

/-- The second factor of `chiB` is the *translate* of `χ`: for `s ≠ 0`,
`chiScale s (x − s•u) = χ(s⁻¹ • x − u)`. -/
lemma chiScale_sub_smul_eq (s : ℝ) (hs : s ≠ 0) (x u : ℝ³) :
    chiScale s (x - s • u) = chi (s⁻¹ • x - u) := by
  rw [chiScale, smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- **The derivative of an even function is odd**: `∂_k χ (−v) = − ∂_k χ (v)`, from the chain
rule for negation and `chi_even`. -/
lemma fderiv_chi_neg_apply (v e : ℝ³) : fderiv ℝ chi (-v) e = - fderiv ℝ chi v e := by
  have hneg : HasFDerivAt (fun y : ℝ³ => -y) (-(ContinuousLinearMap.id ℝ ℝ³)) v :=
    (hasFDerivAt_id v).neg
  have hchi : HasFDerivAt chi (fderiv ℝ chi (-v)) (-v) :=
    (chi_contDiff.differentiable (by norm_num) (-v)).hasFDerivAt
  have hcomp : HasFDerivAt (chi ∘ fun y : ℝ³ => -y)
      ((fderiv ℝ chi (-v)) ∘SL (-(ContinuousLinearMap.id ℝ ℝ³))) v := hchi.comp v hneg
  have hcoe : chi ∘ (fun y : ℝ³ => -y) = chi := by funext y; exact chi_even y
  have h2 : HasFDerivAt chi ((fderiv ℝ chi (-v)) ∘SL (-(ContinuousLinearMap.id ℝ ℝ³))) v :=
    hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => (congrFun hcoe y).symm))
  have h3 : fderiv ℝ chi v = (fderiv ℝ chi (-v)) ∘SL (-(ContinuousLinearMap.id ℝ ℝ³)) := h2.fderiv
  have h4 : fderiv ℝ chi v e = - (fderiv ℝ chi (-v) e) := by
    rw [h3, ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg]
  linarith

/-- The integral of an odd function on `ℝ³` vanishes (negation-invariance of Lebesgue
measure: `∫ F = ∫ F ∘ (−·) = −∫ F`). -/
lemma integral_odd_eq_zero (F : ℝ³ → ℝ) (hF : ∀ v, F (-v) = - F v) :
    (∫ v : ℝ³, F v) = 0 := by
  have h1 : (∫ v : ℝ³, F (-v)) = - (∫ v : ℝ³, F v) := by
    have hcongr : (∫ v : ℝ³, F (-v)) = ∫ v : ℝ³, -F v :=
      integral_congr_ae (Filter.Eventually.of_forall hF)
    rw [hcongr, MeasureTheory.integral_neg]
  have h2 : (∫ v : ℝ³, F (-v)) = (∫ v : ℝ³, F v) := MeasureTheory.integral_neg_eq_self F volume
  linarith

/-- `v ↦ χ v · ∂_k χ (v)` is odd — the integrand whose vanishing integral produces the
`(A²/s)`-term. -/
lemma odd_chi_mul_fderiv_chi (e : ℝ³) :
    ∀ v : ℝ³, chi (-v) * fderiv ℝ chi (-v) e = - (chi v * fderiv ℝ chi v e) := by
  intro v
  rw [chi_even, fderiv_chi_neg_apply]
  ring

end ChiDeriv

/-! ## The target identity -/

theorem integral_chiB_mul_partialDeriv_eq (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d)
    (x : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiB ℓ d u x *
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB ℓ d u y) x
          (Submission.BoseGases.kcStdBasis k)))
      = Submission.BoseGases.chiScale ℓ x *
        (fderiv ℝ (Submission.BoseGases.chiScale ℓ) x (Submission.BoseGases.kcStdBasis k)) := by
  have hld : ℓ * d ≠ 0 := mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)
  -- pointwise: the integrand is `c₁·χ(w−u)² + c₂·χ(w−u)·∂χ(w−u)` with `w = (ℓd)⁻¹ • x`
  have hpt : ∀ u : ℝ³, chiB ℓ d u x * (fderiv ℝ (fun y : ℝ³ => chiB ℓ d u y) x (kcStdBasis k))
      = (chiScale ℓ x * fderiv ℝ (chiScale ℓ) x (kcStdBasis k)) * (chi ((ℓ*d)⁻¹ • x - u))^2
        + (chiScale ℓ x^2 * (ℓ*d)⁻¹) *
            (chi ((ℓ*d)⁻¹ • x - u) * fderiv ℝ chi ((ℓ*d)⁻¹ • x - u) (kcStdBasis k)) := by
    intro u
    have hB : chiScale (ℓ * d) (x - (ℓ * d) • u) = chi ((ℓ*d)⁻¹ • x - u) :=
      ChiDeriv.chiScale_sub_smul_eq (ℓ*d) hld x u
    have hB' : fderiv ℝ (chiScale (ℓ * d)) (x - (ℓ * d) • u) (kcStdBasis k)
        = (ℓ*d)⁻¹ * fderiv ℝ chi ((ℓ*d)⁻¹ • x - u) (kcStdBasis k) := by
      rw [ChiDeriv.fderiv_chiScale_apply]
      have hw : (ℓ*d)⁻¹ • (x - (ℓ*d)•u) = (ℓ*d)⁻¹ • x - u := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hld, one_smul]
      rw [hw]
    have hBx : chiB ℓ d u x = chiScale ℓ x * chi ((ℓ*d)⁻¹ • x - u) := by
      rw [chiB, hB]
    rw [ChiDeriv.fderiv_chiB_apply ℓ d u x (kcStdBasis k), hB, hB', hBx]
    ring
  have hF1_intble : Integrable (fun v : ℝ³ => (chi v)^2) volume := by
    have hcs : HasCompactSupport (fun v : ℝ³ => (chi v)^2) := by
      refine HasCompactSupport.mono chi_hasCompactSupport ?_
      intro v hv
      exact fun h => hv (by simp [h])
    exact chi_contDiff.continuous.pow 2 |>.integrable_of_hasCompactSupport hcs
  have hF2_intble : Integrable (fun v : ℝ³ => chi v * fderiv ℝ chi v (kcStdBasis k)) volume := by
    have hcont : Continuous (fun v : ℝ³ => fderiv ℝ chi v (kcStdBasis k)) :=
      (chi_contDiff.continuous_fderiv_apply (by norm_num)).comp
        (Continuous.prodMk_left (kcStdBasis k))
    have hcs : HasCompactSupport (fun v : ℝ³ => chi v * fderiv ℝ chi v (kcStdBasis k)) := by
      refine HasCompactSupport.mono chi_hasCompactSupport ?_
      intro v hv
      exact fun h => hv (by simp [h])
    exact (chi_contDiff.continuous.mul hcont).integrable_of_hasCompactSupport hcs
  have hF1_int : (∫ v : ℝ³, (chi v)^2) = 1 := chi_L2
  have hF2_int : (∫ v : ℝ³, chi v * fderiv ℝ chi v (kcStdBasis k)) = 0 :=
    ChiDeriv.integral_odd_eq_zero _ (ChiDeriv.odd_chi_mul_fderiv_chi (kcStdBasis k))
  set c₁ : ℝ := chiScale ℓ x * fderiv ℝ (chiScale ℓ) x (kcStdBasis k) with hc₁
  set c₂ : ℝ := chiScale ℓ x^2 * (ℓ*d)⁻¹ with hc₂
  have hsplit : (∫ v : ℝ³, (c₁ * (chi v)^2 + c₂ * (chi v * fderiv ℝ chi v (kcStdBasis k))))
      = (∫ v : ℝ³, c₁ * (chi v)^2)
        + (∫ v : ℝ³, c₂ * (chi v * fderiv ℝ chi v (kcStdBasis k))) :=
    MeasureTheory.integral_add (hF1_intble.const_mul c₁) (hF2_intble.const_mul c₂)
  have hsm1 : (∫ v : ℝ³, c₁ * (chi v)^2) = c₁ * (∫ v : ℝ³, (chi v)^2) :=
    MeasureTheory.integral_const_mul c₁ (fun v : ℝ³ => (chi v)^2)
  have hsm2 : (∫ v : ℝ³, c₂ * (chi v * fderiv ℝ chi v (kcStdBasis k)))
      = c₂ * (∫ v : ℝ³, chi v * fderiv ℝ chi v (kcStdBasis k)) :=
    MeasureTheory.integral_const_mul c₂ (fun v : ℝ³ => chi v * fderiv ℝ chi v (kcStdBasis k))
  calc (∫ u : ℝ³, chiB ℓ d u x * (fderiv ℝ (fun y : ℝ³ => chiB ℓ d u y) x (kcStdBasis k)))
      = ∫ u : ℝ³, (c₁ * (chi ((ℓ*d)⁻¹ • x - u))^2
          + c₂ * (chi ((ℓ*d)⁻¹ • x - u) * fderiv ℝ chi ((ℓ*d)⁻¹ • x - u) (kcStdBasis k))) := by
        rw [hc₁, hc₂]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ v : ℝ³, (c₁ * (chi v)^2 + c₂ * (chi v * fderiv ℝ chi v (kcStdBasis k))) :=
        MeasureTheory.integral_sub_left_eq_self
          (fun v : ℝ³ => c₁ * (chi v)^2 + c₂ * (chi v * fderiv ℝ chi v (kcStdBasis k)))
          volume ((ℓ*d)⁻¹ • x)
    _ = (∫ v : ℝ³, c₁ * (chi v)^2)
          + (∫ v : ℝ³, c₂ * (chi v * fderiv ℝ chi v (kcStdBasis k))) := hsplit
    _ = c₁ * (∫ v : ℝ³, (chi v)^2)
          + c₂ * (∫ v : ℝ³, chi v * fderiv ℝ chi v (kcStdBasis k)) := by
        rw [hsm1, hsm2]
    _ = chiScale ℓ x * fderiv ℝ (chiScale ℓ) x (kcStdBasis k) := by
        rw [hF1_int, hF2_int, hc₁]
        ring

end Work.UBBInputs9.B
