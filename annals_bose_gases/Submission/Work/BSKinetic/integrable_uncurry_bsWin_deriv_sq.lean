import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.integrable_uncurry_bsWin_deriv_sq`

**The joint integrand of the moving-box family is `L¹`.**  For `ℓ > 0` and a smooth compactly
supported one-body state `ψ : ℝ³ → ℝ`, the square of the directional derivative of the sliding
product `y ↦ bsWin ℓ u y * ψ y` (i.e. `y ↦ χ_ℓ(y − ℓu)·ψ y`),

    `p = (x, u) ↦ (∂_k (χ_{Λ(u)}·ψ)(x))²`,

is `Integrable` for the *unrestricted* product of the Lebesgue measure on `ℝ³` with itself.

This is the `(x,u)`-joint integrability which makes the `u`-integral of the moving-box family a
genuine Bochner integral (cf. `B/integrable_fderiv_chiBigPhi_sq`, the same statement for the
box-restricted first coordinate `volume ↾ abox 1 ℓ`).

## Proof

By Leibniz (`fderiv_bsWin_mul_eq`),

    `∂_k(χ_{Λ(u)}·ψ)(x) = ψ(x)·∂_kχ_ℓ(x − ℓu) + χ_ℓ(x − ℓu)·∂_kψ(x)`.

The right-hand side is a *continuous* function of `p = (x,u)`, and it vanishes unless
`p.1 ∈ tsupport ψ` **and** `‖p.1 − ℓ·p.2‖ ≤ ℓ/2`:

* off `tsupport ψ` both `ψ` and `∂_kψ` vanish pointwise;
* on `tsupport ψ` one has `‖p.1‖ ≤ C₀` (compactness), so `‖p.2‖ > R := (C₀ + ℓ/2)/ℓ` forces
  `‖p.1 − ℓp.2‖ > ℓ/2`, where both `χ_ℓ` and `∂_kχ_ℓ` vanish strictly.

Hence the Leibniz form has compact support, so it is integrable
(`Continuous.integrable_of_hasCompactSupport`), and the original integrand agrees with it
pointwise.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The two calculus inputs -/

/-- Chain rule for a translated argument: `∂(f(· − c))(x) = ∂f(x − c)`. -/
lemma fderiv_comp_sub_const_apply (f : ℝ³ → ℝ) (c x e : ℝ³)
    (hf : DifferentiableAt ℝ f (x - c)) :
    fderiv ℝ (fun y : ℝ³ => f (y - c)) x e = fderiv ℝ f (x - c) e := by
  have h1 : HasFDerivAt (fun y : ℝ³ => y - c) (ContinuousLinearMap.id ℝ ℝ³) x :=
    (hasFDerivAt_id x).sub_const c
  have h2 : HasFDerivAt (f ∘ fun y : ℝ³ => y - c)
      ((fderiv ℝ f (x - c)) ∘SL (ContinuousLinearMap.id ℝ ℝ³)) x :=
    hf.hasFDerivAt.comp x h1
  have hfun : (fun y : ℝ³ => f (y - c)) = f ∘ (fun y : ℝ³ => y - c) := rfl
  rw [hfun, h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]

/-- **The Leibniz formula for the moving-box window.**  Since `bsWin ℓ u y = χ_ℓ(y − ℓu)`, the
derivative of the windowed state along `kcStdBasis k` splits as

    `∂_k(χ_ℓ(· − ℓu)·ψ)(x) = ψ(x)·∂_kχ_ℓ(x − ℓu) + χ_ℓ(x − ℓu)·∂_kψ(x)`.

Both `u`-dependent factors are the *same* scaled bump `χ_ℓ`. -/
lemma fderiv_bsWin_mul_eq {ℓ : ℝ} {ψ : ℝ³ → ℝ} (u : ℝ³) (k : Fin 3)
    (hχ : Differentiable ℝ (chiScale ℓ)) {x : ℝ³} (hψ : DifferentiableAt ℝ ψ x) :
    fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x (kcStdBasis k)
      = ψ x * fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k)
        + chiScale ℓ (x - ℓ • u) * fderiv ℝ ψ x (kcStdBasis k) := by
  have hχx : DifferentiableAt ℝ (chiScale ℓ) (x - ℓ • u) := hχ.differentiableAt
  have hsub : DifferentiableAt ℝ (fun y : ℝ³ => y - ℓ • u) x :=
    ((hasFDerivAt_id x).sub_const (ℓ • u)).differentiableAt
  have hcomp : DifferentiableAt ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)) x :=
    DifferentiableAt.fun_comp' x hχx hsub
  have hfun : (fun y : ℝ³ => bsWin ℓ u y * ψ y)
      = (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)) * ψ := rfl
  rw [hfun, fderiv_mul hcomp hψ, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
    fderiv_comp_sub_const_apply (chiScale ℓ) (ℓ • u) x (kcStdBasis k) hχx]
  ring

/-! ## The main theorem -/

theorem integrable_uncurry_bsWin_deriv_sq {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (k : Fin 3) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
          Work.BSKinetic.bsWin ℓ p.2 y * ψ y) p.1
            (Submission.BoseGases.kcStdBasis k)) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
  classical
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hχdiff : Differentiable ℝ (chiScale ℓ) :=
    (chiScale_contDiff hℓne).differentiable (by norm_num)
  have hψdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  -- ### continuity of the Leibniz form
  have hsubc : Continuous (fun p : ℝ³ × ℝ³ => p.1 - ℓ • p.2) :=
    continuous_fst.sub (continuous_snd.const_smul ℓ)
  have hDχcont : Continuous (fun z : ℝ³ => fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) :=
    (chiScale_contDiff hℓne).continuous_fderiv (by simp) |>.clm_apply continuous_const
  have hHcont : Continuous (fun p : ℝ³ × ℝ³ =>
      (ψ p.1 * fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)
        + chiScale ℓ (p.1 - ℓ • p.2) * fderiv ℝ ψ p.1 (kcStdBasis k)) ^ 2) := by
    have hBc : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ (p.1 - ℓ • p.2)) :=
      (chiScale_contDiff hℓne).continuous.comp hsubc
    have hCc : Continuous (fun p : ℝ³ × ℝ³ => ψ p.1) := hψ.continuous.comp continuous_fst
    have hDc : Continuous (fun p : ℝ³ × ℝ³ =>
        fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)) := hDχcont.comp hsubc
    have hAc : Continuous (fun p : ℝ³ × ℝ³ => fderiv ℝ ψ p.1 (kcStdBasis k)) :=
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).comp continuous_fst
    exact ((hCc.mul hDc).add (hBc.mul hAc)).pow 2
  -- ### the support radius of the state
  obtain ⟨C₀, hC₀⟩ := hcs.isCompact.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hKb : ∀ y ∈ tsupport ψ, ‖y‖ ≤ C₀ := fun y hy => by
    have h := hC₀ y hy
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)] at h
  set R : ℝ := (C₀ + ℓ / 2) / ℓ with hRdef
  -- ### the Leibniz form has compact support
  have hHcs : HasCompactSupport (fun p : ℝ³ × ℝ³ =>
      (ψ p.1 * fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)
        + chiScale ℓ (p.1 - ℓ • p.2) * fderiv ℝ ψ p.1 (kcStdBasis k)) ^ 2) := by
    refine HasCompactSupport.intro' (K := tsupport ψ ×ˢ closedBall (0 : ℝ³) R)
      (hcs.isCompact.prod (isCompact_closedBall 0 R))
      (hcs.isCompact.isClosed.prod Metric.isClosed_closedBall) ?_
    intro p hp
    by_cases hxK : p.1 ∈ tsupport ψ
    · have huK : p.2 ∉ closedBall (0 : ℝ³) R := fun h =>
        hp (by rw [Set.mem_prod]; exact ⟨hxK, h⟩)
      rw [mem_closedBall, dist_eq_norm, sub_zero] at huK
      have huR : R < ‖p.2‖ := lt_of_not_ge huK
      have hlt : ℓ / 2 < ‖p.1 - ℓ • p.2‖ := by
        have hnorm : ‖ℓ • p.2‖ = ℓ * ‖p.2‖ := by
          rw [norm_smul, Real.norm_of_nonneg hℓ.le]
        have hkey : ℓ * R = C₀ + ℓ / 2 := by rw [hRdef]; field_simp
        have h1 : C₀ + ℓ / 2 < ℓ * ‖p.2‖ := by
          rw [← hkey]; exact mul_lt_mul_of_pos_left huR hℓ
        have h2 : ℓ * ‖p.2‖ - ‖p.1‖ ≤ ‖p.1 - ℓ • p.2‖ := by
          have h := norm_sub_norm_le (ℓ • p.2) p.1
          rwa [norm_sub_rev, hnorm] at h
        linarith [hKb p.1 hxK]
      have hχ0 : chiScale ℓ (p.1 - ℓ • p.2) = 0 :=
        UBBInputs9.B.chiScale_eq_zero_of_norm_gt hℓ hlt
      have hdχ0 : fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k) = 0 :=
        UBBInputs9.B.fderiv_chiScale_eq_zero_of_norm_gt hℓ hlt
      rw [hχ0, hdχ0, mul_zero, zero_mul, add_zero]
      ring
    · have hψ0 : ψ p.1 = 0 := image_eq_zero_of_notMem_tsupport hxK
      have hdψ0 : fderiv ℝ ψ p.1 (kcStdBasis k) = 0 := by
        rw [(notMem_tsupport_iff_eventuallyEq.mp hxK).fderiv_eq]
        simp
      rw [hψ0, hdψ0, zero_mul, mul_zero, add_zero]
      ring
  -- ### assemble
  have hIntH : Integrable (fun p : ℝ³ × ℝ³ =>
      (ψ p.1 * fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)
        + chiScale ℓ (p.1 - ℓ • p.2) * fderiv ℝ ψ p.1 (kcStdBasis k)) ^ 2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    hHcont.integrable_of_hasCompactSupport hHcs
  refine hIntH.congr (Eventually.of_forall fun p => ?_)
  show (ψ p.1 * fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)
      + chiScale ℓ (p.1 - ℓ • p.2) * fderiv ℝ ψ p.1 (kcStdBasis k)) ^ 2
    = (fderiv ℝ (fun y : ℝ³ => bsWin ℓ p.2 y * ψ y) p.1 (kcStdBasis k)) ^ 2
  rw [fderiv_bsWin_mul_eq p.2 k hχdiff (hψdiff p.1)]

end Work.BSKinetic
