import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.integrable_uncurry_bsWin_deriv_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.integrable_bsJoint_J2`

**The joint `(x,u)`-integrand of the second-order (mean) term of the moving-box family is `L¹`.**

For `ℓ > 0`, a smooth compactly supported one-body state `ψ : ℝ³ → ℝ` and a direction
`e_k = kcStdBasis k`, the function

    `p = (x,u) ↦ χ_ℓ(x − ℓu)² · ψ(x) · ∂_k(∂_kψ)(x)`

is `Integrable` for the unrestricted product of the Lebesgue measure on `ℝ³` with itself.

This is the companion of `integrable_uncurry_bsWin_deriv_sq` (which handles the *boundary* term
`(∂_k(χ_u·ψ))²`) and of `integrable_bsJoint_J1` (the projected square `(Q_uψ)²(∂_kχ_u)²`): it is
the mixed-window factor appearing when the sliding kinetic word is expanded around the box mean,
`|∇(χ_uψ)|² = |χ_u∇ψ|² + 2 χ_u(∇χ_u·∇ψ)ψ + (∇χ_u)²ψ²`, where the *mean/second-order* piece is
`χ_u²·ψ·∂_k²ψ`.

## Proof

Let `g x = ∂_kψ(x) = fderiv ℝ ψ x e_k`. Since `ψ` is `C^∞`, `g` is `C^∞`
(`ContDiff.fderiv_right` followed by `ContDiff.clm_apply` with the constant direction `e_k`),
so its directional derivative `x ↦ ∂_k g(x)` is *continuous*; and since `ψ` has compact support,
`g` does too (`HasCompactSupport.fderiv_apply`), hence so does `x ↦ ∂_k g(x)`.

The integrand therefore coincides with the *continuous, compactly supported* function

    `H p = χ_ℓ(p.1 − ℓp.2)² · ψ(p.1) · ∂_k g(p.1)`

(definitionally, since `bsWin ℓ p.2 p.1 = χ_ℓ(p.1 − ℓ•p.2)` and `g = (y ↦ fderiv ℝ ψ y e_k)`),
which is integrable by `Continuous.integrable_of_hasCompactSupport`.  The compact support is
computed by hand, exactly as in `integrable_uncurry_bsWin_deriv_sq`: `H` vanishes off
`tsupport ψ × closedBall 0 R` with `R = (C₀ + ℓ/2)/ℓ`, `C₀` a bound for `‖·‖` on `tsupport ψ` —
either `p.1 ∉ tsupport ψ` (so `ψ p.1 = 0`) or `‖p.1 − ℓp.2‖ > ℓ/2` (so `χ_ℓ` vanishes strictly).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem integrable_bsJoint_J2 {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (k : Fin 3) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (Work.BSKinetic.bsWin ℓ p.2 p.1) ^ 2 * ψ p.1 *
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            fderiv ℝ ψ y (Submission.BoseGases.kcStdBasis k)) p.1
          (Submission.BoseGases.kcStdBasis k)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  -- The mixed second partial `g = ∂_kψ` is smooth...
  set g : ℝ³ → ℝ := fun y => fderiv ℝ ψ y (kcStdBasis k) with hgdef
  have hg : ContDiff ℝ (⊤ : ENat) g := by
    have h1 : ((⊤ : ENat) : WithTop ℕ∞) + 1 ≤ ((⊤ : ENat) : WithTop ℕ∞) := by simp
    exact (hψ.fderiv_right h1).clm_apply contDiff_const
  -- ... and compactly supported.
  have hgcs : HasCompactSupport g := hcs.fderiv_apply ℝ (kcStdBasis k)
  -- Hence its directional derivative `∂_k g` is continuous and compactly supported.
  have hDg_cont : Continuous (fun x : ℝ³ => fderiv ℝ g x (kcStdBasis k)) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDg_cs : HasCompactSupport (fun x : ℝ³ => fderiv ℝ g x (kcStdBasis k)) :=
    hgcs.fderiv_apply ℝ (kcStdBasis k)
  -- ### the model integrand `H` is continuous
  have hsubc : Continuous (fun p : ℝ³ × ℝ³ => p.1 - ℓ • p.2) :=
    continuous_fst.sub (continuous_snd.const_smul ℓ)
  have hχcont : Continuous (chiScale ℓ) := (chiScale_contDiff hℓne).continuous
  have hA : Continuous (fun p : ℝ³ × ℝ³ => (chiScale ℓ (p.1 - ℓ • p.2)) ^ 2) :=
    (hχcont.comp hsubc).pow 2
  have hB : Continuous (fun p : ℝ³ × ℝ³ => ψ p.1) := hψ.continuous.comp continuous_fst
  have hC : Continuous (fun p : ℝ³ × ℝ³ => fderiv ℝ g p.1 (kcStdBasis k)) :=
    hDg_cont.comp continuous_fst
  have hHcont : Continuous (fun p : ℝ³ × ℝ³ =>
      (chiScale ℓ (p.1 - ℓ • p.2)) ^ 2 * ψ p.1 * fderiv ℝ g p.1 (kcStdBasis k)) :=
    (hA.mul hB).mul hC
  -- ### ... and has compact support
  obtain ⟨C₀, hC₀⟩ := hcs.isCompact.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hKb : ∀ y ∈ tsupport ψ, ‖y‖ ≤ C₀ := fun y hy => by
    have h := hC₀ y hy
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)] at h
  set R : ℝ := (C₀ + ℓ / 2) / ℓ with hRdef
  have hHcs : HasCompactSupport (fun p : ℝ³ × ℝ³ =>
      (chiScale ℓ (p.1 - ℓ • p.2)) ^ 2 * ψ p.1 * fderiv ℝ g p.1 (kcStdBasis k)) := by
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
      rw [hχ0]
      ring
    · have hψ0 : ψ p.1 = 0 := image_eq_zero_of_notMem_tsupport hxK
      rw [hψ0]
      ring
  -- ### assemble
  have hInt : Integrable (fun p : ℝ³ × ℝ³ =>
      (chiScale ℓ (p.1 - ℓ • p.2)) ^ 2 * ψ p.1 * fderiv ℝ g p.1 (kcStdBasis k))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    hHcont.integrable_of_hasCompactSupport hHcs
  refine hInt.congr (Eventually.of_forall fun p => ?_)
  show (chiScale ℓ (p.1 - ℓ • p.2)) ^ 2 * ψ p.1 * fderiv ℝ g p.1 (kcStdBasis k)
    = (bsWin ℓ p.2 p.1) ^ 2 * ψ p.1 *
        (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) p.1 (kcStdBasis k))
  rw [hgdef]
  rfl

end Work.BSKinetic
