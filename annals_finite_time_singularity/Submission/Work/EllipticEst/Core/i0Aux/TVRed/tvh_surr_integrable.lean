/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the trace-matching surrogate against the angular weight

The surrogate `surrFun ψ F₀ F₁ L θ = F₀ * ψ (θ/L) + F₁ * ψ ((π/2-θ)/L)` is bounded by
`|F₀| + |F₁|` and its first two derivatives are bounded by `C (|F₀|+|F₁|)/L` and
`C (|F₀|+|F₁|)/L²` **uniformly in `θ`** (the bounds `surr_bound`, `deriv_surr_bound`,
`deriv2_surr_bound` of `TVRed/BumpFacts.lean` are valid for *every* real `θ` and use only
`hψ` and `0 < L`).  Hence the three weighted squares `(surr)² thEta`, `(surr')² thEta`,
`(surr'')² thEta` are each dominated by a constant multiple of `thEta`, which is integrable
on `Iθ` (`Work.FTS.EllipticEst.integrableOn_thEta`).

In particular **no upper bound on `L` is needed**: the sharper scale condition
`L ≤ π/4` is used only for the *trace-matching* and *support* properties of the surrogate,
not for its integrability.  (The fourth conjunct of `TVRed/surrIntegrable.lean`, involving
`(qTh)² = (2η cot 2θ)²`, does need `L ≤ π/4`, since `qTh` blows up at `θ = 0` and the
support of `surr'` must stay away from the endpoints; that conjunct is deliberately absent
from the statement proved here.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypAux
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

variable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}

/-! ## Continuity of the bump's derivatives and of the surrogate's derivatives -/

/-- A bump is `C²`, so its first derivative is continuous. -/
lemma tvh_continuous_deriv (hψ : IsBump ψ C) : Continuous (deriv ψ) :=
  hψ.contDiff.continuous_deriv (by norm_num)

/-- A bump is `C²`, so its second derivative is continuous. -/
lemma tvh_continuous_deriv2 (hψ : IsBump ψ C) : Continuous (deriv (deriv ψ)) :=
  (hψ.contDiff.deriv' (n := 1)).continuous_deriv (by norm_num)

/-- The surrogate is continuous. -/
lemma tvh_continuous_surr (hψ : IsBump ψ C) (hL : L ≠ 0) :
    Continuous (surrFun ψ F₀ F₁ L) :=
  (surr_smooth hψ hL).continuous

/-- The first derivative of the surrogate is continuous: by the chain-rule identity
`deriv_surr_eq` it is an explicit sum of compositions of `deriv ψ` with affine maps. -/
lemma tvh_continuous_deriv_surr (hψ : IsBump ψ C) (hL : L ≠ 0) :
    Continuous (deriv (surrFun ψ F₀ F₁ L)) := by
  have h1 : Continuous fun θ : ℝ => deriv ψ (θ / L) :=
    (tvh_continuous_deriv hψ).comp (by continuity)
  have h2 : Continuous fun θ : ℝ => deriv ψ ((Real.pi / 2 - θ) / L) :=
    (tvh_continuous_deriv hψ).comp (by continuity)
  rw [show deriv (surrFun ψ F₀ F₁ L) = fun θ : ℝ =>
      F₀ * (deriv ψ (θ / L) * (1 / L))
        + F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L)))
      from funext (deriv_surr_eq hψ hL)]
  exact ((h1.mul_const (1 / L)).const_mul F₀).add ((h2.mul_const (-(1 / L))).const_mul F₁)

/-- The second derivative of the surrogate is continuous, from `deriv2_surr_eq`. -/
lemma tvh_continuous_deriv2_surr (hψ : IsBump ψ C) (hL : L ≠ 0) :
    Continuous (deriv (deriv (surrFun ψ F₀ F₁ L))) := by
  have h1 : Continuous fun θ : ℝ => deriv (deriv ψ) (θ / L) :=
    (tvh_continuous_deriv2 hψ).comp (by continuity)
  have h2 : Continuous fun θ : ℝ => deriv (deriv ψ) ((Real.pi / 2 - θ) / L) :=
    (tvh_continuous_deriv2 hψ).comp (by continuity)
  rw [show deriv (deriv (surrFun ψ F₀ F₁ L)) = fun θ : ℝ =>
      F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)
        + F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))
      from funext (deriv2_surr_eq hψ hL)]
  exact (((h1.mul_const (1 / L)).const_mul F₀).mul_const (1 / L)).add
    (((h2.mul_const (-(1 / L))).const_mul F₁).mul_const (-(1 / L)))

/-! ## The integrability theorem -/

theorem tvh_surr_integrable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ C) (hL : 0 < L) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  refine ⟨?_, ?_, ?_⟩
  · -- `(surr)² thEta` is dominated by `(|F₀| + |F₁|)² thEta`
    refine tvh_integrableOn_of_abs_le
      (F := fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (tvh_integrableOn_const_mul_thEta _) ?_ ?_
    · exact ((tvh_continuous_surr hψ hL0).aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      have hb : |Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ| ≤ |F₀| + |F₁| :=
        surr_bound hψ θ
      have h2 : (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 ≤ (|F₀| + |F₁|) ^ 2 := by
        have h := pow_le_pow_left₀
          (abs_nonneg (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) hb 2
        rwa [sq_abs] at h
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      exact mul_le_mul_of_nonneg_right h2 hσ
  · -- `(surr')² thEta` is dominated by `(C (|F₀| + |F₁|) / L)² thEta`
    refine tvh_integrableOn_of_abs_le
      (F := fun θ => (C * (|F₀| + |F₁|) / L) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (tvh_integrableOn_const_mul_thEta _) ?_ ?_
    · exact ((tvh_continuous_deriv_surr hψ hL0).aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      have hb : |deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ|
          ≤ C * (|F₀| + |F₁|) / L :=
        deriv_surr_bound hψ hL θ
      have h2 : (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2
          ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := by
        have h := pow_le_pow_left₀
          (abs_nonneg (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ)) hb 2
        rwa [sq_abs] at h
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      exact mul_le_mul_of_nonneg_right h2 hσ
  · -- `(surr'')² thEta` is dominated by `(C (|F₀| + |F₁|) / L²)² thEta`
    refine tvh_integrableOn_of_abs_le
      (F := fun θ => (C * (|F₀| + |F₁|) / L ^ 2) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (tvh_integrableOn_const_mul_thEta _) ?_ ?_
    · exact ((tvh_continuous_deriv2_surr hψ hL0).aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      have hb : |deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ|
          ≤ C * (|F₀| + |F₁|) / L ^ 2 :=
        deriv2_surr_bound hψ hL θ
      have h2 : (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2
          ≤ (C * (|F₀| + |F₁|) / L ^ 2) ^ 2 := by
        have h := pow_le_pow_left₀
          (abs_nonneg (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ)) hb 2
        rwa [sq_abs] at h
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      exact mul_le_mul_of_nonneg_right h2 hσ

end

end Work.EllipticEst.Core.i0Aux.TVRed
