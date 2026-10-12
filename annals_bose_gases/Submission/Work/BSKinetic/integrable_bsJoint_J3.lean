import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Decomp.exists_radius_eq_zero_of_hasCompactSupport
import Submission.Work.BSKinetic.abs_bsMean_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.integrable_bsJoint_J3`

**The joint integrand of the moving-box family is `L¹`.**  For `ℓ > 0` and a smooth compactly
supported one-body state `ψ : ℝ³ → ℝ`, the function

    `p = (x,u) ↦ bsMean ℓ u ψ · (χ_{Λ(u)}(x))² · (∂²_k ψ)(x)`,

where `bsMean ℓ u ψ = (ℓ³)⁻¹ ∫_{acube ℓ} ψ(ℓ•u + z) dz` is the moving-box mean,
`χ_{Λ(u)}(x) = bsWin ℓ u x = χ_ℓ(x − ℓu)` is the moving-box window and `∂²_kψ` is the second
directional derivative of `ψ` along `kcStdBasis k`, is `Integrable` for the product of the
Lebesgue measure on `ℝ³` with itself.

## Proof

Three uniform bounds and one support analysis:

* `|bsMean ℓ u ψ| ≤ M` where `M` bounds `|ψ|` (`Work.BSKinetic.abs_bsMean_le`);
* `|bsWin ℓ u x| ≤ chiSup`;
* `|∂²_kψ x| ≤ MD` and `∂²_kψ x = 0` for `‖x‖ ≥ R` (the second directional derivative of a smooth
  compactly supported function is compactly supported, `HasCompactSupport.fderiv_apply`).

The window vanishes unless `‖x − ℓu‖ ≤ ℓ/2`, so if in addition `‖x‖ ≤ R` then
`‖u‖ ≤ R' := (R + ℓ/2)/ℓ`.  Hence the integrand is dominated by

    `M · chiSup² · MD · 1_{‖x‖ ≤ R} · 1_{‖u‖ ≤ R'}`,

a product of an integrable function of `x` alone with an integrable function of `u` alone
(`Integrable.mul_prod`), and `Integrable.mono'` applies once the integrand is seen to be
a.e.-strongly-measurable (the `u`-only factor `u ↦ bsMean ℓ u ψ` is measurable as a parametric
integral, `StronglyMeasurable.integral_prod_right'`; the rest is continuous).
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

/-! ## 1. Measurability of the moving-box mean -/

/-- `p ↦ bsMean ℓ p.2 ψ` is a.e.-measurable for continuous `ψ`: the joint integrand
`(p,z) ↦ 1_{acube ℓ}(z)·ψ(ℓ•p.2 + z)` is jointly measurable, so its parametric integral is
a.e.-strongly-measurable. -/
private lemma aemeasurable_bsMean_prod {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    AEMeasurable (fun p : ℝ³ × ℝ³ => bsMean ℓ p.2 ψ)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  have hjoint : Measurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      (acube ℓ).indicator (fun z : ℝ³ => ψ (ℓ • q.1.2 + z)) q.2) := by
    have h1 : (fun q : (ℝ³ × ℝ³) × ℝ³ =>
        (acube ℓ).indicator (fun z : ℝ³ => ψ (ℓ • q.1.2 + z)) q.2)
        = fun q : (ℝ³ × ℝ³) × ℝ³ =>
            (acube ℓ).indicator (fun _ => (1 : ℝ)) q.2 * ψ (ℓ • q.1.2 + q.2) := by
      funext q
      by_cases hq : q.2 ∈ acube ℓ
      · simp [Set.indicator_of_mem hq]
      · simp [Set.indicator_of_notMem hq]
    rw [h1]
    exact ((measurable_const.indicator (acube_measurable ℓ)).comp measurable_snd).mul
      (hψ.measurable.comp (by fun_prop))
  have hint : StronglyMeasurable (fun p : ℝ³ × ℝ³ =>
      ∫ z : ℝ³, (acube ℓ).indicator (fun z : ℝ³ => ψ (ℓ • p.2 + z)) z) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (f := fun q : (ℝ³ × ℝ³) × ℝ³ =>
        (acube ℓ).indicator (fun z : ℝ³ => ψ (ℓ • q.1.2 + z)) q.2)
      hjoint.stronglyMeasurable
  have hAeq : (fun p : ℝ³ × ℝ³ => bsMean ℓ p.2 ψ)
      = fun p : ℝ³ × ℝ³ =>
          (ℓ ^ 3)⁻¹ * ∫ z : ℝ³, (acube ℓ).indicator (fun z : ℝ³ => ψ (ℓ • p.2 + z)) z := by
    funext p
    rw [bsMean, ← MeasureTheory.integral_indicator (acube_measurable ℓ)]
  rw [hAeq]
  exact hint.aemeasurable.const_mul _

/-! ## 2. The second directional derivative: smoothness, bound, support -/

/-- The second directional derivative `x ↦ fderiv (fderiv ψ · e_k) x e_k` of a smooth state is
smooth. -/
private lemma contDiff_fderiv_fderiv {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (k : Fin 3) :
    ContDiff ℝ (⊤ : ENat) (fun x : ℝ³ =>
      fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)) := by
  have hfderiv : ContDiff ℝ (⊤ : ENat) (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  have hg : ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) :=
    hfderiv.clm_apply contDiff_const
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

/-- The second directional derivative `x ↦ fderiv (fderiv ψ · e_k) x e_k` of a smooth compactly
supported state is bounded and supported in a ball: `HasCompactSupport.fderiv_apply` applied twice
gives compact support, whence a uniform bound (continuity) and a vanishing radius. -/
private lemma exists_bound_and_radius_fderiv_fderiv_aux {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (k : Fin 3) :
    ∃ M R : ℝ, 0 ≤ M ∧ 0 ≤ R ∧
      (∀ x, |fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)| ≤ M) ∧
      (∀ x, R ≤ ‖x‖ → fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x
        (kcStdBasis k) = 0) := by
  have hcs1 : HasCompactSupport (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) :=
    hcs.fderiv_apply ℝ (kcStdBasis k)
  have hcs2 : HasCompactSupport (fun x : ℝ³ =>
      fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)) :=
    hcs1.fderiv_apply ℝ (kcStdBasis k)
  have hcont : Continuous (fun x : ℝ³ =>
      fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)) :=
    (contDiff_fderiv_fderiv hψ k).continuous
  obtain ⟨M, hM⟩ := hcs2.exists_bound_of_continuous hcont
  obtain ⟨R, hR0, hR⟩ := Decomp.exists_radius_eq_zero_of_hasCompactSupport hcs2
  exact ⟨M, R, le_trans (norm_nonneg _) (hM 0), hR0,
    fun x => by rw [← Real.norm_eq_abs]; exact hM x, hR⟩

/-! ## 3. The abstract integrability statement -/

/-- **The abstract `(x,u)`-integrability.**  For `ℓ > 0`, a state `ψ` whose moving-box mean is
a.e.-measurable and bounded by `M`, a window bound `|bsWin ℓ u x| ≤ χb` and a function `D` that is
continuous, bounded by `MD` and vanishing for `‖x‖ ≥ R`, the product
`bsMean ℓ u ψ · (bsWin ℓ u x)² · D x` is integrable for the product of the Lebesgue measures. -/
private theorem integrable_bsMean_mul_bsWin_sq_mul {ℓ M χb MD R : ℝ} (hℓ : 0 < ℓ)
    {ψ : ℝ³ → ℝ} {D : ℝ³ → ℝ}
    (hA : AEMeasurable (fun p : ℝ³ × ℝ³ => bsMean ℓ p.2 ψ)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
    (hAb : ∀ u, |bsMean ℓ u ψ| ≤ M)
    (hχb : ∀ u x : ℝ³, |bsWin ℓ u x| ≤ χb)
    (hDc : Continuous D) (hDb : ∀ x, |D x| ≤ MD) (hDz : ∀ x, R ≤ ‖x‖ → D x = 0) :
    Integrable (fun p : ℝ³ × ℝ³ => bsMean ℓ p.2 ψ * (bsWin ℓ p.2 p.1) ^ 2 * D p.1)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  classical
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (bsMean ℓ 0 ψ)) (hAb 0)
  have hMD0 : 0 ≤ MD := le_trans (abs_nonneg (D 0)) (hDb 0)
  have hχb0 : 0 ≤ χb := le_trans (abs_nonneg (bsWin ℓ 0 0)) (hχb 0 0)
  -- the dominating function is a product of two integrable one-variable functions
  have hind1 : Integrable
      (fun x : ℝ³ => (closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) x)
      (volume : Measure ℝ³) := by
    rw [integrable_indicator_iff (isClosed_closedBall.measurableSet)]
    exact integrableOn_const (measure_closedBall_lt_top).ne
  have hind2 : Integrable
      (fun u : ℝ³ => (closedBall (0 : ℝ³) ((R + ℓ / 2) / ℓ)).indicator (fun _ => (1 : ℝ)) u)
      (volume : Measure ℝ³) := by
    rw [integrable_indicator_iff (isClosed_closedBall.measurableSet)]
    exact integrableOn_const (measure_closedBall_lt_top).ne
  have hgint : Integrable (fun p : ℝ³ × ℝ³ =>
      M * χb ^ 2 * MD * (closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) p.1 *
        (closedBall (0 : ℝ³) ((R + ℓ / 2) / ℓ)).indicator (fun _ => (1 : ℝ)) p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    (hind1.const_mul (M * χb ^ 2 * MD)).mul_prod hind2
  -- pointwise domination
  have hpoint : ∀ p : ℝ³ × ℝ³,
      ‖bsMean ℓ p.2 ψ * (bsWin ℓ p.2 p.1) ^ 2 * D p.1‖
        ≤ M * χb ^ 2 * MD * (closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) p.1 *
            (closedBall (0 : ℝ³) ((R + ℓ / 2) / ℓ)).indicator (fun _ => (1 : ℝ)) p.2 := by
    intro p
    by_cases h1 : ‖p.1‖ ≤ R
    · have hi1 : (closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) p.1 = 1 :=
        Set.indicator_of_mem (by simpa [mem_closedBall, dist_eq_norm] using h1) _
      by_cases h2 : ‖p.2‖ ≤ (R + ℓ / 2) / ℓ
      · -- everything is bounded by its sup
        have hi2 : (closedBall (0 : ℝ³) ((R + ℓ / 2) / ℓ)).indicator
            (fun _ => (1 : ℝ)) p.2 = 1 :=
          Set.indicator_of_mem (by simpa [mem_closedBall, dist_eq_norm] using h2) _
        rw [hi1, hi2, mul_one, mul_one]
        have hAm : |bsMean ℓ p.2 ψ| ≤ M := hAb p.2
        have hχbm : |bsWin ℓ p.2 p.1| ≤ χb := hχb p.2 p.1
        have hDm : |D p.1| ≤ MD := hDb p.1
        have hW2 : (bsWin ℓ p.2 p.1) ^ 2 ≤ χb ^ 2 := by
          have h := hχbm
          rw [abs_le] at h
          nlinarith [h.1, h.2]
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (sq_nonneg (bsWin ℓ p.2 p.1))]
        calc |bsMean ℓ p.2 ψ| * (bsWin ℓ p.2 p.1) ^ 2 * |D p.1|
            ≤ M * χb ^ 2 * MD := by
              have hstep : |bsMean ℓ p.2 ψ| * (bsWin ℓ p.2 p.1) ^ 2 ≤ M * χb ^ 2 :=
                mul_le_mul hAm hW2 (sq_nonneg _) hM0
              exact mul_le_mul hstep hDm (abs_nonneg _) (mul_nonneg hM0 (sq_nonneg χb))
          _ = M * χb ^ 2 * MD := rfl
      · -- the window misses the state
        have h2' : (R + ℓ / 2) / ℓ < ‖p.2‖ := lt_of_not_ge h2
        have hi2 : (closedBall (0 : ℝ³) ((R + ℓ / 2) / ℓ)).indicator
            (fun _ => (1 : ℝ)) p.2 = 0 :=
          Set.indicator_of_notMem (by simpa [mem_closedBall, dist_eq_norm] using not_le.mpr h2') _
        rw [hi2, mul_zero]
        have hwin0 : bsWin ℓ p.2 p.1 = 0 := by
          rw [bsWin]
          refine UBBInputs9.B.chiScale_eq_zero_of_norm_gt hℓ ?_
          have hkey : ℓ * ((R + ℓ / 2) / ℓ) = R + ℓ / 2 := by field_simp
          have hnorm : ‖ℓ • p.2‖ = ℓ * ‖p.2‖ := by rw [norm_smul, Real.norm_of_nonneg hℓ.le]
          have hlt : ℓ * ((R + ℓ / 2) / ℓ) < ℓ * ‖p.2‖ := mul_lt_mul_of_pos_left h2' hℓ
          have htri : ‖ℓ • p.2‖ - ‖p.1‖ ≤ ‖p.1 - ℓ • p.2‖ := by
            have h := norm_sub_norm_le (ℓ • p.2) p.1
            rwa [norm_sub_rev] at h
          rw [hnorm] at htri
          linarith
        rw [hwin0]
        simp
    · -- the second derivative vanishes off the ball
      have h1' : R < ‖p.1‖ := lt_of_not_ge h1
      have hi1 : (closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) p.1 = 0 :=
        Set.indicator_of_notMem (by simpa [mem_closedBall, dist_eq_norm] using not_le.mpr h1') _
      rw [hi1, mul_zero, zero_mul]
      have hD0 : D p.1 = 0 := hDz p.1 (le_of_lt h1')
      rw [hD0]
      simp
  -- a.e.-strong measurability
  have hFmeas : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => bsMean ℓ p.2 ψ * (bsWin ℓ p.2 p.1) ^ 2 * D p.1)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    have hWc : Continuous (fun p : ℝ³ × ℝ³ => bsWin ℓ p.2 p.1) := by
      have hfun : (fun p : ℝ³ × ℝ³ => bsWin ℓ p.2 p.1)
          = fun p : ℝ³ × ℝ³ => chiScale ℓ (p.1 - ℓ • p.2) := by
        funext p
        rw [bsWin]
      rw [hfun]
      exact (chiScale_continuous ℓ).comp (continuous_fst.sub (continuous_snd.const_smul ℓ))
    have h1 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => bsMean ℓ p.2 ψ)
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := hA.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => (bsWin ℓ p.2 p.1) ^ 2)
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      (hWc.pow 2).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => D p.1)
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      (hDc.comp continuous_fst).aestronglyMeasurable
    exact (h1.mul h2).mul h3
  exact hgint.mono' hFmeas (Filter.Eventually.of_forall hpoint)

/-! ## 4. The theorem -/

theorem integrable_bsJoint_J3 {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (k : Fin 3) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Work.BSKinetic.bsMean ℓ p.2 ψ * (Work.BSKinetic.bsWin ℓ p.2 p.1) ^ 2 *
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            fderiv ℝ ψ y (Submission.BoseGases.kcStdBasis k)) p.1
          (Submission.BoseGases.kcStdBasis k)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hψ.continuous
  have hMb : ∀ x : ℝ³, |ψ x| ≤ M := fun x => by
    rw [← Real.norm_eq_abs]; exact hM x
  obtain ⟨MD, R, hMD0, hR0, hMDb, hDz⟩ := exists_bound_and_radius_fderiv_fderiv_aux hψ hcs k
  have hDcont : Continuous (fun x : ℝ³ =>
      fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)) :=
    (contDiff_fderiv_fderiv hψ k).continuous
  have hχb : ∀ u x : ℝ³, |bsWin ℓ u x| ≤ chiSup := fun u x => by
    rw [bsWin]
    exact abs_chiScale_le_chiSup ℓ _
  exact integrable_bsMean_mul_bsWin_sq_mul hℓ (aemeasurable_bsMean_prod hψ.continuous)
    (abs_bsMean_le hℓ hMb) hχb hDcont hMDb hDz

end Work.BSKinetic
