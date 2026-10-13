import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData

open MeasureTheory

theorem integrable_facts {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (u p) ^ 2) ∧
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (u p) ^ 4) ∧
    MeasureTheory.Integrable (fun p : ℝ × ℝ => ‖fderiv ℝ u p‖ ^ 2) ∧
    MeasureTheory.Integrable (fun t : ℝ => ∫ s : ℝ, (u (s, t)) ^ 2) ∧
    MeasureTheory.Integrable (fun s : ℝ => ∫ t : ℝ, (u (s, t)) ^ 2) ∧
    MeasureTheory.Integrable (fun t : ℝ => ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2) ∧
    MeasureTheory.Integrable (fun s : ℝ => ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2) ∧
    (∫ t : ℝ, ∫ s : ℝ, (u (s, t)) ^ 2) = ∫ p : ℝ × ℝ, (u p) ^ 2 ∧
    (∫ s : ℝ, ∫ t : ℝ, (u (s, t)) ^ 2) = ∫ p : ℝ × ℝ, (u p) ^ 2 ∧
    (∫ t : ℝ, ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2) ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 ∧
    (∫ s : ℝ, ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2) ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
  have hcont : Continuous u := hu.continuous
  have hcontD : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  -- compact support of the powers
  have hcs2 : HasCompactSupport (fun p : ℝ × ℝ => (u p) ^ 2) :=
    hc.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hcs4 : HasCompactSupport (fun p : ℝ × ℝ => (u p) ^ 4) :=
    hc.comp_left (g := fun x : ℝ => x ^ 4) (by simp)
  have h2 : Integrable (fun p : ℝ × ℝ => (u p) ^ 2) :=
    (hcont.pow 2).integrable_of_hasCompactSupport hcs2
  have h4 : Integrable (fun p : ℝ × ℝ => (u p) ^ 4) :=
    (hcont.pow 4).integrable_of_hasCompactSupport hcs4
  -- the derivative
  have hcD : HasCompactSupport (fderiv ℝ u) := HasCompactSupport.fderiv ℝ hc
  have hcsD : HasCompactSupport (fun p : ℝ × ℝ => ‖fderiv ℝ u p‖ ^ 2) :=
    (hcD.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => ‖L‖) (by simp)).comp_left
      (g := fun x : ℝ => x ^ 2) (by simp)
  have hg2 : Integrable (fun p : ℝ × ℝ => ‖fderiv ℝ u p‖ ^ 2) :=
    (hcontD.norm.pow 2).integrable_of_hasCompactSupport hcsD
  -- directional derivatives
  have hDcont1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ u p (1, 0)) :=
    hcontD.clm_apply continuous_const
  have hDcont2 : Continuous (fun p : ℝ × ℝ => fderiv ℝ u p (0, 1)) :=
    hcontD.clm_apply continuous_const
  have hpw1 : ∀ p : ℝ × ℝ, (fderiv ℝ u p (1, 0)) ^ 2 ≤ ‖fderiv ℝ u p‖ ^ 2 := by
    intro p
    have h : ‖fderiv ℝ u p (1, 0)‖ ≤ ‖fderiv ℝ u p‖ := by
      have := ContinuousLinearMap.le_opNorm (fderiv ℝ u p) ((1, 0) : ℝ × ℝ)
      simpa using this
    calc (fderiv ℝ u p (1, 0)) ^ 2 = ‖fderiv ℝ u p (1, 0)‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖fderiv ℝ u p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hpw2 : ∀ p : ℝ × ℝ, (fderiv ℝ u p (0, 1)) ^ 2 ≤ ‖fderiv ℝ u p‖ ^ 2 := by
    intro p
    have h : ‖fderiv ℝ u p (0, 1)‖ ≤ ‖fderiv ℝ u p‖ := by
      have := ContinuousLinearMap.le_opNorm (fderiv ℝ u p) ((0, 1) : ℝ × ℝ)
      simpa using this
    calc (fderiv ℝ u p (0, 1)) ^ 2 = ‖fderiv ℝ u p (0, 1)‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖fderiv ℝ u p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hD1 : Integrable (fun p : ℝ × ℝ => (fderiv ℝ u p (1, 0)) ^ 2) :=
    hg2.mono' (hDcont1.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpw1 p)
  have hD2 : Integrable (fun p : ℝ × ℝ => (fderiv ℝ u p (0, 1)) ^ 2) :=
    hg2.mono' (hDcont2.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpw2 p)
  -- product measure form
  have h2p : Integrable (fun p : ℝ × ℝ => (u p) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact h2
  have hD1p : Integrable (fun p : ℝ × ℝ => (fderiv ℝ u p (1, 0)) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hD1
  have hD2p : Integrable (fun p : ℝ × ℝ => (fderiv ℝ u p (0, 1)) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hD2
  -- marginal integrability
  have hIt2 : Integrable (fun t : ℝ => ∫ s : ℝ, (u (s, t)) ^ 2) := by
    simpa using h2p.integral_prod_right
  have hIs2 : Integrable (fun s : ℝ => ∫ t : ℝ, (u (s, t)) ^ 2) := by
    simpa using h2p.integral_prod_left
  have hIt1 : Integrable (fun t : ℝ => ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2) := by
    simpa using hD1p.integral_prod_right
  have hIs1 : Integrable (fun s : ℝ => ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2) := by
    simpa using hD2p.integral_prod_left
  -- Fubini equalities
  have heq8 : (∫ t : ℝ, ∫ s : ℝ, (u (s, t)) ^ 2) = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
    have h := (MeasureTheory.integral_prod_symm (fun p : ℝ × ℝ => (u p) ^ 2) h2p).symm
    rw [← Measure.volume_eq_prod] at h
    exact h
  have heq9 : (∫ s : ℝ, ∫ t : ℝ, (u (s, t)) ^ 2) = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
    have h := (MeasureTheory.integral_prod (fun p : ℝ × ℝ => (u p) ^ 2) h2p).symm
    rw [← Measure.volume_eq_prod] at h
    exact h
  -- the two inequalities
  have hineq1 : (∫ t : ℝ, ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2) ≤
      ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
    calc (∫ t : ℝ, ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2)
        = ∫ p : ℝ × ℝ, (fderiv ℝ u p (1, 0)) ^ 2 :=
          (MeasureTheory.integral_prod_symm (fun p : ℝ × ℝ => (fderiv ℝ u p (1, 0)) ^ 2)
            hD1p).symm
      _ ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := MeasureTheory.integral_mono hD1 hg2 hpw1
  have hineq2 : (∫ s : ℝ, ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2) ≤
      ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
    calc (∫ s : ℝ, ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2)
        = ∫ p : ℝ × ℝ, (fderiv ℝ u p (0, 1)) ^ 2 :=
          (MeasureTheory.integral_prod (fun p : ℝ × ℝ => (fderiv ℝ u p (0, 1)) ^ 2) hD2p).symm
      _ ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := MeasureTheory.integral_mono hD2 hg2 hpw2
  exact ⟨h2, h4, hg2, hIt2, hIs2, hIt1, hIs1, heq8, heq9, hineq1, hineq2⟩

end Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData
