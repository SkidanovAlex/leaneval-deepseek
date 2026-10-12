import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.CrossDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin.Cross

open MeasureTheory
open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **The joint `(p,v,s,u)`-integrand of the cross term is `L¹`.**

For `ℓ > 0`, a radial-`L¹` symbol `F`, and a smooth compactly supported one-body state `ψ`, the
function

  `(p, (v, (u, s))) ↦ bsLf ℓ F p v · ψ(ℓ(v+u)) · ψ(ℓ(u+s))`

is `Integrable` for `volume ⊗ volume ⊗ volume ⊗ (volume ↾ acube 1)`.  This is the a.e.-integrability
input that makes the exchange of integrals (`Cross/bsCross_expand_mean`) and the substitutions
(`Cross/bsCross_subst`) of the cross-term computation legitimate.

## Proof

Write the measure factor in the last variable as `ρ = volume ↾ acube 1`.  The two state factors
confine the *unrestricted* variables to balls: with `R` such that `ψ` vanishes outside `B(0,R)`,
the identity `ψ(ℓ(u+s)) ≠ 0` forces `‖u + s‖ < R/ℓ`, and `ψ(ℓ(v+u)) ≠ 0` forces `‖v + u‖ < R/ℓ`.
Since `‖s‖ ≤ 1` a.e. (`s ∈ acube 1`), the first of these gives `‖u‖ ≤ R/ℓ + 1` and then the second
gives `‖v‖ ≤ 2(R/ℓ) + 1`.  Both radii are the *outermost* pair of the four-fold integrand, and the
remaining `(p,v)`-factor is dominated by `(∫|χ|)·|F ‖p‖|·|χ v|` (`abs_bsLf_le`).  Hence, on the
a.e. set `s ∈ acube 1`,

  `‖bsLf ℓ F p v · ψ(ℓ(v+u)) · ψ(ℓ(u+s))‖ ≤ M · 1_{B_u}(u) · |F ‖p‖| · (|χ v| · 1_{B_v}(v)) · 1`,

with `M = (∫|χ|)·Cψ·Cψ`, a product of an `L¹` function of `u`, an `L¹` function of `p` (the
hypothesis `hFi`), an `L¹` function of `v` (the bump `χ` against a bounded set) and the constant
`1` on the finite set `acube 1`; it is `Integrable` by `Integrable.mul_prod`.  The a.e. membership
`s ∈ acube 1` is pulled back from `ae_restrict_mem` along the quasi-measure-preserving projection
`(p,(v,(u,s))) ↦ s`, and the a.e.-strong-measurability of the integrand comes from
`hFi.aestronglyMeasurable` composed with the corresponding projections together with the
continuity of `profHat`, `χ`, `cos` and `ψ`.  `Integrable.mono'` concludes. -/
lemma bsCross_joint {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable
      (fun w : EuclideanSpace ℝ (Fin 3) ×
          (EuclideanSpace ℝ (Fin 3) ×
            (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) =>
        Work.OneBodyKin.bsLf ℓ F w.2.1 w.2.2.1 * ψ (ℓ • (w.2.2.1 + w.1)) *
          ψ (ℓ • (w.1 + w.2.2.2)))
      (MeasureTheory.volume.prod (MeasureTheory.volume.prod (MeasureTheory.volume.prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube 1))))) := by
  classical
  obtain ⟨Cψ, hCψ0, hCψ⟩ := Work.OneBodyKin.exists_bound_of_contDiff_hasCompactSupport hψ hcs
  obtain ⟨R, hR0, hR⟩ := Work.OneBodyKin.exists_radius_eq_zero_of_hasCompactSupport hcs
  -- ### integrability of the four domination factors
  have hAint : Integrable (fun a : ℝ³ =>
      (Metric.closedBall (0 : ℝ³) (R / ℓ + 1)).indicator (fun _ => (1 : ℝ)) a) volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (measure_closedBall_lt_top (x := (0 : ℝ³)) (r := R / ℓ + 1)).ne
  have hBint : Integrable (fun b : ℝ³ => |F ‖b‖|) volume := by
    simpa [Real.norm_eq_abs] using hFi.norm
  have hCint : Integrable (fun c : ℝ³ =>
      |chi c| * (Metric.closedBall (0 : ℝ³) (2 * (R / ℓ) + 1)).indicator (fun _ => (1 : ℝ)) c) volume := by
    refine Integrable.mono' (g := fun c : ℝ³ => |chi c|) ?_ ?_ ?_
    · exact chi_continuous.abs.integrable_of_hasCompactSupport chi_hasCompactSupport.abs
    · exact Measurable.aestronglyMeasurable ((continuous_abs.comp chi_continuous).measurable.mul
        (measurable_const.indicator measurableSet_closedBall))
    · filter_upwards with c
      have hind0 : 0 ≤ (Metric.closedBall (0 : ℝ³) (2 * (R / ℓ) + 1)).indicator (fun _ => (1 : ℝ)) c := by
        simp only [Set.indicator_apply]; split_ifs <;> norm_num
      have hind1 : (Metric.closedBall (0 : ℝ³) (2 * (R / ℓ) + 1)).indicator (fun _ => (1 : ℝ)) c ≤ 1 := by
        simp only [Set.indicator_apply]; split_ifs <;> norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hind0)]
      exact mul_le_of_le_one_right (abs_nonneg _) hind1
  have hDint : Integrable (fun _ : ℝ³ => (1 : ℝ)) ((volume : Measure ℝ³).restrict (acube 1)) := by
    rw [integrable_const_iff]
    right
    exact ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top 1 (by norm_num)⟩
  have hg_int : Integrable
      (fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) =>
        ((∫ z : ℝ³, |chi z|) * Cψ * Cψ) *
          ((Metric.closedBall (0 : ℝ³) (R / ℓ + 1)).indicator (fun _ => (1 : ℝ)) w.1 *
            (|F ‖w.2.1‖| *
              (|chi w.2.2.1| * (Metric.closedBall (0 : ℝ³) (2 * (R / ℓ) + 1)).indicator (fun _ => (1 : ℝ)) w.2.2.1 *
                (1 : ℝ)))))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1))))) := by
    have h1 := hCint.mul_prod hDint
    have h2 := hBint.mul_prod h1
    have h3 := hAint.mul_prod h2
    exact h3.const_mul _
  -- ### the pointwise bound
  have hpoint : ∀ w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)), w.2.2.2 ∈ acube 1 →
      ‖Work.OneBodyKin.bsLf ℓ F w.2.1 w.2.2.1 * ψ (ℓ • (w.2.2.1 + w.1)) *
          ψ (ℓ • (w.1 + w.2.2.2))‖
      ≤ ((∫ z : ℝ³, |chi z|) * Cψ * Cψ) *
          ((Metric.closedBall (0 : ℝ³) (R / ℓ + 1)).indicator (fun _ => (1 : ℝ)) w.1 *
            (|F ‖w.2.1‖| *
              (|chi w.2.2.1| * (Metric.closedBall (0 : ℝ³) (2 * (R / ℓ) + 1)).indicator (fun _ => (1 : ℝ)) w.2.2.1 *
                (1 : ℝ)))) := by
    intro w hw
    by_cases hA : w.1 ∈ Metric.closedBall (0 : ℝ³) (R / ℓ + 1)
    · by_cases hC : w.2.2.1 ∈ Metric.closedBall (0 : ℝ³) (2 * (R / ℓ) + 1)
      · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hC]
        simp only [mul_one]
        have h1 : |Work.OneBodyKin.bsLf ℓ F w.2.1 w.2.2.1| ≤
            (∫ z : ℝ³, |chi z|) * |F ‖w.2.1‖| * |chi w.2.2.1| :=
          Work.OneBodyKin.abs_bsLf_le _ _ _ _
        have h2 : |ψ (ℓ • (w.2.2.1 + w.1))| ≤ Cψ := hCψ _
        have h3 : |ψ (ℓ • (w.1 + w.2.2.2))| ≤ Cψ := hCψ _
        calc ‖Work.OneBodyKin.bsLf ℓ F w.2.1 w.2.2.1 * ψ (ℓ • (w.2.2.1 + w.1)) *
              ψ (ℓ • (w.1 + w.2.2.2))‖
            = |Work.OneBodyKin.bsLf ℓ F w.2.1 w.2.2.1| * |ψ (ℓ • (w.2.2.1 + w.1))| *
                |ψ (ℓ • (w.1 + w.2.2.2))| := by
              rw [Real.norm_eq_abs, abs_mul, abs_mul]
          _ ≤ ((∫ z : ℝ³, |chi z|) * |F ‖w.2.1‖| * |chi w.2.2.1|) * Cψ * Cψ := by gcongr
          _ = ((∫ z : ℝ³, |chi z|) * Cψ * Cψ) * (1 * (|F ‖w.2.1‖| * |chi w.2.2.1|)) := by ring
      · -- `v` is outside its ball: `ψ(ℓ(v+u)) = 0`
        have hCn : 2 * (R / ℓ) + 1 < ‖w.2.2.1‖ := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hC
          exact hC
        have hAn : ‖w.1‖ ≤ R / ℓ + 1 := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hA
          exact hA
        have hsum : R / ℓ < ‖w.2.2.1 + w.1‖ := by
          have h4 : ‖w.2.2.1‖ - ‖w.1‖ ≤ ‖w.2.2.1 + w.1‖ := by
            have h := norm_sub_norm_le w.2.2.1 (-w.1)
            rw [norm_neg, sub_neg_eq_add] at h
            exact h
          linarith
        have hsm : ‖ℓ • (w.2.2.1 + w.1)‖ = ℓ * ‖w.2.2.1 + w.1‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
        have hlt : R < ℓ * ‖w.2.2.1 + w.1‖ := by
          rw [mul_comm]
          exact (div_lt_iff₀ hℓ).mp hsum
        have hψ0 : ψ (ℓ • (w.2.2.1 + w.1)) = 0 := hR _ (by rw [hsm]; exact le_of_lt hlt)
        rw [hψ0]
        rw [Set.indicator_of_notMem hC]
        simp
    · -- `u` is outside its ball: `ψ(ℓ(u+s)) = 0`
      have hAn : R / ℓ + 1 < ‖w.1‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hA
        exact hA
      have hsum : R / ℓ < ‖w.1 + w.2.2.2‖ := by
        have h4 : ‖w.1‖ - ‖w.2.2.2‖ ≤ ‖w.1 + w.2.2.2‖ := by
          have h := norm_sub_norm_le w.1 (-w.2.2.2)
          rw [norm_neg, sub_neg_eq_add] at h
          exact h
        have hD1 : ‖w.2.2.2‖ ≤ 1 := Work.BSKinetic.bs_norm_le_of_mem_acube one_pos hw
        linarith
      have hsm : ‖ℓ • (w.1 + w.2.2.2)‖ = ℓ * ‖w.1 + w.2.2.2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
      have hlt : R < ℓ * ‖w.1 + w.2.2.2‖ := by
        rw [mul_comm]
        exact (div_lt_iff₀ hℓ).mp hsum
      have hψ0 : ψ (ℓ • (w.1 + w.2.2.2)) = 0 := hR _ (by rw [hsm]; exact le_of_lt hlt)
      rw [hψ0]
      rw [Set.indicator_of_notMem hA]
      simp
  -- ### a.e. `s ∈ acube 1`
  have hmem : ∀ᵐ (w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³))) ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))))), w.2.2.2 ∈ acube 1 := by
    have hq3 : Measure.QuasiMeasurePreserving (Prod.snd : ℝ³ × ℝ³ → ℝ³)
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1)))
        ((volume : Measure ℝ³).restrict (acube 1)) := Measure.quasiMeasurePreserving_snd
    have hq2 : Measure.QuasiMeasurePreserving (Prod.snd : ℝ³ × (ℝ³ × ℝ³) → ℝ³ × ℝ³)
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))))
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))) :=
      Measure.quasiMeasurePreserving_snd
    have hq1 : Measure.QuasiMeasurePreserving (Prod.snd : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) → ℝ³ × (ℝ³ × ℝ³))
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
          ((volume : Measure ℝ³).restrict (acube 1)))))
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1)))) :=
      Measure.quasiMeasurePreserving_snd
    have hq := hq3.comp (hq2.comp hq1)
    have hres : ∀ᵐ (w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³))) ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))))),
        (Prod.snd ∘ (Prod.snd ∘ Prod.snd)) w ∈ acube 1 := hq.ae (ae_restrict_mem (acube_measurable 1))
    simpa only [Function.comp_apply] using hres
  -- ### a.e.-strong-measurability of the integrand
  have hmeasB : AEStronglyMeasurable (fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) => F ‖w.2.1‖)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1))))) := by
    have h1 : AEStronglyMeasurable (fun x : ℝ³ × (ℝ³ × ℝ³) => F ‖x.1‖)
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1)))) :=
      hFi.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    exact h1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hbsLf_meas : AEStronglyMeasurable
      (fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) => Work.OneBodyKin.bsLf ℓ F w.2.1 w.2.2.1)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1))))) := by
    simp only [Work.OneBodyKin.bsLf]
    exact (((hmeasB.mul ((Work.OneBodyKin.continuous_profHat.comp (by fun_prop)).aestronglyMeasurable)).mul
      ((chi_continuous.comp (by fun_prop)).aestronglyMeasurable)).mul
      ((Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable))
  have h1meas : AEStronglyMeasurable (fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) => ψ (ℓ • (w.2.2.1 + w.1)))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1))))) :=
    (hψ.continuous.comp (by fun_prop)).aestronglyMeasurable
  have h2meas : AEStronglyMeasurable (fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) => ψ (ℓ • (w.1 + w.2.2.2)))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1))))) :=
    (hψ.continuous.comp (by fun_prop)).aestronglyMeasurable
  have hf_meas : AEStronglyMeasurable
      (fun w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³)) =>
        Work.OneBodyKin.bsLf ℓ F w.2.1 w.2.2.1 * ψ (ℓ • (w.2.2.1 + w.1)) * ψ (ℓ • (w.1 + w.2.2.2)))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube 1))))) :=
    (hbsLf_meas.mul h1meas).mul h2meas
  -- ### assemble
  have hae : ∀ᵐ (w : ℝ³ × (ℝ³ × (ℝ³ × ℝ³))) ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))))),
      ‖Work.OneBodyKin.bsLf ℓ F w.2.1 w.2.2.1 * ψ (ℓ • (w.2.2.1 + w.1)) * ψ (ℓ • (w.1 + w.2.2.2))‖
      ≤ ((∫ z : ℝ³, |chi z|) * Cψ * Cψ) *
          ((Metric.closedBall (0 : ℝ³) (R / ℓ + 1)).indicator (fun _ => (1 : ℝ)) w.1 *
            (|F ‖w.2.1‖| *
              (|chi w.2.2.1| * (Metric.closedBall (0 : ℝ³) (2 * (R / ℓ) + 1)).indicator (fun _ => (1 : ℝ)) w.2.2.1 *
                (1 : ℝ)))) :=
    hmem.mono (fun w hw => hpoint w hw)
  exact Integrable.mono' hg_int hf_meas hae

end Work.OneBodyKin.Cross
