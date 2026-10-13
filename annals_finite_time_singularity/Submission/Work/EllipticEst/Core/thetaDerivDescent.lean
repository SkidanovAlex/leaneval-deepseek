/-
Copyright: work module for the Elgindi finite-time singularity project.

# Descent from `∂_θ²` to `∂_θ` against the weight `sin(2θ)^{-η}`

This file proves `Work.EllipticEst.Core.thetaDerivDescent`: for `f` of class `C²` on the open
angular interval `(0, π/2)`, integrability of `(f'')² · sin(2θ)^{-η}` over `Iθ = [0, π/2]`
implies integrability of `(f')² · sin(2θ)^{-η}` over `Iθ` (`η = 99/100 < 1`).

## Mathematics

The weight `sin(2θ)^{-η}` is singular at both endpoints but *integrable* there (`η < 1`), and
it is `≥ 1` everywhere on `(0, π/2)`.  Hence, from `(f'')² sin(2θ)^{-η} ∈ L¹`:

* `|f''| ≤ 1 + (f'')²·sin(2θ)^{-η}` a.e. on `Iθ`, so `f'' ∈ L¹(Iθ)`;
* for `θ₀ = π/4` the fundamental theorem of calculus gives, for every `θ ∈ (0, π/2)`,
  `f'(θ) - f'(θ₀) = ∫_{θ₀}^{θ} f''`, whence
  `|f'(θ)| ≤ C := |f'(π/4)| + ∫_{Iθ} |f''|`, a bound *uniform* on the whole open interval;
* consequently `(f')² sin(2θ)^{-η} ≤ C² sin(2θ)^{-η}` pointwise on `Iθ` and the right-hand side
  is integrable (the endpoint terms `θ = 0, π/2` are harmless: `sin(2θ)^{-η} = 0` there by
  Lean's `Real.zero_rpow`).

The interval `Iθ` differs from `(0, π/2)` by the null set `{0, π/2}`, so all measurability
questions are settled on the open interval, where `f'` and `sin(2θ)^{-η}` are continuous.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

theorem thetaDerivDescent : ∀ (f : ℝ → ℝ),
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
  intro f hf hint
  -- `(0,π/2) ⊆ Iθ`
  have hIoo_sub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx; rw [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- the two intervals carry the same measure (`{0, π/2}` is null)
  have hrestrict : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc' (by simp) (by simp))
  -- regularity of `f'`, `f''` on the open interval
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) :=
    hd1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  -- `sin(2θ)^{-η} ≥ 1` on the open interval (since `0 < sin(2θ) ≤ 1` there)
  have hth_one : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 1 ≤ Work.FTS.EllipticEst.thEta θ := by
    intro θ hθ
    have hs0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have h : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1 (by linarith [Work.Spaces.eta_pos])
    simpa [Work.FTS.EllipticEst.thEta] using h
  -- Step 1: `|f''| ∈ L¹(Iθ)`, because `|f''| ≤ 1 + (f'')²·sin(2θ)^{-η}`
  have hgint : MeasureTheory.IntegrableOn (fun θ => |deriv (deriv f) θ|) Work.Spaces.Iθ := by
    have hdom : MeasureTheory.Integrable
        (fun θ => 1 + (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have h1 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
          (volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integrableOn_const (by
          rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      exact h1.add hint
    refine MeasureTheory.Integrable.mono' (g := fun θ => 1 + (deriv (deriv f) θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ) hdom ?_ ?_
    · rw [← hrestrict]
      exact hd2.abs.aestronglyMeasurable measurableSet_Ioo
    · rw [← hrestrict]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hth : 1 ≤ Work.FTS.EllipticEst.thEta θ := hth_one θ hθ
      have hsq : 0 ≤ (deriv (deriv f) θ) ^ 2 := sq_nonneg _
      have habs : |deriv (deriv f) θ| ≤ (deriv (deriv f) θ) ^ 2 + 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (deriv (deriv f) θ)]
      have hmul : (deriv (deriv f) θ) ^ 2 * 1 ≤ (deriv (deriv f) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ :=
        mul_le_mul_of_nonneg_left hth hsq
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      linarith
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hquarter : (Real.pi / 4 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- `∫_{Iθ}|f''|` written as an interval integral
  have hII : IntervalIntegrable (fun x => |deriv (deriv f) x|) volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2.le]
    refine hgint.mono_set ?_
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc, Set.mem_Ioc] at *
    exact ⟨le_of_lt hx.1, hx.2⟩
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |deriv (deriv f) x|)
      = ∫ x in Work.Spaces.Iθ, |deriv (deriv f) x| := by
    rw [intervalIntegral.integral_of_le hpi2.le, Work.Spaces.Iθ,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- Step 2: the fundamental-theorem-of-calculus difference bound at `θ₀ = π/4`
  have hFTCbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv f θ - deriv f (Real.pi / 4)| ≤ ∫ s in Work.Spaces.Iθ, |deriv (deriv f) s| := by
    intro θ hθ
    have hsub : Set.uIcc θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hquarter.2⟩
      · exact ⟨lt_of_lt_of_le hquarter.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    have hcd : ContDiffOn ℝ 1 (deriv f) (Set.uIcc θ (Real.pi / 4)) := hd1.mono hsub
    have hFTC : (∫ x in θ..(Real.pi / 4), deriv (deriv f) x)
        = deriv f (Real.pi / 4) - deriv f θ :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc hcd
    rcases le_total θ (Real.pi / 4) with hle | hle
    · have h1 : |∫ x in θ..(Real.pi / 4), deriv (deriv f) x|
          ≤ ∫ x in θ..(Real.pi / 4), |deriv (deriv f) x| :=
        intervalIntegral.abs_integral_le_integral_abs hle
      have h2 : (∫ x in θ..(Real.pi / 4), |deriv (deriv f) x|)
          ≤ ∫ x in Work.Spaces.Iθ, |deriv (deriv f) x| := by
        rw [← hIeq]
        exact intervalIntegral.integral_mono_interval (by linarith [hθ.1]) hle
          (by linarith [hquarter.2]) (Eventually.of_forall (fun x => abs_nonneg _)) hII
      have h3 : deriv f θ - deriv f (Real.pi / 4)
          = -(∫ x in θ..(Real.pi / 4), deriv (deriv f) x) := by
        linarith
      rw [h3, abs_neg]
      linarith
    · have h1 : |∫ x in (Real.pi / 4)..θ, deriv (deriv f) x|
          ≤ ∫ x in (Real.pi / 4)..θ, |deriv (deriv f) x| :=
        intervalIntegral.abs_integral_le_integral_abs hle
      have h2 : (∫ x in (Real.pi / 4)..θ, |deriv (deriv f) x|)
          ≤ ∫ x in Work.Spaces.Iθ, |deriv (deriv f) x| := by
        rw [← hIeq]
        exact intervalIntegral.integral_mono_interval (by linarith [hquarter.1]) hle
          (by linarith [hθ.2]) (Eventually.of_forall (fun x => abs_nonneg _)) hII
      have h3 : deriv f θ - deriv f (Real.pi / 4)
          = ∫ x in (Real.pi / 4)..θ, deriv (deriv f) x := by
        rw [intervalIntegral.integral_symm, hFTC]; ring
      rw [h3]
      linarith
  -- Step 3: `|f'|` is uniformly bounded on `(0, π/2)`
  set C : ℝ := |deriv f (Real.pi / 4)| + ∫ s in Work.Spaces.Iθ, |deriv (deriv f) s| with hCdef
  have hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C := by
    intro θ hθ
    have h := hFTCbound θ hθ
    have h2 : deriv f θ = deriv f (Real.pi / 4) + (deriv f θ - deriv f (Real.pi / 4)) := by ring
    have h3 : |deriv f (Real.pi / 4) + (deriv f θ - deriv f (Real.pi / 4))|
        ≤ |deriv f (Real.pi / 4)| + |deriv f θ - deriv f (Real.pi / 4)| := abs_add_le _ _
    rw [h2, hCdef]
    linarith
  -- continuity of the weight on the open interval
  have hth_cont : ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
    have h2 : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo 0 (Real.pi / 2)) := h1.rpow_const (p := -(Work.Spaces.eta))
      (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))))
    exact h2
  -- Step 4: dominated integrability on `(0, π/2)`, then transfer to `Iθ`
  change MeasureTheory.Integrable (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
    (volume.restrict Work.Spaces.Iθ)
  rw [← hrestrict]
  refine MeasureTheory.Integrable.mono'
    (f := fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
    (g := fun θ => C ^ 2 * Work.FTS.EllipticEst.thEta θ) ?_ ?_ ?_
  · rw [hrestrict]
    exact (Work.FTS.EllipticEst.integrableOn_thEta).1.const_mul (C ^ 2)
  · exact ((hd1.continuousOn.pow 2).mul hth_cont).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : |deriv f θ| ≤ C := hbound θ hθ
    have hth : 0 ≤ Work.FTS.EllipticEst.thEta θ :=
      Work.FTS.EllipticEst.thEta_nonneg (hIoo_sub ⟨hθ.1, hθ.2⟩)
    have hsq : (deriv f θ) ^ 2 ≤ C ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (deriv f θ)) h1 2
      rwa [sq_abs] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hth)]
    exact mul_le_mul_of_nonneg_right hsq hth

end Work.EllipticEst.Core
