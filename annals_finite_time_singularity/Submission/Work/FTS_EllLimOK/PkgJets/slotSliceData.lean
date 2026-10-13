import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.HkMem_zero_diff
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Elliptic.integrableOn_of_rpow_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Elementary endpoint estimates

The angular weight `sin(2θ)^{-η}` is integrable on `[0,π/2]` (`η < 1`), so the only real
content of the slice integrability of the level-`0` `ℋ`-integrand of `Ψ / cos θ` is the
*boundedness* of `θ ↦ Ψ z θ / cos θ` on the closed interval.  Two facts are used:

* `cos θ` has the same size as `π/2 - θ` (Jordan's inequality, `Real.mul_le_sin`);
* `BoxReg Ψ` together with `Ψ z (π/2) = 0` forces `|Ψ z θ| ≲ (π/2 - θ)` (mean value
  inequality on the closed box, `Convex.norm_image_sub_le_of_norm_derivWithin_le`). -/

/-- Jordan's inequality at the right endpoint: `π/2 - θ ≤ (π/2) cos θ` on `[0,π/2]`. -/
theorem pi_div_two_sub_le_mul_cos {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    π / 2 - θ ≤ (π / 2) * Real.cos θ := by
  have hδ : π / 2 - θ ∈ Set.Icc (0 : ℝ) (π / 2) :=
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hjordan : 2 / π * (π / 2 - θ) ≤ Real.sin (π / 2 - θ) := Real.mul_le_sin hδ.1 hδ.2
  have hcos : Real.cos θ = Real.sin (π / 2 - θ) := by
    have h := Real.cos_pi_div_two_sub (π / 2 - θ)
    rw [show π / 2 - (π / 2 - θ) = θ from by ring] at h
    exact h
  have h1 : (π / 2) * (2 / π * (π / 2 - θ)) ≤ (π / 2) * Real.cos θ := by
    rw [hcos]
    exact mul_le_mul_of_nonneg_left hjordan (by positivity)
  have h2 : (π / 2) * (2 / π * (π / 2 - θ)) = π / 2 - θ := by
    field_simp
  linarith [h1, h2]

/-- **`C¹`-vanishing at the right endpoint.**  A function of class `C²` on `[0,π/2]` which
vanishes at `π/2` is dominated by a constant multiple of `π/2 - θ`: the mean value
inequality applied to `u` on the (convex) interval, the derivative bound being a bound for
the within-derivative, which is continuous on the compact interval by `C²`-ness. -/
theorem exists_le_mul_pi_div_two_sub {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Icc (0 : ℝ) (π / 2))) (h0 : u (π / 2) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), |u θ| ≤ M * (π / 2 - θ) := by
  have hlt : (0 : ℝ) < π / 2 := by positivity
  have hs : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hlt
  have hcont : ContinuousOn (derivWithin u (Set.Icc (0 : ℝ) (π / 2)))
      (Set.Icc (0 : ℝ) (π / 2)) := hu.continuousOn_derivWithin hs (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hdiff : DifferentiableOn ℝ u (Set.Icc (0 : ℝ) (π / 2)) := hu.differentiableOn (by norm_num)
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have hmvt := (convex_Icc (0 : ℝ) (π / 2)).norm_image_sub_le_of_norm_derivWithin_le hdiff hC
    (right_mem_Icc.mpr hlt.le) hθ
  rw [Real.norm_eq_abs, h0, sub_zero] at hmvt
  have hsub : ‖θ - π / 2‖ = π / 2 - θ := by
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hθ.2])]
    ring
  rw [hsub] at hmvt
  have h2 : C * (π / 2 - θ) ≤ max C 0 * (π / 2 - θ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hθ.2])
  linarith

/-- At level `k = 0` the `ℋ`-integrand is a single square, expanded into the three explicit
weight factors `(f z θ)² · w z² · sin(2θ)^{-η}`. -/
theorem HkIntegrand_zero_slice_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [Work.FTS_EllLimOK.HkIntegrand_zero_eq]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (f z θ) (Work.Spaces.w z) hθ

theorem slotSliceData {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hbox : Work.FTS_EllLimOK.BoxReg Ψ)
    (hdir : ∀ z ∈ Set.Ioi (0 : ℝ), Ψ z (π / 2) = 0) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ / Real.cos θ) z θ)
      Work.Spaces.Iθ) ∧
    AEMeasurable (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ / Real.cos θ) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- ## The quotient `Ψ / cos θ` is continuous on the open quadrant.
  have hquot : ContinuousOn (Function.uncurry (fun z θ : ℝ => Ψ z θ / Real.cos θ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    show ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2 / Real.cos p.2) _
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      (Work.FTS_EllLimOK.BoxReg.contDiffOn_Qd hbox).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      Real.continuous_cos.comp_continuousOn continuousOn_snd
    exact h1.div h2 (fun p hp =>
      ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hp.2.1, Real.pi_pos], by linarith [hp.2.2]⟩))
  constructor
  · -- ## Integrability of the angular slice, for every `z ∈ Iz`
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with hz0 | hzpos
    · -- `z = 0`: the radial weight vanishes identically
      subst hz0
      rw [show (fun θ : ℝ =>
            Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ / Real.cos θ) 0 θ) = fun _ => 0 from
          funext fun θ => by
            rw [Work.FTS_EllLimOK.HkIntegrand_zero_eq]
            simp [Work.Spaces.w]]
      exact integrableOn_zero
    · -- `z > 0`: `Ψ z ·` is `C²` on the closed interval and vanishes at `π/2`
      have hslice : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc (0 : ℝ) (π / 2)) :=
        hbox.slice hzpos
      obtain ⟨M, hM0, hM⟩ := exists_le_mul_pi_div_two_sub hslice (hdir z hzpos)
      -- `|Ψ z θ / cos θ| ≤ M · π/2` on the whole interval
      have hK : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), |Ψ z θ / Real.cos θ| ≤ M * (π / 2) := by
        intro θ hθ
        rcases eq_or_lt_of_le hθ.2 with hθ2 | hθ2
        · rw [hθ2, hdir z hzpos, zero_div, abs_zero]
          exact mul_nonneg hM0 (by positivity)
        · have hcos : 0 < Real.cos θ :=
            Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ2⟩
          have h1 : |Ψ z θ| ≤ M * (π / 2 - θ) := hM θ hθ
          have h2 : π / 2 - θ ≤ (π / 2) * Real.cos θ := pi_div_two_sub_le_mul_cos hθ
          have h3 : M * (π / 2 - θ) ≤ M * ((π / 2) * Real.cos θ) :=
            mul_le_mul_of_nonneg_left h2 hM0
          rw [abs_div, abs_of_pos hcos, div_le_iff₀ hcos]
          nlinarith [h1, h3]
      -- the whole slice integrand is dominated by `C · (θ ^ -η + (π/2 - θ) ^ -η)`
      refine Work.Elliptic.integrableOn_of_rpow_majorant
        (η := Work.Spaces.eta)
        (C := (M * (π / 2)) ^ 2 * (Work.Spaces.w z) ^ 2 * (π / 4) ^ (Work.Spaces.eta))
        (g := fun θ : ℝ =>
          Work.Spaces.HkIntegrand α 0 (fun z θ : ℝ => Ψ z θ / Real.cos θ) z θ)
        (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta]) ?_ ?_ ?_
      · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Real.rpow_nonneg (by positivity) _)
      · -- continuity on the open interval, from the continuity of `Ψ z ·` on the closed box
        have hΨ : ContinuousOn (fun θ : ℝ => Ψ z θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
          (hbox.slice hzpos).continuousOn.mono (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
        have hratio : ContinuousOn (fun θ : ℝ => Ψ z θ / Real.cos θ)
            (Set.Ioo (0 : ℝ) (π / 2)) :=
          hΨ.div Real.continuous_cos.continuousOn (fun θ hθ => ne_of_gt
            (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩))
        have hwt : ContinuousOn (fun θ : ℝ =>
            Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            (Set.Ioo (0 : ℝ) (π / 2)) :=
          continuousOn_const.div Work.FTS_EllLimOK.continuousOn_sin_two_rpow
            (fun θ hθ => ne_of_gt (Real.rpow_pos_of_pos
              (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])) _))
        have hexp : ContinuousOn (fun θ : ℝ => (Ψ z θ / Real.cos θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            (Set.Ioo (0 : ℝ) (π / 2)) := (hratio.mul hwt).pow 2
        exact ContinuousOn.congr hexp
          (fun θ _ => Work.FTS_EllLimOK.HkIntegrand_zero_eq α
            (fun z θ : ℝ => Ψ z θ / Real.cos θ) z θ)
      · -- the pointwise majorant
        intro θ hθ
        have hθI : θ ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        have hsin_nn : 0 ≤ Real.sin (2 * θ) :=
          Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
        have hS : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hsin_nn _
        have hsq : (Ψ z θ / Real.cos θ) ^ 2 ≤ (M * (π / 2)) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hK θ hθI) 2
        have hsin : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            ≤ (π / 4) ^ (Work.Spaces.eta)
              * (θ ^ (-(Work.Spaces.eta)) + (π / 2 - θ) ^ (-(Work.Spaces.eta))) :=
          Work.Spaces.sin_rpow_le_majorant Work.Spaces.eta θ Work.Spaces.eta_pos hθI
        have hid := HkIntegrand_zero_slice_eq α (fun z θ : ℝ => Ψ z θ / Real.cos θ) z θ hθI
        have hnn : 0 ≤ (Ψ z θ / Real.cos θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hS
        rw [hid, Real.norm_eq_abs, abs_of_nonneg hnn]
        calc (Ψ z θ / Real.cos θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            ≤ (M * (π / 2)) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) hS
          _ ≤ (M * (π / 2)) ^ 2 * (Work.Spaces.w z) ^ 2
              * ((π / 4) ^ (Work.Spaces.eta)
                * (θ ^ (-(Work.Spaces.eta)) + (π / 2 - θ) ^ (-(Work.Spaces.eta)))) :=
              mul_le_mul_of_nonneg_left hsin (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          _ = (M * (π / 2)) ^ 2 * (Work.Spaces.w z) ^ 2 * (π / 4) ^ (Work.Spaces.eta)
              * (θ ^ (-(Work.Spaces.eta)) + (π / 2 - θ) ^ (-(Work.Spaces.eta))) := by ring
  · -- ## Almost everywhere strong measurability of the uncurried integrand
    exact (Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS_EllLimOK.continuousOn_HkIntegrand_zero α hquot)).aemeasurable

end Work.FTS_EllLimOK.PkgJets
