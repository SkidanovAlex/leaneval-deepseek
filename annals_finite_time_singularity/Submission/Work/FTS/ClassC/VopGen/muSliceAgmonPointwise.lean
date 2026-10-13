/-
Work module for the Elgindi finite-time singularity project.

# The pointwise Agmon inequality on a single angular slice, light weight

For `0 < α ≤ 1/4` and `f : ℝ → ℝ` of class `C²` on the open interval `(0, π/2)`, with the two
endpoint traces `f → 0` at `0⁺` and at `(π/2)⁻`, and with the weighted second derivative
`(f'')² sin(2θ)^{2-γ(α)}` integrable, one has

  `∫_θ (f')² σ ≤ -∫_θ f f'' σ`,   `σ = sin(2θ)^{2-γ(α)}`,  `γ(α) = 1 + α/10`.

This is the `μ`-weight slice Agmon inequality consumed by the level-`2` core slot
(`VopGen.coreASlot11`): it is the sharp (one-`√`-free) form of the slice interpolation, valid
because the light weight `σ` is *concave* on `(0, π/2)`.

## Proof

Write `a := 2 - γ(α) ∈ (0,1)`.  The double angular integration by parts for the light weight
(`TT.slice_ibp_light`, the already-proved generic brick) gives, whenever its five integrability
and four boundary clauses hold,

  `∫ (f')²σ = -∫ f f''σ - 2a ∫ f²σ - 2a(1-a) ∫ f²cos²(2θ) sin(2θ)^{a-2}`,

and the last two terms are `≤ 0` because their integrands are nonnegative and `0 < a < 1`.  The
side conditions (`σψ'²`, `σψ''ψ`, `σ'ψψ'`, `σψ²`, `σ''ψ²`-type integrability and the vanishing of
`ψψ'σ` and `ψ²σ'` at both endpoints) are *not* hypotheses here: they are derived from `f → 0` at
the endpoints and `(f'')²σ ∈ L¹`, exactly as in the sibling `InterpJumpAux.sliceAgmonVanishing`
(whose environment also contains `exists_deriv_abs_bound`, bounding `|f'|` by a constant `M` on
`(0,π/2)`, and the two value bounds `|f θ| ≤ M θ`, `|f θ| ≤ M (π/2 - θ)`, whence
`|f θ| ≤ M sin(2θ)`).  The elementary weight facts and the four boundary limits live in
`Work.FTS.ClassC.VopGen.muSliceAgmonPointwiseAux`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Prop.mixedSlotInterpEta
import Submission.Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.sliceAgmonVanishing
import Submission.Work.FTS.EllipticEst.TT.sliceIBPLight
import Submission.Work.FTS.ClassC.VopGen.muSliceAgmonPointwiseAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.VopGen

open MeasureTheory Set Filter
open scoped Real Topology

/-- The light angular weight of the `μ`-slot: `σ = TT.sigR (2 - γ(α))`. -/
local notation "𝔰[" α "]" => Work.FTS.EllipticEst.TT.sigR (2 - Work.Spaces.gam α)

/-- The derivative of the light angular weight: `σ' = TT.sigDR (2 - γ(α))`. -/
local notation "𝔡[" α "]" => Work.FTS.EllipticEst.TT.sigDR (2 - Work.Spaces.gam α)

/-! ## The slice Agmon inequality -/

theorem muSliceAgmonPointwise {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {f : ℝ → ℝ}
    (hcd : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hT0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hT1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hD : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  have hα1 : α ≤ 1 := by linarith
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  have hp1 : 2 - Work.Spaces.gam α < 1 := Work.FTS.EllipticEst.Cores.sub_gam_lt_one hα
  have hpne : 2 - Work.Spaces.gam α ≠ 0 := ne_of_gt hp0
  have hp1m : 0 ≤ 1 - (2 - Work.Spaces.gam α) := by linarith
  -- the weight, its continuity and its integrability on `(0, π/2)`
  have hsigRcont : Continuous (𝔰[α]) := by
    have h : (𝔰[α]) = fun t : ℝ => (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α) := rfl
    rw [h]
    exact Work.FTS.EllipticEst.Cores.sigA_continuous α hα1
  have hσIoo : IntegrableOn (𝔰[α]) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsigRcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hσnn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ 𝔰[α] θ := fun θ hθ => (sigR_gam_pos α θ hθ).le
  -- the hypothesis in the `sigA` spelling, for the endpoint-control lemmas
  have hD' : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.Cores.sigA α θ)
      (Set.Ioo 0 (Real.pi / 2)) := hD
  obtain ⟨M, hMpos, hMbd⟩ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.exists_deriv_abs_bound hα hα1 hcd hD'
  have hMnn : 0 ≤ M := hMpos.le
  -- ## endpoint control of `f` and `f'`
  have hdcont : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    (hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn
  have hddcont : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) :=
    (((hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 0) (by norm_num))).continuousOn
  have hdint : IntegrableOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) := by
    have hconst : IntegrableOn (fun _ : ℝ => M) (Set.Ioo 0 (Real.pi / 2)) := by
      refine MeasureTheory.integrableOn_const ?_ ?_
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
      · simp
    exact integrableOn_Ioo_of_le hconst hdcont (fun θ hθ => hMbd θ hθ)
  have hvalL := Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.value_abs_le_mul_left
    hcd hdint hT0 hMnn hMbd
  have hvalR := Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.value_abs_le_mul_right
    hcd hdint hT1 hMnn hMbd
  have hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ) := by
    intro θ hθ
    have hSnn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    rcases le_or_gt θ (Real.pi / 4) with hle | hlt
    · have hge : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
        have h := Real.mul_le_sin (x := 2 * θ) (by linarith [hθ.1])
          (by linarith [hle, Real.pi_pos])
        rwa [show (2 : ℝ) / Real.pi * (2 * θ) = (4 / Real.pi) * θ by ring] at h
      have hge' : θ ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
        have h1 : (Real.pi / 4) * ((4 / Real.pi) * θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) :=
          mul_le_mul_of_nonneg_left hge (by positivity)
        rwa [show (Real.pi / 4) * ((4 / Real.pi) * θ) = θ by field_simp] at h1
      calc |f θ| ≤ M * θ := hvalL θ hθ
        _ ≤ M * ((Real.pi / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hge' hMnn
        _ ≤ M * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hSnn, Real.pi_lt_four]) hMnn
    · have hge : (4 / Real.pi) * (Real.pi / 2 - θ)
          ≤ Real.sin (2 * (Real.pi / 2 - θ)) := by
        have h := Real.mul_le_sin (x := 2 * (Real.pi / 2 - θ)) (by linarith [hθ.2])
          (by linarith [hlt, Real.pi_pos])
        rwa [show (2 : ℝ) / Real.pi * (2 * (Real.pi / 2 - θ))
          = (4 / Real.pi) * (Real.pi / 2 - θ) by ring] at h
      have h2θ : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
        rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
      rw [h2θ] at hge
      have hge' : Real.pi / 2 - θ ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
        have h1 : (Real.pi / 4) * ((4 / Real.pi) * (Real.pi / 2 - θ))
            ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hge (by positivity)
        rwa [show (Real.pi / 4) * ((4 / Real.pi) * (Real.pi / 2 - θ)) = Real.pi / 2 - θ from by
          field_simp] at h1
      calc |f θ| ≤ M * (Real.pi / 2 - θ) := hvalR θ hθ
        _ ≤ M * ((Real.pi / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hge' hMnn
        _ ≤ M * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hSnn, Real.pi_lt_four]) hMnn
  -- ## the five integrability clauses of the light-weight integration by parts
  have hI1 : IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * 𝔰[α] θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le (hσIoo.const_mul (M ^ 2)) ((hdcont.pow 2).mul hsigRcont.continuousOn)
        (fun θ hθ => by
          have hsq : (deriv f θ) ^ 2 ≤ M ^ 2 := by
            have h := hMbd θ hθ
            have h2 := pow_le_pow_left₀ (abs_nonneg (deriv f θ)) h 2
            rwa [sq_abs] at h2
          rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)), abs_of_nonneg (hσnn θ hθ)]
          exact mul_le_mul_of_nonneg_right hsq (hσnn θ hθ)))
  have hddσIoo : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * 𝔰[α] θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    simpa only [Work.FTS.EllipticEst.TT.sigR] using hD
  have hI2 : IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * 𝔰[α] θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le ((hσIoo.const_mul (M ^ 2)).add hddσIoo)
        ((hcd.continuousOn.mul hddcont).mul hsigRcont.continuousOn)
        (fun θ hθ => by
          have hfabs : |f θ| ≤ M := by
            calc |f θ| ≤ M * Real.sin (2 * θ) := hfS θ hθ
              _ ≤ M * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) hMnn
              _ = M := by ring
          have hamb : M * |deriv (deriv f) θ| ≤ (M ^ 2 + (deriv (deriv f) θ) ^ 2) / 2 := by
            have h := two_mul_le_add_sq M |deriv (deriv f) θ|
            rw [sq_abs] at h
            linarith [h]
          calc |f θ * deriv (deriv f) θ * 𝔰[α] θ|
              = |f θ| * |deriv (deriv f) θ| * 𝔰[α] θ := by
                rw [abs_mul, abs_mul, abs_of_nonneg (hσnn θ hθ)]
            _ ≤ M * |deriv (deriv f) θ| * 𝔰[α] θ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfabs (abs_nonneg _))
                  (hσnn θ hθ)
            _ ≤ ((M ^ 2 + (deriv (deriv f) θ) ^ 2) / 2) * 𝔰[α] θ :=
                mul_le_mul_of_nonneg_right hamb (hσnn θ hθ)
            _ ≤ M ^ 2 * 𝔰[α] θ + (deriv (deriv f) θ) ^ 2 * 𝔰[α] θ := by
                nlinarith [hσnn θ hθ, sq_nonneg M, sq_nonneg (deriv (deriv f) θ)]))
  have hI3 : IntegrableOn (fun θ : ℝ => f θ * deriv f θ * 𝔡[α] θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le (hσIoo.const_mul (2 * (2 - Work.Spaces.gam α) * M ^ 2))
        ((hcd.continuousOn.mul hdcont).mul (sigDR_gam_continuousOn α))
        (fun θ hθ => by
          have hSp : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hθ
          have hSnn : 0 ≤ Real.sin (2 * θ) := hSp.le
          have hpowid : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1)
              = 𝔰[α] θ := by
            simp only [Work.FTS.EllipticEst.TT.sigR]
            exact Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.mul_rpow_sub_one hSp hpne
          calc |f θ * deriv f θ * 𝔡[α] θ|
              = |f θ| * |deriv f θ| * |𝔡[α] θ| := by rw [abs_mul, abs_mul]
            _ ≤ (M * Real.sin (2 * θ)) * M
                  * (2 * (2 - Work.Spaces.gam α)
                    * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1)) :=
                mul_le_mul (mul_le_mul (hfS θ hθ) (hMbd θ hθ) (abs_nonneg _)
                  (mul_nonneg hMnn hSnn)) (sigDR_gam_abs_le hα1 hSp) (abs_nonneg _)
                  (mul_nonneg (mul_nonneg hMnn hSnn) hMnn)
            _ = 2 * (2 - Work.Spaces.gam α) * M ^ 2
                  * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1)) := by ring
            _ = 2 * (2 - Work.Spaces.gam α) * M ^ 2 * 𝔰[α] θ := by rw [hpowid]))
  have hI4 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * 𝔰[α] θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le (hσIoo.const_mul (M ^ 2)) ((hcd.continuousOn.pow 2).mul hsigRcont.continuousOn)
        (fun θ hθ => by
          have hu2 : (f θ) ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
            have h0' : (0:ℝ) ≤ |f θ| := abs_nonneg _
            calc (f θ) ^ 2 = |f θ| ^ 2 := (sq_abs (f θ)).symm
              _ ≤ (M * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ h0' (hfS θ hθ) 2
          have hMS : (M * Real.sin (2 * θ)) ^ 2 ≤ M ^ 2 := by
            have hSnn : 0 ≤ Real.sin (2 * θ) :=
              Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
                (by linarith [hθ.2, Real.pi_pos])
            have h1 : M * Real.sin (2 * θ) ≤ M * 1 :=
              mul_le_mul_of_nonneg_left (Real.sin_le_one _) hMnn
            calc (M * Real.sin (2 * θ)) ^ 2 ≤ (M * 1) ^ 2 :=
                  pow_le_pow_left₀ (mul_nonneg hMnn hSnn) h1 2
              _ = M ^ 2 := by ring
          rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg (hσnn θ hθ)]
          exact mul_le_mul_of_nonneg_right (le_trans hu2 hMS) (hσnn θ hθ)))
  have hcos2cont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
  have hsin2cont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun x hx => Or.inl (ne_of_gt (Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hx)))
  have hI5 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le (hσIoo.const_mul (M * M))
        (((hcd.continuousOn.pow 2).mul hcos2cont).mul hsin2cont)
        (fun θ hθ => by
          have hSp : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hθ
          have hSpow : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) :=
            Real.rpow_nonneg hSp.le _
          have hc2 : Real.cos (2 * θ) ^ 2 ≤ 1 := by
            have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
            have h2 : |Real.cos (2 * θ)| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
            rwa [sq_abs, one_pow] at h2
          have hu2 : (f θ) ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
            have h0' : (0:ℝ) ≤ |f θ| := abs_nonneg _
            calc (f θ) ^ 2 = |f θ| ^ 2 := (sq_abs (f θ)).symm
              _ ≤ (M * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ h0' (hfS θ hθ) 2
          have h5 : (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) ≤ M * M * 𝔰[α] θ := by
            have hstep : (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)
                ≤ M * M * ((Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) := by
              calc (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)
                  = ((M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2)
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) := by ring
                _ ≤ ((M * Real.sin (2 * θ)) ^ 2 * 1)
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)) hSpow
                _ = M * M * ((Real.sin (2 * θ)) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) := by ring
            rw [Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.mul_rpow_sub_two hSp] at hstep
            simpa only [Work.FTS.EllipticEst.TT.sigR] using hstep
          have hnn : 0 ≤ (f θ) ^ 2 * Real.cos (2 * θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) :=
            mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hSpow
          rw [abs_of_nonneg hnn]
          calc (f θ) ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)
              = (f θ) ^ 2 * (Real.cos (2 * θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) := by ring
            _ ≤ (M * Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) :=
                mul_le_mul_of_nonneg_right hu2 (mul_nonneg (sq_nonneg _) hSpow)
            _ = (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) := by ring
            _ ≤ M * M * 𝔰[α] θ := h5))
  -- ## the four boundary clauses
  have hb1 := tendsto_ff'_sigR_zero (α := α) (M := M) hα1 hMnn hfS hMbd
  have hb2 := tendsto_ff'_sigR_zero_right (α := α) (M := M) hα1 hMnn hfS hMbd
  have hb3 := tendsto_sq_sigDR_zero (α := α) (M := M) hα1 hMnn hfS
  have hb4 := tendsto_sq_sigDR_zero_right (α := α) (M := M) hα1 hMnn hfS
  -- ## the double angular integration by parts
  have hibp := Work.FTS.EllipticEst.TT.slice_ibp_light (2 - Work.Spaces.gam α) hp0 hp1 hcd
    hI1 hI2 hI3 hI4 hI5 hb1 hb2 hb3 hb4
  -- ## the two leftover terms are nonnegative
  have hD0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * 𝔰[α] θ :=
    setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sigR_gam_nonneg α θ hθ))
  have hE0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _))
  have hmain : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * 𝔰[α] θ)
      ≤ -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * 𝔰[α] θ) := by
    have h2a : 0 ≤ 2 * (2 - Work.Spaces.gam α) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * 𝔰[α] θ) :=
      mul_nonneg (mul_nonneg (by norm_num) hp0.le) hD0
    have h2b : 0 ≤ 2 * (2 - Work.Spaces.gam α) * (1 - (2 - Work.Spaces.gam α))
        * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp0.le) hp1m) hE0
    rw [hibp]
    linarith
  simpa only [Work.FTS.EllipticEst.TT.sigR] using hmain

end Work.FTS.ClassC.VopGen
