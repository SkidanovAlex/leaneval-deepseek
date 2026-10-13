import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Have
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped Real Topology
open MeasureTheory Set Filter

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## Elementary angular facts on `Iθ = [0,π/2]`

These are re-proved here (rather than imported from the localisation chapter) so that the file
rests only on the one-dimensional ingredients of `Work.Spaces`: the angular Hardy inequality
`Work.Spaces.HardyTheta`, the weighted Cauchy–Schwarz estimate of `Work.Spaces.HardyZ` and the
quantitative bound `Work.Spaces.sin_two_rpow` for the singular weight. -/

/-- `sin (2θ) ≥ 0` on the closed interval `Iθ = [0,π/2]`. -/
theorem hq_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` on the open interval `(0,π/2)`. -/
theorem hq_sin_two_pos_of_mem_Ioo {θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

/-- Monotonicity of the interval integral against the set integral over `Iθ`: for `0 < a ≤ b`
and `b < π/2` the interval `[a,b]` sits inside `Iθ`, so the integral of a nonnegative
integrable function over `[a,b]` is at most its integral over `Iθ`. -/
theorem hq_interval_integral_le_setIntegral_Iθ {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < π / 2) (hint : IntegrableOn F Iθ) (hnn : ∀ x ∈ Iθ, 0 ≤ F x) :
    (∫ x in a..b, F x) ≤ ∫ x in Iθ, F x := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Icc hnn) ?_
  exact Eventually.of_forall fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩

/-- **Elgindi's angular Hardy inequality in the interior class.**  `Work.Spaces.HardyTheta`
(proved) is the same inequality for `Work.Spaces.SmoothNbhd` functions, i.e. *analyticity* on a
neighbourhood of the closed quadrant — a class that is false for `F_*`, for the stream functions
and for the cut-off `χ`.  The statement below keeps only what the proof uses: `u` is
`SmoothQuad` (genuine `C^∞` on the open strip `(-1,∞) × (0,π/2)`), the `θ`-slice at the fixed
`z > -1` tends to `0` at `θ → 0⁺` (this replaces `VanishTheta`: only the *limit* from inside is
used, never the value at `θ = 0`), and the Hardy integrand is integrable.  Conclusion:

  `(u z θ)² ≤ (100/(γ-1)) ∫_Iθ (∂_θ u(z,σ))² sin(2σ)^{2-γ} dσ`   for `0 < θ < π/2`.

Proof route (the same as the proved `Work.Spaces.HardyTheta`): for `0 < ε < θ < π/2` write
`u z θ - u z ε = ∫_ε^θ ∂_θ u z σ dσ` (FTC, using `SmoothQuad` for differentiability on
`(0,π/2)` and `hz : -1 < z` for the slice), apply the weighted Cauchy–Schwarz
`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` to the two factors
`∂_θu · sin(2σ)^{(2-γ)/2}` and `sin(2σ)^{(γ-2)/2}`, bound the second factor's integral by
`100/(γ-1)` (`Work.Spaces.sin_two_rpow`), and let `ε → 0⁺` using `h0`.
`Submission/Work/FTS/H2/LinfQ.lean` contains a draft of this proof (`HardyThetaO`); note that
that file does not compile, so do not import it — write your own. -/
theorem HardyThetaQ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ) (z : ℝ)
    (hu : Work.FTS.LocData.SmoothQuad u) (hz : z ∈ Set.Ioi (-1))
    (h0 : Filter.Tendsto (fun θ => u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth u z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (u z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * MeasureTheory.integral
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun σ => (Work.Spaces.pth u z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hp1 : -1 < gam α - 2 := by rw [gam]; linarith
  have hp0 : gam α - 2 ≤ 0 := by rw [gam]; linarith
  have hne0 : Work.Stability.smoothOrder ≠ 0 := Work.FTS.LocData.smoothOrder_ne_zero
  -- smoothness of the `θ`-slice and of its derivative on `(0,π/2)`
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => u z θ')
      (Set.Ioo 0 (π / 2)) :=
    hu.curry_θ hz
  have hdth : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => pth u z θ')
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hu) hz
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Iθ, (pth u z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hq_sin_two_nonneg hσ) _)
  have hKnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the bound at every `ε ∈ (0,θ)`
  have hkey : ∀ ε ∈ Set.Ioo 0 θ, (u z θ - u z ε) ^ 2 ≤ (100 / (gam α - 1)) * A := by
    intro ε hε
    have hεθ : ε ≤ θ := le_of_lt hε.2
    have hsub : Set.uIcc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      exact ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_le_of_lt hx.2 hθ1⟩
    have hsubI : Set.Icc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [← Set.uIcc_of_le hεθ]; exact hsub
    have hcontθ : ContinuousOn (fun θ' => u z θ') (Set.Icc ε θ) :=
      hslice.continuousOn.mono hsubI
    have hpthcont : ContinuousOn (fun s => pth u z s) (Set.uIcc ε θ) :=
      hdth.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo ε θ, HasDerivAt (fun θ' => u z θ') (pth u z x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_trans hε.1 hx.1, lt_of_lt_of_le hx.2 hθ1.le⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (fun s => pth u z s) volume ε θ :=
      hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, pth u z s = u z θ - u z ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (hq_sin_two_pos_of_mem_Ioo (hsub hs))))
    have hcs := hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - gam α) / 2))) (hsincont ((gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (pth u z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2))
            * (Real.sin (2 * s)) ^ ((gam α - 2) / 2)
        = ∫ s in ε..θ, pth u z s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := hq_sin_two_pos_of_mem_Ioo hs'
      have h1 : (Real.sin (2 * s)) ^ ((2 - gam α) / 2)
          * (Real.sin (2 * s)) ^ ((gam α - 2) / 2) = 1 := by
        rw [← Real.rpow_add hsin, show (2 - gam α) / 2 + (gam α - 2) / 2 = 0 by ring,
          Real.rpow_zero]
      rw [mul_assoc, h1, mul_one]
    have hAint : ∫ s in ε..θ, (pth u z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2 ≤ A := by
      have hEq : ∫ s in ε..θ, (pth u z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
          = ∫ s in ε..θ, (pth u z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs' := hsub hs
        have h1 : ((Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
            = (Real.sin (2 * s)) ^ (2 - gam α) := by
          rw [pow_two, ← Real.rpow_add (hq_sin_two_pos_of_mem_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact hq_interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hq_sin_two_nonneg hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
        ≤ 100 / (gam α - 1) := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (hq_sin_two_pos_of_mem_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      refine le_trans (hq_interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1
        (sin_two_rpow (gam α - 2) hp1 hp0).1
        (fun x hx => Real.rpow_nonneg (hq_sin_two_nonneg hx) _)) ?_
      have h2 := (sin_two_rpow (gam α - 2) hp1 hp0).2
      rwa [show (gam α - 2) + 1 = gam α - 1 by ring] at h2
    have hstep : |u z θ - u z ε| ≤ Real.sqrt A * Real.sqrt (100 / (gam α - 1)) := by
      rw [← hFTC, ← hcongr]
      exact le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : (u z θ - u z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (u z θ - u z ε), hstep])
        (le_trans (le_abs_self _) hstep)
    calc (u z θ - u z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 := hsq
      _ = A * (100 / (gam α - 1)) := by rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hKnn]
      _ = (100 / (gam α - 1)) * A := by ring
  -- pass to the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => (u z θ - u z ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 ((u z θ) ^ 2)) := by
    have h1 : Tendsto (fun ε => u z θ - u z ε) (𝓝[>] (0 : ℝ)) (𝓝 (u z θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.pow 2
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [isOpen_Iio.mem_nhds hθ0] with ε hε hε0
  exact hkey ε ⟨hε0, hε⟩

end Work.FTS.H2.HQ
