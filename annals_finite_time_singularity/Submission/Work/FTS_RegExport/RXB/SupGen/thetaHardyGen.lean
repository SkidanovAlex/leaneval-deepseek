/-
# The angular Hardy inequality with a general (given) weight constant

`Work.FTS_RegExport.RXB.SupGen.thetaHardyGen` is the angular Hardy inequality of Elgindi's §H2
in the `SmoothOpen` (open quadrant) form, but with the *quantitative* bound on the singular
weight `sin(2θ)^{γ-2}` replaced by an arbitrary constant `K` supplied by the caller together
with the hypothesis `∫_{Iθ} sin(2σ)^{γ-2} dσ ≤ K`.

The classical proof is the same as in `Work.FTS.StrongEps.SupPort.HardyThetaOpen` (and
`Work.FTS.H2.HardyThetaO`, `Work.FTS_RegExport.C4.hardyTheta_slice_C1`): the fundamental
theorem of calculus on `[ε,θ]`, the weighted Cauchy–Schwarz
`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` for the two factors
`∂_θ g · sin(2·)^{(2-γ)/2}` and `sin(2·)^{(γ-2)/2}`, and the limit `ε → 0⁺` using the boundary
hypothesis `h0`.  The only difference: the second factor is bounded by the *hypothesis*
`∫_{Iθ} sin(2σ)^{γ-2} ≤ K` rather than by the explicit `100/(γ-1)` of
`Work.Spaces.sin_two_rpow`.  In particular **no** assumption on `α` beyond `0 < α`
(and `α ≤ 1`-type smallness) is used: the proof never needs `γ - 2 ≤ 0`, only the integrability
of `sin(2·)^{γ-2}`, which is a hypothesis here.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology MeasureTheory
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXB.SupGen

set_option maxHeartbeats 800000

/-- `sin (2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem thetaHardyGen {α : ℝ} (hα : 0 < α) (K : ℝ) (hK0 : 0 ≤ K) (g : ℝ → ℝ → ℝ) (z : ℝ)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => g z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth g z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ)
    (hSint : MeasureTheory.IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2)) Work.Spaces.Iθ)
    (hSval : ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2) ≤ K) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (g z θ) ^ 2 ≤
      K * ∫ σ in Work.Spaces.Iθ,
        (Work.Spaces.pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hne0 : Work.Stability.smoothOrder ≠ 0 := Work.FTS.LocData.smoothOrder_ne_zero
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => g z θ')
      (Set.Ioo 0 (π / 2)) := hg.curry_θ hz
  have hdth : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Work.Spaces.pth g z θ')
      (Set.Ioo 0 (π / 2)) := hg.pth.curry_θ hz
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth g z σ) ^ 2
    * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _)
  -- the bound at every `ε ∈ (0,θ)`
  have hkey : ∀ ε ∈ Set.Ioo 0 θ, (g z θ - g z ε) ^ 2 ≤ K * A := by
    intro ε hε
    have hεθ : ε ≤ θ := le_of_lt hε.2
    have hsub : Set.uIcc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      exact ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_le_of_lt hx.2 hθ1⟩
    have hsubI : Set.Icc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [← Set.uIcc_of_le hεθ]; exact hsub
    have hcontθ : ContinuousOn (fun θ' => g z θ') (Set.Icc ε θ) :=
      hslice.continuousOn.mono hsubI
    have hpthcont : ContinuousOn (fun s => Work.Spaces.pth g z s) (Set.uIcc ε θ) :=
      hdth.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo ε θ,
        HasDerivAt (fun θ' => g z θ') (Work.Spaces.pth g z x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_trans hε.1 hx.1, lt_of_lt_of_le hx.2 hθ1.le⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (fun s => Work.Spaces.pth g z s) volume ε θ :=
      hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, Work.Spaces.pth g z s = g z θ - g z ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo (hsub hs))))
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - Work.Spaces.gam α) / 2)))
      (hsincont ((Work.Spaces.gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (Work.Spaces.pth g z s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2))
            * (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)
        = ∫ s in ε..θ, Work.Spaces.pth g z s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hs'
      have h1 : (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)
          * (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2) = 1 := by
        rw [← Real.rpow_add hsin,
          show (2 - Work.Spaces.gam α) / 2 + (Work.Spaces.gam α - 2) / 2 = 0 by ring,
          Real.rpow_zero]
      rw [mul_assoc, h1, mul_one]
    have hAint : ∫ s in ε..θ,
          (Work.Spaces.pth g z s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
        ≤ A := by
      have hEq : ∫ s in ε..θ,
            (Work.Spaces.pth g z s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
          = ∫ s in ε..θ, (Work.Spaces.pth g z s) ^ 2
              * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs' := hsub hs
        have h1 : ((Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
            = (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
          rw [pow_two, ← Real.rpow_add (Work.FTS.H2.sin_two_pos_of_mem_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2
        ≤ K := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (Work.FTS.H2.sin_two_pos_of_mem_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      exact le_trans (Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hSint
        fun x hx => Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _) hSval
    have hstep : |g z θ - g z ε| ≤ Real.sqrt A * Real.sqrt K := by
      rw [← hFTC, ← hcongr]
      exact le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : (g z θ - g z ε) ^ 2 ≤ (Real.sqrt A * Real.sqrt K) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (g z θ - g z ε), hstep])
        (le_trans (le_abs_self _) hstep)
    calc (g z θ - g z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt K) ^ 2 := hsq
      _ = A * K := by rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hK0]
      _ = K * A := by ring
  -- pass to the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => (g z θ - g z ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 ((g z θ) ^ 2)) := by
    have h1 : Tendsto (fun ε => g z θ - g z ε) (𝓝[>] (0 : ℝ)) (𝓝 (g z θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.pow 2
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [isOpen_Iio.mem_nhds hθ0] with ε hε hε0
  exact hkey ε ⟨hε0, hε⟩

end Work.FTS_RegExport.RXB.SupGen
