import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.Spaces.HardyTheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

namespace Work.FTS.StrongEps.SupPort

set_option maxHeartbeats 1600000

/-! ## The angular Hardy inequality in the `SmoothOpen` (open quadrant) form

The file `Submission/Work/FTS/H2/LinfQ.lean` proves the same inequality (`HardyThetaO`) for the
class `Work.FTS.LocData.SmoothQuad`, i.e. smoothness on the open strip `(-1,∞) × (0,π/2)`.
Here the hypothesis is the weaker `Work.FTS.EllipticEst.SmoothOpen`, smoothness on the open
quadrant `(0,∞) × (0,π/2)` only, which is what the `SupPort`/`StrongEps` layer provides.  The
proof of `HardyThetaO` uses the smoothness hypothesis *only* through the two one-variable facts

* `θ ↦ g z θ` is `C^∞` on `(0,π/2)` (its Cauchy–Schwarz/FTC factors), and
* `θ ↦ ∂_θ g z θ` is `C^∞` on `(0,π/2)` (continuity of the integrand),

which follow from `SmoothOpen` at every fixed `z > 0` by slicing.  Everything else — the
fundamental theorem on `[ε,θ]` with the boundary value supplied by the limit hypothesis `h0`,
the weighted Cauchy–Schwarz inequality, and the bound `∫_{Iθ} sin(2θ)^{γ-2} ≤ 100/(γ-1)` of
`Work.Spaces.sin_two_rpow` — is unchanged.
-/

/-- `0 ≤ sin(2θ)` on the angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem HardyThetaOpen (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ) (z : ℝ)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => g z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth g z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (g z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
        (Work.Spaces.pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hp1 : -1 < gam α - 2 := by rw [gam]; linarith
  have hp0 : gam α - 2 ≤ 0 := by rw [gam]; linarith
  have hne0 : Work.Stability.smoothOrder ≠ 0 := Work.FTS.LocData.smoothOrder_ne_zero
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => g z θ')
      (Set.Ioo 0 (π / 2)) := hg.curry_θ hz
  have hdth : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Work.Spaces.pth g z θ')
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ (hg.pth) hz
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Iθ, (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _)
  have hKnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the bound at every `ε ∈ (0,θ)`
  have hkey : ∀ ε ∈ Set.Ioo 0 θ, (g z θ - g z ε) ^ 2 ≤ (100 / (gam α - 1)) * A := by
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
    have hpthcont : ContinuousOn (fun s => pth g z s) (Set.uIcc ε θ) :=
      hdth.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo ε θ, HasDerivAt (fun θ' => g z θ') (pth g z x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_trans hε.1 hx.1, lt_trans hx.2 hθ1⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (fun s => pth g z s) volume ε θ := hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, pth g z s = g z θ - g z ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo (hsub hs))))
    have hcs := hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - gam α) / 2))) (hsincont ((gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2))
            * (Real.sin (2 * s)) ^ ((gam α - 2) / 2)
        = ∫ s in ε..θ, pth g z s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hs'
      have h1 : (Real.sin (2 * s)) ^ ((2 - gam α) / 2)
          * (Real.sin (2 * s)) ^ ((gam α - 2) / 2) = 1 := by
        rw [← Real.rpow_add hsin, show (2 - gam α) / 2 + (gam α - 2) / 2 = 0 by ring,
          Real.rpow_zero]
      rw [mul_assoc, h1, mul_one]
    have hAint : ∫ s in ε..θ, (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2 ≤ A := by
      have hEq : ∫ s in ε..θ, (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
          = ∫ s in ε..θ, (pth g z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs' := hsub hs
        have h1 : ((Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
            = (Real.sin (2 * s)) ^ (2 - gam α) := by
          rw [pow_two, ← Real.rpow_add (Work.FTS.H2.sin_two_pos_of_mem_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
        ≤ 100 / (gam α - 1) := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (Work.FTS.H2.sin_two_pos_of_mem_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      refine le_trans (Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1
        (sin_two_rpow (gam α - 2) hp1 hp0).1
        (fun x hx => Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)) ?_
      have h2 := (sin_two_rpow (gam α - 2) hp1 hp0).2
      rwa [show (gam α - 2) + 1 = gam α - 1 by ring] at h2
    have hstep : |g z θ - g z ε| ≤ Real.sqrt A * Real.sqrt (100 / (gam α - 1)) := by
      rw [← hFTC, ← hcongr]
      exact le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : (g z θ - g z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (g z θ - g z ε), hstep])
        (le_trans (le_abs_self _) hstep)
    calc (g z θ - g z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 := hsq
      _ = A * (100 / (gam α - 1)) := by rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hKnn]
      _ = (100 / (gam α - 1)) * A := by ring
  -- pass to the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => (g z θ - g z ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 ((g z θ) ^ 2)) := by
    have h1 : Tendsto (fun ε => g z θ - g z ε) (𝓝[>] (0 : ℝ)) (𝓝 (g z θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.pow 2
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [isOpen_Iio.mem_nhds hθ0] with ε hε hε0
  exact hkey ε ⟨hε0, hε⟩

end Work.FTS.StrongEps.SupPort
