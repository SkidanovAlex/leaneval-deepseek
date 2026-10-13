import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngAWeak.AeI1MixedDefs
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.remov.AeIPMemsSlim
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.AngSecond.I1_honesty
import Submission.Work.FTS.EllipticEst.H2W.WeakAux.I1ZibpOpenAbs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngAWeak.aeI1CwBound` — the drift pairing `⟨cw · U, B⟩` in the weak class

Target: `Work.FTS.EllipticEst.AngAWeak.aeI1CwBound`.

With `U = z ∂_z u` (`AngAWeak.i1U u`) and `B = ∂_θθ u` (`AngAWeak.i1B u`), and the weight
`cw z = 2(z-1)/(1+z)` of the radial integration by parts of Step 2 (`prop:H2` of
T. M. Elgindi, Annals **194** (2021)),

  `IP (cw · U) B ≤ 2 √(IP U U) · √(IP B B)`,

where `IP g h = ∫_z ∫_θ g h w²σ`.

This is the drift-term Cauchy–Schwarz of the `I₁` computation, in the almost-everywhere class
`H2W.Ae.AeData` where only the *diagonal* honesties `HkMem α 0 (z∂_z u)` and
`HkMem α 0 (∂_θθu)` are available.

## Route

1. `AngClean.HkMem_zero_IPMem` turns the two `HkMem` hypotheses into the diagonal honesties
   `IPMem U U` and `IPMem B B`;
2. `Work.AngSecond.IPMem_cw_mul_diag` upgrades `IPMem U U` to `IPMem (cw · U) (cw · U)`
   (`|cw| ≤ 2` on `[0,∞)`);
3. the *cross* honesty `IPMem (cw · U) B` is obtained from the two diagonal honesties by the
   AM–GM polarisation `|g h| ≤ (g² + h²)/2`
   (`Work.FTS.EllipticEst.H2W.WeakAux.IPMem_of_diag_open`), which needs only the continuity of
   the two profiles on the open quadrant — supplied by `AeData.smooth` through
   `SmoothOpen` (`smoothOpen_fst_mul_pz`, `smoothOpen_pthIter_two`);
4. Cauchy–Schwarz (`AngSecond.IP_cauchy_schwarz`) then gives
   `|IP (cw·U) B| ≤ √(IP (cw·U) (cw·U)) · √(IP B B)`, and `IP (cw·U) (cw·U) ≤ 4 IP U U`
   because `cw² ≤ 4` on `[0,∞)` (`AngSecond.abs_cw_le_two`).
-/

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
private abbrev Quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- **The diagonal bound `IP (cw · g) (cw · g) ≤ 4 · IP g g`.**

On `[0,∞)` the weight `cw z = 2(z-1)/(1+z)` is bounded by `2` in absolute value, hence
`cw z² ≤ 4`; slicewise the integrand of `IP (cw · g) (cw · g)` is `cw z²` times that of
`IP g g`.  (The proof is the one of `AngSecond.IP_cwPhi_le`, carried out for an arbitrary `g`,
so that it applies to the weak class without a `SmoothNbhd` hypothesis.) -/
private theorem IP_cw_mul_diag_le {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.AngSecond.IPMem g g)
    (hcw : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * g z θ)) :
    Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
      ≤ 4 * Work.FTS.EllipticEst.AngSecond.IP g g := by
  rw [Work.FTS.EllipticEst.AngSecond.IP, Work.FTS.EllipticEst.AngSecond.IP,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_mono_on hcw.2 (hg.2.const_mul 4) measurableSet_Ici
    (fun z hz => ?_)
  have hI : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
      g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    have h1 : (0 : ℝ) ≤ g z θ * g z θ := mul_self_nonneg _
    have h2 : (0 : ℝ) ≤ g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z :=
      mul_nonneg h1 (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
    exact mul_nonneg h2 (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
          * (Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
          * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
      = Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AngSecond.cw z
        * (∫ θ in Work.Spaces.Iθ, g z θ * g z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [hstep]
  have hcq : Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AngSecond.cw z ≤ 4 := by
    have h := abs_le.mp (Work.AngSecond.abs_cw_le_two hz)
    nlinarith [h.1, h.2]
  exact mul_le_mul_of_nonneg_right hcq hI

/-- `cw` is continuous on `(0,∞)`. -/
private theorem continuousOn_cw_Ioi :
    ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z) (Set.Ioi (0 : ℝ)) := by
  have h : ContinuousOn (fun z : ℝ => 2 * (z - 1) / (1 + z)) (Set.Ioi (0 : ℝ)) :=
    ContinuousOn.div
      ((continuous_const.mul (continuous_id.sub continuous_const)).continuousOn)
      ((continuous_const.add continuous_id).continuousOn)
      (fun z hz => by
        have hz' : (0 : ℝ) < z := hz
        have : (0 : ℝ) < 1 + z := by linarith
        positivity)
  simpa only [Work.FTS.EllipticEst.AngSecond.cw] using h

/-- The uncurried `(z,θ) ↦ cw z` is continuous on the open quadrant. -/
private theorem continuousOn_uncurry_cw :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.cw p.1) Quad :=
  continuousOn_cw_Ioi.comp continuous_fst.continuousOn (fun _ hp => hp.1)

theorem aeI1CwBound {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AngAWeak.i1U u)) :
    Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (Work.FTS.EllipticEst.AngAWeak.i1B u)
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) := by
  -- ### The `SmoothOpen` smoothness of the datum on the open quadrant
  have hsm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => hAe.smooth n)
  -- ### The three honesties
  have hUdiag : Work.FTS.EllipticEst.AngSecond.IPMem
      (Work.FTS.EllipticEst.AngAWeak.i1U u)
      (Work.FTS.EllipticEst.AngAWeak.i1U u) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hU
  have hBdiag : Work.FTS.EllipticEst.AngSecond.IPMem
      (Work.FTS.EllipticEst.AngAWeak.i1B u)
      (Work.FTS.EllipticEst.AngAWeak.i1B u) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hAe.memAng2
  have hCwU : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
        * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
        * Work.FTS.EllipticEst.AngAWeak.i1U u z θ) :=
    Work.AngSecond.IPMem_cw_mul_diag hUdiag
  -- ### Continuity of the two profiles on the open quadrant
  have hcontB : ContinuousOn
      (Function.uncurry (Work.FTS.EllipticEst.AngAWeak.i1B u)) Quad :=
    (Work.FTS.EllipticEst.H2W.WeakAux.smoothOpen_pthIter_two hsm).continuousOn
  have hcontU : ContinuousOn
      (Function.uncurry (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
        * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)) Quad :=
    continuousOn_uncurry_cw.mul
      (Work.FTS.EllipticEst.H2W.WeakAux.smoothOpen_fst_mul_pz hsm).continuousOn
  -- ### The cross honesty, by polarisation
  have hcross : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
        * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
      (Work.FTS.EllipticEst.AngAWeak.i1B u) :=
    Work.FTS.EllipticEst.H2W.WeakAux.IPMem_of_diag_open hcontU hcontB hCwU hBdiag
  -- ### Cauchy–Schwarz
  have hcs : |Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (Work.FTS.EllipticEst.AngAWeak.i1B u)|
      ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) :=
    Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz hCwU hBdiag hcross
  -- ### The diagonal comparison and the square root
  have hdiagle : Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
      ≤ 4 * Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.AngAWeak.i1U u)
          (Work.FTS.EllipticEst.AngAWeak.i1U u) :=
    IP_cw_mul_diag_le hUdiag hCwU
  have hsqrt : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ))
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.AngAWeak.i1U u)
          (Work.FTS.EllipticEst.AngAWeak.i1U u)) := by
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    calc Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ))
        ≤ Real.sqrt (4 * Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u)) := Real.sqrt_le_sqrt hdiagle
      _ = Real.sqrt 4 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u)) := Real.sqrt_mul (by norm_num) _
      _ = 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u)) := by rw [h4]
  -- ### Assembly
  calc Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (Work.FTS.EllipticEst.AngAWeak.i1B u)
      ≤ |Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
          (Work.FTS.EllipticEst.AngAWeak.i1B u)| := le_abs_self _
    _ ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) := hcs
    _ ≤ (2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u)))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) := by ring

end

end Work.FTS.EllipticEst.AngAWeak
