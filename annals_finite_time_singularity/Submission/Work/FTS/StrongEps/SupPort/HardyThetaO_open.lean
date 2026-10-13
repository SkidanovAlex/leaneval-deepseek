import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Have
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.SupPort.HardyThetaO_open`

The **angular Hardy inequality in the open-quadrant class**: if `g` is `C^∞` on the open
quadrant `Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen g`, *not* the analytic
neighbourhood class `SmoothNbhd` and *not* `SmoothQuad`), if `z > 0`, if the `θ`-slice
`θ ↦ g z θ` tends to `0` at `θ = 0⁺` and if the weighted angular energy
`(∂_θ g(z,σ))² sin(2σ)^{2-γ}` is integrable over `Iθ = [0,π/2]`, then

  `g(z,θ)² ≤ (100/(γ-1)) ∫_Iθ (∂_θ g(z,σ))² sin(2σ)^{2-γ} dσ`   for every `0 < θ < π/2`,

where `γ = Work.Spaces.gam α = 1 + α/10`.

This is the open-quadrant form of `Work.Spaces.HardyTheta` (`SmoothNbhd`, analytic on a
neighbourhood of the closed quadrant) and of `Work.FTS.H2.HardyThetaO` (`SmoothQuad`, `C^∞` on
`z > -1`).  Neither of those applies here: `SmoothOpen` only constrains `g` on `z > 0`, so no
smoothness of the extended `z`-slice is available.  The proof below keeps only what is
actually used: the two one-variable facts

* `θ ↦ g z θ` is `C^∞` on `(0,π/2)`  (`SmoothOpen.curry_θ`), and
* `θ ↦ ∂_θ g z θ` is `C^∞` on `(0,π/2)` (`SmoothOpen.pth` + `SmoothOpen.curry_θ`).

Everything else is the classical argument, isolated in the helper `hardyThetaO_slice`
(a statement about a single one-variable function), so that the main theorem is the two-line
instantiation `u = fun θ => g z θ`.

**Notation trap.**  The statement of `HardyThetaO_open` is written with a bare `π`.  Without
`open scoped Real` that identifier is *not* `Real.pi`: under the default `autoImplicit` option
it is auto-bound as an implicit variable, and the statement then reads `∀ {π : ℝ}, … ∀ θ ∈
Set.Ioo 0 (π/2), …` — which is **false** (only `θ < π/2` in the genuine sense is constrained by
`SmoothOpen`, so a large bump of `g z ·` at `θ = 3` contradicts the bound for `π = 10`).  The
declaration below therefore opens the real notation so that the statement means what it was
written to mean, exactly as in the consumers (`HardyThetaO_open` is invoked at
`θ ∈ Set.Ioo 0 (Real.pi / 2)`); the statement text is unchanged.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongEps.SupPort

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary angular facts -/

/-- `sin (2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` for `0 < θ < π/2`. -/
private lemma sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The Hardy inequality for a single `θ`-slice -/

/-- **The angular Hardy inequality for a single one-variable function.**

For `u` of class `C^∞` on `(0,π/2)` whose derivative `deriv u` is `C^∞` on `(0,π/2)`, with
`u θ → 0` as `θ → 0⁺` and `(deriv u)² sin(2·)^{2-γ}` integrable on `Iθ`,

  `u(θ)² ≤ (100/(γ-1)) ∫_Iθ (deriv u)² sin(2σ)^{2-γ} dσ`   for every `0 < θ < π/2`.

Proof: for `0 < ε < θ` the fundamental theorem of calculus on `[ε,θ]` gives
`u θ - u ε = ∫_ε^θ deriv u`; Cauchy–Schwarz with the two factors
`deriv u · sin(2·)^{(2-γ)/2}` and `sin(2·)^{(γ-2)/2}`, together with the quantitative bound
`Work.Spaces.sin_two_rpow` for the singular weight, gives the estimate with `u ε` on the left;
the limit `ε → 0⁺` (hypothesis `h0`) finishes.  (This is the proof of
`Work.FTS.H2.HardyThetaO` with the `SmoothQuad`-smoothness replaced by the two `θ`-slice
smoothness hypotheses actually used.) -/
theorem hardyThetaO_slice (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ)
    (hslice : ContDiffOn ℝ Work.Stability.smoothOrder u (Set.Ioo 0 (π / 2)))
    (hdth : ContDiffOn ℝ Work.Stability.smoothOrder (deriv u) (Set.Ioo 0 (π / 2)))
    (h0 : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (deriv u σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (u θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
        (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hp1 : -1 < Work.Spaces.gam α - 2 := by rw [Work.Spaces.gam]; linarith
  have hp0 : Work.Spaces.gam α - 2 ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hne0 : Work.Stability.smoothOrder ≠ 0 := Work.FTS.LocData.smoothOrder_ne_zero
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2
    * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _)
  have hKnn : 0 ≤ 100 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the bound at every `ε ∈ (0,θ)`
  have hkey : ∀ ε ∈ Set.Ioo 0 θ,
      (u θ - u ε) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1)) * A := by
    intro ε hε
    have hεθ : ε ≤ θ := le_of_lt hε.2
    have hsub : Set.uIcc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      exact ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_le_of_lt hx.2 hθ1⟩
    have hsubI : Set.Icc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [← Set.uIcc_of_le hεθ]; exact hsub
    have hcontθ : ContinuousOn u (Set.Icc ε θ) := hslice.continuousOn.mono hsubI
    have hpthcont : ContinuousOn (deriv u) (Set.uIcc ε θ) := hdth.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo ε θ, HasDerivAt u (deriv u x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_trans hε.1 hx.1, lt_of_lt_of_le hx.2 hθ1.le⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (deriv u) volume ε θ := hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, deriv u s = u θ - u ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (sin_two_pos_Ioo (hsub hs))))
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - Work.Spaces.gam α) / 2)))
      (hsincont ((Work.Spaces.gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (deriv u s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2))
            * (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)
        = ∫ s in ε..θ, deriv u s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := sin_two_pos_Ioo hs'
      have h1 : (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)
          * (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2) = 1 := by
        rw [← Real.rpow_add hsin,
          show (2 - Work.Spaces.gam α) / 2 + (Work.Spaces.gam α - 2) / 2 = 0 by ring,
          Real.rpow_zero]
      rw [mul_assoc, h1, mul_one]
    have hAint : ∫ s in ε..θ,
          (deriv u s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2 ≤ A := by
      have hEq : ∫ s in ε..θ,
            (deriv u s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
          = ∫ s in ε..θ, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs' := hsub hs
        have h1 : ((Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
            = (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
          rw [pow_two, ← Real.rpow_add (sin_two_pos_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2
        ≤ 100 / (Work.Spaces.gam α - 1) := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (sin_two_pos_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      refine le_trans (Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1
        (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hp1 hp0).1
        (fun x hx => Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)) ?_
      have h2 := (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hp1 hp0).2
      rwa [show (Work.Spaces.gam α - 2) + 1 = Work.Spaces.gam α - 1 by ring] at h2
    have hstep : |u θ - u ε| ≤ Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1)) := by
      rw [← hFTC, ← hcongr]
      exact le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : (u θ - u ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1))) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (u θ - u ε), hstep])
        (le_trans (le_abs_self _) hstep)
    calc (u θ - u ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1))) ^ 2 := hsq
      _ = A * (100 / (Work.Spaces.gam α - 1)) := by
            rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hKnn]
      _ = (100 / (Work.Spaces.gam α - 1)) * A := by ring
  -- pass to the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => (u θ - u ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 ((u θ) ^ 2)) := by
    have h1 : Tendsto (fun ε => u θ - u ε) (𝓝[>] (0 : ℝ)) (𝓝 (u θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.pow 2
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [isOpen_Iio.mem_nhds hθ0] with ε hε hε0
  exact hkey ε ⟨hε0, hε⟩

/-! ## The open-quadrant form -/

theorem HardyThetaO_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ) (z : ℝ)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => g z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth g z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (g z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
        (Work.Spaces.pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  intro θ hθ
  exact hardyThetaO_slice α hα hα1 (fun θ' => g z θ') (hg.curry_θ hz) ((hg.pth).curry_θ hz)
    h0 hint θ hθ

end Work.FTS.StrongEps.SupPort
