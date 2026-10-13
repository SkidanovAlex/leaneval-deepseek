import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.C4.hardyTheta_slice_C1`

The angular Hardy inequality of Elgindi's §H2 in the **`C¹` slice form**: fix `z > 0` and
suppose that the one-variable `θ`-slice `θ ↦ g z θ` is `C¹` on `(0,π/2)`, that its derivative
`θ ↦ ∂_θ g(z,θ)` is `C¹` there, that the slice tends to `0` as `θ → 0⁺`, and that the weighted
angular energy `(∂_θ g(z,σ))² sin(2σ)^{2-γ}` is integrable on `Iθ = [0,π/2]`.  Then

  `g(z,θ)² ≤ (100/(γ-1)) ∫_{Iθ} (∂_θ g(z,σ))² sin(2σ)^{2-γ} dσ`   for every `0 < θ < π/2`,

where `γ = Work.Spaces.gam α = 1 + α/10`.

The classical proof (the fundamental theorem of calculus on `[ε,θ]`, the weighted
Cauchy–Schwarz `Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` for the two factors
`∂_θ g · sin(2·)^{(2-γ)/2}` and `sin(2·)^{(γ-2)/2}`, the quantitative bound
`Work.Spaces.sin_two_rpow` for the singular weight, and finally the limit `ε → 0⁺` using the
boundary hypothesis) uses **only** the continuity and differentiability of the two
one-variable slices on the open interval — never anything stronger than `C¹`.  That is why
this form of the statement holds; the general one-variable form is isolated below as
`hardyTheta_slice_C1_aux` and the theorem is its instantiation at `u = fun θ => g z θ`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.C4

set_option maxHeartbeats 800000

/-! ## Elementary angular facts -/

/-- `sin (2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` for `0 < θ < π/2`. -/
private lemma sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Monotonicity of the interval integral against the set integral over `Iθ`: for `0 < a ≤ b`
and `b < π/2` the interval `[a,b]` sits inside `Iθ`, so the integral of a nonnegative
integrable function over `[a,b]` is at most its integral over `Iθ`. -/
private lemma interval_integral_le_setIntegral_Iθ {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < π / 2) (hint : MeasureTheory.IntegrableOn F Work.Spaces.Iθ)
    (hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ F x) :
    (∫ x in a..b, F x) ≤ ∫ x in Work.Spaces.Iθ, F x := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Icc hnn) ?_
  exact Eventually.of_forall fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩

/-! ## The Hardy inequality for a single `C¹` slice -/

/-- **The angular Hardy inequality for a single one-variable function, `C¹` form.**

For `u` of class `C¹` on `(0,π/2)` whose derivative `deriv u` is continuous on `(0,π/2)`
(here assumed `C¹`), with `u θ → 0` as `θ → 0⁺` and `(deriv u)² sin(2·)^{2-γ}` integrable
on `Iθ`,

  `u(θ)² ≤ (100/(γ-1)) ∫_Iθ (deriv u)² sin(2σ)^{2-γ} dσ`   for every `0 < θ < π/2`.

Proof: for `0 < ε < θ` the fundamental theorem of calculus on `[ε,θ]` gives
`u θ - u ε = ∫_ε^θ deriv u`; Cauchy–Schwarz with the two factors
`deriv u · sin(2·)^{(2-γ)/2}` and `sin(2·)^{(γ-2)/2}`, together with the quantitative bound
`Work.Spaces.sin_two_rpow` for the singular weight, gives the estimate with `u ε` on the left;
the limit `ε → 0⁺` (hypothesis `h0`) finishes. -/
private lemma hardyTheta_slice_C1_aux {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u : ℝ → ℝ}
    (hslice : ContDiffOn ℝ 1 u (Set.Ioo 0 (π / 2)))
    (hdth : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (π / 2)))
    (h0 : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (deriv u σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (u θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
        (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hp1 : -1 < Work.Spaces.gam α - 2 := by rw [Work.Spaces.gam]; linarith
  have hp0 : Work.Spaces.gam α - 2 ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hne0 : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
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
      exact interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
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
      refine le_trans (interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1
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

/-! ## The requested `C¹`-slice statement -/

theorem hardyTheta_slice_C1 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hz : 0 < z)
    (hslice : ContDiffOn ℝ 1 (fun θ => g z θ) (Set.Ioo 0 (Real.pi / 2)))
    (hpth : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pth g z θ) (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto (fun θ => g z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth g z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (g z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
        (Work.Spaces.pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  intro θ hθ
  exact hardyTheta_slice_C1_aux hα hα1 hslice hpth h0 hint θ hθ

end Work.FTS_RegExport.C4
