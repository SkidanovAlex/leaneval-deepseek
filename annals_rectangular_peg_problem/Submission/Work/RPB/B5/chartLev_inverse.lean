import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.V
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B5.slabExtendPeriodic
import Submission.Work.RPB.B3.UniformInverseAux
import Submission.Work.RPB.B5.slabGlobalExtendPeriodic
import Submission.Work.RPB.B5.slabDerivBounds
import Submission.Work.RPB.B5.slabMonoExistsUnique
import Submission.Work.RPB.B5.slabInverseContDiffOn

/-!
# B5: inverting the level chart of the chord annulus

Given the `ρ = r²`-chart `W` of the chord annulus (`W τ t (r^2) = chordSurf CI.c a τ t r` for
`0 < r < π/2`) the level function `lev τ t ρ = K₀(W τ t ρ) + 1` has, on the chord side,
`lev τ t (r^2) = r^2 * ‖halfChord CI.c τ t r‖^2`; in particular `lev τ t 0 = 0` and
`∂_ρ lev(τ,t,0) = ‖c_τ'(t)‖^2 > 0`.  Hence `lev` is a local diffeomorphism in `ρ` at `ρ = 0`,
uniformly on the compact base `[0,1] × (t mod 2π)`, and can be inverted: this file produces the
inverse chart `rho` with `K₀(W τ t (rho τ t σ)) + 1 = -σ`.

The uniform inversion itself is delegated to `Work.RPB.B5.slabUniformInverse` (a general
`C⁸` inverse function theorem on a slab) and the gluing of `W` across `τ = 0, 1` to
`Work.RPB.B5.slabExtendPeriodic` (Seeley extension in the `τ`-variable, preserving the
`2π`-periodicity in `t`).
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The standard box on which the `ρ`-chart of the chord annulus is used. -/
def chartBox (ρ₀ : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀

/-- The level function of the `ρ`-chart: `chartLev W τ t ρ = K₀(W τ t ρ) + 1`. -/
def chartLev (W : ℝ → ℝ → ℝ → Work.RPV.PS) (τ t ρ : ℝ) : ℝ :=
  Work.RPV.K0 (W τ t ρ) + 1

/-! ## Elementary algebra of the chord chart -/

lemma norm_sq_ofReal (x : ℝ) : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [show ‖(x : ℂ)‖ = |x| by simp, sq_abs]

/-- `chordVec` and `halfChord` differ by the factor `2r` (also at `r = 0`, where both vanish). -/
lemma chordVec_eq_smul_halfChord (c : ℝ → ℝ → ℂ) (τ t r : ℝ) :
    Work.RPB.chordVec c τ t r = ((2 * r : ℝ) : ℂ) * Work.RPB.halfChord c τ t r := by
  have hfac : ((2 * r : ℝ) : ℂ) = (2 : ℂ) * (r : ℂ) := by push_cast; ring
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    simp [Work.RPB.halfChord, Work.RPB.chordVec]
  · have h2 : (2 : ℂ) * (r : ℂ) ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · exact_mod_cast hr
    rw [Work.RPB.chordVec, Work.RPB.halfChord, hfac, ← mul_div_assoc,
      mul_div_cancel_left₀ _ h2]

/-- The level of the chord surface in the `r`-chart. -/
lemma K0_chordSurf_add_one (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) (τ t r : ℝ) :
    Work.RPV.K0 (Work.RPB.chordSurf c a τ t r) + 1
      = r ^ 2 * ‖Work.RPB.halfChord c τ t r‖ ^ 2 := by
  rw [Work.RPB.chordSurf, Work.RPV.K0_chordPS]
  change ‖Work.RPB.chordVec c τ t r‖ ^ 2 / 4 - 1 + 1
    = r ^ 2 * ‖Work.RPB.halfChord c τ t r‖ ^ 2
  rw [chordVec_eq_smul_halfChord c τ t r, norm_mul, mul_pow, norm_sq_ofReal]
  ring

/-- The level function is `2π`-periodic in `t`. -/
lemma chartLev_per {W : ℝ → ℝ → ℝ → Work.RPV.PS}
    (hper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ)) (τ t ρ : ℝ) :
    chartLev W τ (t + 2 * Real.pi) ρ = chartLev W τ t ρ := by
  simp only [chartLev, hper, Work.RPV.K0_Tk]

/-! ## Smoothness of the level function -/

lemma contDiff_K0_add_one :
    ContDiff ℝ 8 (fun x : Work.RPV.PS => Work.RPV.K0 x + 1) := by
  simp only [Work.RPV.K0]
  fun_prop

lemma chartLev_contDiffOn {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ}
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2) (chartBox ρ₀)) :
    ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => chartLev W z.1 z.2.1 z.2.2) (chartBox ρ₀) :=
  (ContDiff.comp_contDiffOn contDiff_K0_add_one hW).congr (fun _ _ => rfl)

/-- The `ρ`-slice of the level function is `C⁸`.  This holds even at `τ = 0, 1`, since the whole
line `ρ ↦ (τ, t, ρ)` lies inside the box. -/
lemma chartLev_slice_contDiffOn {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ}
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2) (chartBox ρ₀))
    (τ t : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 8 (fun ρ : ℝ => chartLev W τ t ρ) (Set.Ioo (-ρ₀) ρ₀) :=
  ((chartLev_contDiffOn hW).comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
    (fun _ hρ => ⟨hτ, Set.mem_univ _, hρ⟩)).congr (fun _ _ => rfl)

/-! ## The level function vanishes at `ρ = 0` -/

lemma chartLev_zero {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (hc_half : ∀ τ t r, r ≠ 0 → hc τ t r = Work.RPB.halfChord CI.c τ t r)
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (τ t : ℝ)
    (hslice : ContDiffOn ℝ 8 (fun ρ : ℝ => chartLev W τ t ρ) (Set.Ioo (-ρ₀) ρ₀))
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    chartLev W τ t 0 = 0 := by
  have hcs : Continuous (fun r : ℝ => hc τ t r) :=
    hc_sm.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  -- the auxiliary function `G ρ = ρ * ‖hc τ t √ρ‖^2`, continuous at `0` with `G 0 = 0`
  have hGcont : ContinuousAt (fun ρ : ℝ => ρ * ‖hc τ t (Real.sqrt ρ)‖ ^ 2) 0 := by
    have h1 : ContinuousAt (fun ρ : ℝ => hc τ t (Real.sqrt ρ)) 0 :=
      hcs.continuousAt.comp Real.continuous_sqrt.continuousAt
    exact continuousAt_id.mul ((h1.norm).pow 2)
  have hGtend : Filter.Tendsto (fun ρ : ℝ => ρ * ‖hc τ t (Real.sqrt ρ)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hGcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  -- `chartLev` agrees with `G` just to the right of `0`
  have hev : (fun ρ : ℝ => ρ * ‖hc τ t (Real.sqrt ρ)‖ ^ 2)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun ρ : ℝ => chartLev W τ t ρ) := by
    have hpi : (0 : ℝ) < (Real.pi / 2) ^ 2 := by positivity
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hpi).filter_mono nhdsWithin_le_nhds] with ρ hρ hρlt
    have hρ0 : 0 < ρ := hρ
    have hsqrt : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
    have hsne : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hρ0)
    have hr : Real.sqrt ρ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨Real.sqrt_pos.mpr hρ0, (Real.sqrt_lt' (by positivity)).mpr hρlt⟩
    have h1 : chartLev W τ t ρ
        = (Real.sqrt ρ) ^ 2 * ‖Work.RPB.halfChord CI.c τ t (Real.sqrt ρ)‖ ^ 2 := by
      have hWρ : W τ t ρ = W τ t ((Real.sqrt ρ) ^ 2) := by rw [hsqrt]
      rw [chartLev, hWρ, hchord τ hτ t (Real.sqrt ρ) hr]
      exact K0_chordSurf_add_one CI.c a τ t (Real.sqrt ρ)
    rw [h1, ← hc_half τ t (Real.sqrt ρ) hsne, hsqrt]
  have hcont : Filter.Tendsto (fun ρ : ℝ => chartLev W τ t ρ) (𝓝 (0 : ℝ))
      (𝓝 (chartLev W τ t 0)) :=
    (hslice.continuousOn.continuousAt
      (isOpen_Ioo.mem_nhds ⟨by linarith, hρ₀⟩)).tendsto
  exact tendsto_nhds_unique (hcont.mono_left nhdsWithin_le_nhds)
    (Filter.Tendsto.congr' hev hGtend)

/-! ## The derivative of the level function at `ρ = 0` -/

lemma chartLev_deriv_zero {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (hc_zero : ∀ τ t, hc τ t 0 = deriv (CI.c τ) t)
    (hc_half : ∀ τ t r, r ≠ 0 → hc τ t r = Work.RPB.halfChord CI.c τ t r)
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (τ t : ℝ)
    (hslice : ContDiffOn ℝ 8 (fun ρ : ℝ => chartLev W τ t ρ) (Set.Ioo (-ρ₀) ρ₀))
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    deriv (fun ρ : ℝ => chartLev W τ t ρ) 0 = ‖deriv (CI.c τ) t‖ ^ 2 := by
  set f : ℝ → ℝ := fun ρ => chartLev W τ t ρ with hf
  have h0 : f 0 = 0 := chartLev_zero hρ₀ hc hc_sm hc_half hchord τ t hslice hτ
  have hdiff : DifferentiableAt ℝ f 0 :=
    (hslice.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨by linarith, hρ₀⟩)
  have hslope : Filter.Tendsto (slope f 0) (𝓝[{0}ᶜ] (0 : ℝ)) (𝓝 (deriv f 0)) :=
    hdiff.hasDerivAt.tendsto_slope
  have hcs : Continuous (fun r : ℝ => hc τ t r) :=
    hc_sm.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  -- slope of `f` at `0` equals `‖hc τ t √ρ‖^2` near `0+`
  have hev : slope f 0 =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ : ℝ => ‖hc τ t (Real.sqrt ρ)‖ ^ 2) := by
    have hpi : (0 : ℝ) < (Real.pi / 2) ^ 2 := by positivity
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hpi).filter_mono nhdsWithin_le_nhds] with ρ hρ hρlt
    have hρ0 : 0 < ρ := hρ
    have hsqrt : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
    have hsne : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hρ0)
    have hr : Real.sqrt ρ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨Real.sqrt_pos.mpr hρ0, (Real.sqrt_lt' (by positivity)).mpr hρlt⟩
    have h1 : f ρ = ρ * ‖hc τ t (Real.sqrt ρ)‖ ^ 2 := by
      have h2 : chartLev W τ t ρ
          = (Real.sqrt ρ) ^ 2 * ‖Work.RPB.halfChord CI.c τ t (Real.sqrt ρ)‖ ^ 2 := by
        have hWρ : W τ t ρ = W τ t ((Real.sqrt ρ) ^ 2) := by rw [hsqrt]
        rw [chartLev, hWρ, hchord τ hτ t (Real.sqrt ρ) hr]
        exact K0_chordSurf_add_one CI.c a τ t (Real.sqrt ρ)
      change chartLev W τ t ρ = ρ * ‖hc τ t (Real.sqrt ρ)‖ ^ 2
      rw [h2, ← hc_half τ t (Real.sqrt ρ) hsne, hsqrt]
    rw [slope_def_field, h1, h0]
    simp only [sub_zero]
    exact mul_div_cancel_left₀ _ (ne_of_gt hρ0)
  -- continuity of `‖hc τ t √ρ‖^2` at `0`
  have hlim : Filter.Tendsto (fun ρ : ℝ => ‖hc τ t (Real.sqrt ρ)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖hc τ t 0‖ ^ 2)) := by
    have h1 : ContinuousAt (fun ρ : ℝ => hc τ t (Real.sqrt ρ)) 0 :=
      hcs.continuousAt.comp Real.continuous_sqrt.continuousAt
    have h2 : ContinuousAt (fun ρ : ℝ => ‖hc τ t (Real.sqrt ρ)‖ ^ 2) 0 :=
      (h1.norm).pow 2
    have h3 := h2.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [Real.sqrt_zero] using h3
  have hderiv : deriv f 0 = ‖hc τ t 0‖ ^ 2 := by
    have hslope' : Filter.Tendsto (slope f 0) (𝓝[>] (0 : ℝ)) (𝓝 (deriv f 0)) := by
      refine hslope.mono_left ?_
      rw [nhdsWithin_le_iff]
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact ne_of_gt hρ
    exact tendsto_nhds_unique (Filter.Tendsto.congr' hev hslope') hlim
  rw [hderiv, hc_zero τ t]

end Work.RPB.B5

end
