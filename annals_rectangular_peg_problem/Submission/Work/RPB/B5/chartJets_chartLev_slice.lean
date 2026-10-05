import Mathlib
import Submission.Work.RPV.V
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B5.K0_chordSurf_level
import Submission.Work.RPB.B5.strictMonoOn_of_deriv_pos_nhds

/-!
# B5: the `ρ`-slice of the level function of the chord chart

Given the `ρ = r²`-chart `W` of the chord annulus
(`W τ t (r ^ 2) = chordSurf CI.c a τ t r` for `0 < r ≤ π/2`, with `W` of class `C⁸` on
`[0,1] × ℝ × (-ρ₀, ρ₀)`), the level function `chartLev W τ t ρ = K₀(W τ t ρ) + 1` satisfies,
along the slice through `ρ = 0`:

* `K₀(W τ t 0) + 1 = 0` — the blown-up diagonal `Σ₀` is the level `K₀ = -1` of the chord
  annulus, and the `ρ`-chart is continuous there;
* `(K₀(W τ t ·) + 1)'(0) = ‖c_τ'(t)‖²` — the level coordinate `s = K₀ + 1` grows along the
  squared chord parameter `ρ = r²` at speed `‖c_τ'(t)‖²`, because on the chord side
  `s(r²) = r² ‖halfChord c τ t r‖²` (this is `Work.RPB.B5.K0_chordSurf_level`) and
  `halfChord c τ t r → c_τ'(t)` as `r → 0`;
* consequently `K₀(W τ t ·) + 1` is strictly increasing on a neighbourhood of `0`: the level
  function is locally invertible at `ρ = 0`, which is what the level chart of the annulus
  (`Work.RPB.B5.chartLev_inverse`) uses.

The half chord is handled through its smooth even extension `halfChordExt` across `r = 0`
built in `Work.RPB.B5.halfChordSmooth`: it has the same values as the half chord off `r = 0`
(`halfChordExt_eq`), the value `c_τ'(t)` at `r = 0` (`halfChordExt_zero`) and is `C^∞`, which
is what lets the one-sided annulus identities be compared with the `C⁸`-regularity of `W`
at `ρ = 0`.  The strictly-positive-derivative step at the end is
`Work.RPB.B5.strictMonoOn_of_deriv_pos_nhds`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The level function of the `ρ`-chart of the chord annulus: `K₀(W τ t ρ) + 1`. -/
private def sLev (W : ℝ → ℝ → ℝ → Work.RPV.PS) (τ t ρ : ℝ) : ℝ :=
  Work.RPV.K0 (W τ t ρ) + 1

/-! ## Smoothness of the level function in the chart coordinates -/

private lemma contDiff_K0_add_one : ContDiff ℝ 8 (fun x : Work.RPV.PS => Work.RPV.K0 x + 1) := by
  simp only [Work.RPV.K0]
  fun_prop

private lemma sLev_contDiffOn {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ}
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀)) :
    ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => sLev W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) :=
  (ContDiff.comp_contDiffOn contDiff_K0_add_one hW).congr (fun _ _ => rfl)

/-- The `ρ`-slice of the level function is `C⁸`; this holds at `τ = 0, 1` too, since the whole
line `ρ ↦ (τ, t, ρ)` lies inside the box. -/
private lemma sLev_slice_contDiffOn {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ}
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (τ t : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 8 (fun ρ : ℝ => sLev W τ t ρ) (Set.Ioo (-ρ₀) ρ₀) :=
  ((sLev_contDiffOn hW).comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
    (fun _ hρ => ⟨hτ, Set.mem_univ _, hρ⟩)).congr (fun _ _ => rfl)

/-! ## The level function vanishes at `ρ = 0` -/

/-- `K₀(W τ t ·) + 1` vanishes at `ρ = 0`: on the chord side it equals
`ρ ‖halfChord c τ t √ρ‖²`, which tends to `0` as `ρ → 0⁺`, while the `ρ`-slice is continuous
at `0` by the `C⁸`-regularity of `W`. -/
private lemma sLev_zero {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (τ t : ℝ)
    (hslice : ContDiffOn ℝ 8 (fun ρ : ℝ => sLev W τ t ρ) (Set.Ioo (-ρ₀) ρ₀))
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    sLev W τ t 0 = 0 := by
  have hcs : Continuous (fun r : ℝ => halfChordExt CI.c τ t r) :=
    (contDiff_halfChordExt CI.c CI.smooth).continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  -- the auxiliary function `G ρ = ρ * ‖hc τ t √ρ‖^2`, continuous at `0` with `G 0 = 0`
  have hGcont : ContinuousAt (fun ρ : ℝ => ρ * ‖halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2) 0 := by
    have h1 : ContinuousAt (fun ρ : ℝ => halfChordExt CI.c τ t (Real.sqrt ρ)) 0 :=
      hcs.continuousAt.comp Real.continuous_sqrt.continuousAt
    exact continuousAt_id.mul ((h1.norm).pow 2)
  have hGtend : Filter.Tendsto (fun ρ : ℝ => ρ * ‖halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hGcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  -- `sLev` agrees with `G` just to the right of `0`
  have hev : (fun ρ : ℝ => ρ * ‖halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun ρ : ℝ => sLev W τ t ρ) := by
    have hpi : (0 : ℝ) < (Real.pi / 2) ^ 2 := by positivity
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hpi).filter_mono nhdsWithin_le_nhds] with ρ hρ hρlt
    have hρ0 : 0 < ρ := hρ
    have hsqrt : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
    have hsne : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hρ0)
    have hr : Real.sqrt ρ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨Real.sqrt_pos.mpr hρ0, (Real.sqrt_lt' (by positivity)).mpr hρlt⟩
    have h1 : sLev W τ t ρ
        = (Real.sqrt ρ) ^ 2 * ‖Work.RPB.halfChord CI.c τ t (Real.sqrt ρ)‖ ^ 2 := by
      have hWρ : W τ t ρ = W τ t ((Real.sqrt ρ) ^ 2) := by rw [hsqrt]
      rw [sLev, hWρ, hchord τ hτ t (Real.sqrt ρ) hr]
      exact K0_chordSurf_level CI.c a τ t (Real.sqrt ρ)
    rw [h1, ← halfChordExt_eq CI.c CI.smooth τ t (Real.sqrt ρ) hsne, hsqrt]
  have hcont : Filter.Tendsto (fun ρ : ℝ => sLev W τ t ρ) (𝓝 (0 : ℝ))
      (𝓝 (sLev W τ t 0)) :=
    (hslice.continuousOn.continuousAt
      (isOpen_Ioo.mem_nhds ⟨by linarith, hρ₀⟩)).tendsto
  exact tendsto_nhds_unique (hcont.mono_left nhdsWithin_le_nhds)
    (Filter.Tendsto.congr' hev hGtend)

/-! ## The derivative of the level function at `ρ = 0` -/

/-- The derivative of the `ρ`-slice of the level function at `0` is `‖c_τ'(t)‖²`: the slope
of `s = K₀(W) + 1` at `0` is `‖halfChord c τ t √ρ‖²` on the chord side, and the half chord
tends to `c_τ'(t)`. -/
private lemma sLev_deriv_zero {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (τ t : ℝ)
    (hslice : ContDiffOn ℝ 8 (fun ρ : ℝ => sLev W τ t ρ) (Set.Ioo (-ρ₀) ρ₀))
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    deriv (fun ρ : ℝ => sLev W τ t ρ) 0 = ‖deriv (CI.c τ) t‖ ^ 2 := by
  set f : ℝ → ℝ := fun ρ => sLev W τ t ρ with hf
  have h0 : f 0 = 0 := sLev_zero hρ₀ hchord τ t hslice hτ
  have hdiff : DifferentiableAt ℝ f 0 :=
    (hslice.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨by linarith, hρ₀⟩)
  have hslope : Filter.Tendsto (slope f 0) (𝓝[{0}ᶜ] (0 : ℝ)) (𝓝 (deriv f 0)) :=
    hdiff.hasDerivAt.tendsto_slope
  have hcs : Continuous (fun r : ℝ => halfChordExt CI.c τ t r) :=
    (contDiff_halfChordExt CI.c CI.smooth).continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  -- slope of `f` at `0` equals `‖hc τ t √ρ‖^2` near `0+`
  have hev : slope f 0 =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ : ℝ => ‖halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2) := by
    have hpi : (0 : ℝ) < (Real.pi / 2) ^ 2 := by positivity
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hpi).filter_mono nhdsWithin_le_nhds] with ρ hρ hρlt
    have hρ0 : 0 < ρ := hρ
    have hsqrt : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
    have hsne : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hρ0)
    have hr : Real.sqrt ρ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨Real.sqrt_pos.mpr hρ0, (Real.sqrt_lt' (by positivity)).mpr hρlt⟩
    have h1 : f ρ = ρ * ‖halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2 := by
      have h2 : sLev W τ t ρ
          = (Real.sqrt ρ) ^ 2 * ‖Work.RPB.halfChord CI.c τ t (Real.sqrt ρ)‖ ^ 2 := by
        have hWρ : W τ t ρ = W τ t ((Real.sqrt ρ) ^ 2) := by rw [hsqrt]
        rw [sLev, hWρ, hchord τ hτ t (Real.sqrt ρ) hr]
        exact K0_chordSurf_level CI.c a τ t (Real.sqrt ρ)
      change sLev W τ t ρ = ρ * ‖halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2
      rw [h2, ← halfChordExt_eq CI.c CI.smooth τ t (Real.sqrt ρ) hsne, hsqrt]
    rw [slope_def_field, h1, h0]
    simp only [sub_zero]
    exact mul_div_cancel_left₀ _ (ne_of_gt hρ0)
  -- continuity of `‖hc τ t √ρ‖^2` at `0`
  have hlim : Filter.Tendsto (fun ρ : ℝ => ‖halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖halfChordExt CI.c τ t 0‖ ^ 2)) := by
    have h1 : ContinuousAt (fun ρ : ℝ => halfChordExt CI.c τ t (Real.sqrt ρ)) 0 :=
      hcs.continuousAt.comp Real.continuous_sqrt.continuousAt
    have h2 : ContinuousAt (fun ρ : ℝ => ‖halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2) 0 :=
      (h1.norm).pow 2
    have h3 := h2.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [Real.sqrt_zero] using h3
  have hderiv : deriv f 0 = ‖halfChordExt CI.c τ t 0‖ ^ 2 := by
    have hslope' : Filter.Tendsto (slope f 0) (𝓝[>] (0 : ℝ)) (𝓝 (deriv f 0)) := by
      refine hslope.mono_left ?_
      rw [nhdsWithin_le_iff]
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact ne_of_gt hρ
    exact tendsto_nhds_unique (Filter.Tendsto.congr' hev hslope') hlim
  rw [hderiv, halfChordExt_zero CI.c CI.smooth τ t]

/-! ## The target -/

theorem chartJets_chartLev_slice (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hchord : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0:ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0:ℝ) 1) (t : ℝ) :
    Work.RPV.K0 (W τ t 0) + 1 = 0 ∧
    deriv (fun ρ : ℝ => Work.RPV.K0 (W τ t ρ) + 1) 0 = ‖deriv (CI.c τ) t‖ ^ 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ StrictMonoOn (fun ρ : ℝ => Work.RPV.K0 (W τ t ρ) + 1) (Set.Ioo (-ε) ε) := by
  -- only the open half of the chord hypothesis is needed
  have hch : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r :=
    fun τ hτ t r hr => hchord τ hτ t r ⟨hr.1, hr.2.le⟩
  have hslice : ContDiffOn ℝ 8 (fun ρ : ℝ => sLev W τ t ρ) (Set.Ioo (-ρ₀) ρ₀) :=
    sLev_slice_contDiffOn hW τ t hτ
  have hderiv := sLev_deriv_zero (CI := CI) (a := a) hρ₀ hch τ t hslice hτ
  refine ⟨sLev_zero hρ₀ hch τ t hslice hτ, hderiv, ?_⟩
  -- strict monotonicity near `0` from the positive derivative
  have hpos : 0 < deriv (fun ρ : ℝ => sLev W τ t ρ) 0 := by
    rw [hderiv]
    exact pow_pos (norm_pos_iff.mpr (CI.imm τ hτ t)) 2
  exact strictMonoOn_of_deriv_pos_nhds (fun ρ : ℝ => sLev W τ t ρ) ρ₀ hρ₀
    ((sLev_slice_contDiffOn hW τ t hτ).of_le (by norm_num)) hpos

end Work.RPB.B5

end
