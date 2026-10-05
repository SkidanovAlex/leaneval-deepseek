import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.chordSurf_lagrangian
import Submission.Work.RPB.B5.chart_rho_lagrangian
import Submission.Work.RPB.B5.chartChain
import Submission.Work.RPB.B5.deriv_comp_sqrt

/-!
# B5: the chart surface `(t,σ) ↦ W τ t (ρh τ t σ)` is Lagrangian, `κ`-parametrised

`Work.RPB.B5.chart_rho_lagrangian_kappa` is the `κ`-parametrised form of
`Work.RPB.B5.chart_rho_lagrangian`.  The only difference is that the level-inverse `ρh` is now
smooth on the strip `(-κ, κ)` for an arbitrary `κ > 0` (instead of `(-1, 1)`), and the regularity
window is `(-δ, 0)` with `δ ≤ κ` (instead of `δ < 1`).

The proof is the same computation as in `chart_rho_lagrangian`: on `(-δ, 0)` the hypothesis `hreg`
keeps `ρh τ t σ ∈ (0, π²/4)`, so with `r = √(ρh τ t σ)` the chord identity `hchord` identifies the
chart value with the chord surface; the two partial derivatives are reparametrisations of the
chord-annulus tangent vectors, and the `symp`-pairing vanishes by
`Work.RPB.B2.chordSurf_lagrangian` together with bilinearity and skewness of `Work.RPV.symp`.

The two chain-rule pieces are restated for `κ` as `chart_rho_deriv_sigma_kappa` and
`chart_rho_deriv_t_kappa` (the hypotheses `hρh`/`hreg` refer to the strip `(-κ, κ)`, and
`δ ≤ κ` replaces `δ < 1`).
-/

open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- **The `σ`-derivative of the chart surface, `κ`-parametrised.**  With `t` held fixed, the chart
`s ↦ W τ t (ρh τ t s)` agrees near `σ` with the reparametrised chord surface
`s ↦ chordSurf CI.c a τ t (√(ρh τ t s))` (because `ρh τ t ·` stays in the open interval
`(0, π²/4)` at `σ`), so the chain rule `Work.RPB.B5.deriv_comp_sqrt` applies. -/
theorem chart_rho_deriv_sigma_kappa (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hchord : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0:ℝ) (Real.pi/2),
        W τ t (r^2) = Work.RPB.chordSurf CI.c a τ t r)
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    {δ : ℝ} (hδκ : δ ≤ κ)
    (hreg : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t:ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
        ρh τ t σ ∈ Set.Ioo (0:ℝ) (Real.pi^2/4)) :
    ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Ioo (-δ) 0, ∀ t : ℝ,
      deriv (fun s => W τ t (ρh τ t s)) σ
        = deriv (fun s => Real.sqrt (ρh τ t s)) σ •
            deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (ρh τ t σ)) := by
  intro τ hτ σ hσ t
  have hσmem : σ ∈ Set.Ioo (-κ) κ := ⟨by linarith [hσ.1, hδκ], by linarith [hσ.2, hκ]⟩
  obtain ⟨hpos, hlt⟩ := hreg τ hτ t σ hσ
  have hne : ρh τ t σ ≠ 0 := ne_of_gt hpos
  -- `s ↦ ρh τ t s` is `C¹²` (hence continuous/differentiable) at `σ`
  have hcont : ContDiffAt ℝ 12 (fun s : ℝ => ρh τ t s) σ := by
    have hmem : ((τ, (t, σ)) : ℝ × (ℝ × ℝ)) ∈
        Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ := ⟨hτ, trivial, hσmem⟩
    have hγ : ContDiffWithinAt ℝ 12 (fun s : ℝ => ((τ, (t, s)) : ℝ × (ℝ × ℝ)))
        (Set.Ioo (-κ) κ) σ :=
      (by fun_prop : ContDiff ℝ 12 (fun s : ℝ => ((τ, (t, s)) : ℝ × (ℝ × ℝ)))).contDiffWithinAt
    have hmap : Set.MapsTo (fun s : ℝ => ((τ, (t, s)) : ℝ × (ℝ × ℝ))) (Set.Ioo (-κ) κ)
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := fun s hs => ⟨hτ, trivial, hs⟩
    exact ((hρh.contDiffWithinAt hmem).comp σ hγ hmap).contDiffAt
      (Ioo_mem_nhds hσmem.1 hσmem.2)
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => ρh τ t s) σ :=
    hcont.differentiableAt (by norm_num)
  -- `√(ρh τ t σ) ∈ (0,π)`
  have hr0mem : Real.sqrt (ρh τ t σ) ∈ Set.Ioo (0:ℝ) Real.pi := by
    refine ⟨Real.sqrt_pos.mpr hpos, ?_⟩
    have h1 : Real.sqrt (ρh τ t σ) ≤ Real.pi / 2 := by
      calc Real.sqrt (ρh τ t σ) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hlt.le
        _ = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    linarith [Real.pi_pos]
  -- the chart agrees with the reparametrised chord surface near `σ`
  have hloc : (fun s => W τ t (ρh τ t s)) =ᶠ[𝓝 σ]
      (fun s => Work.RPB.chordSurf CI.c a τ t (Real.sqrt (ρh τ t s))) := by
    filter_upwards [hcont.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (show ρh τ t σ ∈ Set.Ioo (0:ℝ) (Real.pi^2/4) from ⟨hpos, hlt⟩))]
      with s hs
    have hr : Real.sqrt (ρh τ t s) ∈ Set.Ioc (0:ℝ) (Real.pi/2) := by
      refine ⟨Real.sqrt_pos.mpr hs.1, ?_⟩
      calc Real.sqrt (ρh τ t s) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hs.2.le
        _ = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    have h3 := hchord τ hτ t (Real.sqrt (ρh τ t s)) hr
    rwa [Real.sq_sqrt (le_of_lt hs.1)] at h3
  -- the outer leg `r ↦ chordSurf CI.c a τ t r` is differentiable at `√(ρh τ t σ)`
  have hf : DifferentiableAt ℝ (fun r : ℝ => Work.RPB.chordSurf CI.c a τ t r)
      (Real.sqrt (ρh τ t σ)) := by
    have hpair : ContDiffAt ℝ 8
        (fun z : ℝ × ℝ => Work.RPB.chordSurf CI.c a τ z.1 z.2) (t, Real.sqrt (ρh τ t σ)) :=
      chordSurf_pair_contDiffAt CI a ha hτ hr0mem
    exact (hpair.differentiableAt (by norm_num)).comp _
      (by fun_prop : DifferentiableAt ℝ (fun r : ℝ => ((t, r) : ℝ × ℝ)) (Real.sqrt (ρh τ t σ)))
  rw [hloc.deriv_eq,
    deriv_comp_sqrt (fun r : ℝ => Work.RPB.chordSurf CI.c a τ t r)
      (fun s : ℝ => ρh τ t s) σ hne hf hdiff]

/-- **The `t`-derivative of the chart surface, `κ`-parametrised.**  With `σ` held fixed, the chart
`s ↦ W τ s (ρh τ s σ)` agrees near `t` with the reparametrised chord surface
`s ↦ chordSurf CI.c a τ s (√(ρh τ s σ))`; the two-variable chain rule
`Work.RPB.B5.hasDerivAt_pair_comp` then gives the sum of the `t`-speed of the chord surface at the
frozen radius and `∂_t √(ρh τ · σ)` times the `r`-speed. -/
theorem chart_rho_deriv_t_kappa (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hchord : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0:ℝ) (Real.pi/2),
        W τ t (r^2) = Work.RPB.chordSurf CI.c a τ t r)
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    {δ : ℝ} (hδκ : δ ≤ κ)
    (hreg : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t:ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
        ρh τ t σ ∈ Set.Ioo (0:ℝ) (Real.pi^2/4)) :
    ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Ioo (-δ) 0, ∀ t : ℝ,
      deriv (fun s => W τ s (ρh τ s σ)) t
        = deriv (fun u => Work.RPB.chordSurf CI.c a τ u (Real.sqrt (ρh τ t σ))) t
          + deriv (fun s => Real.sqrt (ρh τ s σ)) t •
              deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (ρh τ t σ)) := by
  intro τ hτ σ hσ t
  have hσmem : σ ∈ Set.Ioo (-κ) κ := ⟨by linarith [hσ.1, hδκ], by linarith [hσ.2, hκ]⟩
  obtain ⟨hpos, hlt⟩ := hreg τ hτ t σ hσ
  have hne : ρh τ t σ ≠ 0 := ne_of_gt hpos
  -- `s ↦ ρh τ s σ` is `C¹²` (hence continuous/differentiable) at `t`
  have hcont : ContDiffAt ℝ 12 (fun s : ℝ => ρh τ s σ) t := by
    have hmem : ((τ, (t, σ)) : ℝ × (ℝ × ℝ)) ∈
        Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ := ⟨hτ, trivial, hσmem⟩
    have hγ : ContDiffWithinAt ℝ 12 (fun s : ℝ => ((τ, (s, σ)) : ℝ × (ℝ × ℝ)))
        Set.univ t :=
      (by fun_prop : ContDiff ℝ 12 (fun s : ℝ => ((τ, (s, σ)) : ℝ × (ℝ × ℝ)))).contDiffWithinAt
    have hmap : Set.MapsTo (fun s : ℝ => ((τ, (s, σ)) : ℝ × (ℝ × ℝ))) Set.univ
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := fun s _ => ⟨hτ, trivial, hσmem⟩
    exact ((hρh.contDiffWithinAt hmem).comp t hγ hmap).contDiffAt Filter.univ_mem
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => ρh τ s σ) t :=
    hcont.differentiableAt (by norm_num)
  have hr0mem : Real.sqrt (ρh τ t σ) ∈ Set.Ioo (0:ℝ) Real.pi := by
    refine ⟨Real.sqrt_pos.mpr hpos, ?_⟩
    have h1 : Real.sqrt (ρh τ t σ) ≤ Real.pi / 2 := by
      calc Real.sqrt (ρh τ t σ) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hlt.le
        _ = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    linarith [Real.pi_pos]
  -- the chart agrees with the reparametrised chord surface near `t`
  have hloc : (fun s => W τ s (ρh τ s σ)) =ᶠ[𝓝 t]
      (fun s => Work.RPB.chordSurf CI.c a τ s (Real.sqrt (ρh τ s σ))) := by
    filter_upwards [hcont.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (show ρh τ t σ ∈ Set.Ioo (0:ℝ) (Real.pi^2/4) from ⟨hpos, hlt⟩))]
      with s hs
    have hr : Real.sqrt (ρh τ s σ) ∈ Set.Ioc (0:ℝ) (Real.pi/2) := by
      refine ⟨Real.sqrt_pos.mpr hs.1, ?_⟩
      calc Real.sqrt (ρh τ s σ) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hs.2.le
        _ = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    have h3 := hchord τ hτ s (Real.sqrt (ρh τ s σ)) hr
    rwa [Real.sq_sqrt (le_of_lt hs.1)] at h3
  rw [hloc.deriv_eq]
  -- the two-variable chain rule for `s ↦ chordSurf CI.c a τ s (√(ρh τ s σ))`
  have hΦ : DifferentiableAt ℝ (fun z : ℝ × ℝ => Work.RPB.chordSurf CI.c a τ z.1 z.2)
      (t, Real.sqrt (ρh τ t σ)) :=
    (chordSurf_pair_contDiffAt CI a ha hτ hr0mem).differentiableAt (by norm_num)
  have hψ : DifferentiableAt ℝ (fun s : ℝ => Real.sqrt (ρh τ s σ)) t :=
    (Real.hasDerivAt_sqrt hne).differentiableAt.comp t hdiff
  exact (hasDerivAt_pair_comp hΦ hψ).deriv

/-- **The chart surface swept out by `W` at the level-inverse `ρh` is Lagrangian, `κ`-parametrised.**

For `τ ∈ [0,1]`, `σ ∈ (-δ,0)` and `t ∈ ℝ`,
`symp (∂_σ (W τ t (ρh τ t ·))) (∂_t (W τ · (ρh τ · σ))) = 0`. -/
theorem chart_rho_lagrangian_kappa (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hchord : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0:ℝ) (Real.pi/2),
        W τ t (r^2) = Work.RPB.chordSurf CI.c a τ t r)
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t:ℝ, ∀ σ ∈ Set.Ioo (-κ) κ, ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ ≤ κ)
    (hreg : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t:ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
        ρh τ t σ ∈ Set.Ioo (0:ℝ) (Real.pi^2/4)) :
    ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Ioo (-δ) 0, ∀ t : ℝ,
      Work.RPV.symp (deriv (fun s => W τ t (ρh τ t s)) σ)
        (deriv (fun s => W τ s (ρh τ s σ)) t) = 0 := by
  intro τ hτ σ hσ t
  -- the two tangent vectors, as reparametrisations of the chord annulus
  rw [chart_rho_deriv_sigma_kappa CI a ha hchord hκ hρh hδκ hreg τ hτ σ hσ t,
    chart_rho_deriv_t_kappa CI a ha hchord hκ hρh hδκ hreg τ hτ σ hσ t]
  -- `√(ρh τ t σ) ∈ (0,π)`, so the chord annulus is Lagrangian there
  obtain ⟨hpos, hlt⟩ := hreg τ hτ t σ hσ
  have hr0mem : Real.sqrt (ρh τ t σ) ∈ Set.Ioo (0:ℝ) Real.pi := by
    refine ⟨Real.sqrt_pos.mpr hpos, ?_⟩
    have h1 : Real.sqrt (ρh τ t σ) ≤ Real.pi / 2 := by
      calc Real.sqrt (ρh τ t σ) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hlt.le
        _ = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    linarith [Real.pi_pos]
  have hLag : Work.RPV.symp
      (deriv (fun s => Work.RPB.chordSurf CI.c a τ s (Real.sqrt (ρh τ t σ))) t)
      (deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (ρh τ t σ))) = 0 :=
    Work.RPB.B2.chordSurf_lagrangian CI a ha τ hτ t (Real.sqrt (ρh τ t σ)) hr0mem
  have hBrBr : Work.RPV.symp
      (deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (ρh τ t σ)))
      (deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (ρh τ t σ))) = 0 :=
    symp_self _
  have hBrBt : Work.RPV.symp
      (deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (ρh τ t σ)))
      (deriv (fun u => Work.RPB.chordSurf CI.c a τ u (Real.sqrt (ρh τ t σ))) t) = 0 := by
    rw [symp_antisymm_chart, hLag, neg_zero]
  rw [symp_smul_add]
  rw [hBrBr, hBrBt, mul_zero, add_zero, mul_zero]

end Work.RPB.B5
