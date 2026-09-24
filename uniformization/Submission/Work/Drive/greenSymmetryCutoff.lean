import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.Kernel.GreenCover
import Submission.Work.Kernel.exists_greenCover_centred
import Submission.Work.Kernel.pairing_pole_smooth
import Submission.Work.Kernel.LevelDecay
import Submission.Work.Kernel.greenCoverPairingAux
import Submission.Work.Kernel.greenCover_pairing_eq_two_pi_mul
import Submission.Work.Drive.greenEnergyPairing
import Submission.Work.Drive.pairing_leibniz
import Submission.Work.Drive.lastMileTools
import Submission.Work.Drive.energyGreenRung
import Submission.Work.Analysis.Harmonic.integral_inner_gradient_mul_log_eq_zero

/-!
# The two-cutoff identity for the symmetry of the Green function (see the NOTES file)

`Submission/Work/Drive/NOTES_greenSymmetryAtPoles_cutoff_route.md` records the route in full.  In
one line:

```
2π (gB a − gA b) = Σᵢ ∫ ψᵢ Ξ'(gB) [ gB ⟨∇gA,∇gB⟩ − gA |∇gB|² ]  =  2π c_σ − O(ε(2σ))  ⟶ 0,
```

* the left-hand side comes from subtracting the two instances of the pole identity `(P)`
  (`Work.Kernel.pairing_pole_smooth`) for the test functions
  `Ψ₁ = Ξ(gB)·gB + T_b` (at the pole `a`) and `Ψ₂ = Ξ(gB)·gA + T_a` (at the pole `b`);
* the first piece on the right is the exact flux identity obtained from `(P)` applied to the test
  function `θ ∘ gB`, where `θ' = t·Ξ'`;
* the second piece is bounded by the *level* identity for `gB` (positive weight, no
  Cauchy–Schwarz), with the uniform bound `gA ≤ ε(2σ)` on `{gB ≤ 2σ}`
  (`Work.Kernel.sup_lt_of_level_lt_symm`);
* the logarithmic bumps `T_a`, `T_b` (defined below) make the test functions of class `C¹`, and
  their own pairings vanish by `Work.Analysis.Harmonic.integral_inner_gradient_mul_log_eq_zero`.
-/

open MeasureTheory Set Filter Classical
open scoped Manifold Topology Gradient ContDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-! ## 1. The step cutoff and its primitive -/

/-- The smooth step at scale `σ`: `0` on `(-∞, σ]`, `1` on `[2σ, ∞)`, monotone. -/
noncomputable def stepCutoff (σ : ℝ) : ℝ → ℝ := fun t => Real.smoothTransition (t / σ - 1)

variable {σ : ℝ}

theorem stepCutoff_eq_zero_of_le (hσ : 0 < σ) {t : ℝ} (h : t ≤ σ) : stepCutoff σ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos, div_le_one hσ]; exact h)

theorem stepCutoff_eq_one_of_two_mul_le (hσ : 0 < σ) {t : ℝ} (h : 2 * σ ≤ t) :
    stepCutoff σ t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hσ]; linarith)

theorem stepCutoff_nonneg (σ t : ℝ) : 0 ≤ stepCutoff σ t := Real.smoothTransition.nonneg _

theorem stepCutoff_le_one (σ t : ℝ) : stepCutoff σ t ≤ 1 := Real.smoothTransition.le_one _

theorem monotone_stepCutoff {σ : ℝ} (hσ : 0 < σ) : Monotone (stepCutoff σ) :=
  Real.smoothTransition.monotone.comp (fun a b hab => by gcongr)

theorem contDiff_stepCutoff (σ : ℝ) {n : ℕ∞} : ContDiff ℝ n (stepCutoff σ) :=
  Real.smoothTransition.contDiff.comp (contDiff_id.div_const σ |>.sub contDiff_const)

/-- The primitive `θ(t) = t·Ξ t - ∫_0^t Ξ`, so that `θ' = t·Ξ'`. -/
noncomputable def thetaCutoff (σ : ℝ) : ℝ → ℝ :=
  fun t => t * stepCutoff σ t - ∫ s in (0 : ℝ)..t, stepCutoff σ s

/-- The derivative of `θ`: `θ' t = t · Ξ' t`. -/
theorem hasDerivAt_thetaCutoff (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (thetaCutoff σ) (t * deriv (stepCutoff σ) t) t := by
  have hc := (contDiff_stepCutoff σ (n := 1)).continuous
  have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  have h2 : HasDerivAt (fun t : ℝ => stepCutoff σ t) (deriv (stepCutoff σ) t) t :=
    ((contDiff_stepCutoff σ (n := 1)).differentiable (by norm_num) t).hasDerivAt
  have h3 : HasDerivAt (fun t : ℝ => t * stepCutoff σ t)
      (1 * stepCutoff σ t + t * deriv (stepCutoff σ) t) t := h1.mul h2
  have h4 : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..t, stepCutoff σ s) (stepCutoff σ t) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      (Continuous.stronglyMeasurableAtFilter hc (volume : Measure ℝ) (𝓝 t)) hc.continuousAt
  have h5 := h3.sub h4
  have heq : (1 * stepCutoff σ t + t * deriv (stepCutoff σ) t) - stepCutoff σ t
      = t * deriv (stepCutoff σ) t := by ring
  rw [heq] at h5
  exact h5

theorem thetaCutoff_eq_zero_of_le (hσ : 0 < σ) {t : ℝ} (h : t ≤ σ) : thetaCutoff σ t = 0 := by
  have h0 : ∀ s ∈ Set.uIcc (0:ℝ) t, stepCutoff σ s = 0 := by
    intro s hs
    rcases le_or_gt 0 t with ht | ht
    · rw [Set.uIcc_of_le ht] at hs
      exact stepCutoff_eq_zero_of_le hσ (le_trans hs.2 h)
    · rw [Set.uIcc_of_ge ht.le] at hs
      exact stepCutoff_eq_zero_of_le hσ (le_trans hs.2 (le_of_lt hσ))
  have hz : (∫ s in (0 : ℝ)..t, stepCutoff σ s) = (∫ s in (0 : ℝ)..t, (0 : ℝ)) :=
    intervalIntegral.integral_congr fun s hs => h0 s hs
  simp only [intervalIntegral.integral_zero] at hz
  rw [thetaCutoff, hz, stepCutoff_eq_zero_of_le hσ h]
  ring

theorem thetaCutoff_eq_of_two_mul_le (hσ : 0 < σ) {t : ℝ} (h : 2 * σ ≤ t) :
    thetaCutoff σ t = 2 * σ - ∫ s in (0 : ℝ)..(2 * σ), stepCutoff σ s := by
  have h1 : thetaCutoff σ t = t - ∫ s in (0 : ℝ)..t, stepCutoff σ s := by
    rw [thetaCutoff, stepCutoff_eq_one_of_two_mul_le hσ h, mul_one]
  rw [h1]
  have hint : ∀ a b : ℝ, IntervalIntegrable (stepCutoff σ) volume a b := fun a b =>
    (contDiff_stepCutoff σ (n := 1)).continuous.intervalIntegrable a b
  have hsplit : (∫ s in (0 : ℝ)..t, stepCutoff σ s)
      = (∫ s in (0 : ℝ)..(2 * σ), stepCutoff σ s) + ∫ s in (2 * σ)..t, stepCutoff σ s :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have hone : (∫ s in (2 * σ)..t, stepCutoff σ s) = t - 2 * σ := by
    have hcongr : (∫ s in (2 * σ)..t, stepCutoff σ s) = ∫ s in (2 * σ)..t, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le h] at hs
      exact stepCutoff_eq_one_of_two_mul_le hσ hs.1
    rw [hcongr]
    simp
  rw [hsplit, hone]
  ring


/-! ## 2. The logarithmic bump (the regulariser of the second pole)

`logBump x₀ h σ` is `h (‖c x - c x₀‖) · log ‖c x - c x₀‖` in the chart `c = chartAt ℂ x₀`, clamped
to the chart ball of radius `σ`, and `0` elsewhere.  With `h ≡ 1` near `0` and `h ≡ 0` beyond `2R`,
`logBump x₀ h σ` is supported in the `σ`-ball and equals `log ‖c x - c x₀‖` near `x₀`, so that
`g + logBump x₀ h σ` is `C¹` for a Green function `g` with pole `x₀`.
-/

/-- The logarithmic bump at `x₀` in its own chart, clamped at the ball of radius `σ`. -/
noncomputable def logBump (x₀ : X) (h : ℝ → ℝ) (σ : ℝ) : X → ℝ := by
  classical
  exact fun x => if x ∈ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) σ then
    h ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ * Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖
  else 0

theorem logBump_eq_zero_of_notMem {x₀ : X} {h : ℝ → ℝ} {σ : ℝ} {x : X}
    (hx : x ∉ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) σ) :
    logBump x₀ h σ x = 0 := by classical rw [logBump]; exact if_neg hx


/-! ## 3. Exchanging the two distinguished poles of a cover -/

/-- The same cover data with the roles of the two poles exchanged.  Needed to obtain the pole
identity `(P)` at the *second* pole from `Work.Kernel.pairing_pole_smooth` (which is stated for
`E.ia`). -/
def GreenCoverSwap {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : Work.Kernel.GreenCover ι Ω K a b) : Work.Kernel.GreenCover ι Ω K b a where
  y := E.y
  s := E.s
  σ := E.σ
  ρ := E.ρ
  ψ := E.ψ
  β := E.β
  ia := E.ib
  ib := E.ia
  hspos := E.hspos
  hsσ := E.hsσ
  hσρ := E.hσρ
  htgt := E.htgt
  hballΩ := E.hballΩ
  hψnonneg := E.hψnonneg
  hψsupp := E.hψsupp
  hsum := E.hsum
  hψdiff := E.hψdiff
  ha_mem := E.hb_mem
  ha_nmem := E.hb_nmem
  hb_mem := E.ha_mem
  hb_nmem := E.ha_nmem
  hβone := E.hβone
  hβsupp := E.hβsupp
  hβdiff := E.hβdiff

@[simp] theorem GreenCoverSwap_y {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : Work.Kernel.GreenCover ι Ω K a b) : (GreenCoverSwap E).y = E.y := rfl


/-! ## 4. The main theorem of the route (interface)

The statement below is the strongest form of the crux.  Its proof assembles:

* `Work.Kernel.exists_greenCover_centred` (the cover, with `a`,`b` as pole charts, `C¹` weights);
* `Work.Kernel.pairing_pole_smooth` (`(P)`) for `Ψ₁ = Ξ(gB)·gB + T_b` at the pole `a`, and for
  `Ψ₂ = Ξ(gB)·gA + T_a` at the pole `b` (via `GreenCoverSwap`);
* `Work.Drive.pairTerm_leibniz`, `pairTerm_comp_right`, `pairTerm_add`, `pairTerm_symm`;
* `Work.Drive.pairing_logBump_eq_zero` (delegated) for the two vanishing `T`-pairings;
* the exact flux value `Σᵢ ∫ ψᵢ Ξ'(gB) gB ⟪∇gA,∇gB⟫ = 2π c_σ` (from `(P)` for `θ ∘ gB`);
* the level identity `Σᵢ ∫ ψᵢ Ξ'(gB) |∇gB|² = 2π` (`(P)` for `Ξ ∘ gB`) and
  `Work.Kernel.sup_lt_of_level_lt_symm` for the bound `gA ≤ ε(2σ)` on the collar.
-/

theorem greenSymmetry_of_isGreenOn_cutoff {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsCompact (closure Ω)) {a b : X} (hab : a ≠ b)
    (haΩ : a ∈ Ω) (hbΩ : b ∈ Ω) {gA gB : X → ℝ}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB) : gA b = gB a := by
  sorry


/-! ## 4. The level identity in the pairing form `(L)`

A local copy of `Work.Drive.pairing_comp_eq_weighted` (whose home module `lastMileLevel.lean` is
currently broken by the namespace move of `pairTerm_comp_right`).  It converts the pole identity for
the test function `Φ ∘ f` into the identity for the *weighted* Dirichlet energy with weight
`deriv Φ ∘ f`; both `Φ = Ξ_σ` (the level identity, value `2π`) and `Φ = θ` (the flux identity, value
`2π c_σ`) below are instances of it. -/

theorem pairing_comp_eq_weighted' {ι : Type*} [Fintype ι]
    {y : ι → X} {ρ σ : ι → ℝ} {ψ : ι → X → ℝ} {f : X → ℝ} {Φ : ℝ → ℝ} {p : X}
    (hσρ : ∀ i, σ i < ρ i) (hΦ0 : Φ (0 : ℝ) = 0) (hΦd : Differentiable ℝ Φ)
    (hdiff : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (clampedPullback (y i) (ρ i) f) z)
    (hP : pairing y ρ σ ψ f (fun z => Φ (f z)) = 2 * Real.pi * Φ (f p)) :
    pairing y ρ σ (fun i => ψ i * fun z => deriv Φ (f z)) f f = 2 * Real.pi * Φ (f p) := by
  rw [← hP, pairing, pairing]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (pairTerm_comp_right (x := y i) (hσρ i) hΦ0 hΦd (hdiff i)).symm


/-! ## 5. Reindexing a cover (to reach the `Fin N`-indexed form of the pole identity)

`Work.Kernel.greenCover_pairing_eq_two_pi_mul` is stated for `GreenCover (Fin N)`, while
`Work.Kernel.exists_greenCover_centred` returns a cover with an abstract index type.  Reindexing is
mechanical; the reward is that this form of `(P)` needs neither the logarithmic expansion nor the
`C¹` properties of the cover weights nor `hgAdiff`, only the support/C¹ hypotheses on the test
function and the `PairIntegrable` certificates. -/

/-- The cover reindexed along an equivalence of index types. -/
def GreenCoverReindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] {Ω K : Set X} {a b : X}
    (E : Work.Kernel.GreenCover ι Ω K a b) (e : ι ≃ ι') :
    Work.Kernel.GreenCover ι' Ω K a b where
  y i := E.y (e.symm i)
  s i := E.s (e.symm i)
  σ i := E.σ (e.symm i)
  ρ i := E.ρ (e.symm i)
  ψ i := E.ψ (e.symm i)
  β i := E.β (e.symm i)
  ia := e E.ia
  ib := e E.ib
  hspos i := E.hspos (e.symm i)
  hsσ i := E.hsσ (e.symm i)
  hσρ i := E.hσρ (e.symm i)
  htgt i := E.htgt (e.symm i)
  hballΩ i := E.hballΩ (e.symm i)
  hψnonneg i := E.hψnonneg (e.symm i)
  hψsupp i := E.hψsupp (e.symm i)
  hsum := by
    intro x hx
    rw [show (∑ i : ι', E.ψ (e.symm i) x) = ∑ i : ι, E.ψ i x from
      Equiv.sum_comp e.symm (fun i => E.ψ i x)]
    exact E.hsum x hx
  hψdiff k i := E.hψdiff (e.symm k) (e.symm i)
  ha_mem := by simpa using E.ha_mem
  ha_nmem i hi := E.ha_nmem (e.symm i)
    (fun h => hi (by rw [← Equiv.apply_symm_apply e i, h]))
  hb_mem := by simpa using E.hb_mem
  hb_nmem i hi := E.hb_nmem (e.symm i)
    (fun h => hi (by rw [← Equiv.apply_symm_apply e i, h]))
  hβone i := E.hβone (e.symm i)
  hβsupp i := E.hβsupp (e.symm i)
  hβdiff k i := E.hβdiff (e.symm k) (e.symm i)



/-! ## 7. The pole value is free (unrestricted version) -/

/-- **The value of a Green function at its own pole is free**, with no sign restriction on the new
value: `IsGreenOn` constrains `E` only off `x₀` (positivity, harmonicity, the decay of the superlevel
sets and the logarithmic pole all exclude `x₀`), and the decay clause survives the change at `x₀`
because the compact set may be enlarged by `{x₀} ⊆ Ω`.  (This is
`Work.Drive.isGreenOn_update_of_pos` with the hypothesis `0 < M` dropped: the proof never uses it.)

This is what lets the pole value be normalised to the finite part `H (c x₀)` of the logarithmic
expansion, which is what the un-punctured form of the pole identity `(P)` requires (see
`NOTES_greenSymmetryAtPoles_cutoff_route.md` §12). -/
theorem isGreenOn_update {Ω : Set X} {b : X} (hbΩ : b ∈ Ω) {gB : X → ℝ}
    (hB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB) (M : ℝ) :
    Work.SimplyConnected.ABS.IsGreenOn Ω b (Function.update gB b M) := by
  classical
  obtain ⟨hpos, hharm, hdec, hpole⟩ := hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hxb
    rw [Function.update_of_ne hxb]
    exact hpos x hx hxb
  · intro x hx
    have hxb : x ≠ b := fun h => hx.2 (by simpa [h])
    have hsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hU : (chartAt ℂ x).source \ {b} ∈ 𝓝 x :=
      ((chartAt ℂ x).open_source.sdiff isClosed_singleton).mem_nhds
        ⟨hsrc, by simpa [Set.mem_singleton_iff] using hxb⟩
    have himg : (chartAt ℂ x) '' ((chartAt ℂ x).source \ {b}) ∈ 𝓝 ((chartAt ℂ x) x) :=
      (chartAt ℂ x).image_mem_nhds hsrc hU
    have hev : ((Function.update gB b M) ∘ (chartAt ℂ x).symm)
        =ᶠ[𝓝 ((chartAt ℂ x) x)] (gB ∘ (chartAt ℂ x).symm) := by
      filter_upwards [himg] with z hz
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply]
      rw [(chartAt ℂ x).left_inv hy.1]
      exact Function.update_of_ne (by simpa [Set.mem_singleton_iff] using hy.2) M gB
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr (hharm x hx)
  · intro ε hε
    obtain ⟨K, hKc, hKΩ, hKlt⟩ := hdec ε hε
    refine ⟨K ∪ {b}, hKc.union isCompact_singleton, ?_, ?_⟩
    · rintro x (hx | hx)
      · exact hKΩ hx
      · rw [Set.mem_singleton_iff] at hx
        exact hx ▸ hbΩ
    · intro x hxΩ hxK
      have hxb : x ≠ b := fun h => hxK (Or.inr (by simpa [h]))
      rw [Function.update_of_ne hxb]
      exact hKlt x hxΩ fun hxK' => hxK (Or.inl hxK')
  · obtain ⟨C, V, hV, hb⟩ := hpole
    refine ⟨C, V, hV, fun x hxV hxΩ hxb => ?_⟩
    rw [Function.update_of_ne hxb]
    exact hb x hxV hxΩ hxb

end Work.Drive
