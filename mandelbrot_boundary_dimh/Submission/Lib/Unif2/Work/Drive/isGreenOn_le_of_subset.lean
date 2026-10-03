import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.green_reduction.exists_isGreenOn_precompact_superset
import Submission.Lib.Unif2.MaxPrincipleRegion
import Submission.Lib.Unif2.Work.Drive.maxPrincipleTwoPoles

/-!
# Monotonicity of the Green function of a region in the region

`Work.Drive.isGreenOn_le_of_subset`: on a *connected* Riemann surface, if `Ω ⊆ Ω'` and `G`, `G'`
are the Green functions of these regions (`Work.SimplyConnected.ABS.IsGreenOn`) with the *same*
pole `a ∈ Ω`, then `G ≤ G'` on `Ω` off the pole.

The proof is the classical one: `h := G - G'` is harmonic on `Ω ∖ {a}` and its logarithmic
singularity at `a` cancels, so `h` extends harmonically across the pole
(`Work.Drive.exists_update_harmonicOnXAt_of_bounded_punctured`); for `ε > 0` the set
`U = {y ∈ Ω | ε < h}` is open, contained in a compact subset of `Ω` (because `G > ε` on `U` off
the pole and `G` has relatively compact superlevel sets), and `h ≤ ε` at every frontier point of
`U`; the maximum principle on a relatively compact region
(`Submission.SubharmonicOnX.le_of_frontier_limsup`) gives `h ≤ ε` on `U`, which contradicts
`h x > ε` for `ε < h x`.

The only delicate point is the case `U = X` (frontier empty): then `Ω = X` is compact, and a
Green function cannot exist on a compact surface — `Work.Drive.not_compactSpace_of_isGreenOn_univ`
below (the maximum/minimum principle argument: a positive harmonic function off a point which
blows up at the point would attain its minimum at an interior point).

The corresponding counterexample with a disconnected `X` (`ℂP¹ ⊕ ℂ`, the pole in `ℂ`) is why
`ConnectedSpace X` appears in the statement.
-/

open Filter Set
open scoped Topology Manifold

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.Drive

/-! ## Two elementary inputs, proved here to avoid the extra hypotheses
(`SecondCountableTopology`) of their relatives `Work.Modulus.exists_ne_of_chartedSpace` and
`Work.Modulus.growth_of_unitGreen`. -/

section Elementary

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A complex one-manifold has at least two points: the preferred chart at `z₀` maps a
neighbourhood of `z₀` homeomorphically onto a nonempty *open* subset of `ℂ`, which contains a ball
around `(chartAt ℂ z₀) z₀` and hence a point different from `(chartAt ℂ z₀) z₀`. -/
theorem exists_ne_of_chartedSpace' (z₀ : X) : ∃ x : X, x ≠ z₀ := by
  set c := chartAt ℂ z₀ with hc'
  have hmem : c z₀ ∈ c.target := c.map_source (mem_chart_source ℂ z₀)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp c.open_target (c z₀) hmem
  set w : ℂ := c z₀ + ((ε / 2 : ℝ) : ℂ) with hw
  have hwmem : w ∈ Metric.ball (c z₀) ε := by
    rw [Metric.mem_ball, hw, dist_eq_norm]
    have h1 : c z₀ + ((ε / 2 : ℝ) : ℂ) - c z₀ = ((ε / 2 : ℝ) : ℂ) := by ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  refine ⟨c.symm w, fun h => ?_⟩
  have h2 : c (c.symm w) = w := c.right_inv (hball hwmem)
  rw [h] at h2
  have h4 : c z₀ = c z₀ + ((ε / 2 : ℝ) : ℂ) := h2.trans hw
  have h5 : c z₀ + ((ε / 2 : ℝ) : ℂ) = c z₀ + 0 := by rw [add_zero]; exact h4.symm
  have h3 : ((ε / 2 : ℝ) : ℂ) = 0 := add_left_cancel h5
  have h6 : ε / 2 = 0 := Complex.ofReal_injective h3
  linarith

/-- Growth at a pole from the (coefficient one) logarithmic bound: if
`|E x + log ‖chart_z₀ x - chart_z₀ z₀‖| ≤ C` on a neighbourhood `V` of `z₀`, then `E → +∞` at
`z₀` off the pole. -/
theorem growth_of_logPole {z₀ : X} {E : X → ℝ} {C : ℝ} {V : Set X} (hV : V ∈ 𝓝 z₀)
    (hbnd : ∀ x ∈ V, x ≠ z₀ →
      |E x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C) :
    ∀ A : ℝ, ∃ W : Set X, W ∈ 𝓝 z₀ ∧ ∀ x ∈ W, x ≠ z₀ → A < E x := by
  intro A
  set e := chartAt ℂ z₀ with he
  have hzsrc : z₀ ∈ e.source := mem_chart_source ℂ z₀
  have htend : Tendsto (fun x => ‖e x - e z₀‖) (𝓝 z₀) (𝓝 0) := by
    have h1 : Tendsto (fun x => e x) (𝓝 z₀) (𝓝 (e z₀)) :=
      e.continuousOn.continuousAt (e.open_source.mem_nhds hzsrc)
    have h2 : Tendsto (fun _ : X => e z₀) (𝓝 z₀) (𝓝 (e z₀)) := tendsto_const_nhds
    simpa using (h1.sub h2).norm
  have hev : {x | ‖e x - e z₀‖ < Real.exp (-(A + C))} ∈ 𝓝 z₀ :=
    htend.eventually (isOpen_Iio.mem_nhds (Real.exp_pos _))
  refine ⟨{x | ‖e x - e z₀‖ < Real.exp (-(A + C))} ∩ e.source ∩ V, ?_, ?_⟩
  · exact inter_mem (inter_mem hev (e.open_source.mem_nhds hzsrc)) hV
  · intro x hx hxne
    obtain ⟨⟨hx1, hx2⟩, hxV⟩ := hx
    have hne : e x ≠ e z₀ := fun h => hxne (e.injOn hx2 hzsrc h)
    have hr0 : 0 < ‖e x - e z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hlog : Real.log ‖e x - e z₀‖ < -(A + C) := by
      have h := Real.log_lt_log hr0 hx1
      rwa [Real.log_exp] at h
    have hb := (abs_le.mp (hbnd x hxV hxne)).1
    linarith

end Elementary

/-- **A Green function with pole on the whole (compact) surface does not exist.**  If `X` is a
connected complex one-manifold and `G` is a Green function of `X` itself with pole `a`
(`Work.SimplyConnected.ABS.IsGreenOn` on `Set.univ`), then `X` is not compact.

The argument is the maximum principle: `G > 0` and harmonic off `a` and `G → +∞` at `a`
(`growth_of_logPole`).  If `X` were compact, `G` would attain its minimum on the compact set
`X ∖ V'`, where `V'` is a neighbourhood of `a` on which `G` is large; that minimum is in fact a
*global* minimum of `G` on `X ∖ {a}`.  The local strong minimum principle
(`Submission.SubharmonicOnXAt.eqOn_of_le` applied to `-G`) makes the level set
`S = {x ≠ a | G x = G y}` open; it is closed because `G` is continuous off `a` and the pole growth
keeps `S` away from `a`.  A nonempty proper clopen subset of the connected space `X` is impossible.
-/
theorem not_compactSpace_of_isGreenOn_univ {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a : X} {G : X → ℝ} (hG : Work.SimplyConnected.ABS.IsGreenOn (Set.univ : Set X) a G) :
    ¬ CompactSpace X := by
  intro hc
  haveI : CompactSpace X := hc
  obtain ⟨hpos, hharm, -, hpole⟩ := hG
  obtain ⟨C, V, hV, hbnd⟩ := hpole
  have hgrowth : ∀ A : ℝ, ∃ W : Set X, W ∈ 𝓝 a ∧ ∀ x ∈ W, x ≠ a → A < G x :=
    growth_of_logPole hV (fun x hxV hxne => hbnd x hxV (mem_univ x) hxne)
  -- a point different from the pole
  obtain ⟨p, hpne⟩ := exists_ne_of_chartedSpace' (X := X) a
  -- a neighbourhood of the pole on which `G > G p + 1`
  obtain ⟨W, hWn, hWgrow⟩ := hgrowth (G p + 1)
  obtain ⟨V', hV'sub, hV'open, hV'a⟩ := mem_nhds_iff.mp hWn
  have hpV' : p ∉ V' := by
    intro hp
    have h := hWgrow p (hV'sub hp) hpne
    linarith
  have hFclosed : IsClosed ((univ : Set X) \ V') := by
    have h : IsClosed (V'ᶜ) := isClosed_compl_iff.mpr hV'open
    simpa [Set.compl_eq_univ_sdiff] using h
  have hFne : ((univ : Set X) \ V').Nonempty := ⟨p, mem_univ p, hpV'⟩
  have hFcont : ContinuousOn G ((univ : Set X) \ V') := by
    intro y hy
    have hyne : y ≠ a := fun h => hy.2 (h ▸ hV'a)
    exact ((hharm y ⟨mem_univ y, by simpa using hyne⟩).continuousAt).continuousWithinAt
  -- `G` attains its minimum on the compact set `X ∖ V'`
  obtain ⟨y, hyF, hymin⟩ := hFclosed.isCompact.exists_isMinOn hFne hFcont
  have hyne : y ≠ a := fun h => hyF.2 (h ▸ hV'a)
  have hmin : ∀ x : X, x ≠ a → G y ≤ G x := by
    intro x hxne
    by_cases hxV : x ∈ V'
    · have hg : G p + 1 < G x := hWgrow x (hV'sub hxV) hxne
      have hp : G y ≤ G p := hymin ⟨mem_univ p, hpV'⟩
      linarith
    · exact hymin ⟨mem_univ x, hxV⟩
  have hmem_punct : ∀ x : X, x ≠ a → ((univ : Set X) \ {a}) ∈ 𝓝 x := by
    intro x hx
    have h : ({a}ᶜ : Set X) ∈ 𝓝 x :=
      (isOpen_compl_singleton (x := a)).mem_nhds (by simpa using hx)
    simpa [Set.compl_eq_univ_sdiff] using h
  -- the set where the minimum is attained, off the pole
  set S : Set X := {x : X | x ≠ a ∧ G x = G y} with hSdef
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro x hxS
    rw [hSdef] at hxS
    obtain ⟨hxne, hxeq⟩ := hxS
    have hsubx : Submission.SubharmonicOnXAt (fun w : X => -G w) x :=
      ((hharm x ⟨mem_univ x, by simpa using hxne⟩).neg).subharmonic
    have hle' : ∀ w ∈ ((univ : Set X) \ {a}), -G w ≤ -G x := by
      intro w hw
      have hwne : w ≠ a := by simpa using hw.2
      have hxw : G x ≤ G w := by rw [hxeq]; exact hmin w hwne
      linarith
    obtain ⟨Wx, hWxn, hWxeq⟩ :=
      Submission.SubharmonicOnXAt.eqOn_of_le hsubx (hmem_punct x hxne) hle'
    have hWx' : Wx ∩ ((univ : Set X) \ {a}) ∈ 𝓝 x :=
      inter_mem hWxn (hmem_punct x hxne)
    refine mem_of_superset hWx' ?_
    rintro w ⟨hwW, hwne'⟩
    have hwne : w ≠ a := by simpa using hwne'.2
    have h1 := hWxeq w hwW
    rw [hSdef]
    exact ⟨hwne, by linarith⟩
  have hScomplopen : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    rintro x hxS
    by_cases hx0 : x = a
    · -- the pole growth keeps `S` away from `a`
      subst hx0
      refine mem_of_superset (hV'open.mem_nhds hV'a) ?_
      rintro w hw hwS
      rw [hSdef] at hwS
      obtain ⟨hwne, hweq⟩ := hwS
      have hg : G p + 1 < G w := hWgrow w (hV'sub hw) hwne
      have hp : G y ≤ G p := hymin ⟨mem_univ p, hpV'⟩
      linarith
    · -- off the pole, `Sᶜ` is the open set where `G ≠ G y`
      have hne : G x ≠ G y := fun h => hxS (by rw [hSdef]; exact ⟨hx0, h⟩)
      have hcont : ContinuousAt G x := (hharm x ⟨mem_univ x, by simpa using hx0⟩).continuousAt
      have hmem : G ⁻¹' ({G y}ᶜ : Set ℝ) ∈ 𝓝 x :=
        hcont.preimage_mem_nhds ((isOpen_compl_singleton (x := G y)).mem_nhds hne)
      refine mem_of_superset hmem ?_
      rintro w hw hwS
      rw [hSdef] at hwS
      exact hw hwS.2
  -- `S` is a nonempty proper clopen subset of the connected space `X`
  have hScl : IsClopen S := ⟨isOpen_compl_iff.mp hScomplopen, hSopen⟩
  have hnon : (univ ∩ S).Nonempty := by
    refine ⟨y, mem_univ y, ?_⟩
    rw [hSdef]
    exact ⟨hyne, rfl⟩
  have hsub' :=
    (connectedSpace_iff_univ.mp ‹ConnectedSpace X›).isPreconnected.subset_isClopen hScl hnon
  have hz : a ∈ S := hsub' (mem_univ a)
  rw [hSdef] at hz
  exact hz.1 rfl

/-- **Monotonicity of the Green function of a region in the region.**  On a *connected* Riemann
surface, if `Ω ⊆ Ω'` and `G`, `G'` are the Green functions of these regions with the *same* pole
`a ∈ Ω`, then `G ≤ G'` on `Ω` off the pole.  (This is the standard comparison: `G - G'` is
subharmonic on `Ω \ {a}` with the logarithmic singularities cancelling, every superlevel set of `G`
is relatively compact in `Ω`, so `G → 0` at the frontier of `Ω` and the maximum principle applied
to `G - G'` on a relatively compact exhaustion of `Ω` gives `G - G' ≤ 0`.)

This is the monotonicity used by the exhaustion arguments for the existence of a harmonic function
with a prescribed logarithmic pole (`Work.Drive.greenExhaustion_locallyBounded`,
`Work.Drive.exists_unitPole_boundedAbove`, `Work.Drive.unitPoleBoundedAbove`,
`Work.Drive.unitPoleBoundedAbove_chartBall`).

REVISION NOTE.  `[ConnectedSpace X]` is *not* redundant: without it the statement is refutable
(take `X = ℂP¹ ⊕ ℂ`, `Ω = Ω' = ℂP¹ ∪ 𝔻`, pole `a = 0 ∈ 𝔻`, `G = 2` resp. `G' = 1` on the compact
`ℂP¹` factor; `IsGreenOn` constrains nothing on a compact clopen component not containing the pole,
since its relative-compactness clause is then vacuous).  With connectedness the argument above goes
through. -/
theorem isGreenOn_le_of_subset {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω Ω' : Set X} (hΩo : IsOpen Ω) {a : X} (ha : a ∈ Ω) (hsub : Ω ⊆ Ω')
    {G G' : X → ℝ} (hG : Work.SimplyConnected.ABS.IsGreenOn Ω a G)
    (hG' : Work.SimplyConnected.ABS.IsGreenOn Ω' a G')
    {x : X} (hx : x ∈ Ω) (hxa : x ≠ a) : G x ≤ G' x := by
  classical
  by_contra hcon
  push Not at hcon
  have hGcopy : Work.SimplyConnected.ABS.IsGreenOn Ω a G := hG
  obtain ⟨hGpos, hGharm, hGdec, hGpole⟩ := hG
  obtain ⟨hG'pos, hG'harm, hG'dec, hG'pole⟩ := hG'
  set h : X → ℝ := G - G' with hhdef
  have hxpos : 0 < h x := by
    have h1 : h x = G x - G' x := rfl
    rw [h1]; linarith
  -- (1) `h` is harmonic off the pole
  have hharm : Submission.HarmonicOnX h (Ω \ {a}) := by
    have h2 : Submission.HarmonicOnX G' (Ω \ {a}) :=
      hG'harm.mono (fun y hy => ⟨hsub hy.1, hy.2⟩)
    have h3 : Submission.HarmonicOnX (G - G') (Ω \ {a}) := hGharm.sub h2
    simpa only [hhdef] using h3
  -- (2) `h` is bounded near the pole (the two logarithmic singularities cancel)
  obtain ⟨C₁, V₁, hV₁, hb₁⟩ := hGpole
  obtain ⟨C₂, V₂, hV₂, hb₂⟩ := hG'pole
  set L : X → ℝ := fun y => Real.log ‖(chartAt ℂ a) y - (chartAt ℂ a) a‖ with hLdef
  have hWmem : V₁ ∩ V₂ ∩ Ω ∈ 𝓝 a :=
    Filter.inter_mem (Filter.inter_mem hV₁ hV₂) (hΩo.mem_nhds ha)
  have hbound : ∃ M : ℝ, ∀ y ∈ V₁ ∩ V₂ ∩ Ω, y ≠ a → |h y| ≤ M := by
    refine ⟨C₁ + C₂, ?_⟩
    intro y hy hya
    obtain ⟨⟨hy₁, hy₂⟩, hyΩ⟩ := hy
    have hb₁' : |G y + L y| ≤ C₁ := hb₁ y hy₁ hyΩ hya
    have hb₂' : |G' y + L y| ≤ C₂ := hb₂ y hy₂ (hsub hyΩ) hya
    have hEq : h y = (G y + L y) - (G' y + L y) := by
      simp only [hhdef, Pi.sub_apply]
      ring
    calc |h y| = |(G y + L y) - (G' y + L y)| := by rw [hEq]
      _ ≤ |G y + L y| + |G' y + L y| := by
          rw [abs_sub_le_iff]
          constructor <;>
            linarith [le_abs_self (G y + L y), neg_le_abs (G y + L y),
              le_abs_self (G' y + L y), neg_le_abs (G' y + L y)]
      _ ≤ C₁ + C₂ := by linarith
  have hharmW : Submission.HarmonicOnX h ((V₁ ∩ V₂ ∩ Ω) \ {a}) :=
    hharm.mono (fun y hy => ⟨hy.1.2, by simpa using hy.2⟩)
  -- the harmonic extension of `h` across the pole
  obtain ⟨A, hA⟩ :=
    Work.Drive.exists_update_harmonicOnXAt_of_bounded_punctured (q := a) hWmem hharmW hbound
  set hhat : X → ℝ := Function.update h a A with hhhatdef
  have hharm_a : Submission.HarmonicOnXAt hhat a := by
    rw [hhhatdef]; exact hA
  have hoff : ∀ y : X, y ≠ a → hhat y = h y := by
    intro y hy
    rw [hhhatdef]
    exact Function.update_of_ne hy A h
  have hcont_Ω : ∀ y ∈ Ω, ContinuousAt hhat y := by
    intro y hy
    by_cases hya : y = a
    · subst hya; exact hharm_a.continuousAt
    · have hev : hhat =ᶠ[𝓝 y] h := by
        have hnb : {a}ᶜ ∈ 𝓝 y := isOpen_compl_singleton.mem_nhds (by simpa using hya)
        filter_upwards [hnb] with z hz
        exact hoff z (by simpa using hz)
      exact ((hharm y ⟨hy, hya⟩).continuousAt).congr hev.symm
  -- (3) the level set
  set ε : ℝ := h x / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hxε : ε < h x := by rw [hεdef]; linarith
  set U : Set X := {y : X | y ∈ Ω ∧ ε < hhat y} with hUdef
  have hxU : x ∈ U := ⟨hx, by rw [hoff x hxa]; exact hxε⟩
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨hyΩ, hyε⟩ := hy
    have h1 : {z : X | ε < hhat z} ∈ 𝓝 y :=
      (hcont_Ω y hyΩ).preimage_mem_nhds (isOpen_Ioi.mem_nhds hyε)
    exact mem_of_superset (Filter.inter_mem (hΩo.mem_nhds hyΩ) h1)
      (fun z hz => ⟨hz.1, hz.2⟩)
  obtain ⟨K, hKcomp, hKsub, hKdec⟩ := hGdec ε hεpos
  have hKins : IsCompact (K ∪ {a}) := hKcomp.union isCompact_singleton
  have hUsub : U ⊆ K ∪ {a} := by
    intro y hy
    by_cases hya : y = a
    · exact Or.inr hya
    · refine Or.inl ?_
      by_contra hyK
      have hGy : ε < G y := by
        have h1 : ε < h y := by rw [← hoff y hya]; exact hy.2
        have h2 : 0 < G' y := hG'pos y (hsub hy.1) hya
        have h3 : h y = G y - G' y := rfl
        rw [h3] at h1
        linarith
      exact absurd (hKdec y hy.1 hyK) (not_lt.mpr (le_of_lt hGy))
  have hclK : closure U ⊆ K ∪ {a} := closure_minimal hUsub hKins.isClosed
  have hclΩ : closure U ⊆ Ω := by
    intro y hy
    rcases hclK hy with hh | hh
    · exact hKsub hh
    · rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact ha
  have hcomp : IsCompact (closure U) := hKins.of_isClosed_subset isClosed_closure hclK
  -- the frontier is nonempty (otherwise `Ω = X` would be compact)
  have hUne : (frontier U).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hclU : closure U = U := by
      rw [closure_eq_interior_union_frontier, hUopen.interior_eq, hempty, Set.union_empty]
    have hUclosed : IsClosed U := isClosed_of_closure_subset (le_of_eq hclU)
    have hclopen : IsClopen U := ⟨hUclosed, hUopen⟩
    rcases isClopen_iff.mp hclopen with hUempty | hUuniv
    · rw [hUempty] at hxU
      exact hxU
    · have hΩuniv : Ω = univ := by
        refine Set.Subset.antisymm (Set.subset_univ Ω) ?_
        intro y hy
        have hyU : y ∈ U := hUuniv.symm ▸ hy
        exact hyU.1
      have hXcomp : CompactSpace X := by
        have huniv : (univ : Set X) ⊆ K ∪ {a} := by
          intro y hy
          exact hUsub (hUuniv.symm ▸ hy)
        exact isCompact_univ_iff.mp (hKins.of_isClosed_subset isClosed_univ huniv)
      exact not_compactSpace_of_isGreenOn_univ (hΩuniv ▸ hGcopy) hXcomp
  -- (4) the boundary values of `hhat` at the frontier are at most `ε`
  have hfrontier_le : ∀ ξ ∈ frontier U, hhat ξ ≤ ε := by
    intro ξ hξ
    by_contra hgt
    push Not at hgt
    have hξΩ : ξ ∈ Ω := hclΩ hξ.1
    have hξU : ξ ∈ U := ⟨hξΩ, hgt⟩
    exact hξ.2 (by rw [hUopen.interior_eq]; exact hξU)
  have hlim : ∀ ξ ∈ frontier U, ∀ δ : ℝ, 0 < δ → ∀ᶠ z in 𝓝[U] ξ, hhat z ≤ ε + δ := by
    intro ξ hξ δ hδ
    have hξε : hhat ξ ≤ ε := hfrontier_le ξ hξ
    have hξΩ : ξ ∈ Ω := hclΩ hξ.1
    have hev : ∀ᶠ z in 𝓝 ξ, hhat z < hhat ξ + δ := by
      have hmem : {y : X | hhat y < hhat ξ + δ} ∈ 𝓝 ξ :=
        (hcont_Ω ξ hξΩ).preimage_mem_nhds (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr (by linarith)))
      filter_upwards [hmem] with z hz
      exact hz
    have hev' : ∀ᶠ z in 𝓝[U] ξ, hhat z < hhat ξ + δ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hev
    exact hev'.mono (fun z hz => by linarith)
  -- (5) `hhat` is subharmonic on `U` and the maximum principle applies
  have hsubU : Submission.SubharmonicOnX hhat U := by
    refine ⟨?_, ?_⟩
    · intro y hy
      exact (hcont_Ω y hy.1).continuousWithinAt
    · intro y hy
      by_cases hya : y = a
      · subst hya
        exact hharm_a.subharmonic
      · have hev : hhat =ᶠ[𝓝 y] h := by
          have hnb : {a}ᶜ ∈ 𝓝 y := isOpen_compl_singleton.mem_nhds (by simpa using hya)
          filter_upwards [hnb] with z hz
          exact hoff z (by simpa using hz)
        exact ((hharm y ⟨hy.1, hya⟩).subharmonic).congr hev.symm
  have hle := Submission.SubharmonicOnX.le_of_frontier_limsup hUopen hsubU hcomp hUne (a := ε) hlim
  have hxle : hhat x ≤ ε := hle x hxU
  rw [hoff x hxa] at hxle
  linarith

end Work.Drive
