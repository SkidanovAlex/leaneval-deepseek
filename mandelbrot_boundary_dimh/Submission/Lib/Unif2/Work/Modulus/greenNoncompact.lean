import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Defs
import Submission.Lib.Unif2.Work.Modulus.growth_of_unitGreen

/-!
# The Green function of a compact surface does not exist

If `X` is a connected complex one-manifold (a Riemann surface) and `E : X → ℝ` is a Green function
with pole `z₀` in the sense of `Work.UnitGreen.IsUnitGreenFunctionAt` — positive and harmonic off
`z₀`, with a logarithmic pole of coefficient one there, and with relatively compact superlevel sets — then `X`
is **not** compact.

The mathematical content is the maximum principle: on a compact surface a positive harmonic
function off a point cannot blow up at the point, because it would attain its minimum at an
interior point, where it must be locally constant.

Concretely, we choose a level `A` so large that `E > A` on a neighbourhood `V` of the pole
(`hE`'s growth condition) and so large that some point `p ≠ z₀` satisfies `E p < A`; then `E`
attains its minimum `E y` on the compact set `X ∖ V`, and every point off `z₀` lies either in
`X ∖ V` or in `V`, where `E > A > E p ≥ E y`.  So `y` is a *global* minimum of `E` on `X ∖ {z₀}`.
The local strong minimum principle (`Submission.SubharmonicOnXAt.eqOn_of_le` applied to `-E`)
then shows that `S = {x ≠ z₀ | E x = E y}` is *open*; it is closed because `E` is continuous off
`z₀` and the pole growth keeps the closure of `S` away from `z₀`.  Since `S` is a nonempty proper
clopen subset of the connected space `X`, this is a contradiction.

The one point that has to be extracted from the charted-space structure is that `X` has at least
two points (`exists_ne_of_chartedSpace`): the preferred chart at a point carries a neighbourhood
of that point homeomorphically onto a nonempty *open* subset of `ℂ`, hence onto something with
more than one point.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set
open scoped Topology

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A complex one-manifold has at least two points: the preferred chart at `z₀` maps a
neighbourhood of `z₀` homeomorphically onto a nonempty *open* subset of `ℂ`, which contains a ball
around `(chartAt ℂ z₀) z₀` and hence a point different from `(chartAt ℂ z₀) z₀`. -/
theorem exists_ne_of_chartedSpace (z₀ : X) : ∃ x : X, x ≠ z₀ := by
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

theorem greenNoncompact
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    ¬ CompactSpace X := by
  intro hc
  haveI : CompactSpace X := hc
  obtain ⟨⟨hpos, hharm, hcomp⟩, ⟨C₀, V₀, hV₀, hbnd₀⟩⟩ := hE
  have hgrowth : ∀ A : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ → A < E x :=
    growth_of_unitGreen hV₀ hbnd₀
  -- a point different from the pole
  obtain ⟨p, hpne⟩ := exists_ne_of_chartedSpace (X := X) z₀
  -- choose the level set of the pole growth carrying a point of `X ∖ {z₀}`
  obtain ⟨V, hVn, hVgrow⟩ := hgrowth (E p + 1)
  obtain ⟨V', hV'sub, hV'open, hV'z⟩ := mem_nhds_iff.mp hVn
  have hpV' : p ∉ V' := by
    intro hp
    have h := hVgrow p (hV'sub hp) hpne
    linarith
  have hFclosed : IsClosed (univ \ V') := by
    have h : IsClosed (V'ᶜ) := isClosed_compl_iff.mpr hV'open
    simpa [Set.compl_eq_univ_sdiff] using h
  -- `E` attains its minimum on the compact set `X ∖ V'`
  obtain ⟨y, hyF, hymin⟩ :=
    hFclosed.isCompact.exists_isMinOn ⟨p, mem_univ p, hpV'⟩ (fun x hx => by
      have hxne : x ≠ z₀ := fun h => hx.2 (h ▸ hV'z)
      exact ((hharm x ⟨mem_univ x, by simpa using hxne⟩).continuousAt).continuousWithinAt)
  have hyne : y ≠ z₀ := fun h => hyF.2 (h ▸ hV'z)
  -- `E y` is the global minimum of `E` on `X ∖ {z₀}`
  have hmin : ∀ x : X, x ≠ z₀ → E y ≤ E x := by
    intro x hxne
    by_cases hxV : x ∈ V'
    · have hg : E p + 1 < E x := hVgrow x (hV'sub hxV) hxne
      have hp : E y ≤ E p := hymin ⟨mem_univ p, hpV'⟩
      linarith
    · exact hymin ⟨mem_univ x, hxV⟩
  have hmem_punct : ∀ x : X, x ≠ z₀ → (univ \ {z₀} : Set X) ∈ 𝓝 x := by
    intro x hx
    have h : ({z₀}ᶜ : Set X) ∈ 𝓝 x :=
      (isOpen_compl_singleton (x := z₀)).mem_nhds (by simpa using hx)
    simpa [Set.compl_eq_univ_sdiff] using h
  -- the set where the minimum is attained, off the pole
  set S : Set X := {x : X | x ≠ z₀ ∧ E x = E y} with hSdef
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro x hxS
    rw [hSdef] at hxS
    obtain ⟨hxne, hxeq⟩ := hxS
    have hsubx : Submission.SubharmonicOnXAt (fun w : X => -E w) x :=
      ((hharm x ⟨mem_univ x, by simpa using hxne⟩).neg).subharmonic
    have hle' : ∀ w ∈ (univ \ {z₀} : Set X), -E w ≤ -E x := by
      intro w hw
      have hwne : w ≠ z₀ := by simpa using hw.2
      have hxw : E x ≤ E w := by rw [hxeq]; exact hmin w hwne
      linarith
    -- the local strong minimum principle
    obtain ⟨Wx, hWxn, hWxeq⟩ :=
      Submission.SubharmonicOnXAt.eqOn_of_le hsubx (hmem_punct x hxne) hle'
    have hWx' : Wx ∩ (univ \ {z₀}) ∈ 𝓝 x := inter_mem hWxn (hmem_punct x hxne)
    refine mem_of_superset hWx' ?_
    rintro w ⟨hwW, hwne'⟩
    have hwne : w ≠ z₀ := by simpa using hwne'.2
    have h1 := hWxeq w hwW
    rw [hSdef]
    exact ⟨hwne, by linarith⟩
  have hScomplopen : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    rintro x hxS
    by_cases hx0 : x = z₀
    · -- the pole growth keeps `S` away from `z₀`
      subst hx0
      refine mem_of_superset hVn ?_
      rintro w hw hwS
      rw [hSdef] at hwS
      obtain ⟨hwne, hweq⟩ := hwS
      have hg : E p + 1 < E w := hVgrow w hw hwne
      have hp : E y ≤ E p := hymin ⟨mem_univ p, hpV'⟩
      linarith
    · -- off the pole, `Sᶜ` is the open set where `E ≠ E y`
      have hne : E x ≠ E y := fun h => hxS (by rw [hSdef]; exact ⟨hx0, h⟩)
      have hcont : ContinuousAt E x := (hharm x ⟨mem_univ x, by simpa using hx0⟩).continuousAt
      have hmem : E ⁻¹' ({E y}ᶜ : Set ℝ) ∈ 𝓝 x :=
        hcont.preimage_mem_nhds ((isOpen_compl_singleton (x := E y)).mem_nhds hne)
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
  have hsub :=
    (connectedSpace_iff_univ.mp ‹ConnectedSpace X›).isPreconnected.subset_isClopen hScl hnon
  have hz : z₀ ∈ S := hsub (mem_univ z₀)
  rw [hSdef] at hz
  exact hz.1 rfl

end Work.Modulus
