import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.basin_basic
import Submission.Work.Parab.basinCoord.exists_basin_coordinate
import Submission.Work.Parab.basinEnters.zero_not_mem_basin

/-!
# The component of the basin through an invariant set is invariant and avoids `0`

Let `g` be a parabolic germ on the open set `D` (`g 0 = 0`, `g'(0) = 1`, `g''(0) = 2`) and let
`V` be a *connected* subset of the uniform parabolic basin `B = ParabolicBasin g D` which is
forward invariant (`g '' V ⊆ V`) and avoids `0`, with `x ∈ V`.  Then the connected component
`C = connectedComponentIn B x` of the basin through `x` is forward invariant for `g`, and no
forward iterate of a point of `C` is `0`.

Two remarks explain why the hypotheses are exactly what they are.

* The basin `B` itself is **not** forward invariant in general: `D` may be disconnected and `g`
  locally constant `= 0` on a component (the two-disc germ of
  `Submission/Work/Parab/basinEnters/counterexample.lean`), so basin points exist whose orbit hits
  `0` at once.  The hypothesis `g '' V ⊆ V` excludes this degeneracy on `V` (if `g` is locally
  constant at `z ∈ V` with value `c`, then `c ∈ V`), and the connectedness of `C` propagates the
  exclusion to all of `C`: a point of `C` at which `g` is *locally* constant is a point at which
  `g` is constant on the whole connected open set `C` (identity theorem), so its value is
  `g x ∈ V`.
* The hypothesis `0 ∉ V` is in fact **redundant**: `V ⊆ B` and `0 ∉ B`
  (`Work.Parab.basinEnters.zero_not_mem_parabolicBasin`) already give it, and the proof below does
  not use it.
* The "avoid `0`" conclusion is simply `0 ∉ B` applied to the invariant component: every iterate of
  a point of `C` stays in `C ⊆ B`.
-/

namespace Work.Horn.HB

open MandelDim Set Metric Filter Topology

/-- The uniform parabolic basin is open: the defining neighbourhood can be reused at all of its
points. -/
lemma parabolicBasin_isOpen (g : ℂ → ℂ) (D : Set ℂ) :
    IsOpen (MandelDim.ParabolicBasin g D) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨U, hU, hUm, hUc⟩ := hz
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  refine Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hε)) fun u hu => ?_
  exact ⟨U, Filter.mem_of_superset (isOpen_ball.mem_nhds hu) hεU, hUm, hUc⟩

/-- A point of the uniform parabolic basin lies in the domain `D`, by the `n = 0` instance of the
defining property. -/
lemma parabolicBasin_subset_domain {g : ℂ → ℂ} {D : Set ℂ} {z : ℂ}
    (hz : z ∈ MandelDim.ParabolicBasin g D) : z ∈ D := by
  obtain ⟨U, hU, hUm, -⟩ := hz
  simpa using hUm 0 (mem_of_mem_nhds hU)

set_option linter.unusedVariables false in
theorem mapsTo_componentIn_and_avoids_zero {g : ℂ → ℂ} {D V : Set ℂ} {x : ℂ}
    (hg : MandelDim.IsParabolicGerm g D) (hVsub : V ⊆ MandelDim.ParabolicBasin g D)
    (hVconn : IsConnected V) (hVmap : Set.MapsTo g V V) (h0V : (0 : ℂ) ∉ V) (hxV : x ∈ V) :
    Set.MapsTo g (connectedComponentIn (MandelDim.ParabolicBasin g D) x)
        (connectedComponentIn (MandelDim.ParabolicBasin g D) x) ∧
      (∀ z ∈ connectedComponentIn (MandelDim.ParabolicBasin g D) x, ∀ n : ℕ, (g^[n]) z ≠ 0) := by
  have hDopen : IsOpen D := hg.1
  have hgdiff : DifferentiableOn ℂ g D := hg.2.2.1
  have hBopen : IsOpen (MandelDim.ParabolicBasin g D) := parabolicBasin_isOpen g D
  have hxB : x ∈ MandelDim.ParabolicBasin g D := hVsub hxV
  have hxC : x ∈ connectedComponentIn (MandelDim.ParabolicBasin g D) x :=
    mem_connectedComponentIn hxB
  have hCB : connectedComponentIn (MandelDim.ParabolicBasin g D) x ⊆
      MandelDim.ParabolicBasin g D := connectedComponentIn_subset _ _
  have hCD : connectedComponentIn (MandelDim.ParabolicBasin g D) x ⊆ D :=
    fun z hz => parabolicBasin_subset_domain (hCB hz)
  have hCpre : IsPreconnected (connectedComponentIn (MandelDim.ParabolicBasin g D) x) :=
    isPreconnected_connectedComponentIn
  have hCopen : IsOpen (connectedComponentIn (MandelDim.ParabolicBasin g D) x) :=
    hBopen.connectedComponentIn
  -- `V` sits in the component of `x`
  have hVC : V ⊆ connectedComponentIn (MandelDim.ParabolicBasin g D) x :=
    IsPreconnected.subset_connectedComponentIn hVconn.isPreconnected hxV hVsub
  have hgxC : g x ∈ connectedComponentIn (MandelDim.ParabolicBasin g D) x :=
    hVC (hVmap hxV)
  -- **the key point**: the image of every point of the component is again in the basin
  have key : ∀ z ∈ connectedComponentIn (MandelDim.ParabolicBasin g D) x,
      g z ∈ MandelDim.ParabolicBasin g D := by
    intro z hz
    have hzB : z ∈ MandelDim.ParabolicBasin g D := hCB hz
    have hzD : z ∈ D := parabolicBasin_subset_domain hzB
    have hzan : AnalyticAt ℂ g z := hgdiff.analyticAt (hDopen.mem_nhds hzD)
    by_cases hnc : ∀ᶠ w in 𝓝 z, g w = g z
    · -- `g` is locally constant at `z`, hence constant on the connected set `C`, hence
      -- `g z = g x ∈ V`
      have hCan : AnalyticOn ℂ g (connectedComponentIn (MandelDim.ParabolicBasin g D) x) :=
        (hgdiff.mono hCD).analyticOn hCopen
      have hCanNhd : AnalyticOnNhd ℂ g (connectedComponentIn (MandelDim.ParabolicBasin g D) x) :=
        (hCopen.analyticOn_iff_analyticOnNhd).mp hCan
      have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hCanNhd
        (analyticOnNhd_const (v := g z)) hCpre hz hnc
      have hgxz : g x = g z := heq hxC
      rw [← hgxz]
      exact hVsub (hVmap hxV)
    · -- `g` is not locally constant at `z`: forward invariance of the basin at `z`
      exact Work.Parab.basin_forward hzan hnc hzB
  -- `C ∪ g '' C` is a preconnected subset of the basin containing `x`, hence lies in `C`
  have himgB : g '' connectedComponentIn (MandelDim.ParabolicBasin g D) x ⊆
      MandelDim.ParabolicBasin g D := by
    rintro y ⟨z, hz, rfl⟩
    exact key z hz
  have hcont : ContinuousOn g (connectedComponentIn (MandelDim.ParabolicBasin g D) x) :=
    hgdiff.continuousOn.mono hCD
  have himgpre : IsPreconnected (g '' connectedComponentIn (MandelDim.ParabolicBasin g D) x) :=
    hCpre.image g hcont
  have hunionpre : IsPreconnected (connectedComponentIn (MandelDim.ParabolicBasin g D) x ∪
      g '' connectedComponentIn (MandelDim.ParabolicBasin g D) x) :=
    IsPreconnected.union (g x) hgxC ⟨x, hxC, rfl⟩ hCpre himgpre
  have hunion_sub : connectedComponentIn (MandelDim.ParabolicBasin g D) x ∪
      g '' connectedComponentIn (MandelDim.ParabolicBasin g D) x ⊆
      connectedComponentIn (MandelDim.ParabolicBasin g D) x :=
    IsPreconnected.subset_connectedComponentIn hunionpre (Or.inl hxC) (by
      rintro w (hw | hw)
      · exact hCB hw
      · exact himgB hw)
  have hmapC : Set.MapsTo g (connectedComponentIn (MandelDim.ParabolicBasin g D) x)
      (connectedComponentIn (MandelDim.ParabolicBasin g D) x) :=
    fun z hz => hunion_sub (Or.inr ⟨z, hz, rfl⟩)
  refine ⟨hmapC, ?_⟩
  -- every iterate stays in the component, and `0` is not in the basin
  intro z hz n hzero
  have hmem : (g^[n]) z ∈ MandelDim.ParabolicBasin g D :=
    hCB ((hmapC.iterate n) hz)
  exact Work.Parab.basinEnters.zero_not_mem_parabolicBasin hg (hzero ▸ hmem)

end Work.Horn.HB
