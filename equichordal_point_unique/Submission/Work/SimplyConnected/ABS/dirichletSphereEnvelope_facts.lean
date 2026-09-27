import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.globalizedBarrier
import Submission.Work.SimplyConnected.ABS.limEnvelope_le_smul_of_barrier
import Submission.Work.SimplyConnected.ABS.limEnvelope_lt_near_of_localBarrier_ball

/-!
# The Perron envelope of the annulus `Ω \ chartClosedBall`, with data `1` on the inner sphere

This module supplies the lemma `Work.SimplyConnected.ABS.dirichletSphereEnvelope_facts` used by
the Green-function construction of Anghel–Bruin–Stan (arXiv:2008.12189): for a relatively compact
Dirichlet-regular region `Ω` of a Riemann surface `X` and a chart ball `chartBall c a ρ ⊆ Ω`
around `x₀` (`c = chartAt ℂ x₀`, `a = c x₀`), the Perron envelope `u = limEnvelope U f 1` on

  `U = Ω \ chartClosedBall c a s`,   `0 < s < ρ`,

with data `f` satisfying `0 ≤ f ≤ 1`, `f = 1` on the chart sphere `chartSphere c a s` and `f = 0`
on `frontier Ω`, enjoys

* harmonicity on `U`, the bounds `0 ≤ u ≤ 1`,
* the lower bound `chartLogClamp c a ρ ≤ log (ρ/s) · u` on `U`,
* `u → 1` at the inner chart sphere,
* `u → 0` at `frontier Ω`, uniformly on a neighbourhood of the latter.

The proof of the last item is the classical barrier argument: a globalized barrier `β` at each
frontier point (the delegated lemma `globalizedBarrier`) is used as a comparison superharmonic
function via the delegated maximum-principle comparison
`limEnvelope_le_smul_of_barrier`, and compactness of `frontier Ω` produces the uniform
neighbourhood.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

/-! ## The frontier of `Ω \ chartClosedBall c a ρ` -/

section Frontier

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- `frontier (A \ B) ⊆ frontier A ∪ frontier B`. -/
theorem frontier_sdiff_subset' {A B : Set X} : frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  have h := frontier_inter_subset A Bᶜ
  rw [← Set.sdiff_eq, frontier_compl] at h
  intro x hx
  rcases h hx with h' | h'
  · exact Or.inl h'.1
  · exact Or.inr h'.2

/-- The interior of a closed chart ball is the chart ball. -/
theorem interior_chartClosedBall_subset_chartBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ : ℝ} : interior (Submission.chartClosedBall c a ρ) ⊆ Submission.chartBall c a ρ := by
  intro y hy
  have hyD : y ∈ Submission.chartClosedBall c a ρ := interior_subset hy
  refine ⟨hyD.1, ?_⟩
  have hmem : c '' (interior (Submission.chartClosedBall c a ρ)) ∈ 𝓝 (c y) :=
    c.image_mem_nhds hyD.1 (isOpen_interior.mem_nhds hy)
  have hsubimg : c '' (interior (Submission.chartClosedBall c a ρ)) ⊆ Metric.closedBall a ρ := by
    rintro w ⟨z, hz, rfl⟩
    exact (interior_subset hz).2
  have : c y ∈ interior (Metric.closedBall a ρ) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset hmem hsubimg
  rwa [interior_closedBall'] at this

/-- The frontier of a closed chart ball is contained in the chart sphere. -/
theorem frontier_chartClosedBall_subset_chartSphere {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ : ℝ} (hsub : Metric.closedBall a ρ ⊆ c.target) :
    frontier (Submission.chartClosedBall c a ρ) ⊆ Submission.chartSphere c a ρ := by
  intro ζ hζ
  have hclosed : IsClosed (Submission.chartClosedBall c a ρ) :=
    Submission.isClosed_chartClosedBall hsub
  have hζD : ζ ∈ Submission.chartClosedBall c a ρ := hclosed.frontier_subset hζ
  rw [Submission.mem_chartSphere]
  refine ⟨hζD.1, ?_⟩
  by_contra hnot
  have hball : c ζ ∈ Metric.ball a ρ := by
    have h1 : c ζ ∈ Metric.closedBall a ρ := hζD.2
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball]
    by_contra h2
    exact hnot (by rw [Metric.mem_sphere]; exact le_antisymm h1 (not_lt.mp h2))
  have hζB : ζ ∈ Submission.chartBall c a ρ := ⟨hζD.1, hball⟩
  have hint : Submission.chartBall c a ρ ⊆ interior (Submission.chartClosedBall c a ρ) :=
    interior_maximal (Submission.chartBall_subset_chartClosedBall c a ρ)
      (Submission.chartBall_isOpen c a ρ)
  exact hζ.2 (hint hζB)

/-- **Decomposition of the frontier of `Ω \ chartClosedBall`**: it is contained in the union of
`frontier Ω` and the inner chart sphere. -/
theorem frontier_sdiff_chartClosedBall_subset {Ω : Set X} {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ : ℝ} (hsub : Metric.closedBall a ρ ⊆ c.target) :
    frontier (Ω \ Submission.chartClosedBall c a ρ) ⊆ frontier Ω ∪ Submission.chartSphere c a ρ := by
  intro x hx
  rcases frontier_sdiff_subset' hx with h | h
  · exact Or.inl h
  · exact Or.inr (frontier_chartClosedBall_subset_chartSphere hsub h)

/-- The inner chart sphere is contained in the frontier of `Ω \ chartClosedBall`, for `Ω` open
containing the closed chart ball. -/
theorem chartSphere_subset_frontier_sdiff_chartClosedBall {Ω : Set X} (hΩo : IsOpen Ω)
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hDΩ : Submission.chartClosedBall c a ρ ⊆ Ω) :
    Submission.chartSphere c a ρ ⊆ frontier (Ω \ Submission.chartClosedBall c a ρ) := by
  intro ζ hζ
  obtain ⟨hζsrc, hζsph⟩ := Submission.mem_chartSphere.mp hζ
  have hζD : ζ ∈ Submission.chartClosedBall c a ρ :=
    Submission.chartSphere_subset_chartClosedBall c a ρ hζ
  have hζΩ : ζ ∈ Ω := hDΩ hζD
  have hnint : ζ ∉ interior (Submission.chartClosedBall c a ρ) := by
    intro hint
    have h2 : ‖c ζ - a‖ < ρ := by
      have h3 := (Submission.mem_chartBall.mp (interior_chartClosedBall_subset_chartBall hint)).2
      rwa [Metric.mem_ball, dist_eq_norm] at h3
    rw [Metric.mem_sphere, dist_eq_norm] at hζsph
    exact absurd h2 (not_lt.mpr hζsph.ge)
  rw [frontier, Set.mem_sdiff]
  refine ⟨?_, ?_⟩
  · rw [mem_closure_iff]
    intro W hWo hWζ
    have hWo' : IsOpen (W ∩ Ω) := hWo.inter hΩo
    have hζWΩ : ζ ∈ W ∩ Ω := ⟨hWζ, hζΩ⟩
    have hnotsub : ¬ (W ∩ Ω ⊆ Submission.chartClosedBall c a ρ) := by
      intro hss
      exact hnint (interior_maximal hss hWo' hζWΩ)
    obtain ⟨y, hyWΩ, hyD⟩ := Set.not_subset.mp hnotsub
    exact ⟨y, hyWΩ.1, hyWΩ.2, hyD⟩
  · intro hint
    exact (interior_subset hint).2 hζD

/-- The chart sphere of a chart ball whose closed ball lies in the target is compact. -/
theorem isCompact_chartSphere {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hsub : Metric.closedBall a ρ ⊆ c.target) :
    IsCompact (Submission.chartSphere c a ρ) := by
  have heq : Submission.chartSphere c a ρ = c.symm '' Metric.sphere a ρ := by
    ext x
    constructor
    · rintro ⟨hxs, hx⟩
      exact ⟨c x, hx, c.left_inv hxs⟩
    · rintro ⟨w, hw, rfl⟩
      have hwT : w ∈ c.target := hsub (Metric.sphere_subset_closedBall hw)
      refine ⟨c.map_target hwT, ?_⟩
      show c (c.symm w) ∈ Metric.sphere a ρ
      rw [c.right_inv hwT]
      exact hw
  rw [heq]
  exact (isCompact_sphere a ρ).image_of_continuousOn
    (c.continuousOn_symm.mono fun w hw => hsub (Metric.sphere_subset_closedBall hw))

/-- The chart sphere of a chart ball of positive radius is nonempty. -/
theorem chartSphere_nonempty {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall a ρ ⊆ c.target) : (Submission.chartSphere c a ρ).Nonempty := by
  have hmem : a + (ρ : ℂ) ∈ Metric.sphere a ρ := by
    rw [Metric.mem_sphere, dist_eq_norm]
    have h1 : a + (ρ : ℂ) - a = ((ρ : ℝ) : ℂ) := by ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hT : a + (ρ : ℂ) ∈ c.target := hsub (Metric.sphere_subset_closedBall hmem)
  refine ⟨c.symm (a + (ρ : ℂ)), c.map_target hT, ?_⟩
  show c (c.symm (a + (ρ : ℂ))) ∈ Metric.sphere a ρ
  rw [c.right_inv hT]
  exact hmem

/-- The clamped logarithmic potential is bounded by `log (ρ/s)` off the closed chart ball of
radius `s`. -/
theorem chartLogClamp_le_log_div_of_notMem_chartClosedBall {c : OpenPartialHomeomorph X ℂ}
    {a : ℂ} {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s < ρ) {x : X}
    (hx : x ∉ Submission.chartClosedBall c a s) :
    Submission.chartLogClamp c a ρ x ≤ Real.log (ρ / s) := by
  by_cases hxb : x ∈ Submission.chartBall c a ρ
  · rw [Submission.chartLogClamp_of_mem hxb]
    have hxsrc : x ∈ c.source := hxb.1
    have hge : s ≤ ‖c x - a‖ := by
      by_contra hlt
      have h2 : dist (c x) a ≤ s := by
        rw [dist_eq_norm]
        exact (not_le.mp hlt).le
      exact hx ⟨hxsrc, Metric.mem_closedBall.mpr h2⟩
    have hpos : 0 < ‖c x - a‖ := lt_of_lt_of_le hs hge
    exact Real.log_le_log (div_pos hρ hpos) (div_le_div_of_nonneg_left hρ.le hs hge)
  · rw [Submission.chartLogClamp_of_not_mem hxb]
    exact Real.log_nonneg ((one_le_div hs).mpr hsρ.le)


end Frontier

/-! ## The member of the Perron family built from the clamped logarithmic potential -/

section Member

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The rescaled clamped logarithmic potential stays below `1` off the closed chart ball. -/
theorem inv_log_mul_chartLogClamp_le_one {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ s : ℝ}
    (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s < ρ) {Ω : Set X} {x : X}
    (hx : x ∈ Ω \ Submission.chartClosedBall c a s) :
    (Real.log (ρ / s))⁻¹ * Submission.chartLogClamp c a ρ x ≤ 1 := by
  have hLpos : 0 < Real.log (ρ / s) := Real.log_pos ((one_lt_div hs).mpr hsρ)
  have hle := chartLogClamp_le_log_div_of_notMem_chartClosedBall hρ hs hsρ hx.2
  have h := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hLpos.le)
  rwa [inv_mul_cancel₀ hLpos.ne'] at h

/-- **The rescaled clamped logarithmic potential is a member of the Perron family.** -/
theorem chartLogClamp_inv_mul_mem_limFamily {Ω : Set X} (hΩo : IsOpen Ω) {x₀ : X} {ρ s : ℝ}
    (hx₀ : x₀ ∈ Ω) (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s < ρ)
    (hρsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hρΩ : Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ⊆ Ω)
    {f : X → ℝ} (hf0 : ∀ z : X, 0 ≤ f z)
    (hfsph : ∀ z ∈ Submission.chartSphere (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s, f z = 1)
    (hfbd : ∀ z ∈ frontier Ω, f z = 0) :
    (fun x : X =>
        min ((Real.log (ρ / s))⁻¹ *
            Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ x) 1)
      ∈ Submission.limFamily
          (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 := by
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let a : ℂ := c x₀
  let D : Set X := Submission.chartClosedBall c a s
  let U : Set X := Ω \ D
  let L : ℝ := Real.log (ρ / s)
  let χ : X → ℝ := Submission.chartLogClamp c a ρ
  let v : X → ℝ := fun x => min (L⁻¹ * χ x) 1
  have hLpos : 0 < L := Real.log_pos ((one_lt_div hs).mpr hsρ)
  have hDsub : Metric.closedBall a s ⊆ c.target :=
    (Metric.closedBall_subset_closedBall hsρ.le).trans hρsub
  have hx₀D : x₀ ∈ D := by
    refine ⟨mem_chart_source ℂ x₀, ?_⟩
    show c x₀ ∈ Metric.closedBall a s
    rw [show c x₀ = a from rfl]
    exact Metric.mem_closedBall.mpr (by rw [dist_self]; exact hs.le)
  have hx₀notU : x₀ ∉ U := fun h => h.2 hx₀D
  have hχsub : Submission.SubharmonicOnX χ (Set.univ \ {x₀}) :=
    Submission.subharmonicOnX_chartLogClamp (z₀ := x₀) (ρ := ρ) hρ hρsub
  have hUo : IsOpen U := hΩo.sdiff (Submission.isClosed_chartClosedBall hDsub)
  have hUsub : U ⊆ Set.univ \ {x₀} := by
    intro x hx
    exact ⟨mem_univ x, fun h => hx₀notU (h ▸ hx)⟩
  have hχU : Submission.SubharmonicOnX χ U :=
    hχsub.mono hUsub (hχsub.1.mono hUsub)
  have hχscaled : Submission.SubharmonicOnX (fun x => L⁻¹ * χ x) U :=
    Submission.SubharmonicOnX.const_mul (inv_nonneg.mpr hLpos.le) hχU
  have hbound : ∀ x ∈ U, L⁻¹ * χ x ≤ 1 := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left
      (chartLogClamp_le_log_div_of_notMem_chartClosedBall (c := c) (a := a) hρ hs hsρ hx.2)
      (inv_nonneg.mpr hLpos.le)
    rwa [inv_mul_cancel₀ hLpos.ne'] at h
  have hv_eq : Set.EqOn v (fun x => L⁻¹ * χ x) U := fun x hx => min_eq_left (hbound x hx)
  have hvsub : Submission.SubharmonicOnX v U := by
    refine ⟨hχscaled.1.congr hv_eq, ?_⟩
    intro x hx
    refine Submission.SubharmonicOnXAt.congr (hχscaled.2 x hx) ?_
    filter_upwards [hUo.mem_nhds hx] with y hy
    exact (hv_eq hy).symm
  refine ⟨hvsub, fun x => min_le_right _ _, ?_⟩
  intro ζ hζ ε hε
  rcases frontier_sdiff_chartClosedBall_subset (Ω := Ω) hDsub hζ with hζΩ | hζS
  · -- the outer boundary: the data vanishes and the potential tends to `0`
    have hfζ : f ζ = 0 := hfbd ζ hζΩ
    have hζnotΩ : ζ ∉ Ω := by
      intro h
      exact hζΩ.2 (by rwa [hΩo.interior_eq])
    have hζnotB : ζ ∉ Submission.chartBall c a ρ := fun h =>
      hζnotΩ (hρΩ (Submission.chartBall_subset_chartClosedBall c a ρ h))
    have hneζ : ζ ≠ x₀ := fun h => hζnotΩ (h ▸ hx₀)
    have hχζ : χ ζ = 0 := Submission.chartLogClamp_of_not_mem hζnotB
    have hcont : ContinuousAt χ ζ :=
      Submission.continuousAt_chartLogClamp (c := c) (a := a) (b := x₀) (x := ζ)
        hρ hρsub (mem_chart_source ℂ x₀) rfl hneζ
    have htend : Tendsto χ (𝓝[U] ζ) (𝓝 0) := by
      rw [← hχζ]
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hmem : ∀ᶠ y in 𝓝 (χ ζ), y < ε * L := by
      rw [hχζ]
      exact isOpen_Iio.mem_nhds (mul_pos hε hLpos)
    have hev : ∀ᶠ z in 𝓝[U] ζ, χ z < ε * L :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (hcont.tendsto.eventually hmem)
    filter_upwards [hev] with z hz
    have h1 : L⁻¹ * χ z < ε := by
      calc L⁻¹ * χ z < L⁻¹ * (ε * L) := mul_lt_mul_of_pos_left hz (inv_pos.mpr hLpos)
        _ = ε := by field_simp
    calc v z ≤ L⁻¹ * χ z := min_le_left _ _
      _ ≤ ε := h1.le
      _ = f ζ + ε := by rw [hfζ, zero_add]
  · -- the inner sphere: the data is `1`, and the member is bounded by `1`
    have hfζ : f ζ = 1 := hfsph ζ hζS
    filter_upwards with z
    calc v z ≤ 1 := min_le_right _ _
      _ ≤ f ζ + ε := by rw [hfζ]; linarith


end Member

/-! ## The main theorem -/

section Main

/-- **The Perron envelope of `Ω \ chartClosedBall c a s` with data `1` on the inner sphere.**
See the module docstring for the statement of the six conclusions. -/
theorem dirichletSphereEnvelope_facts {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩne : Ω ≠ Set.univ)
    (hcomp : IsCompact (closure Ω)) {x₀ : X} (hx₀ : x₀ ∈ Ω) {ρ : ℝ} (hρ : 0 < ρ)
    (hρsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hρΩ : Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ⊆ Ω)
    {s : ℝ} (hs : 0 < s) (hsρ : s < ρ)
    {f : X → ℝ} (hf0 : ∀ z : X, 0 ≤ f z) (hf1 : ∀ z : X, f z ≤ 1)
    (hfsph : ∀ z ∈ Submission.chartSphere (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s, f z = 1)
    (hfbd : ∀ z ∈ frontier Ω, f z = 0)
    (hbar : ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    Submission.HarmonicOnX
        (Submission.limEnvelope (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1)
        (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) ∧
    (∀ x : X, 0 ≤ Submission.limEnvelope (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x) ∧
    (∀ x : X, Submission.limEnvelope (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x ≤ 1) ∧
    (∀ x ∈ (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s),
      Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ x ≤
        Real.log (ρ / s) * Submission.limEnvelope
          (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s),
      x ∈ (chartAt ℂ x₀).source → ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ < s + δ →
        1 - ε ≤ Submission.limEnvelope
          (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : Set X, IsOpen N ∧ frontier Ω ⊆ N ∧
      ∀ x ∈ (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s),
        x ∈ N → Submission.limEnvelope
          (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x < ε) := by
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let a : ℂ := c x₀
  let D : Set X := Submission.chartClosedBall c a s
  let U : Set X := Ω \ D
  let L : ℝ := Real.log (ρ / s)
  let χ : X → ℝ := Submission.chartLogClamp c a ρ
  let v : X → ℝ := fun x => min (L⁻¹ * χ x) 1
  have hLpos : 0 < L := Real.log_pos ((one_lt_div hs).mpr hsρ)
  have hDsub : Metric.closedBall a s ⊆ c.target :=
    (Metric.closedBall_subset_closedBall hsρ.le).trans hρsub
  have hDΩsub : D ⊆ Ω := fun x hx =>
    hρΩ ⟨hx.1, Metric.closedBall_subset_closedBall hsρ.le hx.2⟩
  have hKsphΩ : Submission.chartSphere c a s ⊆ Ω := fun x hx =>
    hDΩsub (Submission.chartSphere_subset_chartClosedBall c a s hx)
  have hUo : IsOpen U := hΩo.sdiff (Submission.isClosed_chartClosedBall hDsub)
  have hUcomp : IsCompact (closure U) :=
    hcomp.of_isClosed_subset isClosed_closure (closure_mono Set.sdiff_subset)
  have hfr_sub : frontier U ⊆ frontier Ω ∪ Submission.chartSphere c a s :=
    frontier_sdiff_chartClosedBall_subset (Ω := Ω) hDsub
  have hKsph_sub : Submission.chartSphere c a s ⊆ frontier U :=
    chartSphere_subset_frontier_sdiff_chartClosedBall hΩo hDΩsub
  have hfr_ne : (frontier U).Nonempty :=
    (chartSphere_nonempty hs hDsub).mono hKsph_sub
  have hv : v ∈ Submission.limFamily U f 1 :=
    chartLogClamp_inv_mul_mem_limFamily (Ω := Ω) hΩo hx₀ hρ hs hsρ hρsub hρΩ hf0 hfsph hfbd
  have hneF : (Submission.limFamily U f 1).Nonempty := ⟨v, hv⟩
  have hzero : (fun _ : X => (0 : ℝ)) ∈ Submission.limFamily U f 1 :=
    ⟨(Submission.subharmonicOnX_const 0).mono (subset_univ U) continuousOn_const,
      fun _ => zero_le_one,
      fun ζ _ ε hε => by
        filter_upwards with z
        linarith [hf0 ζ, hε.le]⟩
  have hharm : Submission.HarmonicOnX (Submission.limEnvelope U f 1) U :=
    Submission.harmonicOnX_limEnvelope hUo hneF
  have hnonneg : ∀ x : X, 0 ≤ Submission.limEnvelope U f 1 x := by
    intro x
    rw [Submission.limEnvelope, Submission.upperEnvelope]
    have hbdd : BddAbove ((Submission.limFamily U f 1).image (fun f : X → ℝ => f x)) := by
      refine ⟨1, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      exact Submission.limFamily_bound hw x
    exact le_csSup hbdd ⟨fun _ => 0, hzero, rfl⟩
  have hleone : ∀ x : X, Submission.limEnvelope U f 1 x ≤ 1 := fun x =>
    Submission.upperEnvelope_le hneF (fun w hw x => Submission.limFamily_bound hw x) x
  have hclamp : ∀ x ∈ U, χ x ≤ L * Submission.limEnvelope U f 1 x := by
    intro x hx
    have hvx : v x ≤ Submission.limEnvelope U f 1 x :=
      Submission.limFamily_le_limEnvelope hUo hneF hv x hx
    have hb : L⁻¹ * χ x ≤ 1 := inv_log_mul_chartLogClamp_le_one hρ hs hsρ hx
    have hmin : v x = L⁻¹ * χ x := min_eq_left hb
    have h1 : L⁻¹ * χ x ≤ Submission.limEnvelope U f 1 x := hmin ▸ hvx
    calc χ x = L * (L⁻¹ * χ x) := (mul_inv_cancel_left₀ hLpos.ne' (χ x)).symm
      _ ≤ L * Submission.limEnvelope U f 1 x := mul_le_mul_of_nonneg_left h1 hLpos.le
  have hnear : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ U, x ∈ c.source →
      ‖c x - a‖ < s + δ → 1 - ε ≤ Submission.limEnvelope U f 1 x := by
    intro ε hε
    have hgs : (1 - ε) * L < Real.log (ρ / s) := by
      have h2 : (1 - ε) * L < L := by nlinarith [hLpos, hε]
      exact h2
    obtain ⟨η, hηpos, hηprop⟩ :
        ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t - s| < η → (1 - ε) * L < Real.log (ρ / t) := by
      have hcont : ContinuousAt (fun t : ℝ => Real.log (ρ / t)) s := by
        have h1 : ContinuousAt (fun t : ℝ => ρ / t) s :=
          continuousAt_const.div continuousAt_id (ne_of_gt hs)
        exact h1.log (div_ne_zero hρ.ne' (ne_of_gt hs))
      have hev : ∀ᶠ t in 𝓝 s, (1 - ε) * L < Real.log (ρ / t) :=
        hcont.tendsto.eventually (isOpen_Ioi.mem_nhds hgs)
      rw [Metric.eventually_nhds_iff] at hev
      obtain ⟨η, hηpos, hηprop⟩ := hev
      refine ⟨η, hηpos, fun t ht => hηprop ?_⟩
      rwa [Real.dist_eq]
    refine ⟨min (η / 2) ((ρ - s) / 2), lt_min (by linarith) (by linarith), ?_⟩
    intro x hxU hxsrc hxsph
    have ht_ge : s ≤ ‖c x - a‖ := by
      by_contra hlt
      have h2 : dist (c x) a ≤ s := by
        rw [dist_eq_norm]
        exact (not_le.mp hlt).le
      exact hxU.2 ⟨hxsrc, Metric.mem_closedBall.mpr h2⟩
    have ht_lt : ‖c x - a‖ < ρ := by
      have h2 : s + min (η / 2) ((ρ - s) / 2) ≤ ρ := by
        linarith [min_le_right (η / 2) ((ρ - s) / 2)]
      linarith
    have hχx : χ x = Real.log (ρ / ‖c x - a‖) := by
      show Submission.chartLogClamp c a ρ x = Real.log (ρ / ‖c x - a‖)
      rw [Submission.chartLogClamp_of_mem]
      exact ⟨hxsrc, Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact ht_lt)⟩
    have hbnd : (1 - ε) * L < χ x := by
      rw [hχx]
      refine hηprop _ ?_
      rw [abs_lt]
      constructor
      · have h3 := min_le_left (η / 2) ((ρ - s) / 2)
        linarith
      · have h3 := min_le_left (η / 2) ((ρ - s) / 2)
        have h4 : s + min (η / 2) ((ρ - s) / 2) ≤ ρ := by
          linarith [min_le_right (η / 2) ((ρ - s) / 2)]
        linarith
    have hinv : 1 - ε ≤ L⁻¹ * χ x := by
      have h1 : L⁻¹ * ((1 - ε) * L) = 1 - ε := by
        rw [mul_comm ((1 - ε)) L, ← mul_assoc, inv_mul_cancel₀ hLpos.ne', one_mul]
      calc 1 - ε = L⁻¹ * ((1 - ε) * L) := h1.symm
        _ ≤ L⁻¹ * χ x := (mul_lt_mul_of_pos_left hbnd (inv_pos.mpr hLpos)).le
    have hvx : v x ≤ Submission.limEnvelope U f 1 x :=
      Submission.limFamily_le_limEnvelope hUo hneF hv x hxU
    have : 1 - ε ≤ v x := le_min hinv (by linarith)
    linarith
  have hfar : ∀ ε : ℝ, 0 < ε → ∃ N : Set X, IsOpen N ∧ frontier Ω ⊆ N ∧
      ∀ x ∈ U, x ∈ N → Submission.limEnvelope U f 1 x < ε := by
    intro ε hε
    have key : ∀ p ∈ frontier Ω, ∃ N : Set X, IsOpen N ∧ p ∈ N ∧
        ∀ x ∈ U, x ∈ N → Submission.limEnvelope U f 1 x < ε := by
      intro p hp
      obtain ⟨up, Vp, hVpo, hpVp, hsup, hpos, hcont, hup0⟩ := hbar p hp
      exact limEnvelope_lt_near_of_localBarrier_ball (X := X) hΩo hcomp hx₀ hρ hs hsρ hρsub hρΩ
        hp hf0 hfbd ⟨up, Vp, hVpo, hpVp, hsup, hpos, hcont, hup0⟩ ε hε
    -- cover the compact frontier by finitely many of these neighbourhoods
    have hfr_compact : IsCompact (frontier Ω) :=
      hcomp.of_isClosed_subset isClosed_frontier frontier_subset_closure
    have key' : ∀ q : {p : X // p ∈ frontier Ω}, ∃ N : Set X, IsOpen N ∧ (q : X) ∈ N ∧
        ∀ x ∈ U, x ∈ N → Submission.limEnvelope U f 1 x < ε := fun q => key q.1 q.2
    choose N hNopen hNmem hNkey using key'
    have hcover : frontier Ω ⊆ ⋃ q : {p : X // p ∈ frontier Ω}, N q := by
      intro p hp
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hNmem ⟨p, hp⟩⟩
    obtain ⟨t, ht⟩ := hfr_compact.elim_finite_subcover N hNopen hcover
    refine ⟨⋃ q ∈ t, N q, isOpen_biUnion fun q _ => hNopen q, ht, ?_⟩
    intro x hxU hxN
    obtain ⟨q, -, hxq⟩ := Set.mem_iUnion₂.mp hxN
    exact hNkey q x hxU hxq
  exact ⟨hharm, hnonneg, hleone, hclamp, hnear, hfar⟩

end Main

end Work.SimplyConnected.ABS
