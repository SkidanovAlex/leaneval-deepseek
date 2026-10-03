import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.SurfaceTopology
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.subharmonic_eqOn_ball_of_isMaxOn

/-!
# The maximum principle on relatively compact regions of a Riemann surface

Two tools are proved here.

* `Submission.SubharmonicAtChart.eqOn_of_le` — the **local strong maximum principle**: a
  subharmonic function which is bounded above by its value at a point is constant near that
  point.  (Reduced to the Euclidean statement by choosing the chart ball inside the region
  where the bound holds.)

* `Submission.SubharmonicOnX.le_of_frontier_limsup` — the **maximum principle on a relatively
  compact open set** `U`: if `v` is subharmonic on `U`, `closure U` is compact, `frontier U` is
  nonempty and the *limsup* of `v` at every frontier point is at most `a`, then `v ≤ a` on `U`.

  This is the form needed for the exhaustion construction of the Green function: the members of
  the Perron family satisfy pointwise bounds only *outside* the open set, and the boundary
  condition has to be imposed in the limsup sense (a pointwise bound alone does not prevent a
  subharmonic function from blowing up at the boundary).

The proof of the second statement follows the classical argument: the closed set
`A = {v ≥ a + δ}` is compact, `v` attains its maximum `M` on it, and `M` is in fact the maximum
of `v` on all of `U`; the set `{v = M} ∩ U` is clopen in `U`, so it contains a whole connected
component of `U`, and a frontier point of `U` in the closure of that component gives a
contradiction with the boundary condition.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section Local

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Local strong maximum principle** (chart version).  If `u` is subharmonic at `x` in the
chart `c` and `u ≤ u x` on a neighbourhood `U` of `x`, then `u = u x` on a (possibly smaller)
neighbourhood of `x`. -/
theorem SubharmonicAtChart.eqOn_of_le {u : X → ℝ} {c : OpenPartialHomeomorph X ℂ} {x : X}
    (hu : SubharmonicAtChart u c x) {U : Set X} (hU : U ∈ 𝓝 x) (hle : ∀ y ∈ U, u y ≤ u x) :
    ∃ V ∈ 𝓝 x, ∀ y ∈ V, u y = u x := by
  obtain ⟨hxsrc, ρ, hρ, -, hcont, hmvp⟩ := hu
  have hxball : x ∈ chartBall c (c x) ρ := ⟨hxsrc, Metric.mem_ball_self hρ⟩
  have hVn : U ∩ chartBall c (c x) ρ ∈ 𝓝 x :=
    inter_mem hU ((chartBall_isOpen c (c x) ρ).mem_nhds hxball)
  have himg : c '' (U ∩ chartBall c (c x) ρ) ∈ 𝓝 (c x) := c.image_mem_nhds hxsrc hVn
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.mp himg
  set R : ℝ := min ρ ρ₁ with hRdef
  have hR : 0 < R := lt_min hρ hρ₁
  have hRρ : R ≤ ρ := min_le_left _ _
  have hRρ₁ : R ≤ ρ₁ := min_le_right _ _
  have hmax' : ∀ z ∈ Metric.ball (c x) R, (u ∘ c.symm) z ≤ (u ∘ c.symm) (c x) := by
    intro z hz
    have hz1 : z ∈ Metric.ball (c x) ρ₁ := Metric.ball_subset_ball hRρ₁ hz
    obtain ⟨y, hy, hyz⟩ := hρ₁sub hz1
    have hysrc : y ∈ c.source := hy.2.1
    have hzy : c.symm z = y := by rw [← hyz, c.left_inv hysrc]
    show u (c.symm z) ≤ u (c.symm (c x))
    rw [hzy, c.left_inv hxsrc]
    exact hle y hy.1
  have hcont' : ContinuousOn (u ∘ c.symm) (Metric.ball (c x) R) :=
    hcont.mono (Metric.ball_subset_ball hRρ)
  have hmvp' : ∀ p ∈ Metric.ball (c x) R, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball (c x) R →
      (u ∘ c.symm) p ≤ Real.circleAverage (u ∘ c.symm) p r :=
    fun p hp r hr hpr =>
      hmvp p (Metric.ball_subset_ball hRρ hp) r hr (hpr.trans (Metric.ball_subset_ball hRρ))
  have heq :=
    Commons.Analysis.Complex.Harmonic.subharmonic_eqOn_ball_of_isMaxOn hR hcont' hmvp' hmax'
  refine ⟨chartBall c (c x) R,
    (chartBall_isOpen c (c x) R).mem_nhds ⟨hxsrc, Metric.mem_ball_self hR⟩, ?_⟩
  intro y hy
  have hysrc : y ∈ c.source := hy.1
  have hyc : c y ∈ Metric.ball (c x) R := hy.2
  have h1 := heq (c y) hyc
  show u y = u x
  simpa [Function.comp_apply, c.left_inv hysrc, c.left_inv hxsrc] using h1

/-- Local strong maximum principle, point version. -/
theorem SubharmonicOnXAt.eqOn_of_le {u : X → ℝ} {x : X} (hu : SubharmonicOnXAt u x)
    {U : Set X} (hU : U ∈ 𝓝 x) (hle : ∀ y ∈ U, u y ≤ u x) :
    ∃ V ∈ 𝓝 x, ∀ y ∈ V, u y = u x :=
  SubharmonicAtChart.eqOn_of_le hu hU hle

end Local

section Region

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
  [ChartedSpace ℂ X]

/-- **Maximum principle on a relatively compact region, limsup form.**  Let `U` be an open set
with compact closure and nonempty frontier, and let `v` be subharmonic on `U`.  If the limsup of
`v` at every frontier point of `U` is at most `a` (in the sense that `v ≤ a + ε` eventually in
the trace filter on `U`), then `v ≤ a` on all of `U`. -/
theorem SubharmonicOnX.le_of_frontier_limsup {U : Set X} (hU : IsOpen U) {v : X → ℝ}
    (hv : SubharmonicOnX v U) (hcomp : IsCompact (closure U)) (hne : (frontier U).Nonempty)
    {a : ℝ} (hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] ξ, v z ≤ a + ε) :
    ∀ z ∈ U, v z ≤ a := by
  rintro z₀ hz₀
  by_contra hcon
  simp only [not_le] at hcon
  have hza : a < v z₀ := hcon
  set δ : ℝ := (v z₀ - a) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδle : a + δ ≤ v z₀ := by rw [hδdef]; linarith
  set A : Set X := {z : X | z ∈ U ∧ a + δ ≤ v z} with hAdef
  have hz₀A : z₀ ∈ A := ⟨hz₀, hδle⟩
  have hAne : A.Nonempty := ⟨z₀, hz₀A⟩
  have hAU : A ⊆ U := fun z hz => hz.1
  have hAsub : A ⊆ closure U := fun z hz => subset_closure hz.1
  -- `A` is closed in `X`
  have hAclosed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro x hx
    by_cases hxU : x ∈ U
    · have hcont : ContinuousAt v x := (hv.2 x hxU).continuousAt
      haveI : NeBot (𝓝[A] x) := (mem_closure_iff_nhdsWithin_neBot).mp hx
      have henv : ∀ᶠ z in 𝓝[A] x, a + δ ≤ v z :=
        Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hz.2)
      have hT : Tendsto (fun z : X => -v z) (𝓝[A] x) (𝓝 (-(v x))) :=
        hcont.neg.tendsto.mono_left nhdsWithin_le_nhds
      have henv' : ∀ᶠ z in 𝓝[A] x, -v z ≤ -(a + δ) :=
        henv.mono (fun z hz => neg_le_neg hz)
      have h1 : -(v x) ≤ -(a + δ) := le_of_tendsto hT henv'
      exact ⟨hxU, by linarith⟩
    · exfalso
      have hxfront : x ∈ frontier U := by
        have hxUcl : x ∈ closure U := closure_mono hAU hx
        refine ⟨hxUcl, fun hxint => hxU (interior_subset hxint)⟩
      have hlim' := hlim x hxfront (δ / 2) (by linarith)
      haveI : NeBot (𝓝[A] x) := (mem_closure_iff_nhdsWithin_neBot).mp hx
      have hlim'' : ∀ᶠ z in 𝓝[A] x, v z ≤ a + δ / 2 :=
        Filter.le_def.mp (nhdsWithin_mono x hAU) _ hlim'
      have h2 : ∀ᶠ z in 𝓝[A] x, z ∈ A ∧ v z ≤ a + δ / 2 :=
        (show ∀ᶠ z in 𝓝[A] x, z ∈ A from self_mem_nhdsWithin).and hlim''
      obtain ⟨z, hzA, hzle⟩ := h2.exists
      have hzge : a + δ ≤ v z := hzA.2
      linarith
  -- `v` attains its maximum on `A`, and that maximum is the maximum over `U`
  have hAcomp : IsCompact A :=
    IsCompact.of_isClosed_subset hcomp hAclosed hAsub
  obtain ⟨p, hpA, hpMax⟩ := hAcomp.exists_isMaxOn hAne (hv.1.mono hAU)
  set M : ℝ := v p with hMdef
  have hAle : a + δ ≤ M := by rw [hMdef]; exact hpA.2
  have hleM : ∀ z ∈ U, v z ≤ M := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact hpMax hzA
    · have hlt : v z < a + δ := not_le.mp (fun h => hzA ⟨hz, h⟩)
      rw [hMdef]; linarith
  -- the level set `S = {v = M} ∩ U` is clopen in `U`
  set S : Set X := {z : X | z ∈ U ∧ v z = M} with hSdef
  have hpS : p ∈ S := ⟨hpA.1, by rw [hMdef]⟩
  have hSne : S.Nonempty := ⟨p, hpS⟩
  have hSU : S ⊆ U := fun z hz => hz.1
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hzS
    obtain ⟨V, hVn, hVeq⟩ := SubharmonicOnXAt.eqOn_of_le (hv.2 z hzS.1)
      (hU.mem_nhds hzS.1) (fun y hy => by simpa [hzS.2] using hleM y hy)
    exact Filter.mem_of_superset (inter_mem hVn (hU.mem_nhds hzS.1))
      (fun y hy => ⟨hy.2, by rw [hVeq y hy.1, hzS.2]⟩)
  have hclU : closure U = U ∪ frontier U := by
    rw [closure_eq_interior_union_frontier, hU.interior_eq]
  by_cases hcl : closure S ∩ frontier U = ∅
  · -- `S` is clopen in `X`, hence everything
    have hcl_sub : closure S ⊆ U := by
      intro x hx
      have hxUcl : x ∈ closure U := closure_mono hSU hx
      rw [hclU] at hxUcl
      rcases hxUcl with h | h
      · exact h
      · have : x ∈ (∅ : Set X) := by rw [← hcl]; exact ⟨hx, h⟩
        exact this.elim
    have hSclosedX : IsClosed S := by
      rw [← closure_subset_iff_isClosed]
      intro x hx
      have hxU : x ∈ U := hcl_sub hx
      haveI : NeBot (𝓝[S] x) := (mem_closure_iff_nhdsWithin_neBot).mp hx
      have hT : Tendsto v (𝓝[S] x) (𝓝 (v x)) :=
        ((hv.2 x hxU).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      have henv : ∀ᶠ z in 𝓝[S] x, v z = M :=
        Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hz.2)
      have hT2 : Tendsto v (𝓝[S] x) (𝓝 M) :=
        tendsto_const_nhds.congr' (henv.mono fun z hz => hz.symm)
      have hM : v x = M := tendsto_nhds_unique hT hT2
      exact ⟨hxU, hM⟩
    rcases isClopen_iff.mp ⟨hSclosedX, hSopen⟩ with h | h
    · exact hSne.ne_empty h
    · exfalso
      have hUuniv : U = univ := by
        refine Subset.antisymm (subset_univ _) ?_
        rw [← h]
        exact fun x hx => hx.1
      rw [hUuniv, frontier_univ] at hne
      exact hne.ne_empty rfl
  · obtain ⟨ξ, hξ⟩ := Set.nonempty_iff_ne_empty.mpr hcl
    have hξcl : ξ ∈ closure S := hξ.1
    have hξfront : ξ ∈ frontier U := hξ.2
    have hlim' := hlim ξ hξfront ((M - a) / 2) (by linarith)
    haveI : NeBot (𝓝[S] ξ) := (mem_closure_iff_nhdsWithin_neBot).mp hξcl
    have hlim'' : ∀ᶠ z in 𝓝[S] ξ, v z ≤ a + (M - a) / 2 :=
      Filter.le_def.mp (nhdsWithin_mono ξ hSU) _ hlim'
    have henv : ∀ᶠ z in 𝓝[S] ξ, v z = M :=
      Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hz.2)
    have h3 : ∀ᶠ z in 𝓝[S] ξ, M ≤ a + (M - a) / 2 :=
      (henv.and hlim'').mono (fun z hz => by linarith [hz.1, hz.2])
    obtain ⟨z, hz⟩ := h3.exists
    linarith

end Region

end Submission

namespace Submission

section Minimum

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Minimum principle on a relatively compact region, limsup form**: a harmonic function whose
liminf at every frontier point of `U` is nonnegative (in the trace filter on `U`) is nonnegative
on `U`.  This is `SubharmonicOnX.le_of_frontier_limsup` applied to `-v`. -/
theorem HarmonicOnX.nonneg_of_frontier_liminf {U : Set X} (hU : IsOpen U) {v : X → ℝ}
    (hv : HarmonicOnX v U) (hcomp : IsCompact (closure U)) (hne : (frontier U).Nonempty)
    (hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] ξ, -ε ≤ v z) :
    ∀ z ∈ U, 0 ≤ v z := by
  have hsub : SubharmonicOnX (-v) U :=
    ⟨fun x hx => (hv x hx).continuousAt.continuousWithinAt.neg,
      fun x hx => (hv x hx).neg.subharmonic⟩
  have hlim' : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝[U] ξ, (-v) z ≤ (0 : ℝ) + ε := by
    intro ξ hξ ε hε
    filter_upwards [hlim ξ hξ ε hε] with z hz
    simpa using neg_le_neg hz
  have := SubharmonicOnX.le_of_frontier_limsup hU hsub hcomp hne (a := 0) hlim'
  intro z hz
  have h := this z hz
  simpa using h

end Minimum

end Submission
