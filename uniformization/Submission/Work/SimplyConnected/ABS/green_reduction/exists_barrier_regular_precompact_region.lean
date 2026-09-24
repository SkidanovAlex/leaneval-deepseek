import Mathlib
import Submission.Work.SimplyConnected.ABS.green_reduction.sard_lite_manifold
import Submission.Work.SimplyConnected.ABS.green_reduction.level_component_supset
import Submission.Work.SimplyConnected.ABS.green_reduction.level_component_frontier
import Submission.Work.SimplyConnected.ABS.green_reduction.sector_boundary_no_sc
import Submission.Work.SimplyConnected.ABS.OneEnded.exists_contMDiff_sublevel_compact
import Submission.Work.SimplyConnected.Perron.greenOn
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.green_reduction.crossing
import Submission.Work.SimplyConnected.ABS.green_reduction.sector_chartBall_freeDirection
import Submission.Work.SimplyConnected.ABS.green_reduction.noTangency_reduction
import Submission.Work.SimplyConnected.ABS.ray_boundary_barrier
import Submission.Work.SimplyConnected.ABS.sectorCondition_of_chart_balls
import Submission.Work.SimplyConnected.ABS.chartBall_transport
import Submission.Work.SimplyConnected.ABS.region_with_sector_boundary

namespace Work.SimplyConnected.ABS.green_reduction

open scoped _root_.Topology Manifold ContDiff
open Set Filter

/-!
# A barrier-regular precompact region containing a given compact set

The target theorem

`Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region`

asks, for a connected, second countable, `ℂ`-charted `C¹` surface `X` which is not compact, a compact
`K ⊆ X` and a point `x₀`, for a precompact connected open `Ω ⊇ K ∪ {x₀}`, `Ω ≠ X`, such that every
frontier point of `Ω` carries a *barrier*: a superharmonic function on `Ω ∩ V`, positive there,
continuous on `V`, vanishing at the point.

## Decomposition

* `barriers_of_sector_or_ray`: the *potential-theoretic half*.  If an open `Ω` satisfies the *sector*
  condition `HasSectorBoundary Ω p` or the *ray* condition `HasRayBoundary Ω p` at every frontier
  point, then the barrier clause of the target holds.  Hence the target follows from the purely
  geometric statement

      (★)  ∃ Ω, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ∪ {x₀} ⊆ Ω ∧ Ω ≠ univ ∧
             ∀ p ∈ frontier Ω, HasSectorBoundary Ω p ∨ HasRayBoundary Ω p .

  `NOTES_status_barrier_region.md` in this directory records the analysis of (★): it is true (a
  smoothed compact subsurface-with-boundary containing `K ∪ {x₀}` satisfies it), and with a finite
  family of chart balls covering `K ∪ {x₀}` one gets, at every frontier point `p`, a non-zero
  direction `v` with `L i v ≥ 0` for all balls `L i` through `p` (the *closed cone* is non-empty,
  because the chart transitions of this workspace are analytic, so each ball has a non-zero
  linearisation functional and the standard linearisation argument applies).  When the closed cone is
  two-dimensional a thin sub-cone lies in the complement of `Ω` near `p`, giving the sector condition.
  The remaining case — every ball through `p` tangent at `p` — needs the members on either side of the
  common tangent line to be *locally disjoint* (then the tangent ray is free); for balls round in a
  common chart this is automatic (`hasSectorBoundary_or_hasRayBoundary_of_two_chartBall`), but for
  balls in different charts a "sliver" overlap produces a zero-angle cusp at which neither condition
  holds.  So (★) reduces to the general-position statement that the ball family can be chosen
  tangency-free, which is a genericity statement about finitely many balls and is not in the
  workspace.


### A second route, recorded in session S25 (`NOTES_s25_engulfing_and_sard_crux.md`)

The module `green_reduction/level_component_frontier.lean` (proved) reduces the target to
the *classical* level-set route of Hubbard / Anghel-Bruin-Stan: if `g` is a proper smooth exhaustion
function of `X` (`Work.SimplyConnected.ABS.OneEnded.exists_contMDiff_sublevel_compact`) and `C` is a
**regular** level (the chart pull-back of `g` is differentiable with non-zero derivative at every
point where `g = C`), then the connected component `A` of `x₀` in `{g < C}` satisfies the *sector*
condition at every frontier point (`hasSectorBoundary_of_regular_level`), so with `K ∪ {x₀} ⊆ A` the
region `Ω := A` is a witness.  The missing input is therefore Sard's lemma for a smooth function of
two variables; the workspace's `Work.CriticalSet` chapter supplies exactly this substitute for
*harmonic* functions (isolated critical points, hence countably many critical values), which is why
the Green-function route (`exists_barrier_regular_precompact_region_of_greenFunction.lean`) works.
The "engulfing" variant of this route (covering the critical frontier points by chart balls) was
developed and refuted in the same session: the trichotomy "sector, ray, or punctured neighbourhood"
at a critical frontier point fails for general smooth `g` (flat "spiral fan" functions).

The potential-theoretic half is already in the workspace: at a frontier point `p` of an open `Ω`, the
*sector* (cone) condition `Work.SimplyConnected.ABS.HasSectorBoundary Ω p` and the *ray* (slit)
condition `Work.SimplyConnected.ABS.HasRayBoundary Ω p` each produce such a barrier
(`Work.SimplyConnected.ABS.barrier_of_sector`, `Work.SimplyConnected.ABS.barrier_of_ray`); the
combination is recorded in `barriers_of_sector_or_ray` below.  So it suffices to produce a region
whose every frontier point satisfies one of the two conditions.
-/

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}

/-- A frontier point of an open set does not lie in it. -/
lemma not_mem_of_mem_frontier {Ω : Set X} (hΩo : IsOpen Ω) {p : X} (hp : p ∈ frontier Ω) :
    p ∉ Ω := by
  have h : frontier Ω = closure Ω \ Ω := hΩo.frontier_eq
  rw [h] at hp
  exact hp.2

/-- **A set with compact closure is never all of a non-compact space.**

(The version `Work.SimplyConnected.ABS.ne_univ_of_isCompact_closure` in the workspace carries a
spurious `[SimplyConnectedSpace X]` hypothesis, so it is recorded here in the general form.) -/
lemma ne_univ_of_isCompact_closure' {U : Set X} (hX : ¬ CompactSpace X)
    (h : IsCompact (closure U)) : U ≠ Set.univ := by
  intro hU
  rw [hU, closure_univ] at h
  exact hX (isCompact_univ_iff.mp h)

/-- **The sector-or-ray condition at every frontier point yields the barrier clause.** -/
theorem barriers_of_sector_or_ray {Ω : Set X} (hΩo : IsOpen Ω)
    (h : ∀ p ∈ frontier Ω,
      Work.SimplyConnected.ABS.HasSectorBoundary Ω p ∨
      Work.SimplyConnected.ABS.HasRayBoundary Ω p) :
    ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0 := by
  intro p hp
  have hpU : p ∉ Ω := not_mem_of_mem_frontier hΩo hp
  rcases h p hp with hs | hr
  · exact Work.SimplyConnected.ABS.barrier_of_sector hΩo hpU hs
  · exact Work.SimplyConnected.ABS.barrier_of_ray hΩo hpU hr

/-- **The sector condition at every frontier point yields the barrier clause.** -/
theorem barriers_of_sector {Ω : Set X} (hΩo : IsOpen Ω)
    (h : ∀ p ∈ frontier Ω, Work.SimplyConnected.ABS.HasSectorBoundary Ω p) :
    ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0 :=
  barriers_of_sector_or_ray hΩo fun p hp => Or.inl (h p hp)

/-- **The target from a single chart ball.**

If `c ∈ atlas ℂ X` is an atlas chart, `a ∈ ℂ`, `ρ > 0`, the closed ball of radius `ρ` about `a` lies
in the target of `c`, and `K ∪ {x₀}` lies in `c.source` and maps into the open ball of radius `ρ`,
then the chart ball `Submission.chartBall c a ρ` is a witness for the target: it is open, connected,
precompact, contained in `X` properly, and at every frontier point the *sector* condition holds
(`Work.SimplyConnected.ABS.hasSectorBoundary_chartBall`), hence so does the barrier condition. -/
theorem region_exists_of_chartBall {K : Set X} (hX : ¬ CompactSpace X)
    {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall a ρ ⊆ c.target)
    (hKsrc : K ∪ {x₀} ⊆ c.source) (hKimg : c '' (K ∪ {x₀}) ⊆ Metric.ball a ρ) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ∪ {x₀} ⊆ Ω ∧
      Ω ≠ Set.univ ∧
      (∀ p ∈ frontier Ω,
        Work.SimplyConnected.ABS.HasSectorBoundary Ω p ∨
        Work.SimplyConnected.ABS.HasRayBoundary Ω p) := by
  refine ⟨Submission.chartBall c a ρ, Submission.chartBall_isOpen c a ρ, ?_, ?_, ?_, ?_, ?_⟩
  · have hball : Submission.chartBall c a ρ = c.symm '' Metric.ball a ρ :=
      Work.SimplyConnected.ABS.chartBall_eq_image hsub
    rw [hball]
    haveI : SimplyConnectedSpace ↥(c.symm '' Metric.ball a ρ) :=
      (Work.SimplyConnected.ABS.chartBall_transport c hρ hsub).2.2.2.2.2.2
    exact isConnected_iff_connectedSpace.mpr inferInstance
  · exact (Submission.isCompact_chartClosedBall hsub).of_isClosed_subset isClosed_closure
      (Submission.closure_chartBall_subset_chartClosedBall hsub)
  · intro x hx
    exact Submission.mem_chartBall.mpr ⟨hKsrc hx, hKimg ⟨x, hx, rfl⟩⟩
  · exact ne_univ_of_isCompact_closure' (X := X) hX
      ((Submission.isCompact_chartClosedBall hsub).of_isClosed_subset isClosed_closure
        (Submission.closure_chartBall_subset_chartClosedBall hsub))
  · intro p hp
    exact Or.inl (Work.SimplyConnected.ABS.hasSectorBoundary_chartBall (X := X) hc hρ hsub p hp)

/-- **The barrier clause from a single global superharmonic function.**

If `f` is continuous and superharmonic on an open `Ω`, positive on `Ω` and vanishes on
`frontier Ω`, then the barrier condition of the target holds at every frontier point of `Ω`: take
`u := f` and `V := univ`.  (This is the reduction of the target to the existence of one global
superharmonic `f` with a precompact positive set.  Note that `f` is NOT required to be
superharmonic off `Ω`.) -/
theorem barrier_clause_of_globalSuperharmonic {Ω : Set X} {f : X → ℝ}
    (hcont : Continuous f) (hpos : ∀ x ∈ Ω, 0 < f x)
    (hsh : Submission.SuperharmonicOnX f Ω) (hzero : ∀ p ∈ frontier Ω, f p = 0) :
    ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0 := by
  intro p hp
  exact ⟨f, Set.univ, isOpen_univ, Set.mem_univ p, by simpa using hsh,
    fun x hx => hpos x hx.1, hcont.continuousOn, hzero p hp⟩

/-- **The target from a finite family of round balls in one chart, in general position.**

If `K ∪ {x₀}` is covered by a finite union `Ω := ⋃ i, chartBall c (a i) (ρ i)` of round balls of one
atlas chart `c`, at most two of the closed balls contain any given point (`htwo`), and `Ω` is
connected, then the target holds: `hasSectorBoundary_or_hasRayBoundary_iUnion_chartBall` gives the
sector-or-ray condition at every frontier point, and `barriers_of_sector_or_ray` converts it into the
barrier clause. -/
theorem exists_barrier_regular_precompact_region_of_one_chart {K : Set X} (hX : ¬ CompactSpace X)
    {ι : Type*} [Fintype ι] [Nonempty ι] {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X)
    {a : ι → ℂ} {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ c.target)
    (htwo : ∀ z : ℂ, ({i | z ∈ Metric.closedBall (a i) (ρ i)} : Set ι).ncard ≤ 2)
    (hcov : K ∪ {x₀} ⊆ ⋃ i, Submission.chartBall c (a i) (ρ i))
    (hconn : IsConnected (⋃ i, Submission.chartBall c (a i) (ρ i))) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ∪ {x₀} ⊆ Ω ∧
      Ω ≠ Set.univ ∧
      (∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
        Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
        ContinuousOn u V ∧ u p = 0) := by
  set Ω : Set X := ⋃ i, Submission.chartBall c (a i) (ρ i) with hΩdef
  have hΩo : IsOpen Ω := isOpen_iUnion fun i => Submission.chartBall_isOpen c (a i) (ρ i)
  have hcompact : IsCompact (closure Ω) := by
    refine (isCompact_iUnion fun i => Submission.isCompact_chartClosedBall (hsub i)).of_isClosed_subset
      isClosed_closure ?_
    rw [hΩdef, closure_iUnion_of_finite (fun i => Submission.chartBall c (a i) (ρ i))]
    exact iUnion_mono fun i => Submission.closure_chartBall_subset_chartClosedBall (hsub i)
  refine ⟨Ω, hΩo, hconn, hcompact, hcov, ne_univ_of_isCompact_closure' (X := X) hX hcompact, ?_⟩
  exact barriers_of_sector_or_ray hΩo fun p hp =>
    Work.SimplyConnected.ABS.hasSectorBoundary_or_hasRayBoundary_iUnion_chartBall
      (X := X) hc a ρ hρ hsub htwo p hp


/-! ## The local reduction: pairwise conditions and frontiers of finite unions

The construction of the region `Ω` of the target is organised around the following facts.  The
frontier is a *local* notion, and for a finite union of open sets the sector-or-ray condition at a
frontier point follows from the same condition for the *pairs* of members meeting that point,
provided at most two members meet it.  In the source construction the members are chart balls, for
which the pairwise condition at a point with a common chart is the verified
`Work.SimplyConnected.ABS.hasSectorBoundary_or_hasRayBoundary_of_two_chartBall`. -/

/-- **The frontier is local.**  If two sets agree in a neighbourhood of `p`, then they have the same
frontier at `p`. -/
lemma frontier_of_inter_eq {U U' V : Set X} {p : X} (hVo : IsOpen V) (hpV : p ∈ V)
    (heq : U ∩ V = U' ∩ V) (hp : p ∈ frontier U) : p ∈ frontier U' := by
  have hp' : p ∈ closure U ∩ closure Uᶜ := by
    rwa [frontier_eq_closure_inter_closure] at hp
  have h1 : p ∈ closure U' := by
    rw [mem_closure_iff]
    intro W hWo hpW
    obtain ⟨x, ⟨hxW, hxV⟩, hxU⟩ :=
      (mem_closure_iff.mp hp'.1) (W ∩ V) (hWo.inter hVo) ⟨hpW, hpV⟩
    exact ⟨x, ⟨hxW, (by rw [← heq]; exact ⟨hxU, hxV⟩ : x ∈ U' ∩ V).1⟩⟩
  have h2 : p ∈ closure U'ᶜ := by
    rw [mem_closure_iff]
    intro W hWo hpW
    obtain ⟨x, ⟨hxW, hxV⟩, hxUc⟩ :=
      (mem_closure_iff.mp hp'.2) (W ∩ V) (hWo.inter hVo) ⟨hpW, hpV⟩
    refine ⟨x, ⟨hxW, ?_⟩⟩
    intro hxU'
    exact hxUc ((by rw [heq]; exact ⟨hxU', hxV⟩ : x ∈ U ∩ V).1)
  rw [frontier_eq_closure_inter_closure]
  exact ⟨h1, h2⟩

/-- **The frontier of the union is inherited by a pair containing all the members through .**

If  is a frontier point of the union of a finite family and lies in the closure of the two members
, , then  is a frontier point of .  (The complement of the union is contained in
the complement of the pair.) -/
lemma mem_frontier_union_pair {ι : Type*} [Fintype ι] {B : ι → Set X} {i j : ι} {p : X}
    (hp : p ∈ frontier (⋃ k, B k)) (hpcl : p ∈ closure (B i) ∪ closure (B j)) :
    p ∈ frontier (B i ∪ B j) := by
  rw [frontier_eq_closure_inter_closure] at hp ⊢
  refine ⟨?_, ?_⟩
  · rwa [closure_union]
  · exact closure_mono (Set.compl_subset_compl.mpr (Set.union_subset
      (Set.subset_iUnion B i) (Set.subset_iUnion B j))) hp.2

section Pairwise

variable {ι : Type*} [Fintype ι] {B : ι → Set X}

/-- **Pairwise condition implies the condition for the union.**

If at most two members of a finite family of open sets meet any given point, and the union of any two
members satisfies the sector-or-ray condition at every point `p`, then so does the union of the whole
family at every frontier point.  The proof splits on whether `p` is in the closure of one or of two
members (if two, all the members meeting `p` are among them) and localises by
`hasSectorBoundary_of_inter_eq` / `hasRayBoundary_of_inter_eq`. -/
theorem sectorOrRay_of_pairwise (hBo : ∀ i, IsOpen (B i))
    (htwo : ∀ p : X, ∀ i j k : ι, p ∈ closure (B i) → p ∈ closure (B j) →
      p ∈ closure (B k) → i = j ∨ i = k ∨ j = k)
    (hpair : ∀ i j : ι, ∀ p ∈ frontier (B i ∪ B j),
      Work.SimplyConnected.ABS.HasSectorBoundary (B i ∪ B j) p ∨
      Work.SimplyConnected.ABS.HasRayBoundary (B i ∪ B j) p)
    {p : X} (hp : p ∈ frontier (⋃ i, B i)) :
    Work.SimplyConnected.ABS.HasSectorBoundary (⋃ i, B i) p ∨
    Work.SimplyConnected.ABS.HasRayBoundary (⋃ i, B i) p := by
  classical
  have hcleq : closure (⋃ i, B i) = ⋃ i, closure (B i) := closure_iUnion_of_finite B
  have hpcl : p ∈ ⋃ i, closure (B i) := by rw [← hcleq]; exact hp.1
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hpcl
  by_cases hsecond : ∃ j : ι, j ≠ i₀ ∧ p ∈ closure (B j)
  · obtain ⟨j₀, hj₀ne, hj₀cl⟩ := hsecond
    have hSsub : ∀ k : ι, p ∈ closure (B k) → k = i₀ ∨ k = j₀ := by
      intro k hk
      rcases htwo p i₀ j₀ k hi₀ hj₀cl hk with h | h | h
      · exact absurd h.symm hj₀ne
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    set s : Finset ι := Finset.univ.filter (fun k => k ≠ i₀ ∧ k ≠ j₀) with hsdef
    have hs_mem : ∀ k : ι, k ∈ s ↔ (k ≠ i₀ ∧ k ≠ j₀) := by
      intro k
      rw [hsdef, Finset.mem_filter]
      simp
    set V : Set X := (⋃ k ∈ (s : Set ι), closure (B k))ᶜ with hVdef
    have hVmem : ∀ x : X, x ∈ V ↔ ∀ k ∈ s, x ∉ closure (B k) := by
      intro x
      rw [hVdef, Set.mem_compl_iff, Set.mem_iUnion]
      simp
    have hVo : IsOpen V := by
      have hVeq : V = ⋂ k ∈ s, (closure (B k))ᶜ := by
        ext x
        rw [hVdef]
        simp [Set.mem_iUnion]
      rw [hVeq]
      exact isOpen_biInter_finset fun k _ => isClosed_closure.isOpen_compl
    have hpV : p ∈ V := by
      rw [hVmem]
      intro k hk hkcl
      obtain ⟨hk1, hk2⟩ := (hs_mem k).mp hk
      rcases hSsub k hkcl with h | h
      · exact hk1 h
      · exact hk2 h
    have heq : (⋃ i, B i) ∩ V = (B i₀ ∪ B j₀) ∩ V := by
      refine Subset.antisymm ?_ ?_
      · rintro x ⟨hxU, hxV⟩
        obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxU
        have hk : k = i₀ ∨ k = j₀ := by
          by_contra hcon
          push Not at hcon
          have hxcl : x ∈ closure (B k) := subset_closure hxk
          exact (hVmem x).mp hxV k ((hs_mem k).mpr ⟨hcon.1, hcon.2⟩) hxcl
        rcases hk with h | h
        · exact ⟨Or.inl (h ▸ hxk), hxV⟩
        · exact ⟨Or.inr (h ▸ hxk), hxV⟩
      · rintro x ⟨hxU', hxV⟩
        refine ⟨?_, hxV⟩
        rcases hxU' with h | h
        · exact Set.mem_iUnion.mpr ⟨i₀, h⟩
        · exact Set.mem_iUnion.mpr ⟨j₀, h⟩
    have hpcl2 : p ∈ closure (B i₀) ∪ closure (B j₀) := Or.inl hi₀
    have hpf : p ∈ frontier (B i₀ ∪ B j₀) := mem_frontier_union_pair hp hpcl2
    rcases hpair i₀ j₀ p hpf with h | h
    · exact Or.inl (Work.SimplyConnected.ABS.hasSectorBoundary_of_inter_eq hVo hpV heq h)
    · exact Or.inr (Work.SimplyConnected.ABS.hasRayBoundary_of_inter_eq hVo hpV heq h)
  · have huniq : ∀ k : ι, p ∈ closure (B k) → k = i₀ := by
      intro k hk
      by_contra hkne
      exact hsecond ⟨k, hkne, hk⟩
    set s : Finset ι := Finset.univ.filter (fun k => k ≠ i₀) with hsdef
    have hs_mem : ∀ k : ι, k ∈ s ↔ k ≠ i₀ := by
      intro k
      rw [hsdef, Finset.mem_filter]
      simp
    set V : Set X := (⋃ k ∈ (s : Set ι), closure (B k))ᶜ with hVdef
    have hVmem : ∀ x : X, x ∈ V ↔ ∀ k ∈ s, x ∉ closure (B k) := by
      intro x
      rw [hVdef, Set.mem_compl_iff, Set.mem_iUnion]
      simp
    have hVo : IsOpen V := by
      have hVeq : V = ⋂ k ∈ s, (closure (B k))ᶜ := by
        ext x
        rw [hVdef]
        simp [Set.mem_iUnion]
      rw [hVeq]
      exact isOpen_biInter_finset fun k _ => isClosed_closure.isOpen_compl
    have hpV : p ∈ V := by
      rw [hVmem]
      intro k hk hkcl
      exact (hs_mem k).mp hk (huniq k hkcl)
    have heq : (⋃ i, B i) ∩ V = (B i₀ ∪ B i₀) ∩ V := by
      refine Subset.antisymm ?_ ?_
      · rintro x ⟨hxU, hxV⟩
        obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxU
        have hk : k = i₀ := by
          by_contra hkne
          exact (hVmem x).mp hxV k ((hs_mem k).mpr hkne) (subset_closure hxk)
        exact ⟨Or.inl (hk ▸ hxk), hxV⟩
      · rintro x ⟨hxU', hxV⟩
        refine ⟨Set.mem_iUnion.mpr ⟨i₀, ?_⟩, hxV⟩
        rcases hxU' with h | h
        · exact h
        · exact h
    have hpcl2 : p ∈ closure (B i₀) ∪ closure (B i₀) := Or.inl hi₀
    have hpf : p ∈ frontier (B i₀ ∪ B i₀) := mem_frontier_union_pair hp hpcl2
    rcases hpair i₀ i₀ p hpf with h | h
    · exact Or.inl (Work.SimplyConnected.ABS.hasSectorBoundary_of_inter_eq hVo hpV heq h)
    · exact Or.inr (Work.SimplyConnected.ABS.hasRayBoundary_of_inter_eq hVo hpV heq h)

end Pairwise

/-- **Pairs of chart balls round in a common chart satisfy the pairwise condition.**  This is
`Work.SimplyConnected.ABS.hasSectorBoundary_or_hasRayBoundary_of_two_chartBall`, restated for the
`Submission.chartBall` API. -/
theorem pairwise_commonChart {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) {a a' : ℂ}
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hsub : Metric.closedBall a ρ ⊆ c.target) (hsub' : Metric.closedBall a' ρ' ⊆ c.target)
    {p : X} (hp : p ∈ frontier (Submission.chartBall c a ρ ∪ Submission.chartBall c a' ρ')) :
    Work.SimplyConnected.ABS.HasSectorBoundary
        (Submission.chartBall c a ρ ∪ Submission.chartBall c a' ρ') p ∨
      Work.SimplyConnected.ABS.HasRayBoundary
        (Submission.chartBall c a ρ ∪ Submission.chartBall c a' ρ') p := by
  have h1 : Submission.chartBall c a ρ = c.symm '' Metric.ball a ρ :=
    Work.SimplyConnected.ABS.chartBall_eq_image hsub
  have h2 : Submission.chartBall c a' ρ' = c.symm '' Metric.ball a' ρ' :=
    Work.SimplyConnected.ABS.chartBall_eq_image hsub'
  rw [h1, h2] at hp ⊢
  exact Work.SimplyConnected.ABS.hasSectorBoundary_or_hasRayBoundary_of_two_chartBall
    c hc hρ hρ' hsub hsub' p hp

/-- **A nested pair satisfies the pairwise condition** (the smaller member is irrelevant): if
`B' ⊆ B` and `B` satisfies the sector condition at `p`, then so does `B ∪ B'`. -/
theorem pairwise_of_subset {B B' : Set X} {p : X} (hsub : B' ⊆ B)
    (h : Work.SimplyConnected.ABS.HasSectorBoundary B p) :
    Work.SimplyConnected.ABS.HasSectorBoundary (B ∪ B') p ∨
      Work.SimplyConnected.ABS.HasRayBoundary (B ∪ B') p :=
  Or.inl (by rwa [Set.union_eq_left.mpr hsub])

/-- **The target from a finite family of chart balls with the pairwise frontier condition.**

If a finite family of chart balls has compact closures, a connected union covering `K ∪ {x₀}`, meets
each point of `X` in at most two members, and the union of any two members satisfies the
sector-or-ray condition at every point, then the target holds.  The two hypotheses on the family
that are *not* automatic are the two-member condition and the pairwise condition; for two balls
round in a common chart the latter is `pairwise_commonChart` (verified), and for nested pairs it is
`pairwise_of_subset`. -/
theorem exists_barrier_regular_precompact_region_of_ballFamily {K : Set X} (hX : ¬ CompactSpace X)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → OpenPartialHomeomorph X ℂ) (hc : ∀ i, c i ∈ atlas ℂ X)
    (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ (c i).target)
    (htwo : ∀ p : X, ∀ i j k : ι, p ∈ closure (Submission.chartBall (c i) (a i) (ρ i)) →
      p ∈ closure (Submission.chartBall (c j) (a j) (ρ j)) →
      p ∈ closure (Submission.chartBall (c k) (a k) (ρ k)) → i = j ∨ i = k ∨ j = k)
    (hpair : ∀ i j : ι,
      ∀ p ∈ frontier (Submission.chartBall (c i) (a i) (ρ i) ∪
        Submission.chartBall (c j) (a j) (ρ j)),
      Work.SimplyConnected.ABS.HasSectorBoundary
          (Submission.chartBall (c i) (a i) (ρ i) ∪ Submission.chartBall (c j) (a j) (ρ j)) p ∨
        Work.SimplyConnected.ABS.HasRayBoundary
          (Submission.chartBall (c i) (a i) (ρ i) ∪ Submission.chartBall (c j) (a j) (ρ j)) p)
    (hcov : K ∪ {x₀} ⊆ ⋃ i, Submission.chartBall (c i) (a i) (ρ i))
    (hconn : IsConnected (⋃ i, Submission.chartBall (c i) (a i) (ρ i))) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ∪ {x₀} ⊆ Ω ∧
      Ω ≠ Set.univ ∧
      (∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
        Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
        ContinuousOn u V ∧ u p = 0) := by
  set Ω : Set X := ⋃ i, Submission.chartBall (c i) (a i) (ρ i) with hΩdef
  have hΩo : IsOpen Ω := isOpen_iUnion fun i => Submission.chartBall_isOpen (c i) (a i) (ρ i)
  have hcompact : IsCompact (closure Ω) := by
    refine (isCompact_iUnion fun i =>
      Submission.isCompact_chartClosedBall (hsub i)).of_isClosed_subset isClosed_closure ?_
    rw [hΩdef, closure_iUnion_of_finite (fun i => Submission.chartBall (c i) (a i) (ρ i))]
    exact iUnion_mono fun i => Submission.closure_chartBall_subset_chartClosedBall (hsub i)
  refine ⟨Ω, hΩo, hconn, hcompact, hcov,
    ne_univ_of_isCompact_closure' (X := X) hX hcompact, ?_⟩
  refine barriers_of_sector_or_ray hΩo fun p hp => ?_
  exact sectorOrRay_of_pairwise (B := fun i => Submission.chartBall (c i) (a i) (ρ i))
    (fun i => Submission.chartBall_isOpen (c i) (a i) (ρ i)) htwo hpair
    (by rw [← hΩdef]; exact hp)

/-! ## The bookkeeping of `{ε < E} ∪ {x₀}`

The two lemmas below are the topological/level-set half of the *Green-function* route to the target
(the "hyperbolic" case): if `E` is continuous away from `x₀`, tends to `+∞` at `x₀`, and `E - ε` is
superharmonic on the superlevel set `{ε < E}`, then `Ω := {ε < E} ∪ {x₀}` carries barriers at all its
frontier points, with the single witness `u := E - ε` and `V := {x₀}ᶜ`. -/

/-- **A frontier point of a superlevel set realises the level.**  If `{x | ε < E x}` is open and `E`
is continuous at `p`, then every frontier point `p` of that superlevel set satisfies `E p = ε`. -/
lemma eq_of_mem_frontier_superlevel {E : X → ℝ} {ε : ℝ} (hopen : IsOpen {x : X | ε < E x})
    {p : X} (hcont : ContinuousAt E p) (hp : p ∈ frontier {x : X | ε < E x}) : E p = ε := by
  rw [frontier_eq_closure_inter_closure] at hp
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp (hopen.mem_nhds hcon)
    obtain ⟨y, hyO, hyc⟩ := (mem_closure_iff.mp hp.2) O hO hpO
    exact hyc (hOsub hyO)
  · by_contra hcon
    rw [not_le] at hcon
    have hEv : ∀ᶠ x in 𝓝 p, E x < ε := hcont.tendsto.eventually (isOpen_Iio.mem_nhds hcon)
    obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp hEv
    obtain ⟨y, hyO, hyS⟩ := (mem_closure_iff.mp hp.1) O hO hpO
    have hy : E y < ε := hOsub hyO
    have hy' : ε < E y := hyS
    exact absurd (le_of_lt hy') (not_le.mpr hy)

/-- **The barrier at a frontier point of `{ε < E} ∪ {x₀}`.**  The witness is `u := E - ε`,
`V := {x₀}ᶜ`: `E` is continuous on `V`, `u` is superharmonic on `{ε < E}`, and `u > 0` on
`{ε < E}` while `u p = 0` at every frontier point `p`. -/
lemma barrier_at_frontier_superlevel_union {E : X → ℝ} {ε : ℝ} {x₀ p : X}
    (hopen : IsOpen {x : X | ε < E x}) (hx₀ : ({x : X | ε < E x} ∪ {x₀}) ∈ 𝓝 x₀)
    (hcontE : ContinuousOn E ({x₀}ᶜ))
    (hsh : Submission.SuperharmonicOnX (fun x => E x - ε) {x : X | ε < E x})
    (hp : p ∈ frontier ({x : X | ε < E x} ∪ {x₀})) :
    ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (({x : X | ε < E x} ∪ {x₀}) ∩ V) ∧
      (∀ x ∈ ({x : X | ε < E x} ∪ {x₀}) ∩ V, 0 < u x) ∧ ContinuousOn u V ∧ u p = 0 := by
  rw [frontier_eq_closure_inter_closure] at hp
  -- `p ≠ x₀` (a neighbourhood of `x₀` lies in the superlevel set, so `x₀` is interior)
  have hpne : p ≠ x₀ := by
    intro hpx
    subst hpx
    obtain ⟨O, hOsub, hO, hx₀O⟩ := mem_nhds_iff.mp hx₀
    obtain ⟨y, hyO, hyc⟩ := (mem_closure_iff.mp hp.2) O hO hx₀O
    exact hyc (hOsub hyO)
  -- hence `p` is a frontier point of the superlevel set itself
  have hpS : p ∈ frontier {x : X | ε < E x} := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨?_, ?_⟩
    · rw [closure_union, closure_singleton] at hp
      rcases hp.1 with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hpne
    · exact closure_mono (Set.compl_subset_compl.mpr Set.subset_union_left) hp.2
  have hpE : E p = ε :=
    eq_of_mem_frontier_superlevel hopen
      (hcontE.continuousAt (isOpen_compl_singleton.mem_nhds (by simpa using hpne))) hpS
  -- the containment `({ε < E} ∪ {x₀}) ∩ {x₀}ᶜ ⊆ {ε < E}`
  have hsub : ({x : X | ε < E x} ∪ {x₀}) ∩ {x₀}ᶜ ⊆ {x : X | ε < E x} := by
    rintro x ⟨hx1, hx2⟩
    rcases hx1 with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.mp h) hx2
  refine ⟨fun x => E x - ε, {x₀}ᶜ, isOpen_compl_singleton, by simpa using hpne, ?_, ?_, ?_, ?_⟩
  · exact hsh.mono hsub ((hcontE.sub continuousOn_const).mono Set.inter_subset_right)
  · rintro x ⟨hx1, hx2⟩
    have hxS : ε < E x := by
      rcases hx1 with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hx2
    exact sub_pos.mpr hxS
  · exact hcontE.sub continuousOn_const
  · exact sub_eq_zero.mpr hpE

/-! ## Crossing of two chart balls: the free-direction lemma

Let `B₁ = φ.symm '' ball a ρ` and `B₂ = ψ.symm '' ball b σ` be round balls in two charts of the
atlas of a Riemann surface, and let `p` be a point of both sources lying on both spheres.  Write
`w₀ = φ p`, `A = ψ p - b` and `D = deriv (ψ ∘ φ.symm) w₀`.  In the chart `φ` the *outward normal
functionals* of the two balls at `p` are

  `N₁ u = Re (conj (w₀ - a) * u)`,  `N₂ u = Re (conj A * D * u)`.

If the two have a **common positive direction**, i.e. `N i v > 0` for some `v` — equivalently: the
two normals are not opposite, i.e. the two balls cross *transversally* at `p` — then `p` is a
*sector* boundary point of the union.

The proof takes a thin cone of directions around `v` on which both `N₁` and `N₂` dominate a multiple
of the norm (the elementary lemma `exists_cone_of_two_positive`), and shows that the union misses
that cone near `p`: for `B₁` this is exact (`‖u + (w₀ - a)‖ ^ 2 - ρ ^ 2 = ‖u‖ ^ 2 + 2 * N₁ u`),
while for `B₂` the quadratic Taylor remainder of the analytic transition is absorbed by the linear
term. -/

/-! ## Crossing of two chart balls: the free-direction lemma

Let `B₁ = φ.symm '' ball a ρ` and `B₂ = ψ.symm '' ball b σ` be round balls in two charts of the
atlas of a Riemann surface, and let `p` be a point of both sources lying on both spheres.  Write
`w₀ = φ p`, `A = ψ p - b` and `D = deriv (ψ ∘ φ.symm) w₀`.  In the chart `φ` the *outward normal
functionals* of the two balls at `p` are

  `N₁ u = Re (conj (w₀ - a) * u)`,  `N₂ u = Re (conj A * D * u)`.

If the two have a **common positive direction**, i.e. `N i v > 0` for some `v` — equivalently: the
two normals are not opposite, i.e. the two balls cross *transversally* at `p` rather than being
externally tangent — then `p` is a *sector* boundary point of the union.

The proof takes a thin cone of directions around `v` on which both `N₁` and `N₂` dominate a multiple
of the norm (the elementary lemma `exists_cone_of_two_positive`), and shows that the union misses
that cone near `p`: for `B₁` this is exact (`‖u + (w₀ - a)‖ ^ 2 - ρ ^ 2 = ‖u‖ ^ 2 + 2 * N₁ u`),
while for `B₂` the quadratic Taylor remainder of the analytic transition is absorbed by the linear
term. -/

/-! ## Crossing of two chart balls: the free-direction lemma

Let `B₁ = φ.symm '' ball a ρ` and `B₂ = ψ.symm '' ball b σ` be round balls in two charts of the
atlas of a Riemann surface, and let `p` be a point of both sources lying on both spheres.  Write
`w₀ = φ p`, `A = ψ p - b` and `D = deriv (ψ ∘ φ.symm) w₀`.  In the chart `φ` the *outward normal
functionals* of the two balls at `p` are

  `N₁ u = Re (conj (w₀ - a) * u)`,  `N₂ u = Re (conj A * D * u)`.

If the two have a **common positive direction**, i.e. `N i v > 0` for some `v` — equivalently: the
two normals are not opposite, i.e. the two balls cross *transversally* at `p` rather than being
externally tangent — then `p` is a *sector* boundary point of the union.

The proof takes a thin cone of directions around `v` on which both `N₁` and `N₂` dominate a multiple
of the norm (the elementary lemma `exists_cone_of_two_positive`), and shows that the union misses
that cone near `p`: for `B₁` this is exact (`‖u + (w₀ - a)‖ ^ 2 - ρ ^ 2 = ‖u‖ ^ 2 + 2 * N₁ u`),
while for `B₂` the quadratic Taylor remainder of the analytic transition is absorbed by the linear
term. -/

/-! ## Crossing of two chart balls: the free-direction lemma

Let `B₁ = φ.symm '' ball a ρ` and `B₂ = ψ.symm '' ball b σ` be round balls in two charts of the
atlas of a Riemann surface, and let `p` be a point of both sources lying on both spheres.  Write
`w₀ = φ p`, `A = ψ p - b` and `D = deriv (ψ ∘ φ.symm) w₀`.  In the chart `φ` the *outward normal
functionals* of the two balls at `p` are

  `N₁ u = Re (conj (w₀ - a) * u)`,  `N₂ u = Re (conj A * D * u)`.

If the two have a **common positive direction**, i.e. `N i v > 0` for some `v` — equivalently: the
two normals are not opposite, i.e. the two balls cross *transversally* at `p` rather than being
externally tangent — then `p` is a *sector* boundary point of the union.

The proof takes a thin cone of directions around `v` on which both `N₁` and `N₂` dominate a multiple
of the norm (the elementary lemma `exists_cone_of_two_positive`), and shows that the union misses
that cone near `p`: for `B₁` this is exact (`‖u + (w₀ - a)‖ ^ 2 - ρ ^ 2 = ‖u‖ ^ 2 + 2 * N₁ u`),
while for `B₂` the quadratic Taylor remainder of the analytic transition is absorbed by the linear
term. -/

/-! ## Crossing of two chart balls: the free-direction lemma

Let `B₁ = φ.symm '' ball a ρ` and `B₂ = ψ.symm '' ball b σ` be round balls in two charts of the
atlas of a Riemann surface, and let `p` be a point of both sources lying on both spheres.  Write
`w₀ = φ p`, `A = ψ p - b` and `D = deriv (ψ ∘ φ.symm) w₀`.  In the chart `φ` the *outward normal
functionals* of the two balls at `p` are

  `N₁ u = Re (conj (w₀ - a) * u)`,  `N₂ u = Re (conj A * D * u)`.

If the two have a **common positive direction**, i.e. `N i v > 0` for some `v` — equivalently: the
two normals are not opposite, i.e. the two balls cross *transversally* at `p` rather than being
externally tangent — then `p` is a *sector* boundary point of the union.

The proof takes a thin cone of directions around `v` on which both `N₁` and `N₂` dominate a multiple
of the norm (the elementary lemma `exists_cone_of_two_positive`), and shows that the union misses
that cone near `p`: for `B₁` this is exact (`‖u + (w₀ - a)‖ ^ 2 - ρ ^ 2 = ‖u‖ ^ 2 + 2 * N₁ u`),
while for `B₂` the quadratic Taylor remainder of the analytic transition is absorbed by the linear
term. -/

/-! ## Crossing of two chart balls: the free-direction lemma

Let `B₁ = φ.symm '' ball a ρ` and `B₂ = ψ.symm '' ball b σ` be round balls in two charts of the
atlas of a Riemann surface, and let `p` be a point of both sources lying on both spheres.  Write
`w₀ = φ p`, `A = ψ p - b` and `D = deriv (ψ ∘ φ.symm) w₀`.  In the chart `φ` the *outward normal
functionals* of the two balls at `p` are

  `N₁ u = Re (conj (w₀ - a) * u)`,  `N₂ u = Re (conj A * D * u)`.

If the two have a **common positive direction**, i.e. `N i v > 0` for some `v` — equivalently: the
two normals are not opposite, i.e. the two balls cross *transversally* at `p` rather than being
externally tangent — then `p` is a *sector* boundary point of the union.

The proof takes a thin cone of directions around `v` on which both `N₁` and `N₂` dominate a multiple
of the norm (the elementary lemma `exists_cone_of_two_positive`), and shows that the union misses
that cone near `p`: for `B₁` this is exact (`‖u + (w₀ - a)‖ ^ 2 - ρ ^ 2 = ‖u‖ ^ 2 + 2 * N₁ u`),
while for `B₂` the quadratic Taylor remainder of the analytic transition is absorbed by the linear
term. -/

/-! ## Crossing of two chart balls: the free-direction lemma

Let `B₁ = φ.symm '' ball a ρ` and `B₂ = ψ.symm '' ball b σ` be round balls in two charts of the
atlas of a Riemann surface, and let `p` be a point of both sources lying on both spheres.  Write
`w₀ = φ p`, `A = ψ p - b` and `D = deriv (ψ ∘ φ.symm) w₀`.  In the chart `φ` the *outward normal
functionals* of the two balls at `p` are

  `N₁ u = Re (conj (w₀ - a) * u)`,  `N₂ u = Re (conj A * D * u)`.

If the two have a **common positive direction**, i.e. `N i v > 0` for some `v` — equivalently: the
two normals are not opposite, i.e. the two balls cross *transversally* at `p` rather than being
externally tangent — then `p` is a *sector* boundary point of the union.

The proof takes a thin cone of directions around `v` on which both `N₁` and `N₂` dominate a multiple
of the norm (the elementary lemma `exists_cone_of_two_positive`), and shows that the union misses
that cone near `p`: for `B₁` this is exact (`‖u + (w₀ - a)‖ ^ 2 - ρ ^ 2 = ‖u‖ ^ 2 + 2 * N₁ u`),
while for `B₂` the quadratic Taylor remainder of the analytic transition is absorbed by the linear
term. -/


/-! ## The remaining geometric input: a family of chart balls with a free direction

Everything is now reduced to the following clean statement, which is the geometric core of the
construction of the region.  It is the finite-family version of the classical fact that a compact
region with a *smooth* boundary can be covered by round chart balls in general position: the
condition demanded below is exactly the *free direction* hypothesis of the local sector theorem
hasSectorBoundary_iUnion_chartBall_of_freeDirection, so that no two ball boundaries are allowed
to be tangent and no point of the closed union outside the open union may be surrounded. -/

theorem exists_barrier_regular_precompact_region {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) (x₀ : X) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ∪ {x₀} ⊆ Ω ∧
      Ω ≠ Set.univ ∧
      (∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
        Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
        ContinuousOn u V ∧ u p = 0) := by
  -- the smooth exhaustion function of the ABS construction
  obtain ⟨g, hgsm, -, hgcomp⟩ :=
    Work.SimplyConnected.ABS.OneEnded.exists_contMDiff_sublevel_compact (X := X) hX
  have hgc : Continuous g := hgsm.continuous
  -- a level whose component contains `K ∪ {x₀}`
  obtain ⟨C₀, hC₀⟩ := exists_component_sublevel_supset (X := X) (g := g) hgc hK x₀
  -- a level in `(C₀, C₀ + 1]` which is not a critical value on `{g ≤ C₀ + 1}`
  obtain ⟨C, hCgt, hCle, hCreg⟩ := exists_regular_level_of_contMDiff (X := X) hgsm
    (K := {x : X | g x ≤ C₀ + 1}) (hgcomp (C₀ + 1)) x₀ (C₀ := C₀)
  have hreg : ∀ p : X, g p = C →
      DifferentiableAt ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ∧
      fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0 :=
    fun p hp => hCreg p (by show g p ≤ C₀ + 1; rw [hp]; exact hCle) hp
  have hsub : K ∪ {x₀} ⊆ connectedComponentIn {x : X | g x < C} x₀ :=
    hC₀.trans (connectedComponentIn_mono x₀ fun y hy => lt_trans hy hCgt)
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hUo : IsOpen {x : X | g x < C} := isOpen_lt hgc continuous_const
  have hcl : closure (connectedComponentIn {x : X | g x < C} x₀) ⊆ {x : X | g x ≤ C} :=
    closure_minimal (fun y hy => show g y ≤ C from
      le_of_lt (connectedComponentIn_subset {x : X | g x < C} x₀ hy))
      (isClosed_le hgc continuous_const)
  have hcompcl : IsCompact (closure (connectedComponentIn {x : X | g x < C} x₀)) :=
    (hgcomp C).of_isClosed_subset isClosed_closure hcl
  refine ⟨connectedComponentIn {x : X | g x < C} x₀, hUo.connectedComponentIn,
    ⟨⟨x₀, hsub (Or.inr rfl)⟩, isPreconnected_connectedComponentIn⟩, hcompcl, hsub,
    ne_univ_of_isCompact_closure' hX hcompcl, ?_⟩
  refine barriers_of_sector_or_ray hUo.connectedComponentIn fun p hp => Or.inl ?_
  have hpC : g p = C :=
    Work.SimplyConnected.ABS.eq_of_mem_frontier_connectedComponentIn hgc (hsub (Or.inr rfl)) hp
  refine hasSectorBoundary_of_local_sublevel' (u := g) (hreg p hpC).1.hasFDerivAt
    (hreg p hpC).2 (Filter.Eventually.of_forall fun y hy => ?_)
  rw [hpC]
  exact not_lt.mpr (le_of_lt (connectedComponentIn_subset {x : X | g x < C} x₀ hy))

end Work.SimplyConnected.ABS.green_reduction
