import Mathlib
import ChallengeDeps
import Submission.Torus1Chart

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology
set_option linter.style.haveILetI false

/-!
# Layer A (xix) — the zero set is a locally path-connected 1-manifold

`Torus1Chart.lean` proved that every point of the trisecant zero set of a
general-position smooth knot has a bundled **1-chart**: an open torus
neighbourhood `V` of the point `p` and a homeomorphism of an open parameter
interval onto the trace `Z ∩ V` of the zero set (sending the base parameter
to `p`).  This module draws the first *global* consequences of that local
1-manifold structure — Milestone-2 part (i):

1. **openness in the zero-set subspace** — `zeroSet_open_iff`: the open
   subsets of `ZeroSetPoint r` (= the trisecant zero set as a subspace of
   the parameter torus) are exactly the traces of the open sets of the
   torus;
2. **`zeroSet_local_pathConnected_nhds`** — inside every open neighbourhood
   `u` of a zero-set point `z` there is an *open path-connected*
   neighbourhood `U` of `z` (`U ⊆ u`): a chart interval-cell
   `U = chartLift c '' {x : interval | x near x₀}` — the image of a small
   open interval of chart parameters under the chart lift (which is open in
   the zero-set subspace because the chart homeomorphism is open and the
   projection of the chart trace onto the zero set is the inclusion of an
   open subset);
3. **`zeroSet_locallyPathConnected`** — the trisecant zero set of a
   general-position smooth knot is a `LocallyPathConnectedSpace` (each
   point has a basis of path-connected neighbourhoods);
4. **component structure** — `zeroSet_component_open`,
   `zeroSet_component_pathConnected`,
   `zeroSet_component_eq_pathComponent`: the connected components of the
   zero set are open, path-connected, and coincide with the path
   components — the standard consequences of local path-connectedness.

These facts give Milestone 2 its first global claim: *the trisecant zero
set is a topological 1-manifold whose connected components are open
path-connected pieces*, on top of which the component/path-following
machinery of `TorusPathFollow.lean`/`ZeroSetPath.lean` operates.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-! ## 1. Open subsets of the zero-set subspace -/

/-- Points of the zero set lying in the torus-open set `V` (the chart
codomain type of `ZeroSet1Chart`, i.e. `{q | q ∈ Z ∧ q ∈ V}`). -/
abbrev ZeroSetChartDomain (r : ℝ → Space) (V : Set KnotParamTriple) : Type :=
  {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ V}

/-- Open subsets of the chart domain are traces of torus-open sets. -/
lemma zeroSetChartDomain_open_iff {r : ℝ → Space} {V : Set KnotParamTriple}
    {O : Set (ZeroSetChartDomain r V)} :
    IsOpen O ↔ ∃ W : Set KnotParamTriple, IsOpen W ∧
      O = (fun q : ZeroSetChartDomain r V => (q : KnotParamTriple)) ⁻¹' W := by
  have hiff := (Topology.IsInducing.subtypeVal (Y := KnotParamTriple)
    (t := {q : KnotParamTriple | q ∈ trisecantZeroSet r ∧ q ∈ V})).isOpen_iff (s := O)
  constructor
  · intro hO
    rcases hiff.mp hO with ⟨W, hWo, hW⟩
    exact ⟨W, hWo, hW.symm⟩
  · rintro ⟨W, hWo, hW⟩
    exact hiff.mpr ⟨W, hWo, hW.symm⟩

/-- Open subsets of the zero-set subspace are traces of torus-open sets. -/
lemma zeroSet_open_iff {r : ℝ → Space} {U : Set (ZeroSetPoint r)} :
    IsOpen U ↔ ∃ V : Set KnotParamTriple, IsOpen V ∧
      U = (fun z : ZeroSetPoint r => (z : KnotParamTriple)) ⁻¹' V := by
  have hiff := (Topology.IsInducing.subtypeVal (Y := KnotParamTriple)
    (t := trisecantZeroSet r)).isOpen_iff (s := U)
  constructor
  · intro hU
    rcases hiff.mp hU with ⟨V, hVo, hV⟩
    exact ⟨V, hVo, hV.symm⟩
  · rintro ⟨V, hVo, hV⟩
    exact hiff.mpr ⟨V, hVo, hV.symm⟩

/-- The trace of a torus-open set is open in the zero-set subspace. -/
lemma isOpen_zeroSet_trace {r : ℝ → Space} {V : Set KnotParamTriple} (hVo : IsOpen V) :
    IsOpen {z : ZeroSetPoint r | (z : KnotParamTriple) ∈ V} :=
  hVo.preimage continuous_subtype_val

/-! ## 2. The projection from the chart domain onto the zero set is open -/

/-- The projection from the chart domain `{q | q ∈ Z ∧ q ∈ V}` onto the
zero-set subspace (dropping the `V`-membership). -/
def zeroSetChartProj (r : ℝ → Space) (V : Set KnotParamTriple) :
    ZeroSetChartDomain r V → ZeroSetPoint r :=
  fun q => ⟨q.1, q.2.1⟩

/-- The projection preserves the torus value. -/
lemma zeroSetChartProj_val {r : ℝ → Space} {V : Set KnotParamTriple}
    (q : ZeroSetChartDomain r V) :
    (zeroSetChartProj r V q : KnotParamTriple) = (q : KnotParamTriple) := rfl

/-- **The projection is an open map**: the chart domain is the trace of the
torus-open set `V` inside the zero set, so its open subsets project to
open subsets of the zero set. -/
lemma zeroSetChartProj_open {r : ℝ → Space} {V : Set KnotParamTriple} (hVo : IsOpen V)
    {O : Set (ZeroSetChartDomain r V)} (hO : IsOpen O) :
    IsOpen (zeroSetChartProj r V '' O) := by
  rcases (zeroSetChartDomain_open_iff.mp hO) with ⟨W, hWo, hW⟩
  rw [show zeroSetChartProj r V '' O = {z : ZeroSetPoint r | (z : KnotParamTriple) ∈ W ∩ V} by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqW : (q : KnotParamTriple) ∈ W := by simpa [hW] using hq
      exact ⟨hqW, q.2.2⟩
    · intro hz
      refine ⟨⟨(z : KnotParamTriple), z.2, hz.2⟩, ?_, ?_⟩
      · simpa [hW] using hz.1
      · apply Subtype.ext
        rfl]
  exact (hWo.inter hVo).preimage continuous_subtype_val

/-! ## 3. The chart-lift image of a small parameter interval is an open
path-connected neighbourhood -/

/-- Membership in a small real interval around `x₀` implies membership in
the ε-ball around `x₀`. -/
lemma mem_ball_of_mem_Ioo {x₀ ε : ℝ} {x : ℝ} (hx : x ∈ Set.Ioo (x₀ - ε) (x₀ + ε)) :
    x ∈ Metric.ball x₀ ε := by
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  have hx1 : x₀ - ε < x := hx.1
  have hx2 : x < x₀ + ε := hx.2
  constructor <;> linarith

/-- **Every open neighbourhood of a zero-set point contains an open
path-connected neighbourhood**: the local 1-chart homeomorphism transfers
an open subinterval of chart parameters around the base point, and the
projection of the chart trace onto the zero set is open. -/
theorem zeroSet_local_pathConnected_nhds {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (z : ZeroSetPoint r)
    (u : Set (ZeroSetPoint r)) (hu : IsOpen u) (hz : z ∈ u) :
    ∃ U : Set (ZeroSetPoint r), IsOpen U ∧ z ∈ U ∧ U ⊆ u ∧ IsPathConnected U := by
  rcases zeroSet_open_iff.mp hu with ⟨V, hVo, hV⟩
  -- a chart at the point
  let p : KnotParamTriple := (z : KnotParamTriple)
  let c := Classical.choice (zeroSet1Chart_at_general_position h hgp p z.2)
  have hpV : p ∈ V := by
    have : (z : KnotParamTriple) ∈ V := by simpa [hV] using hz
    simpa [p] using this
  -- the pullback of V into the parameter interval (chart points lying in V)
  let S : Set (ChartInterval c.lo c.hi) :=
    {x : ChartInterval c.lo c.hi | ((c.homeo x) : KnotParamTriple) ∈ V}
  have hSc : Continuous (fun x : ChartInterval c.lo c.hi => ((c.homeo x) : KnotParamTriple)) := by
    exact continuous_subtype_val.comp c.homeo.continuous
  have hS : IsOpen S := by
    refine hVo.preimage hSc
  have hx₀S : ⟨c.x₀, c.x₀_mem⟩ ∈ S := by
    dsimp [S]
    rw [c.base]
    exact hpV
  -- val is an open embedding of the chart interval into ℝ
  have hOE : Topology.IsOpenEmbedding (fun x : ChartInterval c.lo c.hi => (x : ℝ)) := by
    change Topology.IsOpenEmbedding (Subtype.val : {x : ℝ // x ∈ Set.Ioo c.lo c.hi} → ℝ)
    exact (isOpen_Ioo : IsOpen (Set.Ioo c.lo c.hi)).isOpenEmbedding_subtypeVal
  -- the image of S in ℝ is an open neighbourhood of x₀
  let Sℝ : Set ℝ := (fun x : ChartInterval c.lo c.hi => (x : ℝ)) '' S
  have hSℝ_open : IsOpen Sℝ := (hOE.isOpenMap (U := S)) hS
  have hx₀Sℝ : c.x₀ ∈ Sℝ := by
    dsimp [Sℝ]
    exact ⟨⟨c.x₀, c.x₀_mem⟩, hx₀S, rfl⟩
  -- an ε-ball around x₀ inside Sℝ
  have hball : ∃ ε : ℝ, 0 < ε ∧ Metric.ball c.x₀ ε ⊆ Sℝ := by
    exact Metric.mem_nhds_iff.mp (hSℝ_open.mem_nhds hx₀Sℝ)
  rcases hball with ⟨ε, hε, hball_sub⟩
  let cell : Set (ChartInterval c.lo c.hi) :=
    {x : ChartInterval c.lo c.hi | (x : ℝ) ∈ Set.Ioo (c.x₀ - ε) (c.x₀ + ε)}
  -- cells are inside S (their chart points lie in V)
  have hcell_sub_S : cell ⊆ S := by
    intro x hx
    have hxv : (x : ℝ) ∈ Sℝ := by
      have hxball : (x : ℝ) ∈ Metric.ball c.x₀ ε := mem_ball_of_mem_Ioo hx
      exact hball_sub hxball
    rcases hxv with ⟨y, hyS, hyv⟩
    have hyx : y = x := Subtype.ext hyv
    simpa [hyx] using hyS
  -- cells are path-connected
  have hcell_pc : IsPathConnected cell := by
    have hiff := (Topology.IsInducing.subtypeVal (Y := ℝ)
      (t := Set.Ioo c.lo c.hi)).isPathConnected_iff (F := cell)
    rw [hiff]
    -- the val-image of the cell is the real interval (x₀−ε, x₀+ε)
    have himg : (fun x : ChartInterval c.lo c.hi => (x : ℝ)) '' cell = Set.Ioo (c.x₀ - ε) (c.x₀ + ε) := by
      ext t
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro ht
        have ht_in_lo_hi : t ∈ Set.Ioo c.lo c.hi := by
          -- t ∈ (x₀−ε,x₀+ε) ⊆ ball x₀ ε ⊆ Sℝ ⊆ (c.lo,c.hi)
          have htv : t ∈ Sℝ := hball_sub (mem_ball_of_mem_Ioo ht)
          rcases htv with ⟨y, _hyS, hyv⟩
          have hyv' : (y : ℝ) = t := hyv
          rw [← hyv']
          exact y.2
        refine ⟨⟨t, ht_in_lo_hi⟩, ht, rfl⟩
    rw [himg]
    exact (IsOpen.isConnected_iff_isPathConnected (isOpen_Ioo : IsOpen (Set.Ioo (c.x₀ - ε) (c.x₀ + ε)))).mp
      (isConnected_Ioo (by linarith))
  -- the candidate neighbourhood U: the chart lift of the cell
  let U : Set (ZeroSetPoint r) := chartLift c '' cell
  have hU_open : IsOpen U := by
    dsimp [U]
    have hcl : (fun x : ChartInterval c.lo c.hi => chartLift c x) =
        zeroSetChartProj r c.V ∘ (c.homeo : ChartInterval c.lo c.hi ≃ₜ ZeroSetChartDomain r c.V) := by
      funext x
      rfl
    have hUeq : (fun x : ChartInterval c.lo c.hi => chartLift c x) '' cell =
        zeroSetChartProj r c.V '' ((c.homeo : ChartInterval c.lo c.hi ≃ₜ ZeroSetChartDomain r c.V) '' cell) := by
      rw [hcl, Set.image_comp]
    rw [hUeq]
    have hcell_open : IsOpen cell := by
      refine (isOpen_Ioo : IsOpen (Set.Ioo (c.x₀ - ε) (c.x₀ + ε))).preimage continuous_subtype_val
    have hhomeo_open : IsOpen ((c.homeo : ChartInterval c.lo c.hi ≃ₜ ZeroSetChartDomain r c.V) '' cell) := by
      exact (c.homeo.isOpen_image).mpr hcell_open
    exact zeroSetChartProj_open (V := c.V) (hVo := c.V_open) hhomeo_open
  have hzU : z ∈ U := by
    dsimp [U]
    use ⟨c.x₀, c.x₀_mem⟩
    constructor
    · dsimp [cell]
      constructor <;> linarith
    · apply Subtype.ext
      change (c.homeo ⟨c.x₀, c.x₀_mem⟩).1 = (z : KnotParamTriple)
      rw [c.base]
  have hU_sub : U ⊆ u := by
    intro w hw
    rw [hV]
    rcases hw with ⟨x, hx, rfl⟩
    have hxS : x ∈ S := hcell_sub_S hx
    dsimp [S] at hxS
    exact hxS
  have hU_pc : IsPathConnected U := by
    dsimp [U]
    exact hcell_pc.image (continuous_chartLift c)
  exact ⟨U, hU_open, hzU, hU_sub, hU_pc⟩

/-! ## 4. Local path-connectedness and the component structure -/

/-- **The trisecant zero set of a general-position smooth knot is locally
path-connected.** -/
theorem zeroSet_locallyPathConnected {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) : LocallyPathConnectedSpace (ZeroSetPoint r) := by
  refine { path_connected_basis := fun z => ?_ }
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    rcases mem_nhds_iff.mp ht with ⟨u, hut, hu, hzu⟩
    rcases zeroSet_local_pathConnected_nhds h hgp z u hu hzu with ⟨U, hUo, hzU, hUu, hUc⟩
    exact ⟨U, ⟨hUo.mem_nhds hzU, hUc⟩, hUu.trans hut⟩
  · rintro ⟨s, ⟨hsN, hsC⟩, hst⟩
    exact Filter.mem_of_superset hsN hst

/-- **The connected components of the zero set are open** (local
path-connectedness, hence local connectedness). -/
theorem zeroSet_component_open {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (z : ZeroSetPoint r) :
    IsOpen (connectedComponent z) := by
  letI : LocallyPathConnectedSpace (ZeroSetPoint r) := zeroSet_locallyPathConnected h hgp
  exact isOpen_connectedComponent

/-- **The connected components of the zero set are path-connected** (they
coincide with the path components). -/
theorem zeroSet_component_pathConnected {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (z : ZeroSetPoint r) :
    IsPathConnected (connectedComponent z) := by
  letI : LocallyPathConnectedSpace (ZeroSetPoint r) := zeroSet_locallyPathConnected h hgp
  rw [← pathComponent_eq_connectedComponent]
  exact isPathConnected_pathComponent

/-- **In the zero set, the connected components are the path components.**
-/
theorem zeroSet_component_eq_pathComponent {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (z : ZeroSetPoint r) :
    connectedComponent z = pathComponent z := by
  letI : LocallyPathConnectedSpace (ZeroSetPoint r) := zeroSet_locallyPathConnected h hgp
  exact (pathComponent_eq_connectedComponent z).symm
/-- **Each connected component of the zero set, as a subspace, is a
path-connected space** (the type-level form of
`zeroSet_component_pathConnected`). -/
theorem zeroSet_component_pathConnectedSpace {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (z : ZeroSetPoint r) :
    PathConnectedSpace (connectedComponent z) :=
  (isPathConnected_iff_pathConnectedSpace).mp (zeroSet_component_pathConnected h hgp z)

/-- **Connected open subsets of the zero set are path-connected** (the
local path-connectedness in open-subset form, needed when analysing the
trace of a single component). -/
theorem zeroSet_open_isConnected_iff_isPathConnected {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) {U : Set (ZeroSetPoint r)} (hU : IsOpen U) :
    IsConnected U ↔ IsPathConnected U := by
  letI : LocallyPathConnectedSpace (ZeroSetPoint r) := zeroSet_locallyPathConnected h hgp
  exact (IsOpen.isConnected_iff_isPathConnected hU)

end LeanEval.KnotTheory.Quadrisecant
