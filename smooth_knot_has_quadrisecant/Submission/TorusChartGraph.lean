import Mathlib
import ChallengeDeps
import Submission.LocalCurve
import Submission.TorusCharts

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

/-!
# Layer A (x) — graph coordinates of the local trisecant arc, and no re-entry

The overlap lemma (`TorusCharts.lean`, `torus_arc_overlap`) shows that the
local torus arcs agree *as sets* on their overlaps, but the chart records
`TorusArcData` still hide the *parametrisation*: the underlying real local
curves of Milestone 1 (`LocalCurve.lean`,
`trisecantLocalCurve_of_splitData`) are produced by the implicit function
theorem in **graph form**: the split of the parameter cube
`E = E₁ × E₂` with `E₁ = ℝ` (the remaining coordinate of the rank-two
witness pair) gives

    γ(x) = A (x, ψ(x))     (x ∈ an open interval around u.1),

where `A : E₁ × E₂ ≃ ℝ³` is the (explicit) split homeomorphism and
`ψ : ℝ → E₂` is the `C¹` implicit function (`ψ(u.1) = u.2`,
`red(A(x,ψ(x))) = 0`).  The first coordinate of `B(q) = A⁻¹(q)` is then a
*monotone curve coordinate* on the arc: `(B(γ(x))).1 = x`.

This module packages that graph structure as the record `RealGraphArc` and
proves the two statements that bridge from the local curves to the honest
charts of the 1-manifold theory:

1. **graph-coordinate lemma** (`RealGraphArc.graph_coordinate`): the local
   curve is presented in graph coordinates `γ(x) = A(x, ψ(x))`, it is
   injective (each `x`-slice `{(B q).1 = x}` meets the arc in at most one
   point, `RealGraphArc.injOn_g`), and the first split coordinate is a
   monotone parameter along the arc (`RealGraphArc.coord`, `_coord_eq`);
2. **no re-entry / trace lemma** (`RealGraphArc.trace_eq_zeroSet_of_box`,
   `RealGraphArc.arc_closed_embedding`): inside a *graph-adapted box*
   (`x ∈ [α,β]`, `B q ∈ W` — i.e. within the slice over an `x`-interval and
   the `ψ`-covering neighbourhood `W` of the IFT) the trisecant zero set is
   *exactly* the image of the arc over `[α,β]` — the arc does not re-enter
   such a box (its trace is the whole local zero set there) — and the arc
   over the compact interval is a **closed embedding** (homeomorphism onto
   its image; the image is compact, hence closed) with explicit continuous
   inverse `q ↦ (B q).1`.

The record fields are precisely the data that the product-domain implicit
function theorem produces on a small interval (see `LocalCurve.lean`); a
later module instantiates `RealGraphArc` at every general-position collinear
off-diagonal triple of a smooth knot (the three split instances
`splitAB`/`splitAM`/`splitBM` of `LocalCurve.lean`), transporting these
results to the torus charts of `TorusCharts.lean`.  Everything here is
elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- **Graph coordinates of the local trisecant arc.**  A record carrying:
- the split homeomorphism `A : E₁ × E₂ ≃ ℝ³` (`E₁ = ℝ`, `E₂ = ℝ × ℝ`) with
  inverse `B`, and the base split point `u` (so `p₀ = A u` is the base
  triple);
- the implicit function `ψ` with `ψ u.1 = u.2`, `C¹` on the open interval
  `(a,b) ∋ u.1`;
- on `(a,b)` the graph `γ(x) = A(x, ψ(x))` lies in the off-diagonal
  collinearity zero set and inside the `ψ`-covering neighbourhood `W`;
- the covering property (`cover`): every collinear off-diagonal zero `A z`
  with `z ∈ W` and `z.1 ∈ (a,b)` sits on the graph:
  `ψ(z.1) = z.2`, hence `A z = A(z.1, ψ(z.1))`. -/
structure RealGraphArc (r : ℝ → Space) where
  A : ℝ × (ℝ × ℝ) → RealParamTriple
  B : RealParamTriple → ℝ × (ℝ × ℝ)
  A_cont : Continuous A
  B_cont : Continuous B
  AB : ∀ z : ℝ × (ℝ × ℝ), B (A z) = z
  BA : ∀ q : RealParamTriple, A (B q) = q
  u : ℝ × (ℝ × ℝ)
  ψ : ℝ → ℝ × ℝ
  ψu : ψ u.1 = u.2
  a : ℝ
  b : ℝ
  a_lt : a < u.1
  u_lt_b : u.1 < b
  ψ_C1 : ContDiffOn ℝ 1 ψ (Set.Ioo a b)
  graph_good : ∀ x ∈ Set.Ioo a b,
      collinearityMap r (A (x, ψ x)) = 0 ∧ A (x, ψ x) ∈ RealOffDiagonalTriples r
  W : Set (ℝ × (ℝ × ℝ))
  W_open : IsOpen W
  u_mem_W : u ∈ W
  ψ_graph_in_W : ∀ x ∈ Set.Ioo a b, (x, ψ x) ∈ W
  cover : ∀ z : ℝ × (ℝ × ℝ), z.1 ∈ Set.Ioo a b → z ∈ W →
      collinearityMap r (A z) = 0 → A z ∈ RealOffDiagonalTriples r → ψ z.1 = z.2

/-- The graph map `γ(x) = A (x, ψ(x))` of a graph-arc chart. -/
def RealGraphArc.g {r : ℝ → Space} (d : RealGraphArc r) (x : ℝ) : RealParamTriple :=
  d.A (x, d.ψ x)

/-- The graph lies in the off-diagonal collinearity zero set. -/
lemma RealGraphArc.g_good {r : ℝ → Space} (d : RealGraphArc r) {x : ℝ}
    (hx : x ∈ Set.Ioo d.a d.b) :
    collinearityMap r (d.g x) = 0 ∧ d.g x ∈ RealOffDiagonalTriples r := by
  simpa [RealGraphArc.g] using d.graph_good x hx

/-- The first split coordinate of a graph point is the parameter itself:
`B(γ(x)) = (x, ψ(x))`. -/
lemma RealGraphArc.g_B {r : ℝ → Space} (d : RealGraphArc r) (x : ℝ) :
    d.B (d.g x) = (x, d.ψ x) := by
  dsimp [RealGraphArc.g]
  exact d.AB (x, d.ψ x)

/-- The graph point lies inside the `ψ`-covering neighbourhood. -/
lemma RealGraphArc.g_in_W {r : ℝ → Space} (d : RealGraphArc r) {x : ℝ}
    (hx : x ∈ Set.Ioo d.a d.b) : (x, d.ψ x) ∈ d.W :=
  d.ψ_graph_in_W x hx

/-- **Graph-coordinate lemma (part 1): the curve coordinate.**  On the
graph-arc chart, the first split coordinate of a point of the arc is a
coordinate for the arc: `(B(γ(x))).1 = x` — the parameter is literally the
`x`-coordinate.  In particular `x ↦ γ(x)` is injective on `(a,b)` (each
`x`-slice `{(B q).1 = x}` meets the arc in at most one point). -/
theorem RealGraphArc.graph_coordinate {r : ℝ → Space} (d : RealGraphArc r) :
    (∀ x : ℝ, (d.B (d.g x)).1 = x) ∧ Set.InjOn d.g (Set.Ioo d.a d.b) ∧
      ∀ x ∈ Set.Ioo d.a d.b, d.g x ∈ RealOffDiagonalTriples r := by
  constructor
  · intro x
    rw [d.g_B]
  constructor
  · intro x₁ hx₁ x₂ hx₂ hEq
    have hB : d.B (d.g x₁) = d.B (d.g x₂) := congrArg d.B hEq
    have hfst : (d.B (d.g x₁)).1 = (d.B (d.g x₂)).1 := congrArg Prod.fst hB
    rw [d.g_B, d.g_B] at hfst
    exact hfst
  · intro x hx
    exact (d.g_good hx).2

/-- The parameter interval is centred at `u.1` and nondegenerate:
`a < u.1 < b`. -/
lemma RealGraphArc.center {r : ℝ → Space} (d : RealGraphArc r) :
    d.a < d.u.1 ∧ d.u.1 < d.b :=
  ⟨d.a_lt, d.u_lt_b⟩

/-- Reparametrised in `t` (so that the curve coordinate is
`x(t) = u.1 + t`), the first split coordinate along the curve is `x(t)` —
affine, hence strictly monotone on the arc. -/
lemma RealGraphArc.coord_along_t {r : ℝ → Space} (d : RealGraphArc r) (t : ℝ) :
    (d.B (d.g (d.u.1 + t))).1 = d.u.1 + t := by
  rw [d.g_B]

/-- The graph map is continuous on the parameter interval (the implicit
function `ψ` is `C¹`, `A` is continuous). -/
lemma RealGraphArc.continuousOn_g {r : ℝ → Space} (d : RealGraphArc r) :
    ContinuousOn d.g (Set.Ioo d.a d.b) := by
  have hψc : ContinuousOn d.ψ (Set.Ioo d.a d.b) := d.ψ_C1.continuousOn
  have hid : ContinuousOn (fun x : ℝ => x) (Set.Ioo d.a d.b) := continuousOn_id
  have hpair : ContinuousOn (fun x : ℝ => (x, d.ψ x)) (Set.Ioo d.a d.b) := hid.prodMk hψc
  change ContinuousOn (fun x : ℝ => d.A (x, d.ψ x)) (Set.Ioo d.a d.b)
  exact d.A_cont.comp_continuousOn hpair

/-- The graph map is continuous at every point of a compact subinterval of
the parameter interval. -/
lemma RealGraphArc.continuousAt_g {r : ℝ → Space} (d : RealGraphArc r) {x : ℝ}
    (hx : x ∈ Set.Ioo d.a d.b) : ContinuousAt d.g x := by
  exact d.continuousOn_g.continuousAt (isOpen_Ioo.mem_nhds hx)

/-- **No-re-entry / trace lemma:** inside the graph-adapted box over the
`x`-interval `[α,β]` (a point `q` of the box has `x = (B q).1 ∈ [α,β]` and
`B q ∈ W`), the off-diagonal collinearity zero set is *exactly* the image
of the arc over `[α,β]`.  The arc does not re-enter such a box: its trace
in the box is the whole local zero set there. -/
theorem RealGraphArc.trace_eq_zeroSet_of_box {r : ℝ → Space} (d : RealGraphArc r)
    {α β : ℝ} (hαβ : Set.Icc α β ⊆ Set.Ioo d.a d.b) :
    d.g '' Set.Icc α β =
      {q : RealParamTriple | collinearityMap r q = 0 ∧ q ∈ RealOffDiagonalTriples r ∧
        (d.B q).1 ∈ Set.Icc α β ∧ d.B q ∈ d.W} := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    have hxIoo : x ∈ Set.Ioo d.a d.b := hαβ hx
    have hgood := d.g_good hxIoo
    subst q
    constructor
    · exact hgood.1
    constructor
    · exact hgood.2
    constructor
    · rw [d.g_B]
      exact hx
    · rw [d.g_B]
      exact d.g_in_W hxIoo
  · intro hq
    rcases hq with ⟨hqZ, hqOff, hxI, hqW⟩
    have hcover := d.cover (d.B q) (hαβ hxI) hqW
    have hAZ : collinearityMap r (d.A (d.B q)) = 0 := by
      simpa [d.BA] using hqZ
    have hAOff : d.A (d.B q) ∈ RealOffDiagonalTriples r := by
      simpa [d.BA] using hqOff
    have hψ : d.ψ (d.B q).1 = (d.B q).2 := hcover hAZ hAOff
    refine ⟨(d.B q).1, hxI, ?_⟩
    rw [RealGraphArc.g]
    rw [hψ]
    change d.A (d.B q) = q
    exact d.BA q

/-- **The arc over a compact subinterval is an embedding** (indeed a closed
embedding: its image is compact hence closed).  The explicit continuous
inverse of `x ↦ γ(x)` on the image is the first split coordinate
`q ↦ (B q).1` — this is the precise sense in which the local zero set over a
graph-adapted box is a single embedded arc with a monotone coordinate. -/
noncomputable def RealGraphArc.arcHomeo {r : ℝ → Space} (d : RealGraphArc r)
    {α β : ℝ} (hαβ : Set.Icc α β ⊆ Set.Ioo d.a d.b) :
    {x : ℝ // x ∈ Set.Icc α β} ≃ₜ {q : RealParamTriple // q ∈ d.g '' Set.Icc α β} := by
  let u : {t : ℝ // t ∈ Set.Icc α β} → RealParamTriple := fun x => d.g (x : ℝ)
  have hmemX : ∀ x : {t : ℝ // t ∈ Set.Icc α β}, d.g (x : ℝ) ∈ d.g '' Set.Icc α β := by
    intro x
    exact ⟨(x : ℝ), x.2, rfl⟩
  have hmemY : ∀ q : {z : RealParamTriple // z ∈ d.g '' Set.Icc α β},
      (d.B q.1).1 ∈ Set.Icc α β := by
    intro q
    rcases q.2 with ⟨x₀, hx₀, hq₀⟩
    rw [← hq₀]
    rw [d.g_B]
    exact hx₀
  let e : {x : ℝ // x ∈ Set.Icc α β} ≃ {q : RealParamTriple // q ∈ d.g '' Set.Icc α β} :=
    ⟨Set.codRestrict u (d.g '' Set.Icc α β) hmemX, fun q => ⟨(d.B q.1).1, hmemY q⟩,
      by
        intro x
        apply Subtype.ext
        dsimp [u, Set.codRestrict]
        rw [d.g_B],
      by
        intro q
        apply Subtype.ext
        rcases q.2 with ⟨x₀, hx₀, hq₀⟩
        dsimp [u, Set.codRestrict]
        rw [← hq₀]
        have hx0 : (d.B (d.g x₀)).1 = x₀ := by rw [d.g_B]
        rw [hx0]⟩
  refine ⟨e, ?ct, ?ci⟩
  · -- continuity of e.toFun
    rw [continuous_iff_continuousAt]
    intro x
    have hxI : (x : ℝ) ∈ Set.Icc α β := x.2
    have hxIoo : (x : ℝ) ∈ Set.Ioo d.a d.b := hαβ hxI
    have hcat : ContinuousAt d.g (x : ℝ) := d.continuousAt_g hxIoo
    have hval : ContinuousAt (fun y : {t : ℝ // t ∈ Set.Icc α β} => (y : ℝ)) x :=
      continuous_subtype_val.continuousAt
    have hu : ContinuousAt (fun y : {t : ℝ // t ∈ Set.Icc α β} => d.g (y : ℝ)) x :=
      hcat.comp hval
    dsimp [e, u, Set.codRestrict]
    exact ContinuousAt.codRestrict hmemX (x := x) hu
  · -- continuity of e.invFun
    rw [continuous_iff_continuousAt]
    intro q
    have hB : Continuous (fun z : RealParamTriple => d.B z) := d.B_cont
    have hBq : Continuous (fun z : {z : RealParamTriple // z ∈ d.g '' Set.Icc α β} =>
        d.B z.1) := hB.comp continuous_subtype_val
    have hc : ContinuousAt (fun z : {z : RealParamTriple // z ∈ d.g '' Set.Icc α β} =>
        (d.B z.1).1) q := (Continuous.fst hBq).continuousAt
    dsimp [e]
    exact ContinuousAt.codRestrict hmemY (x := q) hc

/-- The image of the arc over a compact subinterval is compact, hence a
closed subset of the ambient space (the ambient is Hausdorff): the arc is a
*closed* embedded arc. -/
theorem RealGraphArc.image_arc_isClosed {r : ℝ → Space} (d : RealGraphArc r)
    {α β : ℝ} (hαβ : Set.Icc α β ⊆ Set.Ioo d.a d.b) :
    IsClosed (d.g '' Set.Icc α β) := by
  have hY : CompactSpace {q : RealParamTriple // q ∈ d.g '' Set.Icc α β} :=
    Homeomorph.compactSpace (d.arcHomeo hαβ)
  have hcomp : IsCompact (d.g '' Set.Icc α β) := (isCompact_iff_compactSpace).mpr hY
  exact hcomp.isClosed

/-- **Closed-embedding statement** (assembled): over a compact subinterval of
the graph parameter interval, the local arc is an embedding of a closed
interval whose image is a *closed* subset of the ambient space and equals
the whole off-diagonal collinearity zero set of the graph-adapted box. -/
theorem RealGraphArc.arc_closed_embedding {r : ℝ → Space} (d : RealGraphArc r)
    {α β : ℝ} (hαβ : Set.Icc α β ⊆ Set.Ioo d.a d.b) :
    (∃ e : {x : ℝ // x ∈ Set.Icc α β} ≃ₜ
        {q : RealParamTriple // q ∈ d.g '' Set.Icc α β},
      ∀ x : {x : ℝ // x ∈ Set.Icc α β}, (e x).1 = d.g x.1) ∧
    IsClosed (d.g '' Set.Icc α β) ∧
    d.g '' Set.Icc α β =
      {q : RealParamTriple | collinearityMap r q = 0 ∧ q ∈ RealOffDiagonalTriples r ∧
        (d.B q).1 ∈ Set.Icc α β ∧ d.B q ∈ d.W} := by
  constructor
  · refine ⟨d.arcHomeo hαβ, ?_⟩
    intro x
    dsimp [RealGraphArc.arcHomeo]
    rfl
  constructor
  · exact d.image_arc_isClosed hαβ
  · exact d.trace_eq_zeroSet_of_box hαβ
