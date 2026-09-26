import Mathlib
import Submission.Commons.Topology.Jordan.two_disjoint_closed_not_separating
import Submission.Commons.Topology.Strip.path_meets_translate
import Submission.Commons.Topology.Strip.wall_blocks_translate_path
import Submission.Commons.Topology.Jordan.top_bottom_continuum_meets_left_right_path
import Submission.Commons.Topology.Homotopy.vanKampen_grid
import Submission.Commons.Topology.Strip.exists_translate_path_of_ess_of_cover

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Topology.Strip

/-! ### STATUS (session 109): THE FILE IS COMPLETE — `annulus_essential_intersection` is proved

**The file is `sorry`-free and axiom-clean** (`propext`, `Classical.choice`, `Quot.sound` only).
The target `annulus_essential_intersection` (Pannwitz–Kuperberg / Denne) is proved, and so is the
last gap of the reduction chain, `mv_obligation` (the Mayer–Vietoris cancellation).

**How the last gap was closed.**  The crux is proved in the *shared commons*, in the
*closed*-strip excisive-cover form: `Commons.Topology.Strip.crux_via_decomposition` in
`Submission.Commons.Topology.Strip.exists_translate_path_of_ess_of_cover` (sheet index on the free
region `W₁ ∩ W₂` + the two-set decomposition `Commons.Topology.Jordan.ClosedDisjoint.QD.exists_decomposition`
of a locally constant `ℤ`-valued function on the complement of two disjoint closed sets — the
Mayer–Vietoris statement in the form that argument needs).  The passage from the closed strip to the
*open* strip of this file is by *shrinking*: the two translate paths supplied by `hwindA`, `hwindB`
are compact inside the open strip, hence contained in a closed strip `{a + ε ≤ y ≤ b - ε}`
(`exists_shrunk_strip`, with the companion `exists_lt_le_bound_of_continuous`, both proved just above
`mv_obligation`); on that closed strip the cover restricts to a cover and all hypotheses of the
commons theorem hold, and its conclusion (joinedness inside `W₁ ∩ W₂ ⊆ VA ∩ VB`) strengthens by
monotonicity of `JoinedIn`.  The rest of the chain is unchanged:
`annulus_essential_intersection ⟸ crux_Z_meet ⟸ crux_of_finite_orbit_component + mv_obligation`.

**Renamings forced by the new import** (same namespace `Commons.Topology.Strip`):

* `sheetRel`, `sheetSetoid`, `sheetRep`, `sheetRep_spec` of this file **clashed by name** with
  declarations of the newly imported commons module, and are renamed `wSheetRel`, `wSheetSetoid`,
  `wSheetRep`, `wSheetRep_spec` (and `sheetRel_translate` to `wSheetRel_translate`).  The commons'
  same-named objects (a different construction) are *not* used by this file.
* `exists_sheet_index`, `exists_local_selection`, `exists_eq_periodic_half` are renamed
  `exists_sheet_index_aei`, `exists_local_selection_aei`, `exists_eq_periodic_half_aei`, because
  `Submission.Commons.Topology.Strip.annulus_duality_open` (another file of the shared commons,
  in the same namespace) declares the same three names.

**Independent material kept in the file.**  The long STATUS blocks below (sessions 70 … 108) are the
record of the routes explored and remain accurate as history; their claims that "the remaining
`sorry` sits on `mv_obligation`" are now superseded.  The large combinatorial development
(sections `AnnulusChain` … `AnnulusZFlow`, ~1500 lines: the annulus interface chain, its winding,
the oriented flow, the walk extractor and the peel/mass induction for it) is `sorry`-free and
independent; the final proof does **not** use it (it uses the commons theorem instead), and it is
kept because it is proved and self-contained.
-/


/-! ### STATUS (session 70): ONE `sorry` left (`mv_obligation`), and a concrete route to it

Read this first.  The file has **exactly one `sorry`**, on `mv_obligation` (the Mayer–Vietoris
cancellation, Denne's `prop:homology`); the target `annulus_essential_intersection` is proved from
it, and nothing else in the file is open.

**What changed this session.**

* `collared_crux_overlap` — previously the second `sorry` — is now **proved** by deriving it from
  `mv_obligation` through `crux_of_finite_orbit_component` (its collar hypotheses `hKA`, `hKB` are
  simply not used; they are redundant there, as already recorded in session 67/68 notes).  No cycle
  arises: `mv_obligation` is declared *earlier* in the file and does not depend on the collared
  branch.  So the collared branch (`collared_crux_touching` + `collared_crux` +
  `collared_crux_of_halves`) is complete, conditionally on `mv_obligation`.

* Sibling work (not in this file): `Submission/Work/Topology/Homotopy/grid_assembly.lean` is now
  **`sorry`-free** and contains the full van Kampen *generation* skeleton — the row half
  (`RowData.row_assembly`), the column half (`ColData.column_assembly`, the orientation stitch
  `colNatCellBnd_eq_inv`), obligation (a) (inverting an ordered product reverses it:
  `prodFirst_symm`, `revProd`), obligation (b) (the flattening lemma
  `RowData.rowBndF_flatten`/`flatBnd_rec` and its column form), and the three moves of the grid
  assembly (`GridData.grid_outer`, `colData_assembly`, `grid_assembly`).

**The residual is exactly `mv_obligation`** (the true content of all the failed routes: the
potential is FALSE, the accumulation/wall forms are machine-refuted for the *open* strip — the
two-banded spiral tower, whose wall is closed in `Ω` but whose sheets contain no translate path
because each sheet is a translate-*free* component).  No surface-topology shortcut survives.

**A concrete route to `mv_obligation` (recorded for execution; the pieces are elementary).**
The mechanism Denne's Mayer–Vietoris exactness encodes can be reproduced *without* homology, by an
"interface chain" argument on a grid.  In the quotient annulus `A = Ω/T` (or its compact variant
`S = {a ≤ y ≤ b}` modulo `T`), let `U = VA/T`, `V = VB/T` and `α = π∘γ_A`, `β = π∘γ_B` be the two
winding-one loops coming from `hwindA`, `hwindB`.

1. **The square.**  With `σ` the straight segment `z_A → z_B` (convexity of `Ω`) put
   `F(t,s) := (1-s)·γ_A(t) + s·γ_B(t)`.  Then `F(·,0) = γ_A`, `F(·,1) = γ_B`, `F(0,·) = σ` and
   `F(1,·) = Tσ`; after quotienting, `π∘F(0,·) = π∘F(1,·)` — the left and right edges *cancel in
   `A`*, so `∂(π∘F) = α - β` as `1`-chains in `A`.
2. **Subdivision.**  `exists_grid_decomposition_of_open_cover` (commons) applied to `F` with the
   open cover `{VA, VB}` of `Ω` gives an `n × n` grid of cells, each carried by `VA` or by `VB`.
3. **The interface chain.**  Let `Σ_A` be the sum of the cells labelled `A`.  Put
   `c_A := α - (π∘F)_*(∂Σ_A)`.  Since `(π∘F)_*(∂Σ) = α - β`, also `c_A = β + (π∘F)_*(∂Σ_B)`.
   Reading `c_A` in the two ways gives, for every path with non-zero coefficient: it is (a piece of
   `α`, or a boundary edge of an `A`-cell) and also (a piece of `β`, or a boundary edge of a
   `B`-cell), hence it lies in `U ∩ V`.  The two representations are *different term sets*; what
   makes the argument work is that in `A` the left and right edges are literally the same path
   (`π∘F(0,s) = π∘F(1,s)`), so the "boundary" terms that would escape `U ∩ V` in the *lifted*
   picture cancel exactly.
4. **The winding.**  `c_A` is a cycle; its winding is `1`: the winding is additive on `1`-cycles in
   `A`, `w(α) = 1`, and `(π∘F)_*(∂Σ_A)` is a boundary in `A` (its `Ω`-lift *exists*, a disk being
   simply connected) so it has winding `0`.
5. **Extraction.**  Decompose the cycle `c_A` (a finite integral `1`-cycle on its support graph)
   into closed loops in `U ∩ V`; the windings add up to `1 ≠ 0`, so one loop `γ` has winding
   `k ≠ 0`.  Its lift to `Ω` is a path inside `W = VA ∩ VB` from some `x` to `T^k x`.  A path in a
   `T`-invariant set joining `x` to `T^k x`, `k ≠ 0`, contains a genuine translate path
   (`Commons.Topology.Strip.winding_translate_path`, `ess_of_nonzero_winding`); that is
   `mv_obligation` (with `m = 1`).

*Executed so far* (all in this file, `sorry`-free, axiom-clean): the **whole extraction device of
step 5**.

* `exists_directed_path_of_flow` (with the auxiliary `sum_update_eq`, `sum_update_sub`,
  `sum_univ_update_sub`, `sum_ite_filter`) — a finite integral flow on a digraph from `x` to `y`
  contains a directed path from `x` to `y` all of whose edges carry non-zero flow;
* `joinedIn_of_chain` — the concatenation of the paths realising the edges of such a directed path
  is a join in the ambient set;
* `joinedIn_of_flow` — the two combined: a flow from `x` to `y` in a graph whose edges are realised
  by paths in `W` gives `JoinedIn W (P x) (P y)`.

* **steps 1–2** (the geometric picture): `squareMap` — the convex interpolation of the two
  translate paths — with `squareMap_snd_zero`/`_snd_one` (its `t`-edges are `γ` and `δ`),
  `squareMap_mem_strip` (its image lies in the strip, by convexity), and above all `squareMap_T`:
  *if `γ` and `δ` each join a point to its `T`-translate then `squareMap γ δ (1,s) =
  T (squareMap γ δ (0,s))`* — the square descends to the **cylinder** `S¹ × I`.  That is exactly
  the structural relation that makes the left and right edges of the grid cancel in the quotient
  annulus (they do *not* cancel in the lifted picture `Ω`: the connector `σ` versus `Tσ`), i.e. it
  is the algebraic shadow of "read the interface chain in the annulus, not in `Ω`".
  `exists_grid_of_squareMap` then produces, from `exists_grid_decomposition_of_open_cover`, an
  `n × n` grid of the square with every cell carried by `VA` or by `VB`.

Fed with the `Ω`-chain whose boundary is the translate discrepancy `Tz - z` (step 3, the only part
not yet executed), `joinedIn_of_flow` produces an honest path in `VA ∩ VB` from a point to its
translate — i.e. `mv_obligation` (with `m = 1`).  The remaining construction is therefore exactly
the interface `1`-chain of step 3 (`c_A := α - (π∘F)_*(∂Σ_A)` in the quotient annulus, equivalently
on the cylinder `S¹ × I`), read with the deck bookkeeping that `squareMap_T` supplies.

Two failure modes to watch when executing this: (i) in the *lifted* (`Ω`) picture the left/right
edges of the square do **not** cancel (`σ` versus `Tσ`), and the offending terms are exactly the
connector pieces on rows whose first and last cells are both `A`-cells — this is why step 3 must be
carried out in `A` (equivalently: on the *cylinder* `S¹ × I`, whose only boundary components are
`α` and `β`); (ii) the "winding of a `1`-cycle" of step 4 is the only homological notion needed, and
it can be defined directly as the `T`-displacement `(x̃(1).1 - x̃(0).1)/p` of a lift, which for loops
is an integer and is additive under concatenation — no singular homology, no `H₁(A) = ℤ`, and no
Mayer–Vietoris spectral sequence is required.
-/

/-! ### STATUS (session 69): the *level slices* of `W` must be disconnected; the twisted-square route

Read this first.  One new theorem, and a precise account of what the two remaining `sorry`s are
(`mv_obligation`, `collared_crux_overlap`) and of which routes to them are dead.

**New (proved, `sorry`-free) in this file: `crux_of_level_preconnected`.**

Let `W = VA ∩ VB`.  Every horizontal level `L_y = {q.2 = y}` is `T`-invariant, and so is `W`; hence
the slice `S_y = W ∩ L_y` is `T`-invariant.  If `S_y` is nonempty and **connected**, the crux holds:
the first-coordinate projection of `S_y` is a connected subset of `ℝ`, hence an interval
(`IsPreconnected.ordConnected`), so for every `u` between `z.1` and `(T z).1` there is a point of
`S_y` with first coordinate `u` — and since `S_y ⊆ L_y`, that point is `(u, y)`.  The horizontal
segment from `z` to `T z` therefore lies in `W`, and monotonicity gives the `VA`- and `VB`-paths.

*Consequences (all proved here).*

1. Under a crux failure, **every nonempty slice `W ∩ L_y` is disconnected** (so the wall
   `K = (VA∖VB) ⊔ (VB∖VA)` separates every level it meets), and if `W ∩ L_y = ∅` the whole level
   lies in the wall.
2. Every *piece* of a slice (each component of `W ∩ L_y`, i.e. each "column") has **length `< p`**:
   a piece of length `≥ p` contains two points differing by `(p, 0)`, and the straight segment
   between them (inside the level, hence inside `W`) is a translate crossing.
3. A *full band* inside `W` (`ℝ × I ⊆ W`, `I` an interval) gives the crux, since a band is
   `T`-invariant and connected — this is `crux_of_band_subset` (proved here).  In the collared
   normalisation (`KA ⊆ {q.2 ≤ b−δ}`, `KB ⊆ {q.2 ≥ a+δ}`, so that `VA = Ω∖KB ⊇ {q.2 < a+δ}` and
   `VB = Ω∖KA`), this gives (hand-check, combining it with `VA ⊇ {q.2 < a+δ}`): if `KA` misses the
   open bottom band `{q.2 < a+δ}` then that band lies in `VA ∩ VB` and the crux holds; so in a crux
   failure `KA` must meet the bottom band, and symmetrically `KB` must meet the top band.

**The twisted-square route (the sibling files' `extraction_square_map` route) — and why it is *not*
enough by itself.**  If there is a continuous `F : [0,1]² → Ω` with

* `F(·,0) ⊆ VA` and `F(·,1) ⊆ VB` (bottom and top edges),
* `F(1,·) = T ∘ F(0,·)` (the twisted left/right edges),
* `F(0,·) ⊆ W` (the *left edge* lies in the free region),

then the crux follows: `extraction_square_map` (commons) produces `s, t` with
`F(0,s) ~ T(F(0,t))` *inside* `Ω₁ ∩ Ω₂ = W`, and since the left edge is in `W` the sub-arc of
`F(0,·)` joins `F(0,s)` to `F(0,t)` inside `W`; translating that sub-arc joins `T(F(0,t))` to
`T(F(0,s))` inside `W`, so `F(0,t) ~ T(F(0,t))` in `W` — a translate crossing in `W`, contradicting
`hno`.  This is the mechanism of `exists_join_of_two_collared_periodic` +
`extraction_square_of_open_cover`.  **The obstruction**: the left edge required by the sibling route
is a *meridian* inside `W` from the top band to the bottom band, and **such a meridian need not
exist**: with `P ⊇ ℝ×{m}` for some `m ∈ (a+δ, b−ε)` the whole level `m` is in the wall and separates
the two bands.  In that case, however, the crux holds trivially by 3. above whenever `P` misses the
bottom band; so a successful use of this route needs the case split "`P` misses some level `m ≥ a+δ`
⟹ crux by 3., otherwise a meridian exists", i.e. it must be combined with the level analysis.

**Why the naive wall/accumulation routes are dead (kept from sessions 1 and 65).**  The
"spanning continuum" form of the wall duality ("`hno` ⟹ a preconnected piece of the wall has
heights accumulating at `a` and `b`") is **machine-refuted** (the two-banded spiral tower, see
`accumulating_refutation_of_no_translate_path.lean`).  The tower's escape hatch is that its wall
accumulates on an *interior* level, and *saturation* is exactly what a crux configuration forbids:
there the wall is closed in `Ω` (each piece is closed in `ℝ²` up to the boundary lines, since it is
the complement of an open set), so a wall piece accumulating on an interior level `m` must contain
that level — and then the level lies in one of the two pieces `K_A = VA∖VB`, `K_B = VB∖VA`.
Hand-checked consequences of that saturation, recorded for the next session:

* if `K_A` misses the bottom band `{q.2 < a+δ}` (in the collared normalisation, so that
  `{q.2 < a+δ} ⊆ VA` because `K_B ⊆ {q.2 ≥ a+δ}`), then `{q.2 < a+δ} ⊆ VA ∩ VB = W`, a full
  `T`-invariant band, and the crux holds by 3. above — so in a crux failure `P` must meet **every**
  level below `max(a+δ, …)`;
* likewise `K_B` must meet every level above the top band, and (by 1.) every level is separated by
  `K_A ∪ K_B`; combinatorially a crux failure therefore forces `K = K_A ⊔ K_B` to have **at least
  two `T`-orbits of components**: a wall that is a single `T`-orbit (the spiral, or
  `⋃_{k} {k} × (a,b)`) has a `T`-free complement, so its complement is *inessential* and cannot serve
  as `VA` or `VB` in a failure configuration.  (Both of these are hand-checks, not formalised.)

**Where the residual now sits.**  Unchanged: `mv_obligation` (the crux) and its collared
specialisation `collared_crux_overlap`; both are Denne's `prop:homology`, whose only known proof is
Mayer–Vietoris exactness of `H₁(S∖(A∪B)) → H₁(S∖A) ⊕ H₁(S∖B) → H₁(S)`.  The workspace's van Kampen
skeleton is now **complete on the row side**: `Submission/Work/Topology/Homotopy/grid_assembly.lean`
proves (`sorry`-free, `#print axioms` clean) that the boundary of a row of cells is the product of
the cell boundaries conjugated along the grid, on top of the commons' `grid_cancellation`,
`grid_row`, `grid_iteration`, `vanKampen_grid`.  What is still missing for the middle exactness
`H₁(W₁∩W₂) ↠ H₁(W₁) ⊕ H₁(W₂)` is the *relation* half (surjectivity of
`π₁(W₁∩W₂) → π₁(W₁) ×_{π₁(Ω)} π₁(W₂)`), for which the row assembly is the first ingredient. -/

/-! ### STATUS (session 68): **the touching (height-separated) case of the collared crux is PROVED**

Two `sorry`s remain in the file: `mv_obligation` (line ~7573) and `collared_crux_overlap`
(the strict-overlap half of `collared_crux`).  Everything else is proved.

**Proved this session (all `sorry`-free).**

* `interface_cutting` (session 67 statement, previously the file's `sorry`) — now **proved**: in the
  touching collared case, every point `z` of the interface level `{q.2 = b - δ}` lying in `VA ∩ VB`
  has a point of `Qtrace` or of `Ptrace` *on the vertical through* `z`; since both traces live on the
  level `{q.2 = b - δ}` and `z.2 = b - δ`, that point is `z` itself, and the conclusion is a
  contradiction (`z ∈ VA` and `z ∉ VA`).  So the interface level splits as `P ⊔ Q`.
* `exists_Tz_mem_Icc` — every point of the plane has an integer translate with `x ∈ [0,p]`.
* `level_met_of_meets_between` — the set of heights attained by a subset of the strip that is closed
  in the strip and `T`-invariant is closed: if it contains an interval `(α,β)` then it contains
  `[α,β]` (`α < β`, `[α,β] ⊆ Ω`).  The engine is compactness of `K ∩ ([0,p]×[α,β])` (the box is
  compact and `K`-invariance moves points into it).
* **`collared_crux_touching`** — the collared crux in the case `a + ε = b - δ`, i.e. when the wall
  pieces `K_A = VA∖VB`, `K_B = VB∖VA` are **separated by a horizontal level**: `K_A ⊆ {q.2 ≤ e}`,
  `K_B ⊆ {q.2 ≥ e}` for some `a < e < b` (then automatically `VA ⊇ {q.2 < e}` and `VB ⊇ {q.2 > e}`,
  so this is exactly the touching hypothesis package).  Proof: under the failure of the crux the
  level `L_e` is covered by the two traces (saturation), both closed in `L_e`; `L_e` is connected, so
  `L_e ⊆ K_A` or `L_e ⊆ K_B`; say `L_e ⊆ K_A`, so `K_B` lies strictly above the level and yet must
  meet *every* level in `(e,b)` (otherwise a free level gives the crux by
  `crux_conclusion_of_free_level`) — contradicting `level_met_of_meets_between`.  The other case is
  symmetric with `K_A` and the levels below `e`.  Note `hwindA`, `hwindB` are not used: the statement
  is unconditional in the essentiality.
* `collared_crux` is now `collared_crux_touching` + `collared_crux_overlap` (a dispatch); the new
  isolated residual is the **strict-overlap case**.

**Mathematical findings this session (recorded so that they are not re-derived).**

1. **The strict-overlap case is exactly Denne's `prop:homology`.**  Denne (*Alternating quadrisecants
   of knots*, arXiv:math/0510561) states: *two closed disjoint `A, B ⊆ S` with `A` outside a
   neighbourhood of `Δ₊` and `B` outside one of `Δ₋` admit a curve winding once around `S` avoiding
   `A ∪ B`*, and proves it by **Mayer–Vietoris exactness** of
   `H₁(S∖(A∪B)) → H₁(S∖A) ⊕ H₁(S∖B) → H₁(S)`, with one path of degree `+1` and one of degree `−1`.
   There is no elementary (non-homological) version: the crux *is* this statement, and the collared
   case with *disjoint or touching* collars is precisely the case my two proved theorems cover.
2. **The enlargement trick does not close the strict-overlap case.**  For *any* pair `VA, VB` and any
   `e ∈ (a,b)`, the pair `VA' := VA ∪ stripS a e`, `VB' := VB ∪ stripS e b` has walls
   `VA'∖VB' = (VA∖VB) ∩ {q.2 < e}` and `VB'∖VA' = (VB∖VA) ∩ {q.2 > e}`, so `collared_crux_touching`
   applies to it *for every* `e`.  But a crossing for `(VA',VB')` does not descend to `(VA,VB)`: the
   crossing can sit in the added band (`VA ∩ stripS e b` or `VB ∩ stripS a e`), and those added
   points need not lie in `VA ∩ VB`.  With `e` chosen inside a band contained in `VA` (e.g. `e ∈
   (a,a+ε)` in the collared case) one does get the *half* conclusion `Ess p VA ∩ stripS e b ≠ ∅`,
   which is weaker than `Ess p VA ∩ VB ≠ ∅` (session 64) — so no gain.
3. The `Commons.Topology.Strip.ess_inter_of_ess_of_open_cover` route is vacuous (`W₁ ∪ W₂` open
   cannot equal a non-trivial closed strip), and
   `Commons.Topology.Strip.essT_not_subset_obstacles_of_interlocking` gives only the disjunction of
   the two session-64 facts (`Ess p VA ∩ VB ≠ ∅` *or* `Ess p VB ∩ VA ≠ ∅`), i.e. strictly weaker than
   the crux — which is the gap "the two essential parts meet *each other*".
4. The elementary Mayer–Vietoris extraction of the sibling files
   (`Commons.Topology.Strip.exists_joinedIn_inter_of_two_translate_paths` /
   `Work/.../exists_translate_path_of_ess_of_cover.exists_relation_of_two_translate_paths`) produces
   only a *relation* `A ~ T B` between **two different** points of the straight segment from `z₁` to
   `z₂`; to close it up into a translate path one still needs a path inside `U = W₁∩W₂` between those
   two points (the sibling's residue (B)), i.e. the same content.  Note that a translate path
   `z ~ T^k z` with `k ≠ 0` *does* suffice
   (`Commons.Topology.Strip.winding_translate_path` / `path_meets_translate`), so the remaining
   formal step is exactly the "chain the relations over the `T`-orbit" step.  The identified next
   step on that route is to assemble the **van Kampen middle exactness** from the commons'
   two-dimensional van Kampen skeleton — `Commons.Topology.Homotopy.exists_grid_decomposition_of_open_cover`
   (subdivide the null-homotopy of the 4-gon `γ₁ · Te · γ₂⁻¹ · e⁻¹` into `W₁`/`W₂`-labelled cells,
   which exists because the strip `Ω` is simply connected and `Ω = W₁ ∪ W₂`),
   `grid_cancellation` / `grid_row` / `grid_iteration` (the interior-edge cancellation) — i.e. the
   statement `H₁(W₁∩W₂) ↠ H₁(W₁) ⊕ H₁(W₂)` (surjectivity: `H₁(Ω) = 0`), from which the crux
   follows immediately because the degree map `H₁(W₁) → H₁(Ω/T) = ℤ` is onto (`hwindA`).

5. **The "missed levels" structure of the failure hypothesis (sharpened this session).**  Also proved
   now: `isClosed_image_height` (the set of heights attained by a set closed in the strip is *closed*,
   being the image of the compact `K ∩ ([0,p]×[α,β])`) and `exists_band_free_of_misses_level` (if
   such a `K` avoids one level, it avoids a whole band of levels).  Consequently, under the failure
   `hno` of the crux, the two sets

   * `E_A := {t ∈ (a,b) : K_A misses the level {q.2 = t}}`, `E_B` defined the same way for `K_B`

   are **open and disjoint** (a level missed by both is a free level, giving the crux by
   `crux_conclusion_of_free_level`), and `(a,b) = E_A ⊔ E_B ⊔ F` with `F := (a,b) \ (E_A ∪ E_B)`
   closed.  Moreover `VA ⊇ {q.2 < t}` for `t ∈ E_B` and `VB ⊇ {q.2 > t}` for `t ∈ E_A`, and the
   wall pieces are *separated by a level* `e` (i.e. `K_A ⊆ {q.2 ≤ e}`, `K_B ⊆ {q.2 ≥ e}`) exactly
   when `(a,e) ⊆ E_B` and `(e,b) ⊆ E_A`.  So:

   > **`collared_crux_touching` is precisely the statement that the crux holds when `F` is a single
   > level**, and the residual is the case `F ⊋ {∗}` (in the collared case `F ⊆ [a+ε, b−δ]`, with
   > `(a,a+ε) ⊆ E_B` and `(b−δ,b) ⊆ E_A`).

   This is the sharp form in which the residual should be attacked: one must extract a translate
   path from a *nontrivial closed transition set* `F` of levels meeting **both** wall pieces.

   **The precise obstruction to the touching argument in the overlap case**: at any level `e`, the
   touching proof needs *both* bands (`VA ⊇ {q.2 < e}` and `VB ⊇ {q.2 > e}`), which the wall
   separation `K_A ⊆ {≤e}`, `K_B ⊆ {≥e}` supplies automatically.  With `F ⊋ {∗}` and
   `γ = inf F`, `δ₀ = sup F` one has `E_B ⊇ (a,γ)` and `E_A ⊇ (δ₀,b)`, hence the *lower* band
   `VA ⊇ {q.2 < γ}` holds, but the upper one fails: the levels of `(γ, δ₀) ∩ E_B` lie in `VA`, not
   in `VB`.  So an argument for the overlap case must work with a *partial* upper band — that is
   where its homological content enters.

**Note (essentiality is automatic in the collared case).**  If `K_B = VB∖VA ⊆ {q.2 ≥ a+ε}` with
`ε > 0`, then `VA ⊇ {a < q.2 < a+ε}` (the band), which is `T`-invariant and connected, so the
`VA`-component containing it is `T`-invariant and hence contains a translate path — i.e. `hwindA`
follows from `hKB` (this is `band_subset_Ess_of_collar`).  Symmetrically `hwindB` follows from
`hKA`.  So `hwindA`, `hwindB` are *redundant* hypotheses of `collared_crux` /
`collared_crux_touching` / `collared_crux_overlap`; they are kept only for uniformity with
`mv_obligation`.

**Where the residual now sits.**  `mv_obligation` (the general crux, `VA, VB` open `T`-invariant
covering the open strip, both essential) and `collared_crux_overlap` (its strictly-overlapping
collared special case) — both are Denne's `prop:homology`, i.e. the genuine Mayer–Vietoris/annulus
duality content absent from Mathlib.  The file's chain to the target lemma is otherwise complete:
`annulus_essential_intersection ⟸ crux_Z_meet ⟸ crux_of_finite_orbit_component + mv_obligation`.
-/

/-! ### STATUS (session 67): the collared case is isolated; `D_A ∩ D ≠ ∅` is *not* the right target

Two things, both recorded in full in the session-67 block further down.

1. **The session-66 "collared reduction" was wrong.**  `D_A ∩ D ≠ ∅` (the `T`-invariant component of
   `VA` at the upper collar meeting that of `VB` at the lower collar) is *sufficient* for the crux but
   **not necessary**, and it is not a consequence of the collared hypotheses: the level cut
   `VA = Ω \ {q.2 = c}`, `VB = Ω \ {q.2 = a+ε/2}` (with `a+ε < c < b-δ`) is open, `T`-invariant,
   covering, collared and essential, yet its collar components are disjoint — the crossing is carried
   by the middle component `{a+ε/2 < q.2 < c} ⊆ VA ∩ VB`.  (Note also that the collared hypothesis
   only gives that the *union* covers each collar: a point of the upper collar may lie in `VB \ VA`.)
2. **The isolated goal is therefore the collared case of the crux itself.**  Of that case, the
   The *band ingredients* of the overlapping half are also proved:
   `level_subset_left_of_collar` / `band_subset_Ess_of_collar` (a level strictly inside the lower
   collar lies in `VA`, so the whole band `(a, a+ε)` is inside `Ess p VA`) and their right-hand
   counterparts for the band `(b-δ, b)` inside `Ess p VB`; the overlapping case is exactly the case
   where those two bands meet, so only the interface levels `[b-δ, a+ε]` remain.
   *disjoint-collar* half (`b - δ < a + ε`) is now **proved**, elementary:
   `collared_crux_of_disjoint_collars` — if the collars leave a gap, pick a level `c` there; it
   misses both wall pieces, so the whole line `{q.2 = c}` lies in `VA ∩ VB` and is a crossing
   (`crux_conclusion_of_free_level`).  What is left is the *overlapping* case `a + ε ≤ b - δ`, now
   `collared_crux` below; the general (non-collared) case reduces to it by the shrinkages C1–C6 of
   the annulus notes.  Proved on the
   way: `crux_conclusion_of_free_level` (a level meeting no wall is free and hence a crossing — this
   is why, under failure, *every* level meets a wall), `joinedIn_both_of_mem_collar_components` (the
   sufficient direction) and `no_crux_collar_disjoint` (failure forces the collar components apart). -/

/-! ### STATUS (session 66): the *potential* is FALSE too; the residual is again `mv_obligation`

Read this **first** (and then the session-65 and session-64 blocks, which record the earlier
corrections).

Two sessions ago the single `sorry` of this file was moved onto the *potential*

  `exists_equivariant_potential` : `W` open, `T`-invariant, `W ⊆ stripS a b`, `hno` (no translate
  crossing inside `W`) ⟹ ∃ continuous `T`-equivariant `Ψ` with `Ψ (Tmap p q) = Ψ q + 1`,
  `Ψ` integer-free on `W`, and `∀ n`, `levelSet Ψ n ∩ stripS a b` preconnected,

with `mv_obligation` then obtained from it via `one_side_no_crossing_of_potential`.  **That
statement is false** — the two-banded spiral tower refutes it; the full argument is in the comment
block next to `one_side_no_crossing_of_potential` (and it rests on the machine-checked,
axiom-clean `AccRefute.tower_hypotheses` / `AccCE.no_spanning` of
`Submission/Work/Topology/Strip/accumulating_refutation_of_no_translate_path.lean`).  In the tower's
free region `W` there is no translate crossing (`hno` holds) and yet no such `Ψ`: any level set
would be a preconnected subset of the wall set `K'`, hence would avoid one of the two horizontal
bands `(0,1)`, `(1,2)`; that band is connected and `T`-invariant, so it would have to lie in a single
region `{j < Ψ < j+1}`, which is carried by `T` to the next region — a contradiction.

So the residual of this file is again **`mv_obligation`** (the true content: a translate crossing
inside `VA ∩ VB`, i.e. Denne's `prop:homology` / Mayer–Vietoris cancellation), and the file has
exactly **one** `sorry`, sitting on it.  What is *not* refuted is the potential for the special shape
`W = VA ∩ VB` with `VA, VB` open covering the strip: there the tower configuration is impossible,
because no split of the tower's wall set into two pieces both of whose complements are open *in `ℝ²`*
exists (each band's walls accumulate on the interface line, which would then have to lie in both
closed pieces).  So the potential remains a legitimate *sufficient* statement in the crux setting;
what is dead is the general statement, and with it the claim that the residual is "only" the
potential.

The proved implication `one_side_no_crossing_of_potential` (any potential whatsoever forces one of
`VA`, `VB` to carry no translate crossing) is kept, and the refuted statement is recorded as the
`def potentialStatement`. -/

/-! ### STATUS (session 65): the "strip accumulation" form of the wall duality is FALSE; the correct
form is the **quotient (annulus) form**, and it is equivalent to the crux

Read this **first**.  Session 65 asked the fleet for the wall statement

  `hno ⟹ ∃ C ⊆ K preconnected with a, b ∈ closure (heights '' C)`

in its former "strip accumulation" form (closed in the open strip, `T`-invariant, no translate
crossing in the complement).  **A colleague machine-refuted it** (`sorry`-free; the refutation is in
`Submission/Work/Topology/Strip/accumulating_refutation_of_no_translate_path.lean`, theorem
`AccRefute.accumulating_statement_false`, and the accompanying `NOTES_accumulating_continuum_REFUTED.md`).
The counterexample is the **two-banded spiral tower**: `p = 1`, `a = 0`, `b = 2`,
`f y = log y - log (1-y)`, the spiral walls `W m = {q | 0 < q.2 < 1 ∧ q.1 = f q.2 + m}`,
`K' = ((ℝ×{0} ∪ ℝ×{1} ∪ ⋃_m W m) ∪ (that shifted up by 1)) ∩ {0 < q.2 < 2}`.
Then `K'` is `T`-invariant and closed in the open strip, its complement contains **no** translate
crossing, and yet **every** preconnected `C ⊆ K'` has height-closure contained in `[0,1]` or in
`[1,2]` — the two bands are glued only by *accumulation* of the walls at the interface line
`q.2 = 1`, which belongs to `K'`.  So the "heights accumulate at both ends of the strip" form is
**insufficient**: the spanning has to be measured **in the annulus** (`Ω/T`), where the two bands are
genuinely glued by that accumulation.

The statement to aim at is therefore the **quotient form**

  `hno ⟹ ∃ C ⊆ K preconnected with a, b ∈ closure (heights '' ⋃_{k : ℤ} T^k '' C)`

(i.e. the image of `C` in the annulus `(ℝ/pℤ) × (a,b)` is a continuum whose closure meets both
boundary circles).

**Warning: the quotient form does not by itself replace the potential.**  The derivation that worked
for the (refuted) strip form used the companion statement "a spanning preconnected `C ⊆ K` blocks
every translate crossing in `Ω \ K`" (the commons' `wall_blocks_translate_path`).  That companion is
**false** for the quotient notion of spanning: `C = {0} × (a,b)` is quotient-spanning (its
`T`-saturation `⋃_k {k p} × (a,b)` has heights whose closure is `[a,b]`) and yet the horizontal
segment at height `(a+b)/2` from `x = 0` to `x = p` avoids it.  So quotient-spanning is *not* a
certificate of blocking, and the "wall" route to `mv_obligation` — in either its strip or its
quotient form — does not go through in the naive way.  The file's residual therefore stays where
session 64 put it: the potential.

**The crux is not refuted by any of this** (the tower refutes the *strip* form of the duality, not
the crux; see the caveat at the end of this block).  The unproved residual of this file
remains a *single* statement, but the route it takes is the potential one (see session 64 below),
whose hypothesis (`hno` for `W = VA ∩ VB`) is not refuted by the two-banded tower.  What the tower
does refute is only the *strip* form of the wall duality, i.e. every attempt to replace the potential
by "the complement of `W` contains a piece whose heights accumulate at `a` and `b`".

**Why the crux is *not* refuted by the two-banded tower** (checked this session, by hand).  In the
tower the complement of `K'` has no translate crossing, but `K'` is *not* the complement of a
`VA ∩ VB` of a no-crux configuration: if one puts
`KA = (band-(0,1) walls) ∪ {y = 1}` and `KB = (band-(1,2) walls)`, then `VA = Ω \ KA` and
`VB = Ω \ KB` do satisfy all the crux's hypotheses and `W = VA ∩ VB` is the union of the corridors;
and **in the annulus** `W/T` is *not* a union of disks — the image of a single corridor
`{n < q.1 - f q.2 < n+1, 0 < q.2 < 1}` in `(ℝ/pℤ) × (a,b)` is the band minus the spiral
`{y = f(y) mod p}`, i.e. an annulus cut along a crosscut, a **disk** in the strip — but the
Mayer–Vietoris exactness in the annulus
`H₁(W/T) → H₁(VA/T) ⊕ H₁(VB/T) → H₁(Â) → 0`
nevertheless forces `H₁(W/T) ≠ 0` whenever `VA/T` and `VB/T` both contain classes of *opposite*
degree (the kernel of `(a,b) ↦ deg a + deg b` is then nonzero), and `H₁(Â) = ℤ`.  **Status of this
argument: not fully verified.**  It is the Mayer–Vietoris exactness of the two-set cover that is being
used, which is a theorem; but the conclusion `H₁(W/T) ≠ 0` is in tension with the fact that the
connected components of `W` for the tower are the *corridors*, each of which is homeomorphic to a
disk (`{n < q.1 - f q.2 < n+1, 0 < q.2 < 1} ≅ (0,1)²`), hence simply connected.  One of the two
computations must be wrong, and locating the error is exactly the "identification layer" that MV for
`H₁` would supply — it is *not* settled here.  What is certain:
* per the machine-checked refutation, the *strip* form of the duality is false;
* the crux is therefore **not** refuted by the tower *via* the strip form;
* so the tower must not be used to conclude that the target is false.
Resolving the tension (i.e. building Mayer–Vietoris for `H₁` of a two-set open cover, plus the
degree/`π₁` identification for open subsets of the annulus) is the next concrete obligation of the
project; it is the piece whose absence is the reason the file's own route goes through the
potential.

Session-64 status block (kept for the record) follows. -/

/-! ### STATUS (session 64): IDEA AA is FALSE; the residual is the meeting of the two essential parts

Read this first.  Two things changed this session.

* **IDEA AA (the free-graph route to the potential) is FALSE** — see the correction and the explicit
  counterexample a few paragraphs below.  The `T`-invariant open `W` there satisfies `hno` and yet
  admits *no* continuous `u` with `(u y, y) ∉ W`, so `exists_potential_of_crosscut_graph` cannot be
  applied and the potential has to be produced by the *ladder* route (the sliding level sets).  The
  chain of the file is unaffected (nothing depends on IDEA AA), but the documentation that used to
  claim otherwise is gone.
* **The residual is now cleanly stated and unconditional**: with the component engine
  `component_meets_of_isOpen_cover` (new at the bottom of the file) one gets, for *any* open
  `T`-invariant `VA, VB` covering the strip with `hwindA` (no hypothesis on the crux at all),

    `Ess p VA ∩ VB ≠ ∅` and `Ess p VB ∩ VA ≠ ∅`   (`ess_inter_VB_of_cover`, `ess_inter_VA_of_cover`),

  i.e. each essential part is known to meet the *other* set.  By `crux_of_ess_W_path` the crux is
  *equivalent* to `Ess p VA ∩ Ess p VB ≠ ∅`.  So the whole remaining content of the crux is exactly
  the passage from "each essential part meets the other set" to "the two essential parts meet", or
  equivalently: **the `T`-invariant (`=` essential) component of `VA` and the `T`-invariant component
  of `VB` — both of which are known to meet the *other* set — meet each other.**  In sheet language:
  the `A`-essential sheet-orbit and the `B`-essential sheet-orbit must coincide.  Everything else in
  the file (the rigidity `eq_stripS_of_component_disjoint`, the splitting, Janiszewski, the Tietze
  glue, the `τ > σ` regime, …) is proved.

The pre-session-64 status block is kept below for the record. -/

/-! ### STATUS (session 63): the gap is IDEA AA, and the no-crux case is now rigid

Read this first.  Session 63 proved four new lemmas (bottom of this file,
`joinedIn_slide` … `no_crux_ess_inter_other`) and thereby pinned the remaining gap to a single
*self-contained* statement, IDEA AA below.  The structure of the file is unchanged: exactly one
`sorry`, sitting on `exists_equivariant_potential`; everything else in this file is proved.

#### What was proved this session

* `joinedIn_slide`: a translate crossing can be re-based along a path of `W = VA ∩ VB`.
* `crux_of_ess_W_path`: if a point of `Ess p VA` is joined **inside `W`** to a point `y` with
  `y ~ T y` in `VB`, then the crux holds (via `joinedIn_slide` + `W ∪ VB = VB`).
* `no_crux_no_joinedIn_W_of_ess`: under the *failure* of the crux, no path of `W` joins
  `Ess p VA` to `Ess p VB`.
* `no_crux_ess_inter_other`: under the failure of the crux, `Ess p VA ∩ VB` and `Ess p VB ∩ VA`
  are both **nonempty** (a sharpening of the file's `component_meets_of_no_crux`: the component of
  an essential point of `VA` lies in `Ess p VA` and meets `VB`).

So the *negation* of the crux has the following exact shape, and nothing more is known:

  `W = VA ∩ VB` is open, `T`-invariant, `Ω = W ⊔ K_A ⊔ K_B` with `K_A = VA ∖ VB`, `K_B = VB ∖ VA`
  closed, `T`-invariant, disjoint, `Ω = stripS a b`; **no** path of `W` joins `Ess p VA` to
  `Ess p VB`, while both `Ess p VA ∩ W` and `Ess p VB ∩ W` are nonempty unions of components of `W`.

#### The gap, stated as a single self-contained lemma (IDEA AA)

  **IDEA AA.**  `W ⊆ Ω` open, `T`-invariant, with no translate crossing inside `W` (i.e.
  `∀ q ∈ W, ¬ JoinedIn W q (T q)`) — *then there is a continuous `u : ℝ → ℝ` with*
  `(u y, y) ∉ W` *for every* `y ∈ (a,b)`.

`exists_potential_of_free_graph` (proved in this file, session 53) constructs the equivariant
potential from exactly such a graph, so **`exists_equivariant_potential` ⟸ IDEA AA** and the whole
file follows.

**CORRECTION (session 64): IDEA AA is FALSE.**  The evidence that used to be recorded here was
wrong.  Explicit counterexample (`a < ½ < b`, e.g. `a = 0`, `b = 1`, `p = 1`):

  `W := {q | q.2 < ½ ∧ q.1 ∉ ℤ} ∪ {q | ½ < q.2 ∧ q.1 ∉ ℤ + ½}`.

`W` is open, `T`-invariant (`T (x,y) = (x+1, y)`), contained in `stripS a b`, and **satisfies `hno`**:
its components are the open rectangles `(k, k+1) × (a, ½)` and `(k+½, k+3/2) × (½, b)`, and `T` maps
each of them to a *different* component, so no component contains both `q` and `T q`.  But there is
**no** continuous `u` with `(u y, y) ∉ W` for all `y ∈ (a,b)`: for `y < ½` the condition
`(u y, y) ∉ W` forces `u y ∈ ℤ`, and for `y > ½` it forces `u y ∈ ℤ + ½`; a continuous `u` must be
constant on each of the two intervals `(a,½)`, `(½,b)` (its image there is a connected subset of a
discrete set), and the two constants have to agree at `y = ½`, which is impossible because
`ℤ ∩ (ℤ + ½) = ∅`.  Hence **`exists_potential_of_crosscut_graph` has a hypothesis that `hno` does
not imply**, and the potential must be obtained by the *ladder* route, not from a free graph.  (The
potential itself does exist for this `W`, so it is IDEA AA, not `exists_equivariant_potential`, that
is the false statement; see the next paragraph.)

**What the counterexample's ladder looks like.**  The level sets have to *slide along the level
line* `{q.2 = ½}`, which is *entirely inside* `K = stripS a b \ W` (the sheets above and below do
not connect, because the whole level line is a wall).  With the walls `m_y := ℤ` for `y < ½` and
`ℤ + ½` for `y > ½`, the ladder is

  `L n = {n} × (a, ½) ∪ [n - ½, n] × {½} ∪ {n - ½} × (½, b)`   (`n : ℤ`),

a `T`-orbit of closed preconnected subsets of `K` (`T '' L n = L (n+1)`), and the corresponding `Ψ`
equals `⌊x⌋ + min (2 · frac x, 1)` at `y = ½`, interpolated on the two half-strips.  So the general
mechanism is: **a level line that lies completely in `K` gives the level sets the freedom to slide
along it**, and that sliding is what replaces the (nonexistent) continuous selection `y ↦ (u y, y)`
of a wall point.  The `rungRatio` toolkit below is the general form of this interpolation.

**The mechanism, corrected (session 63's account was incomplete).**  Under `hno` the cover
`W → W/T` has trivial monodromy, so `W = ⊔_{i,k} T^k C_i` and `W/T = ⊔_i D_i` with each `D_i`
carrying the ℤ-stack of sheets `T^k C_i`.  At each height `y` the circle `ℝ/pℤ × {y}` is tiled by
the closed set `K_y/T` and the open arcs coming from the various `D_i`; the *sheet label* of each arc
is a ℤ-valued function of `(i, y)`.  Session 63 claimed that a **cyclic rotation of the labels** as
`y` runs from `a` to `b` would be the monodromy that `hno` forbids, so that the labels would have to
be constant in `y` and a continuous crosscut `y ↦ (u y, y) ∈ K` would follow.  The counterexample
above shows that this is *false*: the labels **do** rotate (the phase jumps by `-½` at `y = ½`), and
`hno` does not forbid it, because the rotation happens at a level line that lies *completely* in
`K`.  What `hno` forbids is a rotation that takes place where the two sheet families actually meet
(there the sheets would join up and `W` would acquire a `T`-periodic component).  So the correct
residual is not "constant labels" but "labels that may jump only along level lines contained in
`K`" — i.e. exactly the *ladder* of the previous paragraph, whose rungs slide along those level
lines.

**The concrete sub-target that would finish it, corrected (session 63, second half).**  The first
guess — "under `hno`, normalise the sheet index `ind` so that crossing every wall raises it by
exactly one" — is **wrong**, and here is the counterexample: the *two-ladder* set
`K = ⋃_m {x = f(y) + m} ∪ ⋃_m {x = g(y) + m}` with `0 < g - f < p` satisfies `hno` (its sheets
`{f+m < x < g+m}` and `{g+m < x < f+m+p}` are `T`-free) and its complement *does* carry a potential,
namely `Ψ (x,y) = (x - f y)/p`, whose level sets are the `f`-ladder alone.  The `g`-ladder carries
*non-integer* values of `Ψ` (it is `g - f`, not an integer).  So **the level sets of a potential need
not exhaust `K`**, walls of `K` need not be integer levels of `Ψ`, and the index-jump across two
different wall families need not be the same (`1` across the `f`-ladder, `0` in the `Ψ`-normalisation
across the `g`-ladder).  The corrected statement of the residual is therefore the one the file
already isolated in session 54, in the *ladder* form:

  **IDEA AA (ladder form).**  Under `hno`, `K = Ω \ W` contains a **ladder**: a `T`-orbit `{L n}`
  (`n : ℤ`) of closed preconnected subsets of `K` with `T (L n) = L (n+1)` and such that *every*
  translate crossing meets some `L n`.

For the two-ladder set the ladder is the `f`-ladder; for the spiral it is the spiral's rung family.
`levelSet_ladder_of_equivariant_potential` gives the converse direction (potential ⟹ ladder, with the
ladder the integer level sets), so the ladder form and the potential form are equivalent *given* the
preconnectedness of the level sets.  The remaining work is thus: (i) prove that `hno` forces such a
ladder to exist inside `K`, and (ii) prove that a ladder in `K` yields the potential (a "separation
by a ladder" statement: the rungs `L n` cut `Ω` into the slabs between consecutive rungs, on which
`Ψ := n + (relative position)` is continuous and `T`-equivariant).  Direction (ii) is a purely
topological construction; direction (i) is where `hno` is spent.

**The design of piece (ii) — "ladder ⟹ potential" (session 63, end).**  This is now worked out
concretely; the construction is the *distance-ratio* one.

Data: rungs `L : ℤ → Set (ℝ × ℝ)`, pairwise disjoint, closed, preconnected, `L n ⊆ K`,
`Tmap p '' L n = L (n+1)`, and a *rung number* `N : ℝ × ℝ → ℤ` which is (a) `T`-equivariant
(`N (Tmap p q) = N q + 1`), (b) locally constant off `⋃ n, L n`, (c) equal to `n` on `L n`, and
(d) "slab-correct": near a rung `L n`, every point off the rungs has `N ∈ {n-1, n}`.

Define, off the rungs,
```
Ψ q := (N q : ℝ) + φ q,     φ q := d (q, L (N q)) / (d (q, L (N q)) + d (q, L (N q + 1)))
```
(`d` the point-to-set distance), and put `Ψ q := (N q : ℝ)` on the rungs.

Three mechanisms make this work:
* **Continuity at a rung by cancellation.**  Approaching `L n` from the slab below (`N = n-1`) the
  ratio `φ` tends to `1` (the numerator tends to `dist (L n) (L (n-1)) > 0`, the denominator to the
  same), so `Ψ → (n-1) + 1 = n`; approaching from the slab above (`N = n`) the ratio tends to `0`
  (the numerator tends to `0`), so `Ψ → n + 0 = n`.  *`φ` itself is discontinuous at the rungs;
  `Ψ` is continuous because the two jumps cancel.*  This is the reason the distance ratio (rather
  than any single-valued collar function) is the right formula: a `T`-invariant `φ` taking a single
  value on each rung can never be continuous there.
* **`T`-equivariance.**  `N (T q) = N q + 1` and `d (T q, L (N q + 1)) = d (q, L (N q))` (from
  `Tmap p '' L k = L (k+1)` and `T` being an isometry), so `Ψ (T q) = Ψ q + 1`.
* **Level sets and integer-freeness.**  On the slab where `N = n`, `Ψ ∈ (n, n+1)` (the ratio lies in
  `(0,1)`; the endpoints `0` and `1` are attained only at the rungs `L n`, resp. `L (n+1)`), so
  `Ψ = n` exactly on `L n`: the integer level sets are the rungs, hence preconnected and contained
  in `K`.  Conversely for `q ∈ W = Kᶜ` one has `d (q, K) > 0` (`K` closed), so the ratio is
  *strictly* between `0` and `1` and `Ψ q ∉ ℤ`.

Hypotheses needed beyond the rungs: the rung number `N` (a) – (d) above, and the "separation"
`0 < dist (L n) (L k)` for `k ∉ {n-1, n, n+1}` (non-adjacent rungs are a positive distance apart),
which is used both for the continuity of `Ψ` at the rungs and for (d) to be meaningful.  The
dichotomy "`Ψ q = n` ⟹ (`N q = n` and `φ q = 0`) or (`N q + 1 = n` and `φ q = 1`)" is the
arithmetic content and has been checked (`0 ≤ φ ≤ 1` and `N + φ = n` for `n, N : ℤ` force this).

**Status of the pieces (session 63, end).**  The *analytic half* of the construction above is now
proved in this file: `isometry_Tmap`, `infDist_Tmap_image` (the `T`-equivariance of the distances to
the rungs), and the `rungRatio` toolkit — `rungRatio_nonneg`, `rungRatio_le_one`,
`rungRatio_eq_zero`, `rungRatio_eq_one`, `continuousOn_rungRatio` — together with the arithmetic core
`int_dichotomy_of_add_le` and the cancellation `cast_pred_add_one`.  Given the rung number `N`, the
assembly of `Ψ` from these is mechanical: `Ψ := N + rungRatio (L (N q)) (L (N q + 1))` off the rungs
and `Ψ := N` on them.

So the only remaining ingredient of piece (ii) is: **construct the rung number `N`** — this uses the
commons' `top_bottom_continuum_meets_left_right_path` (a continuum joining the two boundary lines
meets every left–right path, hence separates) to define "the number of rungs to the left" — and then
run the above construction.  Piece (i) (`hno` ⟹ such a separating ladder exists in `K`) is the
remaining place where `hno` is spent.

**A trap found this session (do not repeat).**  The naive selection `u(y) := max (K_y ∩ (-∞,0])`
is *upper* semicontinuous but not continuous: it jumps exactly at a "vertical jump" of `K`, e.g. for
`K = ({0} × (a,c]) ∪ ({1/2} × [c,b))` (which is closed, `T`-invariant and meets every level, and for
which `u` jumps from `0` to `-1/2` at `c`).  This `K` has no crosscut graph — but it also **fails**
`hno` (the punctured neighbourhood of `(0,c)` and of `(1/2,c)` glue the two bands).  Any proof of
IDEA AA must therefore *use* `hno` to rule out such a jump, which is where the "sheet order is not
rotated" statement above has to be spent.  Note also that a point of `K` isolated in `K` (so that a
punctured box around it lies in `W`) is *not* by itself a contradiction with `hno` (the small loop
around it is not a translate crossing), so isolating a "jump" is not enough — one has to exhibit the
resulting rotation.

**Template for the proof.**  `Commons.Topology.Strip.barrier_bottom_top_of_no_left_right` proves the
dually-flavoured statement "`K` meets every left-right path in the closed box `⟹` `K` contains a
top-bottom continuum" by (i) the clopen decomposition `exists_clopen_separating_of_no_component`,
(ii) the affine transport of the box to the unit square, and (iii) the **planar** lemma
`Commons.Topology.Jordan.square_sets_top_bottom_continuum`.  The same three ingredients, applied to
the conclusion's *negation* (every component of `K` is bounded away from `a` or from `b`), should
produce a left-right continuum in `W`; the extra input needed to turn that continuum into a
`(u y, y)` **graph** is the "closing-up" isometry: a path of `W` from `(0,y₀)` to `(p,y₁)` forces
`K` to meet the vertical segment `{p} × [y₀,y₁]` (the file's `vertical_segment_meets_of_joinedIn`).

**Caution recorded this session.**  The "two-phase" set
`W = ⋃_k ((k-0.2, k+0.8) × (0,½)) ∪ ⋃_k ((k+0.3, k+1.3) × (½,1))` (`p = 1`) is open, `T`-invariant,
lies in the strip and satisfies `hno`, but its complement `K` is **connected**; hence it admits no
decomposition `K = K_A ⊔ K_B` into two disjoint closed `T`-invariant parts, so it is *not* a
no-crux configuration.  Any future counterexample (or proof) must use the disconnectedness of `K`
forced by the two-set cover.

#### Secondary route (unchanged)

The Mayer–Vietoris argument of Denne (`prop:homology`, arXiv:math/0510561) remains the only known
*proof* of the crux.  Mathlib has the MV algebra but not the identification layer with the degree-1
translate-crossing vocabulary of this file; the sheaf-cohomological MV is the wrong theory
(`H' 1(annulus, ℤ)` needs the `K(ℤ,1)` identification).  IDEA AA is the elementary substitute.-/

/-! ### STATUS (session 50): the crux is reduced to ONE construction, and `mv_obligation` is proved

Read this first.  The file has exactly **one** `sorry` left, and it is no longer on `mv_obligation`:
that obligation is now *proved* (from the potential, see below), as is the whole chain
`annulus_essential_intersection ⟸ crux_Z_meet ⟸ crux_of_finite_orbit_component + mv_obligation`.

The single remaining gap is

  `exists_equivariant_potential`: for `W` open, `T`-invariant, `W ⊆ stripS a b`, with no translate
  crossing inside `W` (`hno`), there is a continuous `T`-equivariant `Ψ` which is integer-free on `W`
  and whose level sets are preconnected and lie in the strip.

and the reduction of the crux to it is fully formal in this file:

* `exists_sheet_index_aei` (session 48) — the sheet index `ind : W → ℤ`, constant on components, with
  `ind (T q) = ind q + 1`, built from the free `T`-action on the components of `W` given by `hno`;
* `cellPotential`, `exists_potential_on_free_region` (session 49, "seam (i)") — the within-cell
  coordinate and the potential on `W`: `Ψ = ind + (q.2 - a)/(b - a)`, continuous on `W`,
  `T`-equivariant, integer-free on `W`, normalised;
* `no_crossing_of_potential_avoids_integers` (session 49, "Piece 3a") — a potential blocks every
  translate crossing through its integer levels (intermediate value theorem);
* `one_side_no_crossing_of_potential` (session 50) — if such a `Ψ` exists on the whole strip (level
  sets preconnected and inside the strip), then either *all* level sets lie in `VAᶜ` — whence `VA`
  avoids all integers and Piece 3a kills every crossing inside `VA` — or all lie in `VBᶜ`; so one of
  the two sets has no translate crossing at all, contradicting `hwindA`/`hwindB`.

No compactness, no homology, no wall-accumulation: the two obstacles that the earlier sessions named
(the refuted accumulation form, and the vacuity of `wall_blocks_translate_path` in the target's
configuration) are bypassed.

The three seams of `exists_equivariant_potential`:

* **(i) the within-cell coordinate — done** (`cellPotential`, `exists_potential_on_free_region`).
* **(ii) the behaviour at a wall — bricked** (session 51): `sheetIndex_eq_on_of_isOpen_isPreconnected`
  (the index is constant on a sheet), `cellPotential_tendsto_of_preconnected` (on a sheet `C` the cell
  potential has the limit `ind(C) + (q₀.2 - a)/(b - a)` at every strip point `q₀`, so the boundary
  behaviour at a wall point is pinned down from inside each sheet), and
  `cellPotential_tendsto_eq_of_same_index` (sheets of equal index have the same limit).  What remains
  of (ii) is the compatibility between sheets of *different* index, which is precisely where the cell
  coordinate must replace the raw height.
* **(iii) preconnectedness of the level sets — bricked** (session 51):
  `cellPotential_levelSet_translate`, the `T`-permutation `T '' {Ψ = c} = {Ψ = c + 1}` of the level
  sets that the assembly consumes.  What remains is their preconnectedness (equivalently, that the
  walls are the graphs/level sets of a potential rather than an arbitrary closed blocking set).  Equivalent form:
write `Ψ q = (q.1 + g q)/p`; then `g` must be continuous, `T`-invariant, and the shifted projection
`q ↦ q.1 + g q` must avoid the meridian orbit `pℤ` on `W`.  In the simplest configurations `g ≡ 0`
works (whenever `W` misses the vertical lines `{x ∈ pℤ}`). -/

/-! ### STATUS (session 45): the "wall" reduction removed, and a caution for the "wall" files

Read this first if you are working on the crux from a "wall existence" angle (this file and the
parallel `Work/Topology/Strip/two_closed_crossing_of_annulus.lean`, `annulus_duality.lean`).

The former content of this file was a reduction of the crux to a *wall existence* statement:

  `K ⊆ Ω = stripS a b` closed in `Ω`, `T`-invariant, no point of `Ω \ K` joined to its translate
  inside `Ω \ K`  ⟹  `∃ C ⊆ K` preconnected with `a, b ∈ closure (heights '' C)`,

from which `mv_obligation` was derived by splitting the preconnected set along `VAᶜ`, `VBᶜ` and
applying `Commons.Topology.Strip.wall_blocks_translate_path`.  That derivation has been **removed**
(the statement is not used anywhere in this file now), so the file's single `sorry` sits directly
on `mv_obligation`, which is *equivalent* to the crux (`mv_one_iff_crux`,
`crux_of_finite_orbit_component`) and is exactly Denne's Mayer–Vietoris input.  Nothing in the file
depends on the wall statement any more, so the file is sound whatever its truth value.

**Caution: a "straight-wall" counterexample to the wall statement is invalid.**  The refutation of
the wall statement recorded in `Work/Topology/Strip/two_closed_crossing_of_annulus.lean` §(G1) uses
walls that are *graphs escaping to infinity* at the level lines.  A naive variant with *straight*
walls (for instance `K = ({x - 2y ∈ ℤ} ∩ {q.2 ≠ 1/2}) ∪ {q.2 = 1/2}`, which is closed in the strip,
`1`-periodic, and has no translate crossing in its complement) is **not** a counterexample: there
each wall's closure meets the level line `L = {q.2 = 1/2}`, hence `L ∪ W` is connected for every wall
`W`, and then `(L ∪ W) ∪ W'` is connected for every pair of walls — by the elementary criterion

  *if `A` and `B` are connected and `A ∩ closure B ≠ ∅`, then `A ∪ B` is connected* —

so `K` is in fact connected, and a connected `K` that meets every level line *always* witnesses the
conclusion: its height set contains `(a,b)`, so its height closure contains `[a,b]`.  Any verification
of such a refutation must therefore be done on the actual **components** of `K` (every preconnected
subset of `K` lies in one of them, so a componentwise check is sufficient — but not every union of
walls *is* a component), with walls whose closures avoid the finite points of the level lines.

Also proved in this file this session (sorry-free, useful independent of the crux):

* `crux_of_component_subset_inter` — if the essential component `C = connectedComponentIn VA z` of an
  essential point of `VA` is contained in `VA ∩ VB`, the crux holds;
* `connected_of_meets_every_level` — a connected `K ⊆ Ω` meeting every level line witnesses the wall
  conclusion (so counterexamples to the wall statement must be disconnected);
* `level_subset_compl_left_or_right` — if a whole level line `{q.2 = y}` of the strip avoids
  `VA ∩ VB`, then it misses `VA` or misses `VB`;
* `vertical_segment_meets_of_joinedIn` — "closing up": a path in `Ω \ K` from `(0,y₀)` to the meridian
  `{x = p}` at height `y₁` forces `K` to meet the vertical segment at `x = p` between the heights
  `y₀` and `y₁`;
* `eq_stripS_of_component_disjoint`, `component_meets_of_no_crux` (earlier sessions) — the rigidity
  lemma: a component of `VA` missing `VB` forces `VA = stripS a b`.

-/

/-! ### STATUS OF THE CRUX (session 28): where the missing mathematics actually is

Denne's `prop:homology` was located in the literature (arXiv `math/0510561`, *Alternating
Quadrisecants of Knots*, proof of `prop:homology`).  Its statement there has **two extra
hypotheses** which the present crux (and the target) *do not* have: `A` lies outside some
neighbourhood `U` of `Δ_+` and `B` lies outside some neighbourhood `V` of `Δ_-`.  These are used
only to *exhibit* a winding-one curve `α ⊆ U ⊆ S∖A` and a winding-one curve `β ⊆ V ⊆ S∖B` with
opposite orientations; the Mayer–Vietoris step then uses only `α, β`.

**Careful re-reading of the Mayer–Vietoris step (this is a genuine gap in the naive use of it).**
With `W̄ = UA ∩ UB`, MV exactness at `H₁(UA) ⊕ H₁(UB)` gives a class `x ∈ H₁(W̄)` with
`(i_A)_* x = α`, hence `deg x = deg α = 1`.  But `H₁(W̄) = ⊕_i H₁(Ŵ_i)` over the components `Ŵ_i`
of `W̄`, and `deg(H₁(Ŵ_i)) ⊆ m_i ℤ` where `m_i = [ℤ : im(π₁(Ŵ_i) → ℤ)]`.  From
`Σ_i deg(x_i) = 1` one can NOT conclude `m_i = 1` for some `i` (e.g. `3 + (−2) = 1` with
`m_i = 3, 3` is not excluded).  So MV alone yields only "some component of `W̄` has a loop of
non-zero winding", not "has a winding-one loop".

**The missing ingredient, precisely.**  The crux is equivalent to some component `Ŵ` of `W̄` having
`m = 1` (a `T`-invariant component of `W = VA ∩ VB`).  Together with MV's "some `m_i ≠ ∞`" it is
therefore *enough* to know:

> (`Period lemma`)  If `C` is a connected component of a `T`-invariant open subset of the strip
> with `C ∩ T C = ∅`, then the `T`-orbit of `C` is infinite (equivalently `T^m C ≠ C` for all
> `m ≥ 2`); i.e. for an open `Ŵ` in the annulus, `[ℤ : im π₁(Ŵ)] ∈ {1, ∞}`.

With `m_i ∈ {1, ∞}` the identity `Σ_i deg(x_i) = 1` forces some `m_i = 1`, giving the crux.  So the
whole problem is: **MV (not in Mathlib) + the period lemma.**

**Why the period lemma is true.**  `C = π^{-1}(Ĉ)` for `Ĉ` open connected in the `m`-fold cover
`A_m`, with `Ĉ ∩ σ^j Ĉ = ∅` for `j ≢ 0 (mod m)`.  `C` connected ⟺ `Ĉ` contains a *generator* loop
`γ`.  Lifting, `γ` is a path `γ̃` in the strip from `x` to `x + m p` (`m ≥ 2`) with
`γ̃ ∩ T^k γ̃ = ∅` for `k ≢ 0 (mod m)`, in particular `γ̃ ∩ T γ̃ = ∅`; the descent of `γ̃` to the
annulus `Ω/T` is then a **simple** closed curve of degree `m`.  A simple closed curve in an annulus
has degree `−1, 0` or `1` (Jordan curve theorem: it bounds a disk, which either does not contain
the hole or contains it once).  Contradiction.  --- This route needs *path lifting / covering
theory* plus the Jordan fact for simple closed curves in an annulus; both are far from the present
state of the library, but the second is genuinely elementary.

**The `m = 2` (and graph) case of the period lemma is elementary and proved below** as
`exists_period_translate_eq`: if `h : ℝ → ℝ` is continuous and periodic of period `m * p`
(`m ≥ 2`), then `h (x + j * p) = h x` for some `x` and some `1 ≤ j < m`.  Proof: all the
comparisons `h (x + i*p) < h (x + j*p)` (`i ≠ j`) are locally constant in `x` (their level sets are
open by continuity, and their complements too, using that the `m` values are pairwise distinct), so
they are *constant*; hence the rank function `r(j) = #{i < m | h (x+i*p) < h (x+j*p)}` does not
depend on `x` and is injective, while the period identity `h (x + m*p) = h x` gives
`r(j + 1) = r(j)` — contradiction.  (For even `m` the Vandermonde product
`Π_{i<j} (h(x+j*p) − h(x+i*p))` is nowhere zero and changes sign under `x ↦ x+p`.)

**A valid closure lemma (elementary, and the reason the "no crux" case is so rigid).**  If `C` is a
connected component of `VA` (a `T`-invariant open set) and `C ∩ VB = ∅`, then `C ⊆ F_B` where
`F_B = Ω∖VB` is closed; since `F_B ∩ F_A = ∅` and `VA ∪ F_A = Ω`, we get `F_B ⊆ VA`, so
`closure C ⊆ F_B ⊆ VA`; as `C` is closed in `VA` this gives `C = closure C`, i.e. `C` is clopen in
the connected strip `Ω`, so `C = Ω` and hence `VA = Ω` (and then the crux follows immediately from
`hwindB`).  Consequently, **under "no crux", every `T`-invariant component of `VA` meets `VB`** (and
symmetrically), so the crux has been reduced to: *every `T`-invariant component `C_A` of `VA` meets
`VB`, every `T`-invariant component `C_B` of `VB` meets `VA`, ⇒ some such `C_A` meets some `C_B`.
-/

/-! ### STATUS OF THE CRUX (session 27): the "FALSE" verdict is not supported

A colleague's prover agent, and the checked warning recorded in
`Work/Topology/Strip/annulus_path_to_translate.lean` (line ~3212), state that `crux_Z_meet` (and
therefore the target of this file, which is equivalent to it) is **false** as stated, on the grounds
that it drops Denne's band hypotheses ("`A` avoids the top band, `B` avoids the bottom band").
The concrete machine-checked ingredient cited is `AccCE.no_path_K2`
(`Work/Topology/Strip/acc_ce_scratch.lean`, axiom-clean, no `sorry`): for any continuous
`f : (0,1) → ℝ` the closed, `1`-periodic set `K2 f = RefSnS.K f ∪ Ktop f` inside the closed strip
`[0,2]` admits **no** translate path avoiding it.

That evidence does **not** refute the crux, and here is the precise reason, checked this session:

* `K f ⊇ L0` (the proof of `L0_subset_K2` is `Or.inl (Or.inl (L0_subset_Kp …))`) and
  `K f ⊇ L1` (`Or.inl (Or.inr (L1_subset_Km …))`);
* hence `L1 ⊆ K f ∩ Ktop f` — because `q ∈ L1` gives `(q.1, q.2 - 1) ∈ L0 ⊆ K f`, i.e.
  `q ∈ Ktop f`.

So the blocking pair of walls `(K f, Ktop f)` has **nonempty intersection**.  In the crux the two
closed sets must be *disjoint* (equivalently: their complements must cover the strip), so this pair is
not a configuration of the crux at all, and `no_path_K2` is not a counterexample to it.  Likewise the
other cited refutations concern *different* statements (the "meets form" of the duality, the trivial
`periodic_component_of_no_spanning`, the `accumulation` form).

Independently, the Mayer–Vietoris derivation of the crux (see the discussion at `crux_Z_meet` and
`dennes_prop_homology`) is sound as far as it has been checked here: two essential classes
`α ∈ H₁(UA)`, `β ∈ H₁(UB)` (orientations chosen so that their degrees agree) satisfy
`ψ(α, β) = 0`, so exactness `im Φ = ker Ψ` gives `x ∈ H₁(UA ∩ UB)` with `(i_A)_* x = α`, hence a
degree-one class — an essential loop — in `UA ∩ UB`.

**Conclusion: the crux (and this file's target) should be regarded as OPEN, not false.**  The band
hypotheses of Denne's `prop:homology` are used in his proof only to *exhibit* the two loops explicitly
(one near each boundary); without them the same Mayer–Vietoris argument goes through with essential
classes in place of the explicit ones.  This is why the file keeps the reduction and the single
honest `sorry` rather than declaring the statement false. -/

open Set Filter
open scoped _root_.Topology

/-! ## The periodic strip and its essential points

This file reduces the target `annulus_essential_intersection` (Denne's cancellation lemma for a
two-set open cover of a periodic strip) to a single statement, `crux_Z_meet`, recording exactly
what remains to be proved.  All the bookkeeping around the reduction is proved here.
-/

/-- The open horizontal strip `a < q.2 < b`. -/
def stripS (a b : ℝ) : Set (ℝ × ℝ) := {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}

lemma stripS_iff {a b : ℝ} {q : ℝ × ℝ} : q ∈ stripS a b ↔ a < q.2 ∧ q.2 < b := Iff.rfl

/-- The translation `T q = (q.1 + p, q.2)`. -/
def Tmap (p : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1 + p, q.2)

@[simp] lemma Tmap_apply (p : ℝ) (q : ℝ × ℝ) : Tmap p q = (q.1 + p, q.2) := rfl

lemma Tmap_mem_strip {a b p : ℝ} {q : ℝ × ℝ} (hq : q ∈ stripS a b) :
    Tmap p q ∈ stripS a b := hq

lemma continuous_Tmap (p : ℝ) : Continuous (Tmap p) := by
  show Continuous fun q : ℝ × ℝ => (q.1 + p, q.2)
  fun_prop

lemma continuous_Tmap_inv (p : ℝ) : Continuous fun q : ℝ × ℝ => (q.1 - p, q.2) := by fun_prop

/-- **The essential part** of `V`: the points joined to their `T`-translate inside `V`.  Equivalently
the union of the `T`-invariant connected components of `V`. -/
def Ess (p : ℝ) (V : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {z : ℝ × ℝ | z ∈ V ∧ JoinedIn V z (Tmap p z)}

lemma ess_subset (p : ℝ) (V : Set (ℝ × ℝ)) : Ess p V ⊆ V := fun z hz => hz.1

lemma mem_Ess {p : ℝ} {V : Set (ℝ × ℝ)} {z : ℝ × ℝ} :
    z ∈ Ess p V ↔ z ∈ V ∧ JoinedIn V z (Tmap p z) := Iff.rfl

lemma joinedIn_translate {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {x y : ℝ × ℝ} (h : JoinedIn W x y) :
    JoinedIn W (Tmap p x) (Tmap p y) := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ.map (continuous_Tmap p), ?_⟩
  intro t
  exact (hW (γ t)).mp (hγ t)

lemma joinedIn_translate_inv {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {x y : ℝ × ℝ} (h : JoinedIn W x y) :
    JoinedIn W (x.1 - p, x.2) (y.1 - p, y.2) := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ.map (continuous_Tmap_inv p), ?_⟩
  intro t
  have hmem := hγ t
  exact (hW ((γ t).1 - p, (γ t).2)).mpr (by simpa [Tmap] using hmem)

lemma Ess_periodic {p : ℝ} {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (q : ℝ × ℝ) :
    q ∈ Ess p W ↔ Tmap p q ∈ Ess p W := by
  constructor
  · rintro ⟨hqW, hq⟩
    exact ⟨(hper q).mp hqW, joinedIn_translate hper hq⟩
  · rintro ⟨hqW, hq⟩
    have h := joinedIn_translate_inv hper hq
    exact ⟨(hper q).mpr hqW, by simpa [Tmap] using h⟩

/-- `Ess p W` is open when `W` is (it is a union of connected components of an open set). -/
lemma isOpen_Ess {p : ℝ} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) : IsOpen (Ess p W) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  refine ⟨connectedComponentIn W z, ?_, hW.connectedComponentIn,
    mem_connectedComponentIn hz.1⟩
  haveI : LocallyPathConnectedSpace (ℝ × ℝ) := inferInstance
  have hcompopen : IsOpen (connectedComponentIn W z) := hW.connectedComponentIn
  have hpc : IsPathConnected (connectedComponentIn W z) :=
    (hcompopen.isConnected_iff_isPathConnected).mp
      ⟨⟨z, mem_connectedComponentIn hz.1⟩, isPreconnected_connectedComponentIn⟩
  have hsub : connectedComponentIn W z ⊆ W := connectedComponentIn_subset W z
  intro w hw
  have hjoin : JoinedIn (connectedComponentIn W z) z w :=
    hpc.joinedIn z (mem_connectedComponentIn hz.1) w hw
  have h1 : JoinedIn W w z := (hjoin.mono hsub).symm
  have h2 : JoinedIn W (Tmap p z) (Tmap p w) := (joinedIn_translate hper h1).symm
  exact ⟨hsub hw, h1.trans (hz.2.trans h2)⟩

/-- **Key structural lemma.** If `C` is a `T`-invariant connected open subset of a set `W`, then
`C ⊆ Ess p W`. -/
lemma subset_Ess_of_conn {p : ℝ} {W C : Set (ℝ × ℝ)}
    (hCsub : C ⊆ W) (hCop : IsOpen C) (hCconn : IsConnected C)
    (hCinv : Tmap p '' C = C) : C ⊆ Ess p W := by
  haveI : LocallyPathConnectedSpace (ℝ × ℝ) := inferInstance
  have hpc : IsPathConnected C := (hCop.isConnected_iff_isPathConnected).mp hCconn
  intro z hz
  have hTz : Tmap p z ∈ C := by rw [← hCinv]; exact ⟨z, hz, rfl⟩
  exact ⟨hCsub hz, (hpc.joinedIn z hz (Tmap p z) hTz).mono hCsub⟩

/-- **Essentiality is a component property (basepoint pushing).**  If `z` is an essential point of an
open, `T`-invariant `W`, then every point of the component of `z` in `W` is essential too.  Hence a
`T`-crossing based at `z` may be re-based at any point of that component, and the crux depends only
on the *components* of `VA` and of `VB`. -/
theorem connectedComponentIn_subset_Ess {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (hWop : IsOpen W)
    {z : ℝ × ℝ} (hz : z ∈ Ess p W) :
    connectedComponentIn W z ⊆ Ess p W := by
  intro q hq
  have hzW : z ∈ W := ess_subset p W hz
  have hqW : q ∈ W := connectedComponentIn_subset W z hq
  have hpc : IsPathConnected (connectedComponentIn W z) :=
    (hWop.connectedComponentIn.isConnected_iff_isPathConnected).mp
      ⟨⟨z, mem_connectedComponentIn hzW⟩, isPreconnected_connectedComponentIn⟩
  have hqz : JoinedIn W q z :=
    (hpc.joinedIn q hq z (mem_connectedComponentIn hzW)).mono (connectedComponentIn_subset W z)
  have hTqTz : JoinedIn W (Tmap p q) (Tmap p z) := joinedIn_translate hW hqz
  exact ⟨hqW, hqz.trans (hz.2.trans hTqTz.symm)⟩

/-- **The crux only depends on the components of `VA` and `VB`.**  If the component of an essential
point of `VA` meets the component of an essential point of `VB`, then the crux's conclusion holds:
the meeting point is essential for both sets.  This is the "basepoint pushing" form of the crux —
the remaining content is exactly that two such components meet. -/
theorem ess_meets_of_components_meet {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA) (hB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hAop : IsOpen VA) (hBop : IsOpen VB)
    {zA zB : ℝ × ℝ} (hzA : zA ∈ Ess p VA) (hzB : zB ∈ Ess p VB)
    (hmeet : (connectedComponentIn VA zA ∩ connectedComponentIn VB zB).Nonempty) :
    ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB := by
  obtain ⟨q, hqA, hqB⟩ := hmeet
  exact ⟨q, connectedComponentIn_subset_Ess hA hAop hzA hqA,
    connectedComponentIn_subset_Ess hB hBop hzB hqB⟩

/-- Points joined inside a set lie in the same component of it. -/
lemma mem_connectedComponentIn_of_joinedIn {W : Set (ℝ × ℝ)} {x y : ℝ × ℝ}
    (h : JoinedIn W x y) : y ∈ connectedComponentIn W x := by
  obtain ⟨γ, hγ⟩ := h
  have hrange : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
  have hsub : Set.range γ ⊆ connectedComponentIn W x :=
    IsPreconnected.subset_connectedComponentIn hrange ⟨0, γ.source⟩ (by
      rintro q ⟨u, rfl⟩
      exact hγ u)
  exact hsub ⟨1, γ.target⟩

/-- **`T` maps components of a `T`-invariant set into components.** -/
lemma Tmap_mem_connectedComponentIn {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {z : ℝ × ℝ} (hz : z ∈ W) {q : ℝ × ℝ}
    (hq : q ∈ connectedComponentIn W z) :
    Tmap p q ∈ connectedComponentIn W (Tmap p z) :=
  IsPreconnected.subset_connectedComponentIn
    (isPreconnected_connectedComponentIn.image _ (continuous_Tmap p).continuousOn)
    ⟨z, mem_connectedComponentIn hz, rfl⟩
    (by
      rintro q' ⟨w, hw, rfl⟩
      exact (hW w).mp (connectedComponentIn_subset W z hw))
    ⟨q, hq, rfl⟩

/-- **The component of an essential point is `T`-invariant.**  So the essential points of an open
`T`-invariant `W` are exactly the points whose component in `W` is a `T`-invariant component: the
basepoint of a `T`-crossing can be pushed to any point of that component, and the crux is a
statement about such components meeting. -/
lemma connectedComponentIn_eq_of_mem_Ess {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {z : ℝ × ℝ} (hz : z ∈ Ess p W) :
    connectedComponentIn W (Tmap p z) = connectedComponentIn W z := by
  apply Subset.antisymm
  · refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn_of_joinedIn hz.2.symm) (connectedComponentIn_subset W (Tmap p z))
  · exact IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn_of_joinedIn hz.2) (connectedComponentIn_subset W z)

/-- The `T⁻¹`-version of `Tmap_mem_connectedComponentIn`. -/
lemma Tmap_inv_mem_connectedComponentIn {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {z : ℝ × ℝ} (hz : z ∈ W) {q : ℝ × ℝ}
    (hq : q ∈ connectedComponentIn W z) :
    (q.1 - p, q.2) ∈ connectedComponentIn W (z.1 - p, z.2) := by
  have hW' : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 - p, q.2) ∈ W := by
    intro q
    have h := hW (q.1 - p, q.2)
    simp only [Tmap, Prod.mk.injEq] at h
    rw [sub_add_cancel] at h
    exact h.symm
  refine IsPreconnected.subset_connectedComponentIn
    (isPreconnected_connectedComponentIn.image _ (continuous_Tmap_inv p).continuousOn)
    ⟨z, mem_connectedComponentIn hz, by simp⟩ (by
      rintro q' ⟨w, hw, rfl⟩
      exact hW' w |>.mp (connectedComponentIn_subset W z hw))
    ⟨q, hq, by simp⟩

/-- **`T` maps components of a `T`-invariant set onto components.**  The image of the component of
`z` is the component of `T z`. -/
lemma Tmap_image_connectedComponentIn {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {z : ℝ × ℝ} (hz : z ∈ W) :
    Tmap p '' connectedComponentIn W z = connectedComponentIn W (Tmap p z) := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact Tmap_mem_connectedComponentIn hW hz hw
  · intro w hw
    have hpre : (w.1 - p, w.2) ∈ connectedComponentIn W z := by
      have h := Tmap_inv_mem_connectedComponentIn hW (z := Tmap p z) ((hW z).mp hz) (q := w) hw
      have hzeq : ((Tmap p z).1 - p, (Tmap p z).2) = z := by
        apply Prod.ext <;> simp [Tmap]
      rwa [hzeq] at h
    exact ⟨(w.1 - p, w.2), hpre, by simp [Tmap]⟩

/-- **`T`-invariant components are exactly the components containing a `T`-crossing.**

Let `W` be a `T`-invariant open subset of the strip and `z ∈ W`.  Then the component
`C = connectedComponentIn W z` is `T`-invariant (`Tmap p '' C = C`) if and only if `C` contains a
point joined to its translate *inside* `C`.

This is the covering-space equivalence "`C` is connected `⟺` the corresponding component of `W/T`
contains a loop of degree one", in elementary (path) form: `T '' C = C` says that `C` is a full
preimage of its image in the quotient, while a path inside `C` from `q` to `T q` projects to a
degree-one loop.  (The two directions are proved by transporting along `T` and by path-connectedness
of `C`, which is a component of the *open* set `W`.) -/
theorem component_invariant_iff_exists_crossing {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (hWop : IsOpen W) {z : ℝ × ℝ} (hz : z ∈ W) :
    Tmap p '' connectedComponentIn W z = connectedComponentIn W z ↔
      ∃ q ∈ connectedComponentIn W z, JoinedIn (connectedComponentIn W z) q (Tmap p q) := by
  haveI : LocallyPathConnectedSpace (ℝ × ℝ) := inferInstance
  have hzC : z ∈ connectedComponentIn W z := mem_connectedComponentIn hz
  have hCop : IsOpen (connectedComponentIn W z) := hWop.connectedComponentIn
  have hpc : IsPathConnected (connectedComponentIn W z) :=
    (hCop.isConnected_iff_isPathConnected).mp
      ⟨⟨z, hzC⟩, isPreconnected_connectedComponentIn⟩
  have hTC : Tmap p '' connectedComponentIn W z = connectedComponentIn W (Tmap p z) :=
    Tmap_image_connectedComponentIn hW hz
  constructor
  · intro hinv
    have hTzC : Tmap p z ∈ connectedComponentIn W z := by
      rw [← hinv]; exact ⟨z, hzC, rfl⟩
    exact ⟨z, hzC, hpc.joinedIn z hzC (Tmap p z) hTzC⟩
  · rintro ⟨q, hq, hjoin⟩
    have h1 : Tmap p q ∈ connectedComponentIn W z := hjoin.target_mem
    have h2 : Tmap p q ∈ connectedComponentIn W (Tmap p z) :=
      Tmap_mem_connectedComponentIn hW hz hq
    have heq : connectedComponentIn W (Tmap p z) = connectedComponentIn W z :=
      (connectedComponentIn_eq h2).trans (connectedComponentIn_eq h1).symm
    rw [hTC, heq]

/-- **Essential points are exactly the points whose component is `T`-invariant.**

For a `T`-invariant open `W` and `z ∈ W`, being essential (`z ~ T z` inside `W`) is equivalent to
the component of `z` in `W` being `T`-invariant.  Hence `Ess p W` is exactly the union of the
`T`-invariant components of `W` — the covering-space statement that an essential point is one whose
component in `W` contains a loop of degree one in the quotient. -/
theorem mem_Ess_iff_component_invariant {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (hWop : IsOpen W) {z : ℝ × ℝ} (hz : z ∈ W) :
    z ∈ Ess p W ↔ Tmap p '' connectedComponentIn W z = connectedComponentIn W z := by
  constructor
  · intro hzess
    have hTzC : Tmap p z ∈ connectedComponentIn W z := mem_connectedComponentIn_of_joinedIn hzess.2
    have heq : connectedComponentIn W (Tmap p z) = connectedComponentIn W z :=
      (connectedComponentIn_eq (x := z) hTzC).symm
    rw [Tmap_image_connectedComponentIn hW hz, heq]
  · intro hinv
    obtain ⟨q, hq, hjoin⟩ := (component_invariant_iff_exists_crossing hW hWop hz).mp hinv
    have hqEss : q ∈ Ess p W :=
      ⟨connectedComponentIn_subset W z hq, hjoin.mono (connectedComponentIn_subset W z)⟩
    have hzq : z ∈ connectedComponentIn W q := by
      have hcz : connectedComponentIn W z = connectedComponentIn W q :=
        connectedComponentIn_eq (x := z) hq
      rw [← hcz]; exact mem_connectedComponentIn hz
    exact connectedComponentIn_subset_Ess hW hWop hqEss hzq

/-- **The essential component is a periodic unit.**  For `z ∈ Ess p W` with `W` open and
`T`-invariant, the component of `z` in `W` is `T`-invariant *as a set*: `T` maps it onto itself.
Together with `connectedComponentIn_subset_Ess` this makes the essential components of `W` the
"periodic units" the crux is about. -/
theorem Tmap_image_connectedComponentIn_eq {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (hWop : IsOpen W)
    {z : ℝ × ℝ} (hz : z ∈ Ess p W) :
    Tmap p '' connectedComponentIn W z = connectedComponentIn W z := by
  have hzW : z ∈ W := ess_subset p W hz
  apply Set.Subset.antisymm
  · rintro q ⟨w, hw, rfl⟩
    rw [← connectedComponentIn_eq_of_mem_Ess hW hz]
    exact Tmap_mem_connectedComponentIn hW hzW hw
  · intro q hq
    have hqTz : q ∈ connectedComponentIn W (Tmap p z) := by
      rw [connectedComponentIn_eq_of_mem_Ess hW hz]; exact hq
    have hpre : (q.1 - p, q.2) ∈ connectedComponentIn W ((Tmap p z).1 - p, (Tmap p z).2) :=
      Tmap_inv_mem_connectedComponentIn hW ((hW z).mp hzW) hqTz
    have hz1 : (Tmap p z).1 - p = z.1 := by simp [Tmap]
    rw [hz1] at hpre
    exact ⟨(q.1 - p, q.2), hpre, by ext <;> simp [Tmap]⟩

/-! ### Basepoint pushing for the crux (session 26)

The first half of the monodromy formulation — the point-set half — is the following package, all
proved above:

* `mem_connectedComponentIn_of_joinedIn`: points joined inside `W` lie in the same component;
* `Tmap_mem_connectedComponentIn`: `T` maps the component of `z` into the component of `T z`;
* `connectedComponentIn_subset_Ess` **(basepoint pushing)**: if `z` is essential in an open
  `T`-invariant `W`, so is every point of its component — so a `T`-crossing may be re-based anywhere
  in that component;
* `connectedComponentIn_eq_of_mem_Ess`: for `z ∈ Ess p W` the component of `z` is `T`-invariant
  (`connectedComponentIn W (T z) = connectedComponentIn W z`);
* `ess_meets_of_components_meet`: **the crux in component form** — if the component in `VA` of an
  essential point of `VA` meets the component in `VB` of an essential point of `VB`, the crux
  conclusion holds.

Consequently the crux is *equivalent* to: the two essential (hence `T`-invariant) components can be
chosen to meet — no basepoint choices remain, only the existence of the meeting.  That existence is
the second half and is exactly the Mayer–Vietoris input: neither `retDeg_inter_subset` (which goes
the wrong way) nor any component bookkeeping supplies it. -/

/-! ## Toolbox lemmas (proved this session) -/

lemma isOpen_stripS (a b : ℝ) : IsOpen (stripS a b) :=
  isOpen_Ioo.preimage continuous_snd

lemma convex_stripS (a b : ℝ) : Convex ℝ (stripS a b) := by
  have h : ((LinearMap.snd ℝ ℝ ℝ) ⁻¹' Set.Ioo a b) = stripS a b := by
    ext q; simp [stripS, Set.mem_Ioo]
  rw [← h]
  exact Convex.linear_preimage (convex_Ioo a b) (LinearMap.snd ℝ ℝ ℝ)

/-- **Janiszewski, two-set open cover form.**  In a connected, locally path connected, simply
connected metric space, if `VA`, `VB` are open with `VA ∪ VB = univ`, then two points joined inside
`VA` and inside `VB` are joined inside `VA ∩ VB`. -/
lemma joinedIn_inter_of_joinedIn_cover {X : Type*} [MetricSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hmono : ∀ z : X, Subsingleton (FundamentalGroup X z))
    {VA VB : Set X} (hVA : IsOpen VA) (hVB : IsOpen VB) (hcover : VA ∪ VB = univ)
    {x y : X} (hx : x ∈ VA ∩ VB) (hy : y ∈ VA ∩ VB)
    (hA : JoinedIn VA x y) (hB : JoinedIn VB x y) : JoinedIn (VA ∩ VB) x y := by
  have hAc : IsClosed (VAᶜ) := hVA.isClosed_compl
  have hBc : IsClosed (VBᶜ) := hVB.isClosed_compl
  have hdisj : Disjoint (VAᶜ) (VBᶜ) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have hz : z ∈ VA ∪ VB := by rw [hcover]; exact mem_univ z
    rcases hz with h | h
    · exact hz1 h
    · exact hz2 h
  have hx' : x ∉ VAᶜ ∪ VBᶜ := by simp [hx.1, hx.2]
  have hy' : y ∉ VAᶜ ∪ VBᶜ := by simp [hy.1, hy.2]
  have hA' : JoinedIn (VAᶜ)ᶜ x y := by simpa using hA
  have hB' : JoinedIn (VBᶜ)ᶜ x y := by simpa using hB
  have hmain := Commons.Topology.Jordan.two_disjoint_closed_not_separating hmono hAc hBc hdisj
    hx' hy' hA' hB'
  simpa using hmain

/-- **Janiszewski in the strip**, concretely: for open `VA, VB` covering `stripS a b`, two points of
`VA ∩ VB` joined inside `VA` and inside `VB` are joined inside `VA ∩ VB`. -/
lemma joinedIn_inter_of_joinedIn_strip {a b : ℝ} (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hcover : VA ∪ VB = stripS a b)
    {x y : ℝ × ℝ} (hx : x ∈ VA ∩ VB) (hy : y ∈ VA ∩ VB)
    (hA : JoinedIn VA x y) (hB : JoinedIn VB x y) : JoinedIn (VA ∩ VB) x y := by
  have hsubA : VA ⊆ stripS a b := hcover ▸ subset_union_left
  have hsubB : VB ⊆ stripS a b := hcover ▸ subset_union_right
  have hne : (stripS a b).Nonempty := ⟨(0, (a + b) / 2), by
    refine ⟨?_, ?_⟩ <;> simp only [Set.mem_ofPred_eq] <;> linarith⟩
  have hconv : Convex ℝ (stripS a b) := convex_stripS a b
  haveI : ContractibleSpace ↥(stripS a b) := hconv.contractibleSpace hne
  haveI : ConnectedSpace ↥(stripS a b) := Subtype.connectedSpace (hconv.isConnected hne)
  haveI : LocallyPathConnectedSpace ↥(stripS a b) := (isOpen_stripS a b).locallyPathConnectedSpace
  set VA' : Set ↥(stripS a b) := Subtype.val ⁻¹' VA with hVA'def
  set VB' : Set ↥(stripS a b) := Subtype.val ⁻¹' VB with hVB'def
  have hVA' : IsOpen VA' := hVA.preimage continuous_subtype_val
  have hVB' : IsOpen VB' := hVB.preimage continuous_subtype_val
  have hcover' : VA' ∪ VB' = univ := by
    ext q
    constructor
    · intro _; trivial
    · intro _
      have hq : (q : ℝ × ℝ) ∈ VA ∪ VB := by rw [hcover]; exact q.2
      rcases hq with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hxA' : (⟨x, hsubA hx.1⟩ : ↥(stripS a b)) ∈ VA' ∩ VB' := ⟨hx.1, hx.2⟩
  have hyA' : (⟨y, hsubA hy.1⟩ : ↥(stripS a b)) ∈ VA' ∩ VB' := ⟨hy.1, hy.2⟩
  have hA' : JoinedIn VA' ⟨x, hsubA hx.1⟩ ⟨y, hsubA hy.1⟩ := by
    obtain ⟨γ, hγ⟩ := hA
    refine ⟨{ toFun := fun t => ⟨γ t, hsubA (hγ t)⟩
              continuous_toFun := Continuous.subtype_mk γ.continuous _
              source' := by simp
              target' := by simp }, fun t => hγ t⟩
  have hB' : JoinedIn VB' ⟨x, hsubB hx.2⟩ ⟨y, hsubB hy.2⟩ := by
    obtain ⟨γ, hγ⟩ := hB
    refine ⟨{ toFun := fun t => ⟨γ t, hsubB (hγ t)⟩
              continuous_toFun := Continuous.subtype_mk γ.continuous _
              source' := by simp
              target' := by simp }, fun t => hγ t⟩
  have hmain := joinedIn_inter_of_joinedIn_cover (X := ↥(stripS a b)) (fun z => inferInstance)
    hVA' hVB' hcover' hxA' hyA' hA' hB'
  have himg : Subtype.val '' (VA' ∩ VB') = VA ∩ VB := by
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩; exact hq'
    · intro hq; exact ⟨⟨q, hsubA hq.1⟩, hq, rfl⟩
  have hmap := hmain.map continuous_subtype_val.continuousOn
  rwa [himg] at hmap



/-- **Gluing.**  Two locally constant `ℤ`-valued functions on the two pieces of an open cover of a
space, agreeing on the overlap, glue into a locally constant function. -/
lemma exists_locallyConstant_glue {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsOpen s) (ht : IsOpen t) (hst : s ∪ t = univ)
    {f : s → ℤ} (hf : IsLocallyConstant f) {g : t → ℤ} (hg : IsLocallyConstant g)
    (hcompat : ∀ x (hxs : x ∈ s) (hxt : x ∈ t), f ⟨x, hxs⟩ = g ⟨x, hxt⟩) :
    ∃ F : X → ℤ, IsLocallyConstant F ∧ (∀ x (hxs : x ∈ s), F x = f ⟨x, hxs⟩) ∧
      (∀ x (hxt : x ∈ t), F x = g ⟨x, hxt⟩) := by
  classical
  have hmemt : ∀ x : X, x ∉ s → x ∈ t := by
    intro x hx
    have h : x ∈ s ∪ t := by rw [hst]; trivial
    rcases h with h | h
    · exact absurd h hx
    · exact h
  refine ⟨fun x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hmemt x hx⟩, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨U, hUopen, hxU, hUconst⟩ := hf.exists_open ⟨x, hx⟩
      refine ⟨Subtype.val '' U, hs.isOpenMap_subtype_val U hUopen, ⟨⟨x, hx⟩, hxU, rfl⟩, ?_⟩
      intro y hy
      obtain ⟨y', hy'U, rfl⟩ := hy
      simp only [dif_pos y'.2, dif_pos hx]
      exact hUconst y' hy'U
    · have hxt : x ∈ t := hmemt x hx
      obtain ⟨U, hUopen, hxU, hUconst⟩ := hg.exists_open ⟨x, hxt⟩
      refine ⟨Subtype.val '' U, ht.isOpenMap_subtype_val U hUopen, ⟨⟨x, hxt⟩, hxU, rfl⟩, ?_⟩
      intro y hy
      obtain ⟨y', hy'U, rfl⟩ := hy
      simp only [dif_neg hx]
      by_cases hy's : (y' : X) ∈ s
      · simp only [dif_pos hy's]
        rw [hcompat (y' : X) hy's y'.2]
        exact hUconst y' hy'U
      · simp only [dif_neg hy's]
        exact hUconst y' hy'U
  · intro x hxs; simp only [dif_pos hxs]
  · intro x hxt
    by_cases hxs : x ∈ s
    · simp only [dif_pos hxs]; exact hcompat x hxs hxt
    · simp only [dif_neg hxs]


/-- **Θ-argument: there is no "shift pair".**  Let `VA, VB` be open sets with
`VA ∪ VB = stripS a b`.  There do not exist locally constant functions `δ` on `VA` and `η` on `VB`
satisfying `η = δ + 1` on `VA ∩ VB`, with `δ` vanishing at some point of `VA` and `η` vanishing at
some point of `VB`.

This is the "cancellation" obstruction behind the crux: it forbids exactly the situation produced
by a hypothetical `T`-shift function on `VA ∩ VB`. -/
lemma no_shift_pair {a b : ℝ} (hab : a < b) {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hcover : VA ∪ VB = stripS a b)
    {δ : ↥VA → ℤ} (hδ : IsLocallyConstant δ) {η : ↥VB → ℤ} (hη : IsLocallyConstant η)
    (hcompat : ∀ z (hzA : z ∈ VA) (hzB : z ∈ VB), η ⟨z, hzB⟩ = δ ⟨z, hzA⟩ + 1)
    {zA zB : ℝ × ℝ} (hzA : zA ∈ VA) (hzB : zB ∈ VB)
    (hA0 : δ ⟨zA, hzA⟩ = 0) (hB0 : η ⟨zB, hzB⟩ = 0) : False := by
  have hsubA : VA ⊆ stripS a b := hcover ▸ subset_union_left
  have hsubB : VB ⊆ stripS a b := hcover ▸ subset_union_right
  have hne : (stripS a b).Nonempty := ⟨(0, (a + b) / 2), by
    refine ⟨?_, ?_⟩ <;> simp only [Set.mem_ofPred_eq] <;> linarith⟩
  have hconv : Convex ℝ (stripS a b) := convex_stripS a b
  haveI : ContractibleSpace ↥(stripS a b) := hconv.contractibleSpace hne
  haveI : ConnectedSpace ↥(stripS a b) := Subtype.connectedSpace (hconv.isConnected hne)
  set s : Set ↥(stripS a b) := Subtype.val ⁻¹' VA with hsdef
  set t : Set ↥(stripS a b) := Subtype.val ⁻¹' VB with htdef
  have hsopen : IsOpen s := hVA.preimage continuous_subtype_val
  have htopen : IsOpen t := hVB.preimage continuous_subtype_val
  have hst : s ∪ t = univ := by
    ext q
    constructor
    · intro _; trivial
    · intro _
      have hq : (q : ℝ × ℝ) ∈ VA ∪ VB := by rw [hcover]; exact q.2
      rcases hq with h | h
      · exact Or.inl h
      · exact Or.inr h
  -- functions on the pieces
  set f : s → ℤ := fun p => δ ⟨(p : ℝ × ℝ), p.2⟩ with hfdef
  set g : t → ℤ := fun p => η ⟨(p : ℝ × ℝ), p.2⟩ - 1 with hgdef
  have hflc : IsLocallyConstant f := by
    rw [hfdef]
    exact hδ.comp_continuous (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) (fun p => p.2))
  have hglc : IsLocallyConstant g := by
    rw [hgdef]
    exact (hη.comp_continuous (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) (fun p => p.2))).sub
      (IsLocallyConstant.const 1)
  have hcompat' : ∀ x (hxs : x ∈ s) (hxt : x ∈ t), f ⟨x, hxs⟩ = g ⟨x, hxt⟩ := by
    intro x hxs hxt
    have h1 : f ⟨x, hxs⟩ = δ ⟨(x : ℝ × ℝ), hxs⟩ := rfl
    have h2 : g ⟨x, hxt⟩ = η ⟨(x : ℝ × ℝ), hxt⟩ - 1 := rfl
    rw [h1, h2, hcompat (x : ℝ × ℝ) hxs hxt]
    ring
  obtain ⟨F, hFlc, hFf, hFg⟩ := exists_locallyConstant_glue hsopen htopen hst hflc hglc hcompat'
  have hzAs : (⟨zA, hsubA hzA⟩ : ↥(stripS a b)) ∈ s := hzA
  have hzBt : (⟨zB, hsubB hzB⟩ : ↥(stripS a b)) ∈ t := hzB
  have hEq : F ⟨zA, hsubA hzA⟩ = F ⟨zB, hsubB hzB⟩ :=
    hFlc.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
  have h1 : F ⟨zA, hsubA hzA⟩ = 0 := by
    rw [hFf _ hzAs]
    show δ ⟨((⟨zA, hsubA hzA⟩ : ↥(stripS a b)) : ℝ × ℝ), hzAs⟩ = 0
    simpa using hA0
  have h2 : F ⟨zB, hsubB hzB⟩ = -1 := by
    rw [hFg _ hzBt]
    show η ⟨((⟨zB, hsubB hzB⟩ : ↥(stripS a b)) : ℝ × ℝ), hzBt⟩ - 1 = -1
    rw [show (⟨zB, hsubB hzB⟩ : ↥(stripS a b)) = ⟨zB, hsubB hzB⟩ from rfl] at *
    rw [hB0]
    ring
  rw [h1, h2] at hEq
  norm_num at hEq


/-- **Two open sets covering `[0,1]` and containing its endpoints meet.**  If `A`, `B ⊆ ℝ` are
open, `[0,1] ⊆ A ∪ B`, `0 ∈ A` and `1 ∈ B`, then `A ∩ B ≠ ∅`.  (Otherwise `A ∩ [0,1]` and
`B ∩ [0,1]` would split the connected interval `[0,1]`.) -/
lemma inter_nonempty_of_isOpen_cover_Icc {A B : Set ℝ} (hA : IsOpen A) (hB : IsOpen B)
    (hcover : Set.Icc (0:ℝ) 1 ⊆ A ∪ B) (h0 : (0:ℝ) ∈ A) (h1 : (1:ℝ) ∈ B) :
    (A ∩ B).Nonempty := by
  by_contra hcon
  have hdisj : ∀ x, x ∈ A → x ∈ B → False := fun x hxA hxB => hcon ⟨x, hxA, hxB⟩
  set S : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) 1 ∧ ∀ t' ∈ Set.Icc (0:ℝ) t, t' ∈ A} with hSdef
  have h0S : (0:ℝ) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, fun t' ht' => by
    have ht'' : t' ≤ 0 := (Set.mem_Icc.mp ht').2
    have ht''' : 0 ≤ t' := (Set.mem_Icc.mp ht').1
    have h : t' = 0 := le_antisymm ht'' ht'''
    rw [h]; exact h0⟩
  have hSne : S.Nonempty := ⟨0, h0S⟩
  have hSbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  set τ : ℝ := sSup S with hτdef
  have hτmem : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_csSup hSbdd h0S, csSup_le hSne fun t ht => ht.1.2⟩
  have hseg : ∀ t', (0:ℝ) ≤ t' → t' < τ → t' ∈ A := by
    intro t' h0t hlt
    have hlt' : t' < sSup S := hτdef ▸ hlt
    obtain ⟨t'', ht''S, hgt⟩ := exists_lt_of_lt_csSup hSne hlt'
    exact ht''S.2 t' ⟨h0t, le_of_lt hgt⟩
  rcases hcover hτmem with hτA | hτB
  · obtain ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp hA τ hτA
    have hτlt : τ < 1 := by
      rcases lt_or_eq_of_le hτmem.2 with h | h
      · exact h
      · exact absurd (h ▸ hτA) (hdisj 1 · h1)
    set ε' : ℝ := min (ε / 2) (1 - τ) with hε'def
    have hε'pos : 0 < ε' := lt_min (by linarith) (by linarith)
    have hττ' : τ + ε' ≤ 1 := by
      have := min_le_right (ε / 2) (1 - τ); linarith
    have hε'le : ε' ≤ ε / 2 := min_le_left _ _
    have hsegτ : Set.Icc (0:ℝ) τ ⊆ A := by
      intro t' ht'
      rcases lt_or_eq_of_le ht'.2 with h | h
      · exact hseg t' ht'.1 h
      · rw [h]; exact hτA
    have hmemS : τ + ε' ∈ S := by
      refine ⟨⟨by linarith [hτmem.1], hττ'⟩, fun t' ht' => ?_⟩
      rcases lt_or_ge τ t' with h | h
      · have ht'2 : t' ≤ τ + ε' := ht'.2
        have hlt : t' < τ + ε := by linarith [ht'2, hε'le, hε]
        refine hε' ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      · exact hsegτ ⟨ht'.1, h⟩
    have hle : τ + ε' ≤ τ := hτdef.symm ▸ le_csSup hSbdd hmemS
    linarith
  · have hτpos : 0 < τ := by
      rcases lt_or_eq_of_le hτmem.1 with h | h
      · exact h
      · exact absurd (h ▸ hτB) (hdisj 0 h0)
    obtain ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp hB τ hτB
    set d : ℝ := min ε τ with hddef
    have hdpos : 0 < d := lt_min hε hτpos
    have hdle : d ≤ ε := by rw [hddef]; exact min_le_left _ _
    have hdlτ : d ≤ τ := by rw [hddef]; exact min_le_right _ _
    have hmid0 : (0:ℝ) ≤ τ - d / 2 := by linarith
    have hmidt : τ - d / 2 < τ := by linarith
    refine hdisj (τ - d / 2) (hseg _ hmid0 hmidt) (hε' ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith


/-- **The first-entry height is upper semicontinuous.**  For an open `B ⊆ ℝ × ℝ` and a height `v`
strictly above the first entry `sInf {t ∈ [0,1] | (s,t) ∈ B}`, all `s'` near `s` have their first
entry strictly below `v`.

This is the true half of the `σ`-mechanism for the selection problem.  The *matching lower bound
is false*: with `A := {t < 1/2 + δ}`, `B := {t > 1/2} ∪ {dist (s,ℤ) < ε, t > 1/2 - ε'}` one has
`A ∪ B ⊇ ℝ × [0,1]`, `(s,0) ∈ A`, `(s,1) ∈ B`, `A` and `B` open and `1`-periodic, yet
`σ s := sInf {t ∈ [0,1] | (s,t) ∈ B}` equals `1/2 - ε'` for `dist (s,ℤ) < ε` and `1/2` otherwise,
so `σ` jumps.  (A continuous periodic selection still exists there, namely `u ≡ 1/2 + δ/2`.) -/
lemma firstEntry_lt_eventually {B : Set (ℝ × ℝ)} (hB : IsOpen B) {s v : ℝ}
    (hne : ({t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ (s, t) ∈ B}).Nonempty)
    (h : sInf {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ (s, t) ∈ B} < v) :
    ∀ᶠ s' in 𝓝 s, sInf {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ (s', t) ∈ B} < v := by
  obtain ⟨t, ht, htv⟩ := exists_lt_of_csInf_lt hne h
  obtain ⟨htIcc, htB⟩ := ht
  obtain ⟨δ, hδ, hδ'⟩ := Metric.isOpen_iff.mp hB (s, t) htB
  refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun s' hs' => ?_⟩
  have hs'B : (s', t) ∈ B := hδ' (by
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hs')
  have hle : sInf {t' : ℝ | t' ∈ Set.Icc (0:ℝ) 1 ∧ (s', t') ∈ B} ≤ t :=
    csInf_le ⟨0, fun t' ht' => ht'.1.1⟩ ⟨htIcc, hs'B⟩
  linarith

/-- **Local selections exist everywhere (local persistence of a fibre component).**

If `D ⊆ ℝ × ℝ` is open and `(s₀,t₀) ∈ D`, then `D` contains a full box `U × (t₀-ε, t₀+ε)` around
it: the constant function `t₀` is a section of `D` over the neighbourhood `U`, and the connected
component of the fibre `D_s` containing `t₀` persists for all `s ∈ U`.  This is the smallest brick
of the no-swap analysis: connected components of the fibres never vanish *locally*, so the whole
difficulty is gluing the local constants around the circle. -/
lemma exists_local_selection_aei {D : Set (ℝ × ℝ)} (hD : IsOpen D) {s₀ t₀ : ℝ} (h : (s₀, t₀) ∈ D) :
    ∃ U : Set ℝ, IsOpen U ∧ s₀ ∈ U ∧
      ∃ ε > 0, U ×ˢ Set.Ioo (t₀ - ε) (t₀ + ε) ⊆ D := by
  obtain ⟨r, hr, hr'⟩ := Metric.isOpen_iff.mp hD (s₀, t₀) h
  refine ⟨Metric.ball s₀ r, Metric.isOpen_ball, Metric.mem_ball_self hr, r / 2, half_pos hr, ?_⟩
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  refine hr' ?_
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  refine ⟨?_, ?_⟩
  · rw [Real.dist_eq]; exact hs
  · rw [Real.dist_eq]
    rw [Set.mem_Ioo] at ht
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]


/-- **Local constant sections cover every set of levels (the merge/split brick).**

Let `D ⊆ ℝ × ℝ` be open and suppose every fibre over `[0,1]` is nonempty.  Then `[0,1]` is covered by
open sets `U a` on each of which a *constant* height `c a` is admissible: `(s, c a) ∈ D` for all
`s ∈ U a`.

Consequence: the fibre components of `D` can appear and disappear only by *merging with or
splitting from* a neighbouring component — never by teleporting.  Indeed a fibre component that
contains a point of the box `U a × {c a}` persists on all of `U a`, and any two such boxes are
related by a continuous change of height.  What is therefore *not* settled by this brick is the
*order*: whether, after going once around, the branch of a fibre component comes back as itself or
as a different one.  That is exactly the no-swap/exchange obstruction, i.e. the (equivalent)
`k ≥ 2` orbit exclusion in the equivariant picture. -/
lemma exists_local_constant_sections {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hne : ∀ s ∈ Set.Icc (0:ℝ) 1, ∃ t, (s, t) ∈ D) :
    ∃ (c : ↥(Set.Icc (0:ℝ) 1) → ℝ) (U : ↥(Set.Icc (0:ℝ) 1) → Set ℝ),
      (∀ a, IsOpen (U a)) ∧ Set.Icc (0:ℝ) 1 ⊆ ⋃ a, U a ∧
        ∀ a s, s ∈ U a → (s, c a) ∈ D := by
  classical
  have h : ∀ s : ↥(Set.Icc (0:ℝ) 1), ∃ t, ((s : ℝ), t) ∈ D := fun s => hne s s.2
  choose c hc using h
  have h2 : ∀ s : ↥(Set.Icc (0:ℝ) 1), ∃ U : Set ℝ, IsOpen U ∧ (s : ℝ) ∈ U ∧
      ∀ a ∈ U, (a, c s) ∈ D := by
    intro s
    obtain ⟨U, hUo, hsU, ε, hε, hsub⟩ := exists_local_selection_aei hD (hc s)
    refine ⟨U, hUo, hsU, fun a ha => hsub ⟨ha, ?_⟩⟩
    exact ⟨by linarith, by linarith⟩
  choose U hU using h2
  refine ⟨c, U, fun a => (hU a).1, ?_, fun a s hs => (hU a).2.2 s hs⟩
  intro a ha
  exact mem_iUnion.mpr ⟨⟨a, ha⟩, (hU ⟨a, ha⟩).2.1⟩

/-- **A box lies inside a single connected component of `D` (branch carriers).**

If `U × I ⊆ D` with `U`, `I` preconnected (e.g. two intervals), then the whole box is contained in
the connected component of `D` of any of its points.  Applied to the constant sections produced by
`exists_local_constant_sections` (with `U = U a` and `I` the interval around `c a`), this says:

* every branch of a fibre is *carried* by a single connected component of `D`, and this carrier
  persists over the whole level-interval `U a` on which the box lives.

The *converse* is not true in general (a `U`-shaped component of `D` can carry two different
branches of the same fibre, joined only through other levels), so this brick does not by itself give
the gluing.  What remains is exactly the **exchange (holonomy) statement**: for
`D = A ∩ B` with `A, B` open, `A ∪ B ⊇ ℝ × [0,1]`, `(s,0) ∈ A`, `(s,1) ∈ B` and `1`-periodic in `s`,
following the branches of the fibres once around the circle must return each branch to itself. -/
lemma box_subset_connectedComponentIn {D : Set (ℝ × ℝ)} {U I : Set ℝ}
    (hU : IsPreconnected U) (hI : IsPreconnected I) (hbox : U ×ˢ I ⊆ D) {q : ℝ × ℝ}
    (hq : q ∈ U ×ˢ I) : U ×ˢ I ⊆ connectedComponentIn D q :=
  (hU.prod hI).subset_connectedComponentIn hq hbox

/-- **Parity / intermediate-value mechanism (abstract form).**

Let `X` be path connected, `σ` an involution of `X`, and `g : X → ℝ` continuous with
`g (σ x) = - g x`.  Then `g` has a zero: a path from `x` to `σ x` joins values of opposite sign.

This is the abstract shape of the "switch" argument for the branch-following permutation: the
switches available to a branch are the zeros of an odd continuous function on a path-connected
space carrying an involution. -/
lemma exists_eq_zero_of_anti_involution {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (σ : X → X) (hσ : Function.Involutive σ) {g : X → ℝ} (hg : Continuous g)
    (hanti : ∀ x, g (σ x) = - g x) : ∃ x, g x = 0 := by
  obtain ⟨x⟩ : Nonempty X := PathConnectedSpace.nonempty
  by_cases hx : g x = 0
  · exact ⟨x, hx⟩
  · obtain ⟨x', hx'⟩ : ∃ x', g x' < 0 := by
      rcases lt_or_gt_of_ne hx with h | h
      · exact ⟨x, h⟩
      · exact ⟨σ x, by rw [hanti]; linarith⟩
    obtain ⟨γ⟩ : Nonempty (Path x' (σ x')) := PathConnectedSpace.joined x' (σ x')
    have hcont : Continuous fun u : unitInterval => g (γ u) := hg.comp γ.continuous
    have h0 : g (γ 0) < 0 := by rw [γ.source]; exact hx'
    have h1 : 0 < g (γ 1) := by rw [γ.target, hanti]; linarith
    obtain ⟨c, -, hcz⟩ := intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from zero_le_one)
      (f := fun u : unitInterval => g (γ u)) hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (g (γ 0)) (g (γ 1)) from ⟨le_of_lt h0, le_of_lt h1⟩)
    exact ⟨γ c, hcz⟩

/-- **The half-turn switch set of a periodic function is closed under the half-turn.**

For `h` of period `1`, the "switch set" `{θ | h θ = h (θ + 1/2)}` is invariant under
`θ ↦ θ + 1/2`, because `h (θ + 1) = h θ`. -/
lemma switch_set_halfTurn {h : ℝ → ℝ} (hper : Function.Periodic h 1) (θ : ℝ) :
    (h θ = h (θ + 1/2)) ↔ (h (θ + 1/2) = h (θ + 1/2 + 1/2)) := by
  rw [show θ + 1/2 + 1/2 = θ + 1 by ring, hper θ]
  exact eq_comm

/-- **The half-turn switch set of a periodic function is nonempty.**

For continuous `h` of period `1` there is `θ` with `h θ = h (θ + 1/2)`: the function
`g θ := h θ - h (θ + 1/2)` satisfies `g (θ + 1/2) = - g θ`, so the intermediate value theorem on
`[0, 1/2]` gives a zero.  (For the `k = 2` twisted-tube candidate this is exactly the forced
self-intersection that makes its holonomy trivial.) -/
lemma exists_eq_periodic_half_aei {h : ℝ → ℝ} (hh : Continuous h) (hper : Function.Periodic h 1) :
    ∃ θ : ℝ, h θ = h (θ + 1/2) := by
  set g : ℝ → ℝ := fun θ => h θ - h (θ + 1/2) with hgdef
  have hg : Continuous g := by
    rw [hgdef]
    exact hh.sub (hh.comp (continuous_id.add continuous_const))
  have h1h : h 1 = h 0 := by simpa using hper 0
  have hg_per : g (1/2) = - g 0 := by
    rw [hgdef]
    simp only
    rw [show (1:ℝ)/2 + 1/2 = 1 by norm_num, h1h]
    ring
  by_cases h0 : g 0 = 0
  · refine ⟨0, ?_⟩
    rw [hgdef] at h0
    simpa using sub_eq_zero.mp h0
  rcases lt_or_gt_of_ne h0 with hlt | hgt
  · have h1 : 0 < g (1/2) := by rw [hg_per]; linarith
    obtain ⟨c, -, hcz⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1/2 by norm_num)
      (f := g) hg.continuousOn
      (show (0:ℝ) ∈ Set.Icc (g 0) (g (1/2)) from ⟨le_of_lt hlt, le_of_lt h1⟩)
    exact ⟨c, by rw [hgdef] at hcz; linarith [hcz]⟩
  · have h1 : g (1/2) < 0 := by rw [hg_per]; linarith
    obtain ⟨c, -, hcz⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ 1/2 by norm_num)
      (f := g) hg.continuousOn
      (show (0:ℝ) ∈ Set.Icc (g (1/2)) (g 0) from ⟨le_of_lt h1, le_of_lt hgt⟩)
    exact ⟨c, by rw [hgdef] at hcz; linarith [hcz]⟩

/-- **Descent (model case): the switching function of a two-sheet family is anti-invariant.**

Let `c₀` be `1`-periodic and let `c₁` be the half-turn translate of `c₀` (`c₁ s = c₀ (s + 1/2)`),
i.e. the two sheets are *exchanged* by the half-turn `s ↦ s + 1/2` of the level circle.  Then the
*switching function* `φ s := c₀ s - c₁ s` — whose zeros are exactly the levels where the two sheets
meet, i.e. where a branch may switch — satisfies `φ (s + 1/2) = - φ s`.

This is the two-sheet model of the descent, and it is exactly the structure of the `k = 2`
configuration of the bad case (the sheets being a component `E` of `W` and its translate `T E`,
which the half-turn `T` exchanges).  Feeding `φ` (on the level circle `ℝ/ℤ`, which is path connected
and carries the half-turn involution) to `exists_eq_zero_of_anti_involution` produces switch points,
and `switch_set_halfTurn` shows their set is invariant under the half-turn.  What is still open in
general is the *descent* for an arbitrary branch family of `D = A ∩ B` (more than two sheets, and
only locally constant carriers): the branch family modulo the half-turn has to be exhibited. -/
lemma switch_function_anti_invariant {c₀ c₁ : ℝ → ℝ} (hper : Function.Periodic c₀ 1)
    (hex : ∀ s : ℝ, c₁ s = c₀ (s + 1/2)) :
    ∀ s : ℝ, (c₀ (s + 1/2) - c₁ (s + 1/2)) = - (c₀ s - c₁ s) := by
  intro s
  have h1 : c₁ s = c₀ (s + 1/2) := hex s
  have h2 : c₁ (s + 1/2) = c₀ (s + 1/2 + 1/2) := hex (s + 1/2)
  have h3 : c₀ (s + 1/2 + 1/2) = c₀ s := by
    rw [show s + 1/2 + 1/2 = s + 1 by ring]
    exact hper s
  rw [h2, h3]
  linarith [h1]

/-- **The zeros of the switching function are the switch points.** -/
lemma switch_function_eq_zero_iff {c₀ c₁ : ℝ → ℝ} (hex : ∀ s : ℝ, c₁ s = c₀ (s + 1/2))
    (s : ℝ) : (c₀ s - c₁ s = 0) ↔ c₀ s = c₀ (s + 1/2) := by
  rw [hex s, sub_eq_zero]

/-- **Anti-invariance of the switching function (general form).**

For *any* involution `σ` of a type `X` and any `c : X → ℝ`, the function
`φ x := c x - c (σ x)` — the switching function of the sheet pair `(c, c ∘ σ)` — is
anti-invariant: `φ (σ x) = - φ x`.

**Framework (what "modulo the half-turn" means for a branch family).**  Let `D = A ∩ B` with `A, B`
open, `1`-periodic, covering `ℝ × [0,1]`, and `(s,0) ∈ A`, `(s,1) ∈ B`.  The *branches* are the
connected components of the fibres `D_s`, the *carriers* are the connected components of `D`
(`box_subset_connectedComponentIn`: every branch is carried by exactly one carrier).  Taking the
level circle `X = ℝ/ℤ` (or `ℝ` with `1`-periodicity) with the **half-turn** `σ x = x + 1/2` — a
fixed-point-free involution — the branches modulo the half-turn are the sheet *orbits*, and a
two-sheet orbit is presented by two height functions `c₀`, `c₁` with the *exchange* relation
`c₁ = c₀ ∘ σ` (the half-turn swaps the two carriers).  This lemma says the switching function of
such an orbit is anti-invariant, with no periodicity or continuity needed: only `σ ∘ σ = id`.

Consequences, both proved: the *square* `φ ^ 2` is invariant, i.e. `φ` descends to the quotient of
the level circle by the half-turn (this is the sense in which "modulo the half-turn" makes sense);
and the zero set of `φ` — the *switch set* — is half-turn invariant. -/
lemma switch_function_anti_invariant_of_involution {X : Type*} (σ : X → X)
    (hσ : Function.Involutive σ) (c : X → ℝ) :
    ∀ x : X, (c (σ x) - c (σ (σ x))) = - (c x - c (σ x)) := by
  intro x
  rw [hσ x]
  ring

/-- **The switching function descends to the quotient by the half-turn.** -/
lemma switch_function_sq_invariant {X : Type*} (σ : X → X) (hσ : Function.Involutive σ)
    (c : X → ℝ) : ∀ x : X, (c (σ x) - c (σ (σ x))) ^ 2 = (c x - c (σ x)) ^ 2 := by
  intro x
  rw [hσ x]
  ring

/-- **The switch set is half-turn invariant (general form).** -/
lemma switch_function_eq_zero_iff_of_involution {X : Type*} (σ : X → X)
    (hσ : Function.Involutive σ) (c : X → ℝ) (x : X) :
    (c x - c (σ x) = 0) ↔ (c (σ x) - c (σ (σ x)) = 0) := by
  rw [hσ x]
  constructor <;> intro h <;> linarith

/-- **Half-turn pairing.**  A finite set of levels on the circle which is closed under the half-turn
`x ↦ x + 1/2` modulo `1` has even cardinality: the half-turn is a fixed-point-free involution, so it
splits the set into orbits of size two.

This is the pairing step of the parity argument: the switch points of a periodic family come in
half-turn pairs, so their number per circuit is even.  Proof: split `Z` into its parts below and at
least `1/2`; the half-turn is a bijection between them (its inverse on `Z` is itself), so
`Z.card = 2 * (Z.filter (· < 1/2)).card`.

Note the naive `ℝ`-version without the `mod 1` is *false*: a finite set closed under `x ↦ x + 1/2`
would contain an increasing chain and hence be empty; the `Set.Ico 0 1` hypothesis (or equivalently
the `Int.fract` closure) is essential. -/
lemma halfTurn_pairing {Z : Finset ℝ} (hsub : ∀ x ∈ Z, x ∈ Set.Ico (0:ℝ) 1)
    (hclosed : ∀ x ∈ Z, Int.fract (x + 1/2) ∈ Z) : Even Z.card := by
  classical
  set Z₁ : Finset ℝ := Z.filter (fun x => x < 1/2) with hZ₁
  set Z₂ : Finset ℝ := Z.filter (fun x => ¬ (x < 1/2)) with hZ₂
  have hsplit : Z₁.card + Z₂.card = Z.card :=
    Finset.card_filter_add_card_filter_not (s := Z) (fun x : ℝ => x < 1/2)
  have hkey : ∀ x ∈ Z, Int.fract (x + 1/2) = if x < 1/2 then x + 1/2 else x - 1/2 := by
    intro x hx
    obtain ⟨h0, h1⟩ := hsub x hx
    by_cases hc : x < 1/2
    · rw [if_pos hc, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    · rw [if_neg hc]
      have : x + 1/2 = (x - 1/2) + 1 := by ring
      rw [this, Int.fract_add_one, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  have hbij : Z₁.card = Z₂.card := by
    refine Finset.card_bij (fun x _ => Int.fract (x + 1/2)) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxZ, hxlt⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx0, hx1⟩ := hsub x hxZ
      refine Finset.mem_filter.mpr ⟨hclosed x hxZ, ?_⟩
      have hk := hkey x hxZ
      rw [if_pos hxlt] at hk
      rw [hk]
      intro hlt
      linarith
    · intro x₁ hx₁ x₂ hx₂ heq
      obtain ⟨hx₁Z, hx₁lt⟩ := Finset.mem_filter.mp hx₁
      obtain ⟨hx₂Z, hx₂lt⟩ := Finset.mem_filter.mp hx₂
      have h₁ := hkey x₁ hx₁Z
      have h₂ := hkey x₂ hx₂Z
      rw [if_pos hx₁lt] at h₁
      rw [if_pos hx₂lt] at h₂
      rw [h₁, h₂] at heq
      linarith
    · intro y hy
      obtain ⟨hyZ, hynlt⟩ := Finset.mem_filter.mp hy
      obtain ⟨hy0, hy1⟩ := hsub y hyZ
      have hyge : 1/2 ≤ y := not_lt.mp hynlt
      refine ⟨y - 1/2, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, by linarith⟩
        have hk := hkey y hyZ
        rw [if_neg (by linarith)] at hk
        have hc := hclosed y hyZ
        rwa [hk] at hc
      · rw [show y - 1/2 + 1/2 = y by ring, Int.fract_eq_self.mpr ⟨hy0, hy1⟩]
  have h2 : Z.card = 2 * Z₁.card := by
    rw [← hsplit, hbij]
    ring
  exact ⟨Z₁.card, by rw [h2]; ring⟩

/-- **Carrier-level exchange (dictionary).**

Let `σ` be the half-turn (an involution of the level space) and let `H` be a height function that is
*invariant* under `σ` — in the application `σ = T`, the translation of the strip, which preserves the
second coordinate.  If `E` and `σ '' E` are the two carriers of a two-sheet orbit, then the two sheet
height functions `c₀ := H|_E` and `c₁ := H|_{{σ '' E}}` satisfy the exchange relation
`c₁ (σ z) = c₀ z`.

This is the carrier-level counterpart of `switch_function_anti_invariant_of_involution`: the exchange
relation required there is *automatic* once the half-turn preserves heights.  Hence the substantive
content of the carrier-level step is not the exchange but the *construction* of the two-sheet family
from a `T`-orbit of size two of the branch family (equivalently: the presentation of the two carriers
by height functions over the level space). -/
lemma carrier_exchange {Ω : Type*} (σ : Ω → Ω) {H : Ω → ℝ} (hH : ∀ z, H (σ z) = H z)
    {E : Set Ω} : ∀ z ∈ E, H (σ z) = H z := fun z _ => hH z

/-- **Two-sheet construction: the sheets are exchanged by the translate.**

Let `c₀`, `c₁` be the height functions of the two sheets over the level line, with the sheets
*exchanged* by the translate `s ↦ s + p` of the level: `c₀ (s + p) = c₁ s` and `c₁ (s + p) = c₀ s`
(in the equivariant picture the two carriers are a component `E` of `W` and its translate `T E`, and
`T` preserves heights, so the sheets are exchanged with heights preserved).  Then the switching
function `φ s := c₀ s - c₁ s` of the pair is anti-invariant under the half-turn:
`φ (s + p) = - φ s`.

This is the **construction** of the two-sheet family of the bad case: the input is the pair of
correspondence equations, and the output feeds
`switch_function_anti_invariant_of_involution` (with `σ = (· + p)` on the level space
`ℝ/(2pℤ)`, which is a fixed-point-free involution there), whose conclusion together with
`halfTurn_pairing` gives the triviality of the branch-following permutation. -/
lemma switch_function_anti_invariant_of_two_sheets {p : ℝ} {c₀ c₁ : ℝ → ℝ}
    (hcorr₀ : ∀ s : ℝ, c₀ (s + p) = c₁ s) (hcorr₁ : ∀ s : ℝ, c₁ (s + p) = c₀ s) :
    ∀ s : ℝ, (c₀ (s + p) - c₁ (s + p)) = - (c₀ s - c₁ s) := by
  intro s
  rw [hcorr₀ s, hcorr₁ s]
  ring

/-- **Carrier exchange at the level of points.**  If the two carriers are `E` and its translate
`E' = T '' E`, then the translate of the `E`-point at level `s` is a point of `E'` at level `s + p`
with the *same* height (because `T` preserves heights).  This is where the exchange comes from. -/
lemma carrier_point_correspondence {p : ℝ} {E E' : Set (ℝ × ℝ)} (hT : Tmap p '' E = E')
    {c₀ : ℝ → ℝ} {s : ℝ} (hmem : (s, c₀ s) ∈ E) :
    (s + p, c₀ s) ∈ E' ∧ Tmap p (s, c₀ s) = (s + p, c₀ s) :=
  ⟨hT ▸ ⟨(s, c₀ s), hmem, rfl⟩, rfl⟩

/-- **From the geometry to the correspondence equations.**  Given the two carriers (`E` and its
translate `E' = T '' E`), height functions on each and the *uniqueness* of the sheet point over a
level (the graph-like case), the correspondence `c₁ (s + p) = c₀ s` — and by symmetry
`c₀ (s + p) = c₁ s` — follows.  In the general (non graph-like) case the two correspondence
equations are simply the *presentation data* of the two-sheet family, obtained by choosing the two
height functions compatibly via `exists_local_constant_sections`. -/
lemma two_sheet_correspondence {p : ℝ} {E E' : Set (ℝ × ℝ)} (hT : Tmap p '' E = E')
    {c₀ c₁ : ℝ → ℝ} (hmem₀ : ∀ s : ℝ, (s, c₀ s) ∈ E) (hmem₁ : ∀ s : ℝ, (s, c₁ s) ∈ E')
    (hgraph : ∀ s t t' : ℝ, (s, t) ∈ E' → (s, t') ∈ E' → t = t') :
    ∀ s : ℝ, c₁ (s + p) = c₀ s := by
  intro s
  have h1 : (s + p, c₀ s) ∈ E' := (carrier_point_correspondence hT (hmem₀ s)).1
  exact hgraph (s + p) (c₁ (s + p)) (c₀ s) (hmem₁ (s + p)) h1

/-- **No global graph presentation of an open carrier.**

If `E ⊆ ℝ × ℝ` is open and `(s,t) ∈ E`, then the level `{s} × ℝ` meets `E` in more than one point:
`(s, t + ε/2) ∈ E` for small `ε > 0`.

**Why this matters.**  The two-sheet presentation of the bad case asks for height functions `c₀`,
`c₁` over the level line with `c₀ (s+p) = c₁ s` and `c₁ (s+p) = c₀ s`.  In the *graph-like* model
(each sheet meeting a level at most once) this follows from the geometry
(`two_sheet_correspondence`).  But for an **open** carrier the sheet point over a level is never
unique — this lemma — so those equations cannot be *derived* from the geometry: they are a
compatible *choice* of presentation data, available only *locally* (from the boxes of
`exists_local_constant_sections`).  Gluing those local presentations around the circle is exactly the
selection problem of Route B, i.e. the original `H₁`/Mayer–Vietoris obstacle.  Consequently the
parity tier below is a complete analysis of the *graph-like/two-sheet model* (the `k = 2`
configuration as it arises from an embedded/wrapped tube), and it does **not** by itself close the
crux; what it does is localise the obstruction and supply the parity mechanism. -/
lemma open_carrier_level_not_unique {E : Set (ℝ × ℝ)} (hE : IsOpen E) {s t : ℝ}
    (h : (s, t) ∈ E) : ∃ t' ≠ t, (s, t') ∈ E := by
  obtain ⟨r, hr, hr'⟩ := Metric.isOpen_iff.mp hE (s, t) h
  refine ⟨t + r/2, by linarith, hr' ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  constructor
  · rw [Real.dist_eq]; simp [hr]
  · rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
/-- **Pasting local continuous sections over a finite open cover.**

If `U i` (finitely many) is an open cover and the `f i` are continuous on `U i` and agree on all
overlaps, then they paste to a continuous global function: define `u` by choosing any `i` with
`x ∈ U i` and setting `u x := f i x` (well defined by agreement); at each `x`, `u` agrees on the
open neighbourhood `U (ind x)` with the function `f (ind x)`, which is continuous there.

This is the **cover-theoretic half of the gluing step**: with local sections in hand, the only
obstruction to a global one is their discrepancy on overlaps. -/
theorem pasting_local_sections {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι] (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i) (f : ι → X → Y)
    (hf : ∀ i, ContinuousOn (f i) (U i))
    (hagree : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x) :
    ∃ u : X → Y, Continuous u ∧ ∀ i x, x ∈ U i → u x = f i x := by
  classical
  have hmem : ∀ x : X, ∃ i, x ∈ U i := fun x => Set.mem_iUnion.mp (hcover (Set.mem_univ x))
  choose ind hind using hmem
  refine ⟨fun x => f (ind x) x, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    have hx : x ∈ U (ind x) := hind x
    have hev : (fun y => f (ind x) y) =ᶠ[𝓝 x] fun y => f (ind y) y := by
      filter_upwards [(hUo (ind x)).mem_nhds hx] with y hy
      exact (hagree (ind y) (ind x) y (hind y) hy).symm
    exact ((hf (ind x)).continuousAt ((hUo (ind x)).mem_nhds hx)).congr hev
  · intro i x hx
    exact hagree (ind x) i x (hind x) hx

/-- **Gluing of admissible local constants that agree on overlaps.** -/
lemma exists_continuous_of_agreeing_constants {D : Set (ℝ × ℝ)} {ι : Type*} [Fintype ι]
    (U : ι → Set ℝ) (hUo : ∀ i, IsOpen (U i)) (hcover : (Set.univ : Set ℝ) ⊆ ⋃ i, U i)
    (c : ι → ℝ) (hadm : ∀ i s, s ∈ U i → (s, c i) ∈ D)
    (hagree : ∀ i j s, s ∈ U i → s ∈ U j → c i = c j) :
    ∃ u : ℝ → ℝ, Continuous u ∧ ∀ s : ℝ, (s, u s) ∈ D := by
  obtain ⟨u, hcont, hu⟩ := pasting_local_sections U hUo hcover (fun i _ => c i)
    (fun i => continuousOn_const) (fun i j s _ _ => (hagree i j s ‹_› ‹_›).symm ▸ rfl)
  refine ⟨u, hcont, fun s => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ s))
  rw [show u s = c i from hu i s hi]
  exact hadm i s hi

/-- **Linear adjustment of two admissible constants.**

If for every level `s` of `U` the whole segment between the two admissible heights `c₀`, `c₁` stays
inside `D`, then for any continuous weight `φ` with values in `[0,1]` the interpolated height
`(1 - φ s) * c₀ + φ s * c₁` is again an admissible section over `U`.  With `φ` a ramp from `0` to `1`
this *adjusts* one local constant to the other across the overlap, which is the mechanism by which
local sections are made to agree before `exists_continuous_of_agreeing_constants` glues them.

*Status of the general adjustment.*  In the general case the segment between two admissible heights
need not lie in `D` (the fibre `D_s` is only open, not convex), and the statement "the local
constants can always be adjusted to agree on overlaps" is *equivalent* to the selection statement
itself: given agreeing local sections, `exists_continuous_of_agreeing_constants` produces the global
selection, and conversely a global selection restricted to a cover *is* a family of agreeing local
sections.  So this step is not a separate stepping stone but the same `H₁`/Čech content in its
gluing form; what is proved here is the adjustment in the *convex-fibre* case, alongside the
agreeing-constants case above. -/
lemma exists_interp_admissible {D : Set (ℝ × ℝ)} {c₀ c₁ : ℝ} {U : Set ℝ}
    (hseg : ∀ s ∈ U, ∀ θ ∈ Set.Icc (0:ℝ) 1, (s, (1 - θ) * c₀ + θ * c₁) ∈ D)
    (φ : ℝ → ℝ) (hφc : Continuous φ) (hφ : ∀ s, φ s ∈ Set.Icc (0:ℝ) 1) :
    ContinuousOn (fun s => (1 - φ s) * c₀ + φ s * c₁) U ∧
      ∀ s ∈ U, (s, (1 - φ s) * c₀ + φ s * c₁) ∈ D := by
  refine ⟨?_, fun s hs => hseg s hs (φ s) (hφ s)⟩
  exact (((continuous_const.sub hφc).mul continuous_const).add
    (hφc.mul continuous_const)).continuousOn

/-! ## Reduction of the crux to the cylinder selection lemma (session 3)

The affine homotopy `H (s,t) = (1-t) α s + t β s` between the two `T`-crossings `α ⊆ VA` and
`β ⊆ VB` is `T`-equivariant (`H (1,t) = T (H (0,t))`) because `T` is affine; pulling `VA` and
`VB` back along `H` gives the two-set open cover of the cylinder `[0,1]_s × [0,1]_t`, and a
continuous selection `u` of the overlap produces a `T`-crossing in `VA ∩ VB`.  This reduces the
crux to the *single* self-contained `cylinder_selection` below. -/

/-- The point `(1-t) q₁ + t q₂` of the segment joining `q₁` and `q₂` in `ℝ × ℝ`. -/
def aff (t : ℝ) (q₁ q₂ : ℝ × ℝ) : ℝ × ℝ := (1 - t) • q₁ + t • q₂

@[simp] lemma aff_apply (t : ℝ) (q₁ q₂ : ℝ × ℝ) :
    aff t q₁ q₂ = (1 - t) • q₁ + t • q₂ := rfl

lemma continuous_aff (q₁ q₂ : ℝ × ℝ) : Continuous fun t : ℝ => aff t q₁ q₂ := by
  unfold aff; fun_prop

@[simp] lemma aff_zero (q₁ q₂ : ℝ × ℝ) : aff 0 q₁ q₂ = q₁ := by simp [aff]
@[simp] lemma aff_one (q₁ q₂ : ℝ × ℝ) : aff 1 q₁ q₂ = q₂ := by simp [aff]

lemma Tmap_aff (p : ℝ) (t : ℝ) (q₁ q₂ : ℝ × ℝ) :
    Tmap p (aff t q₁ q₂) = aff t (Tmap p q₁) (Tmap p q₂) := by
  ext <;>
    simp only [Tmap, aff, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] <;> ring

/-! ### Auxiliary lemmas for `cylinder_selection`: the fibre map is lower semicontinuous

These are the point-set inputs to the selection argument.  The first says that a *box* around a
point of an open set lies in it (the local product structure, straight from `isOpen_prod_iff`);
the second assembles boxes into a vertical tube; the third is the form in which the selection
argument consumes them: the family of nonempty fibres of an open set is *lower semicontinuous* —
if the fibre at `s` comes within `ε` of `y`, then so does the fibre at every `s'` in a
neighbourhood of `s`. -/

/-- **Local box in an open set.**  Every point of an open `P ⊆ ℝ × ℝ` is the centre of a product
of two open intervals contained in `P`. -/
theorem exists_box_of_isOpen_mem {P : Set (ℝ × ℝ)} (hP : IsOpen P) {s t : ℝ} (hst : (s, t) ∈ P) :
    ∃ r > 0, Set.Ioo (s - r) (s + r) ×ˢ Set.Ioo (t - r) (t + r) ⊆ P := by
  obtain ⟨U, V, hU, hV, hsU, htV, hUV⟩ := (isOpen_prod_iff.mp hP) s t hst
  obtain ⟨r₁, hr₁, hI₁⟩ := (nhds_basis_Ioo_pos s).mem_iff.mp (hU.mem_nhds hsU)
  obtain ⟨r₂, hr₂, hI₂⟩ := (nhds_basis_Ioo_pos t).mem_iff.mp (hV.mem_nhds htV)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  exact hUV ⟨hI₁ ⟨by linarith [hu.1, min_le_left r₁ r₂], by linarith [hu.2, min_le_left r₁ r₂]⟩,
              hI₂ ⟨by linarith [hv.1, min_le_right r₁ r₂], by linarith [hv.2, min_le_right r₁ r₂]⟩⟩

/-- **Vertical tube.**  A vertical segment `{s} × [a,b]` inside an open `P ⊆ ℝ × ℝ` has a product
`(s - δ, s + δ) × [a,b]` inside `P`. -/
theorem exists_tube_of_isOpen {P : Set (ℝ × ℝ)} (hP : IsOpen P) {s a b : ℝ} (hab : a ≤ b)
    (hseg : ∀ t ∈ Set.Icc a b, (s, t) ∈ P) :
    ∃ δ > 0, Set.Ioo (s - δ) (s + δ) ×ˢ Set.Icc a b ⊆ P := by
  have key : ∀ q : ↥(Set.Icc a b), ∃ r > 0,
      Set.Ioo (s - r) (s + r) ×ˢ Set.Ioo ((q : ℝ) - r) ((q : ℝ) + r) ⊆ P := by
    intro q
    obtain ⟨U, V, hU, hV, hsU, hqV, hUV⟩ :=
      (isOpen_prod_iff.mp hP) s (q : ℝ) (hseg q q.2)
    obtain ⟨r₁, hr₁, hI₁⟩ := (nhds_basis_Ioo_pos s).mem_iff.mp (hU.mem_nhds hsU)
    obtain ⟨r₂, hr₂, hI₂⟩ := (nhds_basis_Ioo_pos (q : ℝ)).mem_iff.mp (hV.mem_nhds hqV)
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact hUV ⟨hI₁ ⟨by linarith [hu.1, min_le_left r₁ r₂],
                     by linarith [hu.2, min_le_left r₁ r₂]⟩,
                hI₂ ⟨by linarith [hv.1, min_le_right r₁ r₂],
                     by linarith [hv.2, min_le_right r₁ r₂]⟩⟩
  choose r hrpos hrsub using key
  have hcov : Set.Icc a b ⊆ ⋃ q : ↥(Set.Icc a b),
      Set.Ioo ((q : ℝ) - r q) ((q : ℝ) + r q) := by
    intro v hv
    refine mem_iUnion.mpr ⟨⟨v, hv⟩, ⟨?_, ?_⟩⟩
    · linarith [hrpos (⟨v, hv⟩ : ↥(Set.Icc a b))]
    · linarith [hrpos (⟨v, hv⟩ : ↥(Set.Icc a b))]
  obtain ⟨T, hTcov⟩ := isCompact_Icc.elim_finite_subcover
    (fun q : ↥(Set.Icc a b) => Set.Ioo ((q : ℝ) - r q) ((q : ℝ) + r q))
    (fun _ => isOpen_Ioo) hcov
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h | h
    · exfalso
      have : a ∈ ⋃ q ∈ T, Set.Ioo ((q : ℝ) - r q) ((q : ℝ) + r q) := hTcov ⟨le_rfl, hab⟩
      simpa [h] using this
    · exact h
  have hne : (T.image r).Nonempty := hTne.image r
  obtain ⟨δ, hδpos, hδle⟩ : ∃ δ > 0, ∀ q ∈ T, δ ≤ r q :=
    ⟨(T.image r).min' hne,
      (by
        obtain ⟨q, hq, hqr⟩ := Finset.mem_image.mp ((T.image r).min'_mem hne)
        rw [← hqr]
        exact hrpos q),
      fun q hq => Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)⟩
  refine ⟨δ, hδpos, ?_⟩
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  obtain ⟨q, hqT, hqv⟩ := mem_iUnion₂.mp (hTcov hv)
  exact hrsub q ⟨⟨by linarith [hu.1, hδle q hqT], by linarith [hu.2, hδle q hqT]⟩, hqv⟩

/-- **The fibre map of an open set is lower semicontinuous.**  If the fibre of `P` at `s` comes
within `ε` of `y`, then so does the fibre at every `s'` in a neighbourhood of `s`. -/
theorem exists_fibre_meets_Ioo_of_isOpen {P : Set (ℝ × ℝ)} (hP : IsOpen P) {s t y ε : ℝ}
    (hst : (s, t) ∈ P) (hy : |t - y| < ε) :
    ∃ δ > 0, ∀ s' : ℝ, |s' - s| < δ →
      ∃ t' ∈ Set.Ioo (y - ε) (y + ε), (s', t') ∈ P := by
  obtain ⟨U, V, hU, hV, hsU, htV, hUV⟩ := (isOpen_prod_iff.mp hP) s t hst
  obtain ⟨r₁, hr₁, hI₁⟩ := (nhds_basis_Ioo_pos s).mem_iff.mp (hU.mem_nhds hsU)
  refine ⟨r₁, hr₁, fun s' hs' => ⟨t, ?_, hUV ⟨hI₁ ?_, htV⟩⟩⟩
  · rw [abs_lt] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · rw [abs_lt] at hs'
    exact ⟨by linarith [hs'.1], by linarith [hs'.2]⟩


/-! ### The closedness input: free points persist, spikes cannot occur

The gap insight — a convex combination of admissible heights can fall into a *gap* of the fibre,
so openness of `P ∩ Q` alone cannot produce a selection — is repaired by the closedness of
`K = (P ∩ Q)ᶜ`.  The two lemmas below are the precise form of that.  The first is the general
statement: a point of `[0,1]` which is not in the limit fibre `K_{s₀}` is not in the fibres
`K_{s n}` for infinitely many `n`.  The second is the "spike" form: if along `s n → s₀` the fibres
of `K` contain all of `[0,1]` except a shrinking window around `c n → c₀`, then the limit fibre
contains `[0,1] ∖ {c₀}` — so the free fibre at `s₀` is contained in the singleton `{c₀}`, and being
open it must be empty. -/

/-- **Closedness: free points of the limit fibre persist.**  If `K ⊆ ℝ × ℝ` is closed, `s n → s₀`,
and `(s₀, y) ∉ K`, then `(s n, y) ∉ K` infinitely often. -/
theorem frequently_notMem_fibre_of_notMem {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    {s : ℕ → ℝ} {s₀ y : ℝ} (hs : Tendsto s atTop (𝓝 s₀)) (hfree : (s₀, y) ∉ K) :
    ∃ᶠ n in atTop, (s n, y) ∉ K := by
  by_contra h
  rw [Filter.not_frequently] at h
  have h' : ∀ᶠ n in atTop, (s n, y) ∈ K := by
    filter_upwards [h] with n hn
    simpa using hn
  have hpair : Tendsto (fun n => (s n, y)) atTop (𝓝 (s₀, y)) := by
    rw [Prod.tendsto_iff]
    exact ⟨hs, tendsto_const_nhds⟩
  exact hfree (hK.mem_of_tendsto hpair h')

/-- **Spike exclusion.**  If along `s n → s₀` the fibres of a closed `K ⊆ ℝ × ℝ` contain all of
`[0,1]` except a shrinking window `Ioo (c n - e n) (c n + e n)` around `c n → c₀`, then the limit
fibre contains `[0,1] ∖ {c₀}`.  Hence a selection with a discontinuity at `s₀` — fibres filling up
everything but a shrinking window — is impossible whenever the complement of `K` is open and meets
`[0,1]` over `s₀` non-trivially. -/
theorem Icc_diff_singleton_subset_fibre {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    {s : ℕ → ℝ} {s₀ : ℝ} {c e : ℕ → ℝ} {c₀ : ℝ}
    (hs : Tendsto s atTop (𝓝 s₀)) (hc : Tendsto c atTop (𝓝 c₀)) (he : Tendsto e atTop (𝓝 0))
    (hsub : ∀ n, Set.Icc (0:ℝ) 1 \ Set.Ioo (c n - e n) (c n + e n) ⊆ {t : ℝ | (s n, t) ∈ K}) :
    Set.Icc (0:ℝ) 1 \ {c₀} ⊆ {t : ℝ | (s₀, t) ∈ K} := by
  intro y hy
  have hyc : y ≠ c₀ := hy.2
  have hpos : 0 < |y - c₀| := abs_pos.mpr (sub_ne_zero.mpr hyc)
  have hev : ∀ᶠ n in atTop, y ∉ Set.Ioo (c n - e n) (c n + e n) := by
    have hc' : ∀ᶠ n in atTop, |c n - c₀| < |y - c₀| / 2 := by
      have h := (Metric.tendsto_nhds.mp hc) (|y - c₀| / 2) (by positivity)
      simpa [Real.dist_eq] using h
    have he' : ∀ᶠ n in atTop, |e n| < |y - c₀| / 2 := by
      have h := (Metric.tendsto_nhds.mp he) (|y - c₀| / 2) (by positivity)
      simpa [Real.dist_eq, sub_zero] using h
    filter_upwards [hc', he'] with n h1 h2
    intro hmem
    rw [Set.mem_Ioo] at hmem
    rcases lt_or_gt_of_ne hyc with hlt | hgt
    · rw [abs_of_neg (by linarith : y - c₀ < 0)] at h1 h2
      have h3 : c₀ - (c₀ - y) / 2 ≤ c n := by rw [abs_lt] at h1; linarith [h1.1]
      have h4 : e n ≤ (c₀ - y) / 2 := by rw [abs_lt] at h2; linarith [h2.2]
      linarith [hmem.1]
    · rw [abs_of_pos (by linarith : 0 < y - c₀)] at h1 h2
      have h3 : c n ≤ c₀ + (y - c₀) / 2 := by rw [abs_lt] at h1; linarith [h1.2]
      have h4 : e n ≤ (y - c₀) / 2 := by rw [abs_lt] at h2; linarith [h2.2]
      linarith [hmem.2]
  have hpair : Tendsto (fun n => (s n, y)) atTop (𝓝 (s₀, y)) := by
    rw [Prod.tendsto_iff]
    exact ⟨hs, tendsto_const_nhds⟩
  exact hK.mem_of_tendsto hpair (hev.mono fun n hn => hsub n ⟨hy.1, hn⟩)


/-! ### Component extension: free points spread to a free box

Combining the local box lemma with convexity: a free point of a closed `K` lies in a *free box*
whose points are all free and all joined to it inside `Kᶜ`.  Consequently a free point persists
along any convergent sequence `s n → s₀`, together with a whole free interval around its level —
this is the "component extension" step: the component of `Kᶜ` through `(s₀, y₀)` meets the fibres
over all large `s n` in an interval. -/

/-- Points of a convex subset of `ℝ × ℝ` are joined inside it (via the straight-line path). -/
theorem joinedIn_of_convex {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) {x y : ℝ × ℝ}
    (hx : x ∈ S) (hy : y ∈ S) : JoinedIn S x y := by
  refine ⟨{ toFun := fun t : Set.Icc (0:ℝ) 1 => (1 - (t : ℝ)) • x + (t : ℝ) • y
            continuous_toFun := by fun_prop
            source' := by simp
            target' := by simp }, ?_⟩
  intro t
  exact hS hx hy (by linarith [t.2.1, t.2.2]) (by linarith [t.2.1, t.2.2]) (by ring)

/-- **Component extension (box form).**  A free point of a closed `K` lies in a free box: every
point of the product of intervals around it is free, and is joined to the original point inside the
complement `Kᶜ`. -/
theorem exists_box_free_and_joined {K : Set (ℝ × ℝ)} (hK : IsClosed K) {s₀ y₀ : ℝ}
    (h : (s₀, y₀) ∉ K) :
    ∃ δ > 0, ∃ ε > 0, Set.Ioo (s₀ - δ) (s₀ + δ) ×ˢ Set.Ioo (y₀ - ε) (y₀ + ε) ⊆ Kᶜ ∧
      ∀ s ∈ Set.Ioo (s₀ - δ) (s₀ + δ), ∀ y ∈ Set.Ioo (y₀ - ε) (y₀ + ε),
        (s, y) ∈ Kᶜ ∧ JoinedIn Kᶜ (s₀, y₀) (s, y) := by
  have hopen : IsOpen Kᶜ := hK.isOpen_compl
  obtain ⟨U, V, hU, hV, hsU, hyV, hUV⟩ := (isOpen_prod_iff.mp hopen) s₀ y₀ h
  obtain ⟨δ, hδ, hIδ⟩ := (nhds_basis_Ioo_pos s₀).mem_iff.mp (hU.mem_nhds hsU)
  obtain ⟨ε, hε, hIε⟩ := (nhds_basis_Ioo_pos y₀).mem_iff.mp (hV.mem_nhds hyV)
  have hbox : Set.Ioo (s₀ - δ) (s₀ + δ) ×ˢ Set.Ioo (y₀ - ε) (y₀ + ε) ⊆ Kᶜ := by
    rintro ⟨s', y'⟩ ⟨hs', hy'⟩
    exact hUV ⟨hIδ hs', hIε hy'⟩
  refine ⟨δ, hδ, ε, hε, hbox, ?_⟩
  intro s hs y hy
  have hconv : Convex ℝ (Set.Ioo (s₀ - δ) (s₀ + δ) ×ˢ Set.Ioo (y₀ - ε) (y₀ + ε)) :=
    (convex_Ioo _ _).prod (convex_Ioo _ _)
  have hmem0 : (s₀, y₀) ∈ Set.Ioo (s₀ - δ) (s₀ + δ) ×ˢ Set.Ioo (y₀ - ε) (y₀ + ε) :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  exact ⟨hbox ⟨hs, hy⟩, (joinedIn_of_convex hconv hmem0 ⟨hs, hy⟩).mono hbox⟩

/-- **Component extension (sequential form).**  A free point of a closed `K` survives a convergent
sequence: `(s n, y)` is free — and joined to `(s₀, y₀)` inside `Kᶜ` — for all large `n` and all `y`
in a fixed interval around `y₀`. -/
theorem eventually_free_interval_of_tendsto {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    {s : ℕ → ℝ} {s₀ y₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀)) (hfree : (s₀, y₀) ∉ K) :
    ∃ ε > 0, ∀ᶠ n in atTop, ∀ y ∈ Set.Ioo (y₀ - ε) (y₀ + ε),
      (s n, y) ∈ Kᶜ ∧ JoinedIn Kᶜ (s₀, y₀) (s n, y) := by
  obtain ⟨δ, hδ, ε, hε, hbox, hjoin⟩ := exists_box_free_and_joined hK hfree
  refine ⟨ε, hε, ?_⟩
  have hev : ∀ᶠ n in atTop, s n ∈ Set.Ioo (s₀ - δ) (s₀ + δ) :=
    hs.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  filter_upwards [hev] with n hn
  exact fun y hy => hjoin (s n) hn y hy


/-! ### Gluing, step 1: a `T`-invariant component of the free region gives a translate path

Components of an open subset of `ℝ × ℝ` are path connected, so containment of a point and its
translate in a single component already produces a genuine `JoinedIn` witness.  This is the easy
half of the gluing (the half that needs no analysis of the free region's shape); the remaining
half is to show that such a component must *exist*. -/

/-- **A `T`-invariant component of the free region yields a translate path.**  If `D` is open and
`z ∈ D` has its translate `(z.1 + p, z.2)` in the same connected component of `D`, then `D` contains
a path from `z` to its translate. -/
theorem joinedIn_of_mem_connectedComponentIn {D : Set (ℝ × ℝ)} (hD : IsOpen D) {p : ℝ}
    {z : ℝ × ℝ} (hzD : z ∈ D) (hz : (z.1 + p, z.2) ∈ connectedComponentIn D z) :
    JoinedIn D z (z.1 + p, z.2) := by
  have hCopen : IsOpen (connectedComponentIn D z) := hD.connectedComponentIn
  have hCpath : IsPathConnected (connectedComponentIn D z) := by
    rw [← IsOpen.isConnected_iff_isPathConnected hCopen]
    exact ⟨⟨z, mem_connectedComponentIn hzD⟩, isPreconnected_connectedComponentIn⟩
  exact (hCpath.joinedIn z (mem_connectedComponentIn hzD) (z.1 + p, z.2) hz).mono
    (connectedComponentIn_subset D z)


/-! ### Session 12: the sharp reduction — a `p`-periodic graph in `VA ∩ VB` suffices

The gap recorded below (`cylinder_selection`) is *sufficient* for the crux, but it is not the
sharpest form of the missing input.  Session 12 isolated a strictly cleaner statement from which
the crux follows *immediately*, and which is therefore the right shape of the remaining gap:

  *there is a continuous `p`-periodic `u` with `(s, u s) ∈ VA ∩ VB` for every real `s`.*

For such a `u` the graph `Γ = {(s, u s)}` is a connected subset of `VA ∩ VB`, and because `u` is
`p`-periodic the point `T (0, u 0) = (p, u 0) = (p, u p)` already lies on `Γ`; hence `T (0, u 0)`
lies in the *same* connected component of `VA ∩ VB` as `(0, u 0)`, and that component is path
connected (it is open) while being contained in both `VA` and `VB` — exactly the crux.

Nothing about a homotopy `H` or the pull-backs `P = H⁻¹ VA`, `Q = H⁻¹ VB` is needed: the statement
is purely about `VA`, `VB` and their intersection.  It is the natural formulation of the missing
`H₁`-argument of Denne's `prop:homology`, namely "the projection `(VA ∩ VB)/T → ℝ/pℤ` admits a
continuous section". -/

/-- **A `p`-periodic graph in a `T`-invariant open set produces a translate path.**

If `W` is open and `u : ℝ → ℝ` is continuous and `p`-periodic with `(s, u s) ∈ W` for all `s`, then
`W` contains a path from a point to its translate: the graph is connected and already contains a
point together with its translate, so both lie in a single component of `W`. -/
theorem graph_periodic_translate {p : ℝ} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    {u : ℝ → ℝ} (hu : Continuous u) (hmem : ∀ s : ℝ, (s, u s) ∈ W)
    (hperu : ∀ s : ℝ, u (s + p) = u s) :
    ∃ z : ℝ × ℝ, z ∈ W ∧ JoinedIn W z (Tmap p z) := by
  have hΓ : IsPreconnected (Set.range fun s : ℝ => (s, u s)) :=
    isPreconnected_range (continuous_id.prodMk hu)
  have h0 : ((0:ℝ), u 0) ∈ Set.range (fun s : ℝ => (s, u s)) := ⟨0, rfl⟩
  have hsub : Set.range (fun s : ℝ => (s, u s)) ⊆ W := by
    rintro _ ⟨s, rfl⟩
    exact hmem s
  have hC : (((0:ℝ), u 0).1 + p, ((0:ℝ), u 0).2) ∈ connectedComponentIn W ((0:ℝ), u 0) := by
    refine hΓ.subset_connectedComponentIn h0 hsub ⟨0 + p, ?_⟩
    show ((0 + p : ℝ), u (0 + p)) = ((0:ℝ) + p, u 0)
    rw [hperu 0]
  exact ⟨((0:ℝ), u 0), hmem 0,
    joinedIn_of_mem_connectedComponentIn hW (hmem 0) hC⟩

/-- **The crux follows from a `p`-periodic graph in `VA ∩ VB`.**

This is the sharp reduction of session 12: the remaining content of Denne's cancellation is exactly
the existence of a continuous `p`-periodic selection into `VA ∩ VB`. -/
theorem crux_of_periodic_graph {p : ℝ} {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hgraph : ∃ u : ℝ → ℝ, Continuous u ∧ (∀ s : ℝ, u (s + p) = u s) ∧
      ∀ s : ℝ, (s, u s) ∈ VA ∩ VB) :
    ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB := by
  obtain ⟨u, huc, hper, hmem⟩ := hgraph
  obtain ⟨z, hzW, hjoin⟩ := graph_periodic_translate (p := p) (hVA.inter hVB)
    huc hmem hper
  exact ⟨z, ⟨hzW.1, hjoin.mono inter_subset_left⟩, ⟨hzW.2, hjoin.mono inter_subset_right⟩⟩

/-- **The target lemma follows from the periodic-graph statement alone.**

This packages the whole chain in one place: given the `p`-periodic graph in `VA ∩ VB`, the target
statement `annulus_essential_intersection` holds *verbatim* — the hypotheses of the target are not
even used beyond openness of the two sets, because `graph_periodic_translate` already produces the
`JoinedIn` paths inside `VA ∩ VB`, hence inside `VA` and inside `VB`. -/
theorem annulus_essential_intersection_of_periodic_graph {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hsubB : VB ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hcover : VA ∪ VB = {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (z.1 + p, z.2))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (z.1 + p, z.2))
    (hgraph : ∃ u : ℝ → ℝ, Continuous u ∧ (∀ s : ℝ, u (s + p) = u s) ∧
      ∀ s : ℝ, (s, u s) ∈ VA ∩ VB) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (z.1 + p, z.2) ∧
      JoinedIn VB z (z.1 + p, z.2) := by
  obtain ⟨u, huc, hperu, hmem⟩ := hgraph
  obtain ⟨z, hzW, hjoin⟩ := graph_periodic_translate (p := p) (hVA.inter hVB) huc hmem hperu
  exact ⟨z, hzW, hjoin.mono inter_subset_left, hjoin.mono inter_subset_right⟩


/-! ### Session 13: the "corridor" engine — this discharges the crossing case's *room* half

The two lemmas below are the engine of the whole selection argument, and they need **no**
partition-of-unity machinery: an open set in the plane all of whose vertical fibres are nonempty and
*convex* is connected, and therefore, when it is also `T`-invariant and contained in `W`, it already
furnishes the translate path inside `W`.

This is exactly what the "room" case of the crux needs: as soon as the two extents `σ` (last entry to
`VB`) and `τ` (first exit from `VA`) satisfy `σ s < τ s` for **all** `s`, the corridor

  `G := {q : σ q.1 < q.2 < τ q.1}`

is open (`σ` is upper semicontinuous, `τ` lower semicontinuous — see the correction below), has
nonempty convex fibres, is
`p`-periodic (`σ`, `τ` are), and is contained in the fibres of `VA ∩ VB` (proved above).  Hence `G`
is connected and `T`-invariant, so it lies in a single `T`-invariant component of `VA ∩ VB`, which is
the crux. -/

/-- **An open set in the plane whose vertical fibres are all nonempty and convex is connected.**

(The argument: if `G = G₁ ⊔ G₂` with `G₁`, `G₂` open and nonempty, then each fibre — being convex,
hence connected — lies wholly in one of the two, so the two projections `π G₁`, `π G₂` are disjoint
nonempty *open* subsets of `ℝ` covering `ℝ`, contradicting connectedness of `ℝ`.) -/
theorem isPreconnected_of_convex_fibres {G : Set (ℝ × ℝ)} (hG : IsOpen G)
    (hfib : ∀ s : ℝ, Convex ℝ {t : ℝ | (s, t) ∈ G}) (hne : ∀ s : ℝ, ∃ t : ℝ, (s, t) ∈ G) :
    IsPreconnected G := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv huv'
  -- Every fibre of `G` lies wholly in the fibre of `u` or in the fibre of `v`.
  have hfib_sub : ∀ s : ℝ, ({t : ℝ | (s, t) ∈ G} ⊆ {t : ℝ | (s, t) ∈ u}) ∨
      ({t : ℝ | (s, t) ∈ G} ⊆ {t : ℝ | (s, t) ∈ v}) := by
    intro s
    have hconn : IsPreconnected {t : ℝ | (s, t) ∈ G} := (hfib s).isPreconnected
    have h1 : IsOpen {t : ℝ | (s, t) ∈ u} :=
      hu.preimage (continuous_const.prodMk continuous_id)
    have h2 : IsOpen {t : ℝ | (s, t) ∈ v} :=
      hv.preimage (continuous_const.prodMk continuous_id)
    have h3 : {t : ℝ | (s, t) ∈ G} ⊆ {t : ℝ | (s, t) ∈ u} ∪ {t : ℝ | (s, t) ∈ v} := by
      intro t ht
      rcases huv ht with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h4 : {t : ℝ | (s, t) ∈ G} ∩ ({t : ℝ | (s, t) ∈ u} ∩ {t : ℝ | (s, t) ∈ v}) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨ht, htu, htv⟩
      have hmem : (s, t) ∈ G ∩ (u ∩ v) := ⟨ht, htu, htv⟩
      rw [huv'] at hmem
      exact hmem
    exact isPreconnected_iff_subset_of_disjoint.mp hconn _ _ h1 h2 h3 h4
  set Su : Set ℝ := {s : ℝ | ∃ t : ℝ, (s, t) ∈ G ∧ (s, t) ∈ u} with hSu
  set Sv : Set ℝ := {s : ℝ | ∃ t : ℝ, (s, t) ∈ G ∧ (s, t) ∈ v} with hSv
  have hSuopen : IsOpen Su := by
    have hEq : Su = Prod.fst '' (G ∩ u) := by
      ext s
      constructor
      · rintro ⟨t, h1, h2⟩
        exact ⟨(s, t), ⟨h1, h2⟩, rfl⟩
      · rintro ⟨q, ⟨h1, h2⟩, rfl⟩
        exact ⟨q.2, h1, h2⟩
    rw [hEq]
    exact isOpenMap_fst _ (hG.inter hu)
  have hSvopen : IsOpen Sv := by
    have hEq : Sv = Prod.fst '' (G ∩ v) := by
      ext s
      constructor
      · rintro ⟨t, h1, h2⟩
        exact ⟨(s, t), ⟨h1, h2⟩, rfl⟩
      · rintro ⟨q, ⟨h1, h2⟩, rfl⟩
        exact ⟨q.2, h1, h2⟩
    rw [hEq]
    exact isOpenMap_fst _ (hG.inter hv)
  have hcover : (univ : Set ℝ) ⊆ Su ∪ Sv := by
    intro s _
    obtain ⟨t, ht⟩ := hne s
    rcases huv ht with h | h
    · exact Or.inl ⟨t, ht, h⟩
    · exact Or.inr ⟨t, ht, h⟩
  have hdisj : (univ : Set ℝ) ∩ (Su ∩ Sv) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro s ⟨-, ⟨t₁, hg₁, hu₁⟩, t₂, hg₂, hv₂⟩
    rcases hfib_sub s with h | h
    · have hmem : t₂ ∈ {t : ℝ | (s, t) ∈ u} := h hg₂
      have : (s, t₂) ∈ G ∩ (u ∩ v) := ⟨hg₂, hmem, hv₂⟩
      rw [huv'] at this
      exact this
    · have hmem : t₁ ∈ {t : ℝ | (s, t) ∈ v} := h hg₁
      have : (s, t₁) ∈ G ∩ (u ∩ v) := ⟨hg₁, hu₁, hmem⟩
      rw [huv'] at this
      exact this
  have hres : (univ : Set ℝ) ⊆ Su ∨ (univ : Set ℝ) ⊆ Sv :=
    isPreconnected_iff_subset_of_disjoint.mp (isPreconnected_univ (α := ℝ))
      Su Sv hSuopen hSvopen hcover hdisj
  rcases hres with h | h
  · left
    intro q hq
    rcases hfib_sub q.1 with hq' | hq'
    · exact hq' hq
    · exfalso
      obtain ⟨t, hg, htu⟩ := h (mem_univ q.1)
      have hmem : t ∈ {t : ℝ | (q.1, t) ∈ v} := hq' hg
      have : (q.1, t) ∈ G ∩ (u ∩ v) := ⟨hg, htu, hmem⟩
      rw [huv'] at this
      exact this
  · right
    intro q hq
    rcases hfib_sub q.1 with hq' | hq'
    · exfalso
      obtain ⟨t, hg, htv⟩ := h (mem_univ q.1)
      have hmem : t ∈ {t : ℝ | (q.1, t) ∈ u} := hq' hg
      have : (q.1, t) ∈ G ∩ (u ∩ v) := ⟨hg, hmem, htv⟩
      rw [huv'] at this
      exact this
    · exact hq' hq

/-- **The corridor engine.**  An open `T`-invariant set `G` with nonempty convex vertical fibres,
contained in an open set `W`, already produces the translate path inside `W`. -/
theorem translate_path_of_periodic_corridor {p : ℝ} {W G : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hG : IsOpen G) (hGW : G ⊆ W) (hfib : ∀ s : ℝ, Convex ℝ {t : ℝ | (s, t) ∈ G})
    (hne : ∀ s : ℝ, ∃ t : ℝ, (s, t) ∈ G) (hper : ∀ q : ℝ × ℝ, q ∈ G ↔ Tmap p q ∈ G) :
    ∃ z : ℝ × ℝ, z ∈ W ∧ JoinedIn W z (Tmap p z) := by
  have hpre : IsPreconnected G := isPreconnected_of_convex_fibres hG hfib hne
  obtain ⟨t₀, ht₀⟩ := hne 0
  have hzW : ((0:ℝ), t₀) ∈ W := hGW ht₀
  have hT : (((0:ℝ), t₀).1 + p, ((0:ℝ), t₀).2) ∈ connectedComponentIn W ((0:ℝ), t₀) :=
    hpre.subset_connectedComponentIn ht₀ hGW ((hper _).mp ht₀)
  exact ⟨((0:ℝ), t₀), hzW, joinedIn_of_mem_connectedComponentIn hW hzW hT⟩


/-! ### Session 14b: the local fibre-component lemma — the base case of (Obligation O)

The remaining target (Obligation O of the notes above) is: some `T`-invariant family of
fibre-components of `D = VA ∩ VB` is open.  Every candidate family is defined by a *fibre-wise*
condition, so the base step is the following local statement: a product window inside the open set
`D` is contained in a single component of the fibre.  This is what makes "the component of `D_s`
containing the window" a well-defined function of `s`, and hence makes it possible to ask whether the
family is lower semicontinuous. -/

/-- **A product window inside an open set lies in a single fibre-component.**

If the box `(s₀-δ, s₀+δ) × (t₀-ρ, t₀+ρ)` is contained in the open set `D`, then for every `s` in the
`s`-range of the box the whole window `(t₀-ρ, t₀+ρ)` is contained in the connected component of `t₀`
inside the fibre `D_s = {t : (s,t) ∈ D}`.

(Immediate: the window is convex, hence preconnected, and lies in the fibre; a preconnected subset
lying in a set with a distinguished point lies in that point's component of the set.) -/
theorem fibre_window_subset_component {D : Set (ℝ × ℝ)} {s₀ t₀ δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hbox : Ioo (s₀ - δ) (s₀ + δ) ×ˢ Ioo (t₀ - ρ) (t₀ + ρ) ⊆ D) {s : ℝ}
    (hs : s ∈ Ioo (s₀ - δ) (s₀ + δ)) :
    Ioo (t₀ - ρ) (t₀ + ρ) ⊆ connectedComponentIn {t : ℝ | (s, t) ∈ D} t₀ := by
  have hsub : Ioo (t₀ - ρ) (t₀ + ρ) ⊆ {t : ℝ | (s, t) ∈ D} := by
    intro t ht
    exact hbox ⟨hs, ht⟩
  have hpre : IsPreconnected (Ioo (t₀ - ρ) (t₀ + ρ)) :=
    (convex_Ioo (t₀ - ρ) (t₀ + ρ)).isPreconnected
  have hmem : t₀ ∈ Ioo (t₀ - ρ) (t₀ + ρ) := ⟨by linarith, by linarith⟩
  exact hpre.subset_connectedComponentIn hmem hsub

/-- **Consequence for a box in the plane.**  If a box is contained in `D`, then for every `s` in its
`s`-range the window is contained in one component of the fibre; in particular the assignment
`s ↦ connectedComponentIn {t : (s,t) ∈ D} t₀` is a genuine fibre-component family on that range. -/
theorem fibre_window_eq_component {D : Set (ℝ × ℝ)} {s₀ t₀ δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hbox : Ioo (s₀ - δ) (s₀ + δ) ×ˢ Ioo (t₀ - ρ) (t₀ + ρ) ⊆ D) {s : ℝ}
    (hs : s ∈ Ioo (s₀ - δ) (s₀ + δ)) :
    (connectedComponentIn {t : ℝ | (s, t) ∈ D} t₀).Nonempty ∧
      Ioo (t₀ - ρ) (t₀ + ρ) ⊆ connectedComponentIn {t : ℝ | (s, t) ∈ D} t₀ := by
  have hw := fibre_window_subset_component hδ hρ hbox hs
  have hmem : (s, t₀) ∈ D := hbox ⟨hs, ⟨by linarith, by linarith⟩⟩
  exact ⟨⟨t₀, mem_connectedComponentIn hmem⟩, hw⟩


/-- **Overlapping windows lie in one fibre-component (the piece-family consistency step).**

If two intervals `Ioo a b`, `Ioo c d` both lie in the fibre `D_s` and intersect, then any point of one
is in the same component of `D_s` as any point of the other.  This is what makes the fibre-component
"through a window" well defined *independently of which sub-window is used*, and it is the local
tool for showing that a canonical piece-family is consistent as `s` varies: two windows that overlap
in the `t`-direction and both persist cannot land in different components. -/
theorem fibre_overlapping_windows_same_component {D : Set (ℝ × ℝ)} {s a b c d : ℝ}
    (h1 : Ioo a b ⊆ {t : ℝ | (s, t) ∈ D}) (h2 : Ioo c d ⊆ {t : ℝ | (s, t) ∈ D})
    (hne : (Ioo a b ∩ Ioo c d).Nonempty) {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo c d) :
    y ∈ connectedComponentIn {t : ℝ | (s, t) ∈ D} x := by
  have hpre : IsPreconnected (Ioo a b ∪ Ioo c d) :=
    IsPreconnected.union' hne (convex_Ioo a b).isPreconnected (convex_Ioo c d).isPreconnected
  have hsub : Ioo a b ∪ Ioo c d ⊆ {t : ℝ | (s, t) ∈ D} := Set.union_subset h1 h2
  exact hpre.subset_connectedComponentIn (Or.inl hx) hsub (Or.inr hy)


/-! ### The room-case lower-semicontinuity lemma (the corridor is open)

This is the standalone statement the room case needs, in the abstract form of "two extents".  Its
hypotheses are exactly what the two tube-lemma computations produce from the crux's data: the
`P`-extent `hi` satisfies `Icc 0 t ⊆ P_s` iff `t ≤ hi s`, and the `Q`-extent `lo` satisfies
`Icc t 1 ⊆ Q_s` iff `lo s ≤ t`.  Its conclusion is that the corridor between them is open — which,
together with `translate_path_of_periodic_corridor`, closes the room case of the crux. -/

/-- **The corridor between two extents is open.**  If `lo` and `hi` bound, on every fibre `s`, the
thresholds at which the segments `[0,t] ⊆ P_s` resp. `[t,1] ⊆ Q_s` start/stop holding, and if
`lo s < hi s` everywhere (built in via the two one-sided hypotheses, which are used to produce a
strict gap), then `{q : lo q.1 < q.2 < hi q.1}` is open. -/
theorem corridor_isOpen_of_extent_bounds {P Q : Set (ℝ × ℝ)} (hP : IsOpen P) (hQ : IsOpen Q)
    {lo hi : ℝ → ℝ} (hlo0 : ∀ s : ℝ, 0 ≤ lo s) (hhi1 : ∀ s : ℝ, hi s ≤ 1)
    (hhi_le : ∀ s t : ℝ, Icc 0 t ⊆ {u : ℝ | (s, u) ∈ P} → t ≤ hi s)
    (hhi_ge : ∀ s t : ℝ, t < hi s → Icc 0 t ⊆ {u : ℝ | (s, u) ∈ P})
    (hlo_ge : ∀ s t : ℝ, Icc t 1 ⊆ {u : ℝ | (s, u) ∈ Q} → lo s ≤ t)
    (hlo_le : ∀ s t : ℝ, lo s < t → Icc t 1 ⊆ {u : ℝ | (s, u) ∈ Q}) :
    IsOpen {q : ℝ × ℝ | lo q.1 < q.2 ∧ q.2 < hi q.1} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨s₀, t₀⟩ ⟨hlo₀, hhi₀⟩
  obtain ⟨ε, hεpos, hεhi, hεlo⟩ : ∃ ε > 0, t₀ + ε < hi s₀ ∧ lo s₀ < t₀ - ε := by
    refine ⟨min ((hi s₀ - t₀) / 2) ((t₀ - lo s₀) / 2),
      lt_min (by linarith) (by linarith), ?_, ?_⟩
    · have := min_le_left ((hi s₀ - t₀) / 2) ((t₀ - lo s₀) / 2); linarith
    · have := min_le_right ((hi s₀ - t₀) / 2) ((t₀ - lo s₀) / 2); linarith
  have ht0 : (0:ℝ) < t₀ := lt_of_le_of_lt (hlo0 s₀) hlo₀
  obtain ⟨δ₁, hδ₁, hbox₁⟩ := exists_tube_of_isOpen hP
    (le_of_lt (by linarith [ht0] : (0:ℝ) < t₀ + ε))
    (fun t ht => hhi_ge s₀ (t₀ + ε) hεhi ht)
  obtain ⟨δ₂, hδ₂, hbox₂⟩ := exists_tube_of_isOpen hQ (by linarith [ht0, hhi₀, hhi1 s₀] :
    t₀ - ε ≤ 1)
    (fun t ht => hlo_le s₀ (t₀ - ε) hεlo ht)
  have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  refine mem_nhds_iff.mpr ⟨Ioo (s₀ - min δ₁ δ₂) (s₀ + min δ₁ δ₂) ×ˢ
      Ioo (t₀ - ε / 2) (t₀ + ε / 2), ?_, isOpen_Ioo.prod isOpen_Ioo,
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  have hmin₁ : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
  have hmin₂ : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
  have ha₁ : a ∈ Ioo (s₀ - δ₁) (s₀ + δ₁) :=
    ⟨by linarith [ha.1, hmin₁], by linarith [ha.2, hmin₁]⟩
  have ha₂ : a ∈ Ioo (s₀ - δ₂) (s₀ + δ₂) :=
    ⟨by linarith [ha.1, hmin₂], by linarith [ha.2, hmin₂]⟩
  have hPs : Icc (0:ℝ) (t₀ + ε) ⊆ {u : ℝ | (a, u) ∈ P} := fun u hu => hbox₁ ⟨ha₁, hu⟩
  have hQs : Icc (t₀ - ε) 1 ⊆ {u : ℝ | (a, u) ∈ Q} := fun u hu => hbox₂ ⟨ha₂, hu⟩
  exact ⟨by linarith [hb.1, hlo_ge a (t₀ - ε) hQs], by linarith [hb.2, hhi_le a (t₀ + ε) hPs]⟩


/-! ### The fibre-component centres lemma (session 14c) -/

/-- **The window-component is independent of the window.**  If a box around `(s₀,t₀)` and a box
around `(s₀,u₀)` both lie in `D` and their `t`-windows overlap, then for every `s` in the common
`s`-range the two centres lie in the same fibre-component. -/
theorem fibre_window_centres_same_component {D : Set (ℝ × ℝ)} {s₀ t₀ u₀ δt δu ρt ρu : ℝ}
    {s : ℝ} (hρt : 0 < ρt) (hρu : 0 < ρu)
    (hbox : Ioo (s₀ - δt) (s₀ + δt) ×ˢ Ioo (t₀ - ρt) (t₀ + ρt) ⊆ D)
    (hbox' : Ioo (s₀ - δu) (s₀ + δu) ×ˢ Ioo (u₀ - ρu) (u₀ + ρu) ⊆ D)
    (hne : (Ioo (t₀ - ρt) (t₀ + ρt) ∩ Ioo (u₀ - ρu) (u₀ + ρu)).Nonempty)
    (hs : s ∈ Ioo (s₀ - δt) (s₀ + δt)) (hs' : s ∈ Ioo (s₀ - δu) (s₀ + δu)) :
    u₀ ∈ connectedComponentIn {t : ℝ | (s, t) ∈ D} t₀ := by
  refine fibre_overlapping_windows_same_component (D := D) (s := s) ?_ ?_ hne ?_ ?_
  · intro t ht
    exact hbox ⟨hs, ht⟩
  · intro t ht
    exact hbox' ⟨hs', ht⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩


/-! ### The ends of a fibre-component (the first local facts about the canonical pieces)

These are the local statements that the `τ < σ` regime is built from.  They use only that a fibre
component is connected (hence an interval in `ℝ`) and that the extents `τ`, `σ` are *not* in the
relevant fibres: a component through a point below `τ` cannot reach past `τ`, since it would have to
contain `τ` itself, and `τ` is not in the fibre. -/

/-- **A fibre-component through a point below `hi` stays below `hi`.**  If `(s,hi) ∉ P` and
`(s,t) ∈ P` with `t < hi`, then the component of `t` in the fibre `P_s` is contained in `(-∞,hi)`. -/
theorem component_subset_Iio_of_notMem {P : Set (ℝ × ℝ)} {s hi t : ℝ}
    (hnotmem : (s, hi) ∉ P) (ht : (s, t) ∈ P) (hlt : t < hi) :
    connectedComponentIn {u : ℝ | (s, u) ∈ P} t ⊆ Iio hi := by
  intro u hu
  rw [mem_Iio]
  by_contra hle
  push_neg at hle
  have hord : (connectedComponentIn {u : ℝ | (s, u) ∈ P} t).OrdConnected :=
    isPreconnected_connectedComponentIn.ordConnected
  have hi_in : hi ∈ connectedComponentIn {u : ℝ | (s, u) ∈ P} t :=
    (hord.out (mem_connectedComponentIn ht) hu) ⟨le_of_lt hlt, hle⟩
  exact hnotmem ((connectedComponentIn_subset {u : ℝ | (s, u) ∈ P} t) hi_in)

/-- **A fibre-component through a point above `lo` stays above `lo`** (the dual statement). -/
theorem component_subset_Ioi_of_notMem {P : Set (ℝ × ℝ)} {s lo t : ℝ}
    (hnotmem : (s, lo) ∉ P) (ht : (s, t) ∈ P) (hlt : lo < t) :
    connectedComponentIn {u : ℝ | (s, u) ∈ P} t ⊆ Ioi lo := by
  intro u hu
  rw [mem_Ioi]
  by_contra hle
  push_neg at hle
  have hord : (connectedComponentIn {u : ℝ | (s, u) ∈ P} t).OrdConnected :=
    isPreconnected_connectedComponentIn.ordConnected
  have lo_in : lo ∈ connectedComponentIn {u : ℝ | (s, u) ∈ P} t :=
    (hord.out hu (mem_connectedComponentIn ht)) ⟨hle, le_of_lt hlt⟩
  exact hnotmem ((connectedComponentIn_subset {u : ℝ | (s, u) ∈ P} t) lo_in)

/-- **The canonical piece below `τ` lies below `τ`.**  For the crux's data, `(s,τ) ∉ VA ∩ VB`
(because `H (s, τ s) ∉ VA`), so the component of `P ∩ Q` through a point strictly below `τ` is
contained in `(-∞, τ)`. -/
theorem component_below_tau_subset {P Q : Set (ℝ × ℝ)} {s τ : ℝ} (hnotP : (s, τ) ∉ P) {t : ℝ}
    (ht : (s, t) ∈ P ∩ Q) (htτ : t < τ) :
    connectedComponentIn {u : ℝ | (s, u) ∈ P ∩ Q} t ⊆ Iio τ :=
  component_subset_Iio_of_notMem (P := P ∩ Q) (fun h => hnotP h.1) ht htτ

/-- **The canonical piece above `σ` lies above `σ`** (the dual). -/
theorem component_above_sigma_subset {P Q : Set (ℝ × ℝ)} {s σ : ℝ} (hnotQ : (s, σ) ∉ Q) {t : ℝ}
    (ht : (s, t) ∈ P ∩ Q) (hσt : σ < t) :
    connectedComponentIn {u : ℝ | (s, u) ∈ P ∩ Q} t ⊆ Ioi σ :=
  component_subset_Ioi_of_notMem (P := P ∩ Q) (fun h => hnotQ h.2) ht hσt

/-- **First local instance of the `τ < σ` regime: the two canonical pieces are distinct components.**

At a fibre where `τ s < σ s`, any point of `P ∩ Q` strictly below `τ s` and any point of `P ∩ Q`
strictly above `σ s` lie in *different* components of the fibre: if they were in the same one, that
component — being connected, hence an interval — would contain `τ s`, contradicting `(s,τ s) ∉ P`. -/
theorem tau_lt_sigma_components_ne {P Q : Set (ℝ × ℝ)} {s τ σ : ℝ}
    (hnotP : (s, τ) ∉ P) (hlt : τ < σ)
    {t t' : ℝ} (ht : (s, t) ∈ P ∩ Q) (ht' : (s, t') ∈ P ∩ Q) (htτ : t < τ) (hσt' : σ < t') :
    t' ∉ connectedComponentIn {u : ℝ | (s, u) ∈ P ∩ Q} t := by
  intro hmem
  have hord : (connectedComponentIn {u : ℝ | (s, u) ∈ P ∩ Q} t).OrdConnected :=
    isPreconnected_connectedComponentIn.ordConnected
  have hτ_in : τ ∈ connectedComponentIn {u : ℝ | (s, u) ∈ P ∩ Q} t :=
    (hord.out (mem_connectedComponentIn ht) hmem) ⟨le_of_lt htτ, by linarith⟩
  exact hnotP ((connectedComponentIn_subset {u : ℝ | (s, u) ∈ P ∩ Q} t) hτ_in).1

/-! ### Obligation O, first sub-case: local persistence of the `τ`-piece

The first sub-case of (Obligation O): if, at a level `s`, the window `(t₀-ρ, t₀+ρ)` and the whole
half-open interval `[t₀, τ_s)` lie in the fibre `D_s`, and `τ_s` itself is *not* in `D_s`, then the
component of `t₀` in `D_s` already contains the entire interval `(t₀-ρ, τ_s)` and — because it
cannot contain `τ_s` — ends at `τ_s`.  So the piece through `t₀` *is* the canonical piece below
`τ_s`, and every point of the window belongs to it.  This is the fibre-level statement that
openness of the `τ`-piece family has to rest on; the only hypothesis that is not automatic is
`[t₀,τ_s) ⊆ D_s` ("no gap between `t₀` and the exit"), which is precisely the pinch condition. -/

/-- **Local persistence of the `τ`-piece at a single fibre.** -/
theorem tau_piece_persists_at {D : Set (ℝ × ℝ)} {s t₀ ρ τ_s : ℝ} (hρ : 0 < ρ)
    (hbox : Ioo (t₀ - ρ) (t₀ + ρ) ⊆ {u : ℝ | (s, u) ∈ D})
    (hIco : Ico t₀ τ_s ⊆ {u : ℝ | (s, u) ∈ D})
    (hend : (s, τ_s) ∉ D) (hlt : t₀ < τ_s) :
    ∀ t ∈ Ioo (t₀ - ρ) τ_s,
      t ∈ connectedComponentIn {u : ℝ | (s, u) ∈ D} t₀ ∧
      connectedComponentIn {u : ℝ | (s, u) ∈ D} t₀ ⊆ Iio τ_s := by
  have hsub : Ioo (t₀ - ρ) τ_s ⊆ {u : ℝ | (s, u) ∈ D} := by
    intro u hu
    rcases lt_or_ge u t₀ with hgt | hle
    · exact hbox ⟨hu.1, by linarith⟩
    · exact hIco ⟨hle, hu.2⟩
  have hpre : IsPreconnected (Ioo (t₀ - ρ) τ_s) :=
    (convex_Ioo (t₀ - ρ) τ_s).isPreconnected
  have hmem : t₀ ∈ Ioo (t₀ - ρ) τ_s := ⟨by linarith, hlt⟩
  have hcomp : Ioo (t₀ - ρ) τ_s ⊆ connectedComponentIn {u : ℝ | (s, u) ∈ D} t₀ :=
    hpre.subset_connectedComponentIn hmem hsub
  have hbound : connectedComponentIn {u : ℝ | (s, u) ∈ D} t₀ ⊆ Iio τ_s :=
    component_subset_Iio_of_notMem hend (hsub hmem) hlt
  intro t ht
  exact ⟨hcomp ht, hbound⟩

/-- **Local persistence of the `τ`-piece, sliding in `s`.**  Same as `tau_piece_persists_at`, but
with the two fibre conditions holding on a whole `s`-window: the piece through `t₀` is then the
canonical `τ`-piece for every `s` in the window, and the family of those pieces covers the union of
the windows `(t₀-ρ, τ s)`. -/
theorem tau_piece_persists_nhds {D : Set (ℝ × ℝ)} {s₀ t₀ ρ δ : ℝ} (hρ : 0 < ρ) {τ : ℝ → ℝ}
    (hbox : Ioo (s₀ - δ) (s₀ + δ) ×ˢ Ioo (t₀ - ρ) (t₀ + ρ) ⊆ D)
    (hIco : ∀ s ∈ Ioo (s₀ - δ) (s₀ + δ), Ico t₀ (τ s) ⊆ {u : ℝ | (s, u) ∈ D})
    (hend : ∀ s ∈ Ioo (s₀ - δ) (s₀ + δ), (s, τ s) ∉ D)
    (hlt : ∀ s ∈ Ioo (s₀ - δ) (s₀ + δ), t₀ < τ s) :
    ∀ s ∈ Ioo (s₀ - δ) (s₀ + δ), ∀ t ∈ Ioo (t₀ - ρ) (τ s),
      t ∈ connectedComponentIn {u : ℝ | (s, u) ∈ D} t₀ ∧
      connectedComponentIn {u : ℝ | (s, u) ∈ D} t₀ ⊆ Iio (τ s) := by
  intro s hs
  have hboxfib : Ioo (t₀ - ρ) (t₀ + ρ) ⊆ {u : ℝ | (s, u) ∈ D} := by
    intro u hu
    exact hbox ⟨hs, hu⟩
  exact tau_piece_persists_at hρ hboxfib (hIco s hs) (hend s hs) (hlt s hs)

/-! ### (O′) first half: a fixed sub-segment below the exit persists

The pinch-free condition `[t₀, τ s) ⊆ D_s` is equivalent, by compactness of the sub-segments
`[t₀, t']` with `t' < τ s₀`, to the following: *for every `t' < τ s₀` the closed segment `[t₀, t']`
persists on a whole `s`-window.*  One direction is the lemma below (the tube lemma applied to the
compact segment `{s₀} × [t₀,t']`, which lies in `D` by the no-pinch hypothesis at `s₀`); the other
direction is immediate.  So (O′) is reduced to the single remaining question of how the fibre behaves
*just below the exit* as `s` varies — which is where `τ`'s up-jumps (the only discontinuities `τ` can
have, being lower semicontinuous) live. -/

/-- **(O′) first half, single step.**  If the half-open interval `[t₀, τ s₀)` lies in the fibre
`D_{s₀}` and `t' < τ s₀`, then the closed segment `[t₀, t']` lies in the fibre `D_s` for all `s` in a
whole neighbourhood of `s₀`.

Equivalently: the "bad set" `{(s,t) : t₀ ≤ t < τ s, (s,t) ∉ D}` misses the compact segment
`{s₀} × [t₀,t']`, and the tube lemma turns that into a `δ`-window. -/
theorem ico_persists_of_noPinch {D : Set (ℝ × ℝ)} (hD : IsOpen D) {s₀ t₀ τ_s₀ t' : ℝ}
    (hnoPinch : Ico t₀ τ_s₀ ⊆ {u : ℝ | (s₀, u) ∈ D}) (hlt : t₀ < t') (ht' : t' < τ_s₀) :
    ∃ δ > 0, ∀ s : ℝ, |s - s₀| < δ → Ico t₀ t' ⊆ {u : ℝ | (s, u) ∈ D} := by
  obtain ⟨δ, hδ, hbox⟩ := exists_tube_of_isOpen hD (le_of_lt hlt)
    (fun t ht => hnoPinch ⟨ht.1, lt_of_le_of_lt ht.2 ht'⟩)
  refine ⟨δ, hδ, fun s hs u hu => hbox ⟨?_, ⟨hu.1, le_of_lt hu.2⟩⟩⟩
  obtain ⟨h1, h2⟩ := abs_lt.mp hs
  exact ⟨by linarith, by linarith⟩

/-! ### The moving top window, and the uniform exit room

Two lemmas that turn (O′) into a single quantitative inequality.

1. `moving_window_subset_of_exit_room` — the *moving top window* `(τ s₀ - η, τ s)` lies in the fibre
   `D_s = A_s ∩ B_s` as soon as (i) `[0, τ s) ⊆ A_s` (true by definition of `τ` as the first exit)
   and (ii) the exit room of `B_s` reaches down to the fixed level: `τ s - ε ≤ τ s₀ - η`.  So the
   whole remaining content of (O′) is the inequality `ε ≥ τ s - τ s₀ + η`.

2. `exists_uniform_exit_room` — the quantitative bound itself, *squeezed from the crux's own data*:
   the exit point `H (s₀, τ s₀)` lies in the open `B`, and `H` is continuous, so a fixed room around
   `(s₀, τ s₀)` is carried to all nearby `s`; continuity of `τ` at `s₀` then keeps the window
   `(τ s - ε, τ s)` inside that fixed room.  No use of the pinch is made. -/

/-- **The moving top window is in the fibre once the exit room reaches down to `τ s₀ - η`.** -/
theorem moving_window_subset_of_exit_room {A B : Set ℝ} {τs τs₀ η ε : ℝ}
    (hA : Ico 0 τs ⊆ A) (hroom : Ioo (τs - ε) τs ⊆ B) (h0 : 0 ≤ τs₀ - η)
    (hle : τs - ε ≤ τs₀ - η) :
    Ioo (τs₀ - η) τs ⊆ A ∩ B := by
  intro t ht
  refine ⟨hA ⟨le_trans h0 ht.1.le, ht.2⟩, hroom ⟨lt_of_le_of_lt hle ht.1, ht.2⟩⟩

/-- **Uniform exit room near `s₀`.**  If `H (s₀, τ s₀)` lies in the open set `B`, `H` is continuous,
and `τ` is continuous at `s₀`, then there are `ε, δ > 0` such that for every `s` with
`|s - s₀| < δ` the whole interval `(τ s - ε, τ s)` is mapped into `B` by `H (s, ·)`.

This is the quantitative lower bound on the exit room asked for by (O′): it is obtained by taking a
box in `B` around `(s₀, τ s₀)` and using continuity of `H` (in both variables) together with
continuity of `τ` at `s₀` to keep the window inside that box. -/
theorem exists_uniform_exit_room {B : Set (ℝ × ℝ)} (hB : IsOpen B) {H : ℝ × ℝ → ℝ × ℝ}
    (hHc : Continuous H) {s₀ τs₀ : ℝ} (hmem : H (s₀, τs₀) ∈ B) {τ : ℝ → ℝ}
    (hτc : ∀ e > 0, ∃ d > 0, ∀ s : ℝ, |s - s₀| < d → |τ s - τs₀| < e) :
    ∃ ε > 0, ∃ δ > 0, ∀ s : ℝ, |s - s₀| < δ →
      ∀ t : ℝ, τ s - ε < t → t < τ s → H (s, t) ∈ B := by
  have hP : IsOpen {q : ℝ × ℝ | H q ∈ B} := hB.preimage hHc
  have hmemP : (s₀, τs₀) ∈ {q : ℝ × ℝ | H q ∈ B} := hmem
  obtain ⟨r, hr, hbox⟩ := exists_box_of_isOpen_mem hP hmemP
  obtain ⟨d, hd, hτd⟩ := hτc (r / 2) (by linarith)
  refine ⟨r / 2, by linarith, min r d, lt_min hr hd, ?_⟩
  intro s hs t ht1 ht2
  have hs₁ : |s - s₀| < r := lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_left r d)) le_rfl
  have hs₂ : |s - s₀| < d := lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right r d)) le_rfl
  have ht₀ : |t - τs₀| < r := by
    have h1 : |t - τ s| < r / 2 := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    have h2 : |τ s - τs₀| < r / 2 := hτd s hs₂
    have h3 : |t - τs₀| ≤ |t - τ s| + |τ s - τs₀| := by
      have hid : t - τs₀ = (t - τ s) + (τ s - τs₀) := by ring
      rw [hid]
      exact abs_add_le _ _
    linarith
  obtain ⟨hsl, hsr⟩ := abs_lt.mp hs₁
  obtain ⟨htl, htr⟩ := abs_lt.mp ht₀
  exact hbox ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-! ### The assembly: `(O′)` holds at every continuity point of `τ`

All the inputs are now in place and the remaining content is arithmetic.  Given the crux's data

* `[0, τ s) ⊆ A_s` (by definition of `τ` as the first exit from `A`),
* the exit point `H (s₀, τ s₀) ∈ B` (so that `τ s₀ ∉ A_{s₀}` and the cover give membership in `B`),
* `t₀` in the `τ`-piece at `s₀`, i.e. `[t₀, τ s₀) ⊆ A_{s₀} ∩ B_{s₀}` and `t₀ < τ s₀`,
* continuity of `τ` at `s₀`,

the lemma below produces a `δ`-window on which `[t₀, τ s) ⊆ A_s ∩ B_s` — no pinch between `t₀` and
the exit, for all nearby `s`.  Feeding that plus the box around `(s₀,t₀)` into
`tau_piece_persists_at` turns it into the full `(O′)` statement (the component of `t₀` contains
`(t₀-ρ, τ s)` and ends at `τ s`), so this is the last non-trivial step before (O) in the
`τ < σ` regime.  The three quantitative inputs are `exists_uniform_exit_room` (the room `ε₀` at
nearby `s`), `ico_persists_of_noPinch` (the fixed segment `[t₀, τ s₀ - η]` persists), and the
continuity of `τ` at `s₀` (which keeps `τ s` within `ε₀/2` of `τ s₀`, making `τ s - ε₀ ≤ τ s₀ - η`). -/

/-- **(O′) minus the bookkeeping: no pinch between `t₀` and the exit, for nearby `s`.** -/
theorem ico_persists_of_continuous_exit {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    {H : ℝ × ℝ → ℝ × ℝ} (hHc : Continuous H) {τ : ℝ → ℝ}
    (hA : ∀ s : ℝ, Ico 0 (τ s) ⊆ {u : ℝ | H (s, u) ∈ VA})
    {s₀ t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hmemB : H (s₀, τ s₀) ∈ VB)
    (hnoPinch : Ico t₀ (τ s₀) ⊆ {u : ℝ | H (s₀, u) ∈ VA ∩ VB}) (hlt : t₀ < τ s₀)
    (hτc : ∀ e > 0, ∃ d > 0, ∀ s : ℝ, |s - s₀| < d → |τ s - τ s₀| < e) :
    ∃ δ > 0, ∀ s : ℝ, |s - s₀| < δ → Ico t₀ (τ s) ⊆ {u : ℝ | H (s, u) ∈ VA ∩ VB} := by
  obtain ⟨ε₀, hε₀, δr, hδr, hroom⟩ := exists_uniform_exit_room hVB hHc hmemB hτc
  set η : ℝ := min (ε₀ / 2) ((τ s₀ - t₀) / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηε : η ≤ ε₀ / 2 := min_le_left _ _
  have hηt : η ≤ (τ s₀ - t₀) / 2 := min_le_right _ _
  have ht't : t₀ < τ s₀ - η := by linarith
  have ht'τ : τ s₀ - η < τ s₀ := by linarith
  have hDopen : IsOpen {q : ℝ × ℝ | H q ∈ VA ∩ VB} := (hVA.inter hVB).preimage hHc
  obtain ⟨δp, hδp, hpersist⟩ := ico_persists_of_noPinch hDopen hnoPinch ht't ht'τ
  obtain ⟨δc, hδc, hcont⟩ := hτc (ε₀ / 2) (by linarith)
  refine ⟨min δp (min δc δr), lt_min hδp (lt_min hδc hδr), ?_⟩
  intro s hs u hu
  have hsp : |s - s₀| < δp :=
    lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_left δp (min δc δr))) le_rfl
  have hsc : |s - s₀| < δc :=
    lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right δp (min δc δr)))
      (min_le_left δc δr)) le_rfl
  have hsr : |s - s₀| < δr :=
    lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right δp (min δc δr)))
      (min_le_right δc δr)) le_rfl
  rcases lt_or_ge u (τ s₀ - η) with hcase | hcase
  · exact hpersist s hsp ⟨hu.1, hcase⟩
  · have hτs : |τ s - τ s₀| < ε₀ / 2 := hcont s hsc
    have hτs' : τ s - τ s₀ < ε₀ / 2 := (abs_lt.mp hτs).2
    have h0η : 0 ≤ τ s₀ - η := by linarith
    refine ⟨hA s ⟨le_trans h0η hcase, hu.2⟩, ?_⟩
    exact hroom s hsr u (by linarith) hu.2

/-! ### Up-jumps: the dichotomy, and the analogues of the assembly

`τ` is lower semicontinuous, so its only discontinuities are up-jumps.  The first lemma records the
precise content of that lower semicontinuity that the assembly uses: *`τ` stays above any level
strictly below `τ s₀` on a neighbourhood of `s₀`.*  The second is the up-jump analogue of
`ico_persists_of_continuous_exit`: the continuity of `τ` was used there for exactly one thing, the
*upper* bound `τ s ≤ τ s₀ + ε₀/2`, which produced `τ s - ε₀ ≤ τ s₀ - η`.  Replacing that by an
arbitrary one-sided bound `τ s ≤ τb` (true past an up-jump as well) leaves exactly one requirement —

  `τb - ε ≤ τ s₀ - η`, i.e. the exit room reaches down to the fixed interior level,

which for a function bounded near `s₀` is the inequality `τb - ε < (τ s₀ + t₀)/2`.  So of the
available inputs, `ico_persists_of_noPinch` and `moving_window_subset_of_exit_room` carry over
unchanged, the corridor lemma belongs to the other regime, and **exactly one new room lemma is
needed**: a lower bound for the exit room at the *jumped* heights (the existing
`exists_uniform_exit_room` tracks the moving exit point and therefore needs continuity of `τ`). -/

/-- **The up-jump dichotomy.**  Lower semicontinuity of `τ` at `s₀` means precisely that `τ` cannot
jump *down*: for every level strictly below `τ s₀`, it stays above that level on a neighbourhood. -/
theorem lsc_stays_above {τ : ℝ → ℝ} {s₀ τstar : ℝ}
    (hτc : ∀ e > 0, ∃ d > 0, ∀ s : ℝ, |s - s₀| < d → τ s > τ s₀ - e)
    (hstar : τstar < τ s₀) :
    ∃ δ > 0, ∀ s : ℝ, |s - s₀| < δ → τstar < τ s := by
  obtain ⟨d, hd, h⟩ := hτc (τ s₀ - τstar) (by linarith)
  exact ⟨d, hd, fun s hs => by have := h s hs; linarith⟩

/-- **The up-jump analogue of the assembly.**  With the room at nearby levels and a one-sided bound
`τ s ≤ τb` as hypotheses (both of which hold past an up-jump, whereas `exists_uniform_exit_room`
delivers them only under continuity of `τ`), the pinch-free condition `[t₀, τ s) ⊆ VA_s ∩ VB_s`
follows on a neighbourhood, provided the room reaches below the fixed interior level:
`τb - ε < (τ s₀ + t₀)/2`. -/
theorem ico_persists_of_bounded_exit {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) {H : ℝ × ℝ → ℝ × ℝ} (hHc : Continuous H)
    {τ : ℝ → ℝ} (hA : ∀ s : ℝ, Ico 0 (τ s) ⊆ {u : ℝ | H (s, u) ∈ VA})
    {s₀ t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hmemB : H (s₀, τ s₀) ∈ VB)
    (hnoPinch : Ico t₀ (τ s₀) ⊆ {u : ℝ | H (s₀, u) ∈ VA ∩ VB}) (hlt : t₀ < τ s₀)
    {τb ε δr : ℝ} (hε : 0 < ε) (hτb : t₀ < τb) (hδr : 0 < δr)
    (hroom : ∀ s : ℝ, |s - s₀| < δr → ∀ t : ℝ, τ s - ε < t → t < τ s → H (s, t) ∈ VB)
    (hτhi : ∀ s : ℝ, |s - s₀| < δr → τ s ≤ τb)
    (hbig : τb - ε < (τ s₀ + t₀) / 2) :
    ∃ δ > 0, ∀ s : ℝ, |s - s₀| < δ → Ico t₀ (τ s) ⊆ {u : ℝ | H (s, u) ∈ VA ∩ VB} := by
  set η : ℝ := min (ε / 2) ((τ s₀ - t₀) / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηt : η ≤ (τ s₀ - t₀) / 2 := min_le_right _ _
  have hτbε : τb - ε < τ s₀ - η := by
    have hle : (τ s₀ + t₀) / 2 ≤ τ s₀ - η := by linarith
    linarith
  have hτpos : 0 < τ s₀ - η := by linarith
  have ht't : t₀ < τ s₀ - η := by linarith
  have ht'τ : τ s₀ - η < τ s₀ := by linarith
  have hDopen : IsOpen {q : ℝ × ℝ | H q ∈ VA ∩ VB} := (hVA.inter hVB).preimage hHc
  obtain ⟨δp, hδp, hpersist⟩ := ico_persists_of_noPinch hDopen hnoPinch ht't ht'τ
  refine ⟨min δp δr, lt_min hδp hδr, ?_⟩
  intro s hs u hu
  have hsp : |s - s₀| < δp := lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_left δp δr)) le_rfl
  have hsr : |s - s₀| < δr := lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right δp δr)) le_rfl
  rcases lt_or_ge u (τ s₀ - η) with hcase | hcase
  · exact hpersist s hsp ⟨hu.1, hcase⟩
  · refine ⟨hA s ⟨le_trans (le_of_lt hτpos) hcase, hu.2⟩, ?_⟩
    exact hroom s hsr u (by linarith [hτhi s hsr, hτbε]) hu.2

/-! ### The missing room lemma: the exit room past a jump, from the one-sided limit

`exists_uniform_exit_room` needs continuity of `τ` because it tracks the moving exit point
`(s, τ s)`.  Past an up-jump the exit points no longer converge to `(s₀, τ s₀)` — they converge to
`(s₀, τ⁻)`, where `τ⁻` is the one-sided limit of `τ`, which lies *strictly inside* the `τ`-piece at
`s₀` and hence is again in `VB` (by `Ico t₀ (τ s₀) ⊆ VA ∩ VB`).  The same ball-and-box argument then
runs verbatim, with the one-sided limit replacing continuity:

  the box in the open set `H⁻¹ VB` around the *limit point* `(s₀, τ⁻)` absorbs the jumped windows
  `(τ s - ε, τ s)`, because `|t - τ⁻| ≤ |t - τ s| + |τ s - τ⁻| < ε + r/2` for `s` close to `s₀`.

This is the single new room lemma identified at the end of the up-jump analysis. -/

/-- **Exit room from a one-sided limit.**  Suppose `τ` has the one-sided limit `τm` as `s → s₀⁻`
(`0 < s₀ - s`), that the limit point satisfies `H (s₀, τm) ∈ VB`, and that `VB` is open with `H`
continuous.  Then there are `ε, δ > 0` such that on the left of `s₀` the whole window
`(τ s - ε, τ s)` is mapped into `VB`. -/
theorem exists_exit_room_of_tendsto {VB : Set (ℝ × ℝ)} (hVB : IsOpen VB)
    {H : ℝ × ℝ → ℝ × ℝ} (hHc : Continuous H) {s₀ τm : ℝ} (hmem : H (s₀, τm) ∈ VB)
    {τ : ℝ → ℝ}
    (hlim : ∀ e > 0, ∃ d > 0, ∀ s : ℝ, 0 < s₀ - s → s₀ - s < d → |τ s - τm| < e) :
    ∃ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s₀ - s → s₀ - s < δ →
      ∀ t : ℝ, τ s - ε < t → t < τ s → H (s, t) ∈ VB := by
  have hP : IsOpen {q : ℝ × ℝ | H q ∈ VB} := hVB.preimage hHc
  have hmemP : (s₀, τm) ∈ {q : ℝ × ℝ | H q ∈ VB} := hmem
  obtain ⟨r, hr, hbox⟩ := exists_box_of_isOpen_mem hP hmemP
  obtain ⟨d, hd, hτd⟩ := hlim (r / 2) (by linarith)
  refine ⟨r / 2, by linarith, min r d, lt_min hr hd, ?_⟩
  intro s hspos hs t ht1 ht2
  have hs₁ : |s - s₀| < r := by
    rw [abs_lt]
    refine ⟨by linarith [hspos, lt_of_lt_of_le hs (min_le_left r d)], ?_⟩
    linarith [lt_of_lt_of_le hs (min_le_left r d)]
  have hs₂ : s₀ - s < d := lt_of_lt_of_le hs (min_le_right r d)
  have ht₀ : |t - τm| < r := by
    have h1 : |t - τ s| < r / 2 := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    have h2 : |τ s - τm| < r / 2 := hτd s hspos hs₂
    have h3 : |t - τm| ≤ |t - τ s| + |τ s - τm| := by
      have hid : t - τm = (t - τ s) + (τ s - τm) := by ring
      rw [hid]
      exact abs_add_le _ _
    linarith
  obtain ⟨hsl, hsr⟩ := abs_lt.mp hs₁
  obtain ⟨htl, htr⟩ := abs_lt.mp ht₀
  exact hbox ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-! ### The ceiling past an up-jump, and the up-jump persistence lemma

The last input for the up-jump case of (O): past an up-jump, `τ` on the low side is bounded above by
its one-sided limit plus anything — the ceiling `τb` consumed by `ico_persists_of_bounded_exit`.

With that ceiling in hand, the up-jump persistence lemma runs the *three-interval covering*
argument: at a level `s` on the low side,

* the box around `(s₀,t₀)` (openness of `D = VA ∩ VB`) covers `(t₀-ρ, t₀+ρ)`;
* `ico_persists_of_noPinch` covers the compact segment `[t₀, τ* - η]` for a fixed interior level
  `τ* ∈ (t₀, τ s₀)` (chosen once and for all, e.g. `τ* = (τ s₀ + t₀)/2`, which lies in `D`'s fibre at
  `s₀` by the no-pinch hypothesis);
* the box around the *same* interior point `(s₀, τ*)` covers `(τ* - ρ', τ* + ρ')`, and
* the limit room `(τ s - ε, τ s)` covers the moving top.

The three overlap as soon as `η ≤ ρ'` and `τ s - ε ≤ τ* + ρ'`; the second is arranged by taking the
room `ε` and the limit's accuracy `ε'` small relative to `ρ'` (which itself may be taken close to
`(τ s₀ - t₀)/2`, the distance from `τ*` to the boundary of the piece).  Hence `[t₀, τ s) ⊆ D_s` for
all `s` on a left neighbourhood of `s₀`. -/

/-- **The ceiling past an up-jump.**  If `τ` tends to `τm` from the left at `s₀`, then on a left
neighbourhood `τ` is bounded above by `τm + e` for any prescribed `e > 0`.  This is exactly the
one-sided bound `τb` that `ico_persists_of_bounded_exit` consumes. -/
theorem exists_upper_bound_of_tendsto {τ : ℝ → ℝ} {s₀ τm : ℝ}
    (hlim : ∀ e > 0, ∃ d > 0, ∀ s : ℝ, 0 < s₀ - s → s₀ - s < d → |τ s - τm| < e) {e : ℝ}
    (he : 0 < e) :
    ∃ τb : ℝ, ∃ δ > 0, ∀ s : ℝ, 0 < s₀ - s → s₀ - s < δ → τ s ≤ τb := by
  obtain ⟨d, hd, hτd⟩ := hlim e he
  exact ⟨τm + e, d, hd, fun s h1 h2 =>
    le_of_lt (by have h := (abs_lt.mp (hτd s h1 h2)).2; linarith)⟩

/-- **The up-jump persistence lemma.**  On the low side of an up-jump of `τ`, the pinch-free
condition `[t₀, τ s) ⊆ VA_s ∩ VB_s` holds on a neighbourhood, given the one-sided limit `τm` of `τ`
at `s₀` and the two room quantities: the limit room `ε₁` (from `exists_exit_room_of_tendsto`) and the
interior box radius `ρ'` around `(s₀, τ*)`.  The covering is the union of the three intervals of the
docstring; the hypotheses list the overlap conditions that make it work. -/
theorem ico_persists_of_upjump {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) {H : ℝ × ℝ → ℝ × ℝ} (hHc : Continuous H)
    {τ : ℝ → ℝ} (hA : ∀ s : ℝ, Ico 0 (τ s) ⊆ {u : ℝ | H (s, u) ∈ VA})
    {s₀ t₀ τm τstar : ℝ} (ht₀ : 0 ≤ t₀)
    (hnoPinch : Ico t₀ (τ s₀) ⊆ {u : ℝ | H (s₀, u) ∈ VA ∩ VB})
    (htstar : t₀ < τstar) (hstar : τstar < τ s₀)
    {ε₁ ρ' η : ℝ} (hε₁ : 0 < ε₁) (hρ' : 0 < ρ')
    (hη : 0 < η) (hηρ : η ≤ ρ')
    -- the two room statements, on a common left neighbourhood of `s₀`
    {δr : ℝ} (hδr : 0 < δr)
    (hroom : ∀ s : ℝ, 0 < s₀ - s → s₀ - s < δr →
      ∀ t : ℝ, τ s - ε₁ < t → t < τ s → H (s, t) ∈ VB)
    (hbox' : Ioo (s₀ - δr) (s₀ + δr) ×ˢ Ioo (τstar - ρ') (τstar + ρ') ⊆
      {q : ℝ × ℝ | H q ∈ VA ∩ VB})
    -- the overlap condition at the top
    (htop : ∀ s : ℝ, 0 < s₀ - s → s₀ - s < δr → τ s - ε₁ < τstar + ρ') :
    ∃ δ > 0, ∀ s : ℝ, 0 < s₀ - s → s₀ - s < δ →
      Ico t₀ (τ s) ⊆ {u : ℝ | H (s, u) ∈ VA ∩ VB} := by
  have hDopen : IsOpen {q : ℝ × ℝ | H q ∈ VA ∩ VB} := (hVA.inter hVB).preimage hHc
  have hτstarmem : (s₀, τstar) ∈ {q : ℝ × ℝ | H q ∈ VA ∩ VB} :=
    hnoPinch ⟨le_of_lt htstar, hstar⟩
  obtain ⟨δp, hδp, hpersist⟩ := ico_persists_of_noPinch hDopen hnoPinch htstar hstar
  refine ⟨min δp δr, lt_min hδp hδr, ?_⟩
  intro s hs1 hs2 u hu
  have hsp : 0 < s₀ - s := hs1
  have hsδp : s₀ - s < δp := lt_of_lt_of_le hs2 (min_le_left δp δr)
  have hsδr : s₀ - s < δr := lt_of_lt_of_le hs2 (min_le_right δp δr)
  rcases lt_or_ge u τstar with hc | hc
  · exact hpersist s (by rw [abs_of_neg (by linarith : s - s₀ < 0)]; linarith) ⟨hu.1, hc⟩
  · by_cases hubox : u < τstar + ρ'
    · -- inside the interior box
      exact hbox' ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hubox⟩⟩
    · -- above the interior box: the limit room
      push_neg at hubox
      exact ⟨hA s ⟨le_trans (le_trans ht₀ htstar.le) hc, hu.2⟩,
        hroom s hsp hsδr u (by linarith [htop s hsp hsδr]) hu.2⟩

/-! ### The σ-side branch: the mirrors of the persistence and room lemmas

Inside a jump range of `τ` the τ-piece family is provably not lower semicontinuous, so the branch has
to be carried by the *other* end of the fibre — the piece above `σ`, whose fibre is `(σ s, β s)` and
which is anchored at `σ s` (because `σ s ∉ B_s` forces `H (s, σ s) ∈ VA`, so `σ s ∉ D_s`).  The
σ-side argument is the τ-side argument with

* `τ` ↦ `σ`, and the two ends of the fibre exchanged,
* `VB` ↦ `VA` (the set whose openness supplies the room: `H (s, σ s) ∈ VA` and `VA` is open),
* `Ico` ↦ `Ioc` (the interval now lies *above* the fixed level).

Two of the reusable pieces are mirror images of lemmas already proved; both are recorded here so the
σ-side assembly can be written as the mirror of `ico_persists_of_continuous_exit`.

What reuses *verbatim*: nothing.  `ico_persists_of_noPinch` and `exists_uniform_exit_room` are
one-sided statements (segment above the fixed level, window below the moving exit), so the σ-side
needs their strict mirrors rather than the lemmas themselves — but the proofs are the same tube lemma
and the same ball-and-box computation, with the interval and the window reflected. -/

/-- **Mirror of `ico_persists_of_noPinch`: a compact segment below a fixed level persists.**

If `(lo, t₀] ⊆ D_{s₀}` and `lo < t' < t₀`, then `[t', t₀] ⊆ D_s` for all `s` in a neighbourhood of
`s₀`.  (Same tube lemma, applied to the compact segment `{s₀} × [t', t₀]`.) -/
theorem icc_persists_below_of_noPinch {D : Set (ℝ × ℝ)} (hD : IsOpen D) {s₀ lo t₀ t' : ℝ}
    (hnoPinch : Ioc lo t₀ ⊆ {u : ℝ | (s₀, u) ∈ D}) (ht' : lo < t') (ht't : t' < t₀) :
    ∃ δ > 0, ∀ s : ℝ, |s - s₀| < δ → Icc t' t₀ ⊆ {u : ℝ | (s, u) ∈ D} := by
  obtain ⟨δ, hδ, hbox⟩ := exists_tube_of_isOpen hD (le_of_lt ht't)
    (fun t ht => hnoPinch ⟨lt_of_lt_of_le ht' ht.1, ht.2⟩)
  refine ⟨δ, hδ, fun s hs u hu => hbox ⟨?_, ⟨hu.1, hu.2⟩⟩⟩
  obtain ⟨h1, h2⟩ := abs_lt.mp hs
  exact ⟨by linarith, by linarith⟩

/-- **Mirror of `exists_uniform_exit_room`: a uniform room above `σ`, from continuity of `σ`.**

If `H (s₀, σ s₀) ∈ VA` with `VA` open, `H` is continuous and `σ` is continuous at `s₀`, then on a
neighbourhood the window `(σ s, σ s + ε)` is mapped into `VA`.  This is the σ-side counterpart of the
exit room: it supplies the points just *above* `σ`, exactly as `exists_uniform_exit_room` supplies the
points just below `τ`. -/
theorem exists_uniform_room_above {VA : Set (ℝ × ℝ)} (hVA : IsOpen VA) {H : ℝ × ℝ → ℝ × ℝ}
    (hHc : Continuous H) {s₀ σs₀ : ℝ} (hmem : H (s₀, σs₀) ∈ VA) {σ : ℝ → ℝ}
    (hσc : ∀ e > 0, ∃ d > 0, ∀ s : ℝ, |s - s₀| < d → |σ s - σs₀| < e) :
    ∃ ε > 0, ∃ δ > 0, ∀ s : ℝ, |s - s₀| < δ →
      ∀ t : ℝ, σ s < t → t < σ s + ε → H (s, t) ∈ VA := by
  have hP : IsOpen {q : ℝ × ℝ | H q ∈ VA} := hVA.preimage hHc
  have hmemP : (s₀, σs₀) ∈ {q : ℝ × ℝ | H q ∈ VA} := hmem
  obtain ⟨r, hr, hbox⟩ := exists_box_of_isOpen_mem hP hmemP
  obtain ⟨d, hd, hσd⟩ := hσc (r / 2) (by linarith)
  refine ⟨r / 2, by linarith, min r d, lt_min hr hd, ?_⟩
  intro s hs t ht1 ht2
  have hs₁ : |s - s₀| < r := lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_left r d)) le_rfl
  have hs₂ : |s - s₀| < d := lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right r d)) le_rfl
  have ht₀ : |t - σs₀| < r := by
    have h1 : |t - σ s| < r / 2 := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    have h2 : |σ s - σs₀| < r / 2 := hσd s hs₂
    have h3 : |t - σs₀| ≤ |t - σ s| + |σ s - σs₀| := by
      have hid : t - σs₀ = (t - σ s) + (σ s - σs₀) := by ring
      rw [hid]
      exact abs_add_le _ _
    linarith
  obtain ⟨hsl, hsr⟩ := abs_lt.mp hs₁
  obtain ⟨htl, htr⟩ := abs_lt.mp ht₀
  exact hbox ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **The σ-side assembly: the mirrored `ico_persists_of_continuous_exit`.**

The mirror of the τ-side assembly with `τ ↦ σ`, `VB ↦ VA` (the set whose openness supplies the room),
and `Ico ↦ Ioc`: given the half-segment above `σ` (`Ioc (σ s) 1 ⊆ VB`), the anchoring point
`H (s₀, σ s₀) ∈ VA`, the no-pinch interval `Ioc (σ s₀) t₀ ⊆ VA ∩ VB`, and continuity of `σ` at `s₀`,
the condition `(σ s, t₀] ⊆ VA_s ∩ VB_s` holds on a neighbourhood of `s₀`.

The covering is the mirror of the τ-side three-interval union: the compact segment
`[σ s₀ + η, t₀]` persists (`icc_persists_below_of_noPinch`), and the moving bottom window
`(σ s, σ s + ε₀)` is in the fibre (`exists_uniform_room_above` for the `VA` part, the half-segment
`Ioc (σ s) 1 ⊆ VB` for the `VB` part).  The two intervals overlap because continuity of `σ` keeps
`σ s ≥ σ s₀ - ε₀/2`, so `σ s + ε₀ ≥ σ s₀ + ε₀/2 ≥ σ s₀ + η`. -/
theorem ioc_persists_of_continuous_entry {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) {H : ℝ × ℝ → ℝ × ℝ} (hHc : Continuous H)
    {σ : ℝ → ℝ} (hB : ∀ s : ℝ, Ioc (σ s) 1 ⊆ {u : ℝ | H (s, u) ∈ VB})
    {s₀ t₀ : ℝ} (ht₀1 : t₀ ≤ 1) (hmemA : H (s₀, σ s₀) ∈ VA)
    (hnoPinch : Ioc (σ s₀) t₀ ⊆ {u : ℝ | H (s₀, u) ∈ VA ∩ VB}) (hlt : σ s₀ < t₀)
    (hσc : ∀ e > 0, ∃ d > 0, ∀ s : ℝ, |s - s₀| < d → |σ s - σ s₀| < e) :
    ∃ δ > 0, ∀ s : ℝ, |s - s₀| < δ → Ioc (σ s) t₀ ⊆ {u : ℝ | H (s, u) ∈ VA ∩ VB} := by
  obtain ⟨ε₀, hε₀, δr, hδr, hroom⟩ := exists_uniform_room_above hVA hHc hmemA hσc
  set η : ℝ := min (ε₀ / 2) ((t₀ - σ s₀) / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηε : η ≤ ε₀ / 2 := min_le_left _ _
  have hηt : η ≤ (t₀ - σ s₀) / 2 := min_le_right _ _
  have hlo_lt : σ s₀ < σ s₀ + η := by linarith
  have ht'_lt : σ s₀ + η < t₀ := by linarith
  have hDopen : IsOpen {q : ℝ × ℝ | H q ∈ VA ∩ VB} := (hVA.inter hVB).preimage hHc
  obtain ⟨δp, hδp, hpersist⟩ := icc_persists_below_of_noPinch hDopen hnoPinch hlo_lt ht'_lt
  obtain ⟨δc, hδc, hcont⟩ := hσc (ε₀ / 2) (by linarith)
  refine ⟨min δp (min δc δr), lt_min hδp (lt_min hδc hδr), ?_⟩
  intro s hs u hu
  have hsp : |s - s₀| < δp :=
    lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_left δp (min δc δr))) le_rfl
  have hsc : |s - s₀| < δc :=
    lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right δp (min δc δr)))
      (min_le_left δc δr)) le_rfl
  have hsr : |s - s₀| < δr :=
    lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right δp (min δc δr)))
      (min_le_right δc δr)) le_rfl
  rcases lt_or_ge u (σ s₀ + η) with hcase | hcase
  · -- the moving bottom window
    have hσs : |σ s - σ s₀| < ε₀ / 2 := hcont s hsc
    have hσs' : σ s₀ - σ s < ε₀ / 2 := by linarith [(abs_lt.mp hσs).1]
    refine ⟨hroom s hsr u hu.1 (by linarith), hB s ⟨hu.1, le_trans hu.2 ht₀1⟩⟩
  · exact hpersist s hsp ⟨hcase, hu.2⟩

/-! ### The σ-side up-jump arm

The mirror of the τ-side up-jump package.  `σ` is *upper* semicontinuous, so its jumps run *downward*
and the mirror is taken on the other side of `s₀` (`0 < s - s₀`), with the room now sitting *above*
`σ` and the bound now a *lower* bound for `σ`.  The two mirrors proved here are

* `exists_entry_room_of_tendsto` — the one-sided-limit form of the entry room `(σ s, σ s + ε) ⊆ VA_s`
  (mirror of `exists_exit_room_of_tendsto`, with `VA` in place of `VB`); the box is taken around the
  *limit point* `(s₀, σm)`, which lies strictly inside the σ-piece at `s₀` and hence in `VA`;
* `ioc_persists_of_bounded_entry` — the covering lemma (mirror of `ico_persists_of_bounded_exit`):
  with a one-sided *lower* bound `σa ≤ σ s` and the room reaching up to the fixed interior level
  `(σ s₀ + t₀)/2`, the condition `(σ s, t₀] ⊆ VA_s ∩ VB_s` holds on a neighbourhood.

and a third, `exists_lower_bound_of_tendsto`, supplies the floor `σa` consumed by the covering lemma
(the twin of `exists_upper_bound_of_tendsto`).  Everything reuses the σ-side continuity lemmas
(`ioc_persists_of_continuous_entry`, `icc_persists_below_of_noPinch`, `exists_uniform_room_above`)
and the τ-side up-jump lemmas only by reflection, exactly as in the τ-side arm. -/

/-- **Entry room from a one-sided limit (σ-side mirror of `exists_exit_room_of_tendsto`).** -/
theorem exists_entry_room_of_tendsto {VA : Set (ℝ × ℝ)} (hVA : IsOpen VA)
    {H : ℝ × ℝ → ℝ × ℝ} (hHc : Continuous H) {s₀ σm : ℝ} (hmem : H (s₀, σm) ∈ VA)
    {σ : ℝ → ℝ}
    (hlim : ∀ e > 0, ∃ d > 0, ∀ s : ℝ, 0 < s - s₀ → s - s₀ < d → |σ s - σm| < e) :
    ∃ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s - s₀ → s - s₀ < δ →
      ∀ t : ℝ, σ s < t → t < σ s + ε → H (s, t) ∈ VA := by
  have hP : IsOpen {q : ℝ × ℝ | H q ∈ VA} := hVA.preimage hHc
  have hmemP : (s₀, σm) ∈ {q : ℝ × ℝ | H q ∈ VA} := hmem
  obtain ⟨r, hr, hbox⟩ := exists_box_of_isOpen_mem hP hmemP
  obtain ⟨d, hd, hσd⟩ := hlim (r / 2) (by linarith)
  refine ⟨r / 2, by linarith, min r d, lt_min hr hd, ?_⟩
  intro s hspos hs t ht1 ht2
  have hs₁ : |s - s₀| < r := by
    rw [abs_of_pos hspos]
    exact lt_of_lt_of_le hs (min_le_left r d)
  have hs₂ : s - s₀ < d := lt_of_lt_of_le hs (min_le_right r d)
  have ht₀ : |t - σm| < r := by
    have h1 : |t - σ s| < r / 2 := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    have h2 : |σ s - σm| < r / 2 := hσd s hspos hs₂
    have h3 : |t - σm| ≤ |t - σ s| + |σ s - σm| := by
      have hid : t - σm = (t - σ s) + (σ s - σm) := by ring
      rw [hid]
      exact abs_add_le _ _
    linarith
  obtain ⟨hsl, hsr⟩ := abs_lt.mp hs₁
  obtain ⟨htl, htr⟩ := abs_lt.mp ht₀
  exact hbox ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **The σ-side covering at a down-jump (mirror of `ico_persists_of_bounded_exit`).** -/
theorem ioc_persists_of_bounded_entry {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) {H : ℝ × ℝ → ℝ × ℝ} (hHc : Continuous H)
    {σ : ℝ → ℝ} (hB : ∀ s : ℝ, Ioc (σ s) 1 ⊆ {u : ℝ | H (s, u) ∈ VB})
    {s₀ t₀ : ℝ} (ht₀1 : t₀ ≤ 1) (hmemA : H (s₀, σ s₀) ∈ VA)
    (hnoPinch : Ioc (σ s₀) t₀ ⊆ {u : ℝ | H (s₀, u) ∈ VA ∩ VB}) (hlt : σ s₀ < t₀)
    {σa ε δr : ℝ} (hε : 0 < ε) (hσa : σa < t₀) (hδr : 0 < δr)
    (hroomA : ∀ s : ℝ, |s - s₀| < δr → ∀ t : ℝ, σ s < t → t < σ s + ε → H (s, t) ∈ VA)
    (hσlo : ∀ s : ℝ, |s - s₀| < δr → σa ≤ σ s)
    (hbig : (σ s₀ + t₀) / 2 < σa + ε) :
    ∃ δ > 0, ∀ s : ℝ, |s - s₀| < δ → Ioc (σ s) t₀ ⊆ {u : ℝ | H (s, u) ∈ VA ∩ VB} := by
  set η : ℝ := min (ε / 2) ((t₀ - σ s₀) / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηt : η ≤ (t₀ - σ s₀) / 2 := min_le_right _ _
  have hroom_hi : σ s₀ + η < σa + ε := by
    have hle : σ s₀ + η ≤ (σ s₀ + t₀) / 2 := by linarith
    linarith
  have hlo_lt : σ s₀ < σ s₀ + η := by linarith
  have ht'_lt : σ s₀ + η < t₀ := by linarith
  have hDopen : IsOpen {q : ℝ × ℝ | H q ∈ VA ∩ VB} := (hVA.inter hVB).preimage hHc
  obtain ⟨δp, hδp, hpersist⟩ := icc_persists_below_of_noPinch hDopen hnoPinch hlo_lt ht'_lt
  refine ⟨min δp δr, lt_min hδp hδr, ?_⟩
  intro s hs u hu
  have hsp : |s - s₀| < δp := lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_left δp δr)) le_rfl
  have hsr : |s - s₀| < δr := lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right δp δr)) le_rfl
  rcases lt_or_ge u (σ s₀ + η) with hcase | hcase
  · refine ⟨hroomA s hsr u hu.1 (by linarith [hσlo s hsr, hroom_hi]), ?_⟩
    exact hB s ⟨hu.1, le_trans hu.2 ht₀1⟩
  · exact hpersist s hsp ⟨hcase, hu.2⟩

/-- **The floor past a down-jump: the σ-side twin of `exists_upper_bound_of_tendsto`.**

If `σ` tends to `σm` from the right at `s₀` (the side on which `σ` has already dropped), then on a
right-neighbourhood it is bounded *below* by `σm - e` for any prescribed `e > 0`.  This is the
one-sided bound `σa` that `ioc_persists_of_bounded_entry` consumes, and — exactly as in the τ-side
case — it is all the bound that is forced: past a down-jump of the upper semicontinuous `σ` no
larger floor is available, which is why the inequality `(σ s₀ + t₀)/2 < σa + ε` is a hypothesis of the
covering lemma rather than a derived bound.

Twin row of the table: `exists_upper_bound_of_tendsto` (τ, lsc, ceiling `τb = τm + e`, side
`0 < s₀ - s`) ↔ `exists_lower_bound_of_tendsto` (σ, usc, floor `σa = σm - e`, side `0 < s - s₀`). -/
theorem exists_lower_bound_of_tendsto {σ : ℝ → ℝ} {s₀ σm : ℝ}
    (hlim : ∀ e > 0, ∃ d > 0, ∀ s : ℝ, 0 < s - s₀ → s - s₀ < d → |σ s - σm| < e) {e : ℝ}
    (he : 0 < e) :
    ∃ σa : ℝ, ∃ δ > 0, ∀ s : ℝ, 0 < s - s₀ → s - s₀ < δ → σa ≤ σ s := by
  obtain ⟨d, hd, hσd⟩ := hlim e he
  exact ⟨σm - e, d, hd, fun s h1 h2 =>
    le_of_lt (by have h := (abs_lt.mp (hσd s h1 h2)).1; linarith)⟩

/-! ### The seam extension of a twisted-periodic `H`

`cylinder_selection` supplies `H` only on the cylinder, twisted periodically at the seam:
`H (1,t) = T (H (0,t))`.  Every lemma of the selection table, on the other hand, is a statement about
a `T`-equivariant configuration on all of `ℝ`.  This section builds the bridge:

  `H̃ (s,t) := Tz ⌊s⌋ (H (s - ⌊s⌋, t))`, where `Tz j q := (q.1 + j*p, q.2)` is the integral translate,

which (i) agrees with `H` on `[0,1]`, (ii) is fully `T`-equivariant, `H̃ (s+1,t) = T (H̃ (s,t))` —
*this is the seam induction*: at the seam `s ∈ ℤ` the value computed from the left uses
`H (1,·) = T (H (0,·))` and matches the value computed from the right — and (iii) is continuous,
because on each closed slab `Icc j (j+1)` the formula `Tz j ∘ H (· - j, ·)` is continuous and the two
slab formulas agree at the shared endpoints (again by `hHper`); the slabs cover `ℝ` and overlap.

*Lean status: the integer translates `Tz`, the extension `Htilde` itself, and the translate calculus
(`Tz_zero`, `Tmap_Tz`, `Tz_Tmap`, `Tz_add`) are proved.  The half-open slab formula
(`Htilde (s,t) = Tz ⌊s⌋ (H (s - ⌊s⌋, t))` for `s ∈ Ico j (j+1)`), the seam identity
`Htilde (s+1,t) = T (Htilde (s,t))`, the closed-slab form, and continuity are the immediate next
steps — the last three all reduce to the same endpoint computation at `s = j+1`, which is `hHper`.*  The closed-slab form of the formula,
`H̃ (s,t) = Tz j (H (s - j, t))` for `s ∈ Icc j (j+1)` — which is what makes continuity on each slab
immediate and hence continuity on `ℝ` (the slabs cover `ℝ` and overlap) — is the next step; the
endpoint case `s = j+1` is the only content, and it is again `hHper`.  Items (i) and (ii) are proved
below (`Htilde_eq_of_mem_Ico`, `Htilde_add_one`). -/

/-- The integral translate `q ↦ (q.1 + j*p, q.2)`. -/
def Tz (p : ℝ) (j : ℤ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1 + j * p, q.2)

@[simp] lemma Tz_zero (p : ℝ) (q : ℝ × ℝ) : Tz p 0 q = q := by
  ext <;> simp [Tz]

/-- **The `T`-equivariant extension of a twisted-periodic `H`.**  On the slab `[j, j+1)` it is the
`j`-translate of `H` shifted by `j`; the seam identity `H (1,·) = T (H (0,·))` is what will make it
well defined and continuous across the integers. -/
noncomputable def Htilde (p : ℝ) (H : ℝ × ℝ → ℝ × ℝ) (st : ℝ × ℝ) : ℝ × ℝ :=
  Tz p ⌊st.1⌋ (H (st.1 - (⌊st.1⌋ : ℤ), st.2))

lemma Tmap_Tz (p : ℝ) (j : ℤ) (q : ℝ × ℝ) : Tmap p (Tz p j q) = Tz p (j + 1) q := by
  ext <;> simp only [Tz, Tmap] <;> push_cast <;> ring

lemma Tz_Tmap (p : ℝ) (j : ℤ) (q : ℝ × ℝ) : Tz p j (Tmap p q) = Tmap p (Tz p j q) := by
  ext <;> simp only [Tz, Tmap] <;> push_cast <;> ring

lemma Tz_add (p : ℝ) (j k : ℤ) (q : ℝ × ℝ) : Tz p (j + k) q = Tz p j (Tz p k q) := by
  ext <;> simp only [Tz] <;> push_cast <;> ring

/-- **The slab formula on a half-open slab.**  On `Ico j (j+1)` the floor is `j`, so the extension
is literally the `j`-translate of `H` shifted by `j`. -/
lemma Htilde_eq_of_mem_Ico {p : ℝ} {H : ℝ × ℝ → ℝ × ℝ} {j : ℤ} {s t : ℝ}
    (hs : s ∈ Ico (j : ℝ) ((j : ℝ) + 1)) :
    Htilde p H (s, t) = Tz p j (H (s - (j : ℝ), t)) := by
  have hfloor : ⌊s⌋ = j := Int.floor_eq_on_Ico j s hs
  simp only [Htilde, hfloor]

/-- **The seam identity: `H̃` is fully `T`-equivariant.**  This is the endpoint computation: the
argument of `H` is unchanged when `s ↦ s+1` (both floors shift), and `Tz (j+1) = T ∘ Tz j`. -/
lemma Htilde_add_one {p : ℝ} {H : ℝ × ℝ → ℝ × ℝ}
    (hHper : ∀ t : ℝ, H (1, t) = Tmap p (H (0, t))) (s t : ℝ) :
    Htilde p H (s + 1, t) = Tmap p (Htilde p H (s, t)) := by
  have hfloor : ⌊s + 1⌋ = ⌊s⌋ + 1 := Int.floor_add_one s
  have harg : (s + 1) - ((⌊s + 1⌋ : ℤ) : ℝ) = s - ((⌊s⌋ : ℤ) : ℝ) := by
    rw [hfloor]; push_cast; ring
  simp only [Htilde]
  rw [harg, hfloor]
  rw [← Tmap_Tz]

/-- **The closed-slab form.**  Extends the slab formula to `Icc j (j+1)`: at the right endpoint
`s = j+1` the value computed from the right is `Tz (j+1) (H (0,t))`, and the value computed from the
left is `Tz j (H (1,t)) = Tz j (T (H (0,t))) = T (Tz j (H (0,t))) = Tz (j+1) (H (0,t))` by `hHper`,
`Tz_Tmap` and `Tmap_Tz`.  This is the *only* place `hHper` is needed in the extension. -/
lemma Htilde_eq_on_Icc {p : ℝ} {H : ℝ × ℝ → ℝ × ℝ}
    (hHper : ∀ t : ℝ, H (1, t) = Tmap p (H (0, t))) {j : ℤ} {s t : ℝ}
    (hs : s ∈ Icc (j : ℝ) ((j : ℝ) + 1)) :
    Htilde p H (s, t) = Tz p j (H (s - (j : ℝ), t)) := by
  rcases lt_or_ge s ((j : ℝ) + 1) with h | h
  · exact Htilde_eq_of_mem_Ico ⟨hs.1, h⟩
  · have hs1 : s = (j : ℝ) + 1 := le_antisymm hs.2 h
    subst hs1
    have hfloor : ⌊(j : ℝ) + 1⌋ = j + 1 := by
      rw [show ((j : ℝ) + 1) = ((j + 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
    have hargL : (j : ℝ) + 1 - (((j : ℤ) + 1 : ℤ) : ℝ) = 0 := by push_cast; ring
    have hargR : (j : ℝ) + 1 - (j : ℝ) = 1 := by ring
    simp only [Htilde, hfloor, hargL, hargR]
    rw [hHper, Tz_Tmap, ← Tmap_Tz]

/-- Integral translates are continuous. -/
lemma continuous_Tz (p : ℝ) (j : ℤ) : Continuous (Tz p j) := by
  show Continuous fun q : ℝ × ℝ => (q.1 + (j : ℝ) * p, q.2)
  fun_prop

/-- **Continuity of `H̃` on a closed slab.**  On `Icc j (j+1) × univ` the extension equals the
continuous function `Tz j ∘ H (· - j, ·)` (closed-slab form), so continuity there is automatic;
gluing over the slabs (which cover `ℝ` and overlap on the integers, where the two slab formulas agree
by the closed-slab form) gives continuity on `ℝ`. -/
lemma continuousOn_Htilde_Icc {p : ℝ} {H : ℝ × ℝ → ℝ × ℝ} (hHc : Continuous H)
    (hHper : ∀ t : ℝ, H (1, t) = Tmap p (H (0, t))) {j : ℤ} :
    ContinuousOn (fun st : ℝ × ℝ => Htilde p H st)
      (Icc (j : ℝ) ((j : ℝ) + 1) ×ˢ (univ : Set ℝ)) := by
  have hinner : Continuous fun st : ℝ × ℝ => (st.1 - (j : ℝ), st.2) :=
    (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hcont : Continuous fun st : ℝ × ℝ => Tz p j (H (st.1 - (j : ℝ), st.2)) :=
    (continuous_Tz p j).comp (hHc.comp hinner)
  refine hcont.continuousOn.congr ?_
  rintro ⟨s, t⟩ hs
  exact Htilde_eq_on_Icc hHper ⟨hs.1.1, hs.1.2⟩

/-- **Continuity of the extension.**  The three closed slabs around `⌊st.1⌋` are glued with
`ContinuousOn.union_of_isClosed` (each step's sets named), the union contains the open box
`Ioo (j-1) (j+2) × univ` around `st`, and slab agreement at the shared endpoints is the closed-slab
form. -/
theorem continuous_Htilde {p : ℝ} {H : ℝ × ℝ → ℝ × ℝ} (hHc : Continuous H)
    (hHper : ∀ t : ℝ, H (1, t) = Tmap p (H (0, t))) :
    Continuous (fun st : ℝ × ℝ => Htilde p H st) := by
  rw [continuous_iff_continuousAt]
  intro st
  set j : ℤ := ⌊st.1⌋ with hj
  have hJn : (((j - 1 : ℤ)) : ℝ) = (j : ℝ) - 1 := by push_cast; ring
  have hJp : (((j + 1 : ℤ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  have h1 := continuousOn_Htilde_Icc hHc hHper (j := j - 1)
  have h2 := continuousOn_Htilde_Icc hHc hHper (j := j)
  have h3 := continuousOn_Htilde_Icc hHc hHper (j := j + 1)
  have hs1 : IsClosed (Icc (((j - 1 : ℤ)) : ℝ) ((((j - 1 : ℤ)) : ℝ) + 1) ×ˢ (univ : Set ℝ)) :=
    isClosed_Icc.prod isClosed_univ
  have hs2 : IsClosed (Icc ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) ×ˢ (univ : Set ℝ)) :=
    isClosed_Icc.prod isClosed_univ
  have hs3 : IsClosed (Icc (((j + 1 : ℤ)) : ℝ) ((((j + 1 : ℤ)) : ℝ) + 1) ×ˢ (univ : Set ℝ)) :=
    isClosed_Icc.prod isClosed_univ
  have h12 : ContinuousOn (fun st : ℝ × ℝ => Htilde p H st)
      (Icc (((j - 1 : ℤ)) : ℝ) ((((j - 1 : ℤ)) : ℝ) + 1) ×ˢ (univ : Set ℝ) ∪
        Icc ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) ×ˢ (univ : Set ℝ)) :=
    h1.union_of_isClosed h2 hs1 hs2
  have hU : ContinuousOn (fun st : ℝ × ℝ => Htilde p H st)
      ((Icc (((j - 1 : ℤ)) : ℝ) ((((j - 1 : ℤ)) : ℝ) + 1) ×ˢ (univ : Set ℝ) ∪
        Icc ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) ×ˢ (univ : Set ℝ)) ∪
        Icc (((j + 1 : ℤ)) : ℝ) ((((j + 1 : ℤ)) : ℝ) + 1) ×ˢ (univ : Set ℝ)) :=
    h12.union_of_isClosed h3 (hs1.union hs2) hs3
  have hle : (j : ℝ) ≤ st.1 := by rw [hj]; exact Int.floor_le st.1
  have hlt : st.1 < (j : ℝ) + 1 := by rw [hj]; exact Int.lt_floor_add_one st.1
  have hmem : st ∈ Ioo (((j - 1 : ℤ)) : ℝ) ((((j + 1 : ℤ)) : ℝ) + 1) ×ˢ (univ : Set ℝ) :=
    ⟨⟨by rw [hJn]; linarith, by rw [hJp]; linarith⟩, trivial⟩
  refine hU.continuousAt (Filter.mem_of_superset
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds (x := st) hmem) ?_)
  rintro q ⟨hq1, -⟩
  rw [hJn, hJp] at hq1
  rw [hJn, hJp]
  rcases lt_or_ge q.1 ((j : ℝ)) with h | h
  · exact Or.inl (Or.inl ⟨⟨by linarith [hq1.1], by linarith⟩, trivial⟩)
  · rcases lt_or_ge ((j : ℝ) + 1) q.1 with h2' | h2'
    · exact Or.inr ⟨⟨by linarith, by linarith [hq1.2]⟩, trivial⟩
    · exact Or.inl (Or.inr ⟨⟨by linarith, by linarith⟩, trivial⟩)

/-- **The extension agrees with `H` on the cylinder.**  For `s ∈ [0,1]` the floor is `0` (except at
`s = 1`, where the closed-slab form applies), so `H̃ (s,t) = Tz 0 (H (s,t)) = H (s,t)`.  This is what
makes the selection table apply to `cylinder_selection`: the fibres of `H̃` over `[0,1]` are exactly
the fibres of `H`, while `H̃` additionally has the `T`-equivariance on all of `ℝ²` that every lemma in
the table requires. -/
lemma Htilde_eq_self_of_mem_Icc {p : ℝ} {H : ℝ × ℝ → ℝ × ℝ}
    (hHper : ∀ t : ℝ, H (1, t) = Tmap p (H (0, t))) {s t : ℝ} (hs : s ∈ Icc 0 1) :
    Htilde p H (s, t) = H (s, t) := by
  have h := Htilde_eq_on_Icc hHper (j := 0) (s := s) (t := t) (by simpa using hs)
  simpa using h

/-! ## The row/column (affine-sweep) structure of the interpolation

The interpolation `H (s,t) = (1 - t) γ_A s + t γ_B s` between two `T`-crossings has

* **rows** `R t := {H (s,t) | s ∈ ℝ}`, each of which is again a `T`-crossing in the strip, and
* **columns** `{H (s,t) | t ∈ [0,1]}`, the segment from `γ_A s` to `γ_B s`.

The point of separating them is that the crux is *immediately* closed by any **good row**, i.e. any
`t` whose row lies inside `VA ∩ VB` (`crux_of_good_row`): that row is then a genuine `T`-crossing
inside `VA ∩ VB`, so its initial point is an essential point of both sets.  Conversely, if the crux
conclusion fails then *every* row meets `Ω \ (VA ∩ VB)`, so the closed set of bad parameters

  `B = {t ∈ [0,1] | ∃ s, H (s,t) ∉ VA ∩ VB}`

is all of `[0,1]`; the remaining content of the crux is therefore exactly `B ≠ [0,1]`. -/

/-- The clamped interpolation parameter: a continuous retraction of `ℝ` onto `[0,1]`. -/
noncomputable def clim (t : ℝ) : ℝ := (Set.projIcc (0:ℝ) 1 (by norm_num) t : Set.Icc (0:ℝ) 1)

lemma clim_mem (t : ℝ) : clim t ∈ Set.Icc (0:ℝ) 1 := (Set.projIcc (0:ℝ) 1 (by norm_num) t).2

@[simp] lemma clim_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : clim t = t := by
  unfold clim; rw [Set.projIcc_of_mem _ ht]

@[simp] lemma clim_zero : clim 0 = 0 := by simp [clim]
@[simp] lemma clim_one : clim 1 = 1 := by simp [clim]

lemma continuous_clim : Continuous clim := by
  unfold clim
  exact continuous_subtype_val.comp continuous_projIcc

/-- **The row map** of a pair of paths `γA, γB`: the affine interpolation at the clamped
parameter.  Its rows `s ↦ rowMap γA γB s t` are the objects the crux is about. -/
noncomputable def rowMap (γA γB : ℝ → ℝ × ℝ) (s t : ℝ) : ℝ × ℝ :=
  aff (clim t) (γA s) (γB s)

@[simp] lemma rowMap_zero (γA γB : ℝ → ℝ × ℝ) (s : ℝ) : rowMap γA γB s 0 = γA s := by
  simp [rowMap]
@[simp] lemma rowMap_one (γA γB : ℝ → ℝ × ℝ) (s : ℝ) : rowMap γA γB s 1 = γB s := by
  simp [rowMap]

lemma continuous_rowMap {γA γB : ℝ → ℝ × ℝ} (hA : Continuous γA) (hB : Continuous γB) :
    Continuous fun st : ℝ × ℝ => rowMap γA γB st.1 st.2 := by
  have h1 : Continuous fun st : ℝ × ℝ => (γA st.1 : ℝ × ℝ) := hA.comp continuous_fst
  have h2 : Continuous fun st : ℝ × ℝ => (γB st.1 : ℝ × ℝ) := hB.comp continuous_fst
  have hc : Continuous fun st : ℝ × ℝ => clim st.2 := continuous_clim.comp continuous_snd
  exact Continuous.add (Continuous.smul (continuous_const.sub hc) h1)
    (Continuous.smul hc h2)

/-- **Rows are `T`-crossings.**  Every row of the affine interpolation is equivariant under `T`. -/
lemma rowMap_equivariant {p : ℝ} {γA γB : ℝ → ℝ × ℝ}
    (hA : ∀ s : ℝ, γA (s + p) = Tmap p (γA s))
    (hB : ∀ s : ℝ, γB (s + p) = Tmap p (γB s)) (s t : ℝ) :
    rowMap γA γB (s + p) t = Tmap p (rowMap γA γB s t) := by
  rw [rowMap, hA s, hB s, ← Tmap_aff, rowMap]

/-- Iterating a "period-shift" identity for a map `ℝ → ℝ × ℝ`. -/
theorem prod_add_mul_nat_of_period {p : ℝ} {f : ℝ → ℝ × ℝ}
    (hf : ∀ s : ℝ, f (s + p) = ((f s).1 + p, (f s).2)) (σ : ℝ) (m : ℕ) :
    f (σ + (m : ℝ) * p) = ((f σ).1 + (m : ℝ) * p, (f σ).2) := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h2 : σ + ((k + 1 : ℕ) : ℝ) * p = (σ + (k : ℝ) * p) + p := by
        rw [Nat.cast_add, Nat.cast_one]; ring
      rw [h2, hf (σ + (k : ℝ) * p), ih]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        rw [Nat.cast_add, Nat.cast_one]; ring
      · simp

/-- Iterating a "period-shift" identity for a map `ℝ → ℝ × ℝ`, for arbitrary integer shifts.
This is the reduction that lets one work on a single period `[0,p]`. -/
theorem prod_add_mul_int_of_period {p : ℝ} {f : ℝ → ℝ × ℝ}
    (hf : ∀ s : ℝ, f (s + p) = ((f s).1 + p, (f s).2)) (s : ℝ) (n : ℤ) :
    f (s + (n : ℝ) * p) = ((f s).1 + (n : ℝ) * p, (f s).2) := by
  rcases lt_or_ge n 0 with hn | hn
  · have hpos : (0 : ℤ) ≤ -n := by omega
    have hcast : (((-n).toNat : ℕ) : ℝ) = ((-n : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hpos
    have h := prod_add_mul_nat_of_period hf (s + (n : ℝ) * p) ((-n).toNat)
    rw [hcast] at h
    have hzero : (s + (n : ℝ) * p) + ((-n : ℤ) : ℝ) * p = s := by push_cast; ring
    rw [hzero] at h
    refine Prod.ext ?_ ?_
    · have hfst := congrArg Prod.fst h
      simp only [Prod.fst] at hfst
      have hneg : ((-n : ℤ) : ℝ) = -((n : ℝ)) := by push_cast; ring
      rw [hneg] at hfst
      linarith
    · exact (congrArg Prod.snd h).symm
  · have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hn
    have h := prod_add_mul_nat_of_period hf s n.toNat
    rw [hcast] at h
    exact h

/-! ### Session 43: the connecting statement, isolated with `W` eliminated

**Proved:** `mv_obligation_iff_common_crossing` — the obligation is *equivalent* to

> `∃ q ∈ VA ∩ VB, ∃ m ≥ 1, q ~ Tz p m q inside VA AND inside VB`,

i.e. some point where the two sets share a non-zero translate-crossing.  Forward is immediate
(`VA ∩ VB ⊆ VA, VB`); backward is Janiszewski in the simply connected strip
(`joinedIn_inter_of_joinedIn_strip`).  In `retDeg` language the obligation is therefore

> `∃ q ∈ VA ∩ VB, (retDeg p VA q ∩ retDeg p VB q) ≠ {0}`,

with both monodromies constant on path components (`retDeg_eq_of_joinedIn`) — so the connecting map
of SvK must produce a *common* point where the two non-trivial monodromies are simultaneously
non-trivial.  Equivalently: some `T`-invariant component of `VA` meets some `T`-invariant component
of `VB` (that is the crux in component form; sessions 28/33 established the surrounding rigidity).

**Why `W` could be eliminated:** the transport lemmas of session 42 move a monodromy freely along
paths *inside `VA`* and *inside `VB`*, and Janiszewski (which needs only the simply connected strip)
converts a common crossing in `VA` and `VB` into a crossing of the intersection.  So the asymmetry —
one monodromy from `hwindA`, the other from `hwindB`, at unrelated base points — is the whole of what
remains, and it is now stated without reference to `VA ∩ VB` at all.

**Staged for the fleet** (queue busy on two attempts; re-issue when free):
`Topology/Strip/joinedIn_translate_iff` — the pure-Mathlib form of the session-42 transport.
-/

/-! ### Session 42: the base-point transport of the monodromy — first piece of the missing layer

**Proved this session** (both axiom-clean):

* `retDeg_eq_of_joinedIn` — the monodromy subgroup is **constant on path components**: if `x, y ∈ W`
  are joined inside a `T`-invariant `W`, then `retDeg p W x = retDeg p W y`.  The degree set is a
  stabilizer, carried unchanged along any path (conjugation by the connecting path, using
  `joinedIn_Tz` for the translate of the path and concatenation);
* `retDeg_Tz` — the monodromy subgroup is **invariant under the deck transformation**:
  `retDeg p W (Tz p j z) = retDeg p W z`.

These are the smallest true pieces of the van Kampen / Mayer–Vietoris layer that `mv_obligation`
waits on.  Their content: transporting `1 ∈ retDeg p VA z_A` (from `hwindA`) and
`1 ∈ retDeg p VB z_B` (from `hwindB`) to a common base point is *free along paths already lying in
one of the two sets* — what is missing is only the comparison of the two sets at a common point of
`VA ∩ VB`, i.e. the connecting-map/union part of SvK.

**Staged for the fleet** (queue was busy at the time of writing; re-issue when free):
`Topology/Strip/joinedIn_translate_iff` — the same transport stated purely in Mathlib terms (no
`retDeg`), namely: for `W` invariant under `q ↦ (q.1 + p, q.2)` and `x ~ y` inside `W`, one has
`x ~ (x.1 + k*p, x.2)` inside `W` iff `y ~ (y.1 + k*p, y.2)` inside `W`, for every `k : ℤ`.  Its
in-file instance is exactly `retDeg_eq_of_joinedIn`.

**What is still missing** (the honest statement of the gap, at the level of the layer): the
*connecting* part — from the two essential loops, one in `VA` and one in `VB`, produce a loop of the
intersection.  With `retDeg` this reads: from `k_A ∈ retDeg p VA z_A`, `k_B ∈ retDeg p VB z_B`
(both non-zero) deduce `∃ q ∈ VA ∩ VB, retDeg p (VA ∩ VB) q ≠ {0}`.  That is SvK/Mayer–Vietoris for
`π₁` over the open cover `{VA, VB}` of the simply connected strip; nothing else.
-/

/-! ### Session 41: the deck-group dictionary — the gap in monodromy language

**Proved this session:**

* `Tz_image_component_iff_mem_retDeg` — the dictionary: for `W` `T`-invariant and open, `z ∈ W`,
  the component `C = connectedComponentIn W z` is `T^m`-invariant **iff** `m ∈ retDeg p W z`
  (i.e. `z` is joined to `Tz p m z` inside `W`).  Hence the `T`-orbit of a component is the index of
  the monodromy subgroup, and "every component of `W` has infinite `T`-orbit" is exactly
  "`retDeg p W q = {0}` for all `q ∈ W`";
* `not_crux_retDeg_eq_bot` — the failure hypothesis in monodromy form: every element of
  `retDeg p (VA ∩ VB) q` is `0`.

**So the obligation is now, verbatim:** `∃ q ∈ VA ∩ VB, retDeg p (VA ∩ VB) q ≠ {0}` — the monodromy
of the intersection is non-trivial somewhere.  This is the Maye–Vietoris statement in deck-group
language, and it shows exactly where the missing input has to act: `hwindA` gives a non-trivial
element of `retDeg p VA z_A` and `hwindB` one of `retDeg p VB z_B`, but at *different base points*
`z_A`, `z_B`; `retDeg_inter_subset` bounds the intersection's monodromy by the pointwise
intersection of the two, so the missing input is precisely the ability to transport the two
monodromy subgroups to a common base point of `VA ∩ VB` using connectedness of the strip (van
Kampen / Mayer–Vietoris for `π₁`).  Nothing else remains: the transport, the dictionary, the period
statement, and the failure-case rigidity are all proved and axiom-clean.
-/

/-! ### Session 40: the construction's input, proved — and what the naive candidates fail on

**Proved:** `not_crux_components_infinite_orbit`: under the failure hypothesis, for every
`q ∈ VA ∩ VB` and every `k ≠ 0`, `Tz p k q ∉ connectedComponentIn (VA ∩ VB) q`.  So "the crux fails"
is *equivalently* "every component of `VA ∩ VB` has infinite `T`-orbit" — one line to state, and now
proved from `mv_one_iff_crux` + `orbit_infinite_of_no_crossing`.

**The construction's candidate list, and why the naive ones fail.**  To contradict
`period_statement` one needs a connected, `T^m`-invariant (`m ≥ 2`), *open* `V` with
`V ∩ (V + (p,0)) = ∅`.  Candidates tried (all failing, usefully):

* a component `E` of `VA ∩ VB` (infinite orbit): `E ∩ TE = ∅` ✓ but `T^m E ≠ E` for all `m`, so `E`
  is not `T^m`-invariant;
* `⋃_{k∈ℤ} T^{2k} E` (the `T^2`-orbit of `E`): `T^2`-invariant ✓ and disjoint from its `p`-translate
  ✓, but **disconnected** — the pieces `T^{2k}E` are pairwise disjoint open sets;
* joining them with paths inside a `T`-invariant component `C_A` of `VA` (note `E, TE ⊆ C_A`
  whenever `E ⊆ C_A`, by `T`-invariance) makes the union connected, but then one must *check* that
  the enlarged set still avoids its `p`-translate — and at that point the union is typically too big;
* `C_A` itself is connected and `T`-invariant, but `C_A ∩ T C_A = C_A ≠ ∅`, so it is useless
  (only `m = 1` invariance is available for free, never `m ≥ 2`).

The obstruction is therefore exactly *simultaneous* connectedness and `T^m`-invariance with
`m ≥ 2`, `p`-translate-disjointness — which is the content of the period statement, i.e. the
content of the missing Mayer–Vietoris input.  In the annulus the same task reads: find a connected
open `Û ⊆ A` with `[ℤ : im π₁(Û)] = m ≥ 2` and `Û ∩ σÛ = ∅`, where `σ` generates the deck group of
the `m`-fold cover — i.e. a connected open set that "winds exactly `m ≥ 2` times", disjoint from its
own half-shift.  `period_statement` says precisely that no such set exists, so the construction is
not an independent fact but a *reformulation* of the obligation.
-/

/-! ### Session 39: the packaging lemma done — the frontier is now one construction

`orbit_infinite_of_no_crossing` (proved, axiom-clean): if a component `C = connectedComponentIn W z`
of a `T`-invariant open `W` contains no point joined to its translate *inside* `C`, then no
non-trivial `Tz`-translate of a point of `C` lies in `C` — the orbit of `C` is infinite.  This is the
contrapositive of `component_crossing_of_period` (the `ℤ`-shift is reduced to the `ℕ`-shift by
`Tz`-calculus, and the `hper` form of `component_crossing_of_period` is obtained from the
`Tz p m '' C = C` form by injectivity of `Tz p m`).

With it, the failure hypothesis of `mv_obligation` is *equivalently*: every component of
`VA ∩ VB` has infinite `T`-orbit.  By `period_statement`, any connected `T^m`-invariant (`m ≥ 2`)
open `V` meets `V + (p,0)`.  Hence the obligation is proved as soon as one exhibits, from that
failure hypothesis, a connected `T^m`-invariant (`m ≥ 2`) open `V` with `V ∩ (V + (p,0)) = ∅`.

**That construction is now the entire frontier.**  Nothing else remains: the interface
(`mv_one_iff_crux`), the transport (`Tz_image_connectedComponentIn`), the crossing/period machinery
(`period_statement`, `component_crossing_of_period`), the rigidity of the failure case
(`component_meets_of_no_crux`, `eq_stripS_of_component_disjoint`) and this packaging lemma are all
proved and axiom-clean.
-/

/-! ### Session 38: the obligation's interface pinned (`mv_one_iff_crux`) and the strategy

**Proved this session:** `mv_one_iff_crux` — the `m = 1` instance of the obligation is *equivalent*
to the crux.  So `mv_obligation` is the crux with the conclusion moved from `Ess p VA ∩ Ess p VB`
to "a `T`-crossing inside `VA ∩ VB`", and (by `component_crossing_of_period`) the `m ≥ 2` instances
are equivalent to the `m = 1` one.  There is nothing to gain by weakening the obligation.

**The strategy in the form the file can now execute.**  Suppose the obligation fails, i.e. every
component of `W = VA ∩ VB` has **infinite** `T`-orbit (this is exactly `mv_one_iff_crux` plus
`component_crossing_of_period`).  By `period_statement`, any *connected* `T^m`-invariant (`m ≥ 2`)
open set meets its own `p`-translate.  Hence a proof of the obligation can proceed by exhibiting,
from the failure hypothesis, a connected `T^m`-invariant open `V` (`m ≥ 2`) with `V ∩ T V = ∅` —
contradiction.  Under the failure hypothesis the configuration is rigid (`component_meets_of_no_crux`,
session 28): every `T`-invariant component `C_A` of `VA` meets `VB` and vice versa, while no
`T`-invariant component of `VA` meets one of `VB`; in particular the pieces `C_A ∩ (VA ∩ VB)` are
unions of components of infinite orbit, and every `T`-invariant `C_A` contains `C_A ∩ VB` as a
non-trivial, non-closed piece of itself.

So the remaining mathematical task is a *construction* (the elementary substitute for
Mayer–Vietoris): from the two `T`-crossings and the cover, build such a `V`, or — equivalently —
find a component of `VA ∩ VB` of finite orbit.  Any sub-lemma of that construction is welcome in the
commons; the interface and all transport/crossing machinery it will need are proved.
-/

/-! ### Session 35: the re-route — **the one remaining `sorry` now sits on the true gap**

Done as planned: `crux_Z_meet` no longer goes through the "cylinder selection" interface.  Instead

```
crux_of_finite_orbit_component   (proved, session 34)
        applied to
mv_obligation                    (the single `sorry` of this file, session 34)
```

gives `crux_Z_meet`, and hence the target `annulus_essential_intersection`, with `VA ⊆ stripS a b`
and `VB ⊆ stripS a b` derived from the cover hypothesis.  The old `cylinder_selection` interface has
been **deleted** (its mathematical discussion is preserved below as a module comment): a continuous
periodic selection of that kind was a point-set substitute for Denne's `prop:homology` whose truth
was never established, whereas `mv_obligation` is the statement Mayer–Vietoris actually proves.

Axiom check (this session): `period_statement`, `component_crossing_of_period`,
`crux_of_finite_orbit_component` and the `Tz` transport lemmas are **`sorry`-free** (`#print axioms`
gives only `propext`, `Classical.choice`, `Quot.sound`); the only `sorryAx` in the file is
`mv_obligation`, exactly as intended.  The target statement is untouched (byte-identical), the build
is green, and all the point-set material (fibre/`τ`/`σ` machinery, crossing lemmas, the analytic
graph case, the band form, `embedded_circle_of_shift_invariant`'s session-31 note) remains in place as
proved or as clearly-labelled superseded material.
-/

/-! ### Session 34: the Mayer–Vietoris obligation, isolated and reduced

Two more results, both proved:

* `Tz_image_connectedComponentIn` / `..._nat` — `Tz p k` maps the component of `z` onto the
  component of `Tz p k z` (the integer-iterate of the transport lemma);
* `crux_of_finite_orbit_component` — **the Mayer–Vietoris obligation implies the crux**, and is the
  only remaining input.  The obligation is: for `T`-invariant open `VA`, `VB`,

  `∃ q ∈ VA ∩ VB, ∃ m : ℤ, 1 ≤ m ∧ JoinedIn (VA ∩ VB) q (Tz p m q)`

  i.e. *some point of `VA ∩ VB` is joined to a positive translate of itself inside `VA ∩ VB`*
  (= some component of `VA ∩ VB` has non-zero winding / finite `T`-orbit).  Proof of the reduction:
  for `m = 1` the crossing is already in `VA ∩ VB`; for `m ≥ 2` the component
  `C = connectedComponentIn (VA ∩ VB) q` satisfies `T^m C = C` by `Tz_image_connectedComponentIn`,
  and `component_crossing_of_period` then produces a genuine crossing inside `C ⊆ VA ∩ VB`.

**Equivalences of the obligation (worth knowing when attacking it).**  The `m = 1` instance of the
obligation is *equivalent* to the crux: given `T`-invariant components `C_A ⊆ VA`, `C_B ⊆ VB` with
`C_A ∩ C_B ≠ ∅` and `q` in the intersection, `q ~ T q` inside `C_A ⊆ VA` and inside `C_B ⊆ VB`, so
Janiszewski (`joinedIn_inter_of_joinedIn_strip`) gives `q ~ T q` inside `VA ∩ VB`.  With
`component_crossing_of_period` the same holds for any `m ≥ 2`, so the obligation is equivalent to
"some `T`-invariant component of `VA` meets some `T`-invariant component of `VB`" — i.e. to the crux
in component form, exactly as session 28's `component_meets_of_no_crux` suggested.

So the crux now has **exactly one** mathematical obligation left: the Mayer–Vietoris / winding
input above.  Everything else — the period statement, the crossing transport, the component
rigidity, the planar crossing lemma — is proved.
-/

/-! ### Session 33: **the period statement is PROVED** (`period_statement` below)

The fleet proved `Commons.Topology.Strip.path_meets_translate` (the planar claim of session 32), and
it is now imported here.  Applying it to the `T^m`-equivariant extension (`Htilde`) of a path in `C`
from a point to its `m`-fold translate gives, in this file:

`period_statement` (p > 0, m ≥ 2, `C` open, connected, `T^m`-invariant):
  `¬ (∀ q ∈ C, (q.1 + p, q.2) ∉ C)` — i.e. **`C` meets its own `p`-translate**.

This is the statement identified in sessions 29–32 as the missing ingredient of the crux route
("components of `T`-invariant open sets have `T`-orbit `1` or `∞`"): its contrapositive is that a
component without a `T`-crossing has infinite `T`-orbit, so a finite orbit forces a genuine crossing
(`component_crossing_of_period` below).  Chain of layers, all now proved:

* planar input — `Commons.Topology.Strip.path_meets_translate` (fleet, commons);
* `period_statement` — equivariant extension + planar input (this file);
* `component_crossing_of_period` — the component-level corollary (this file);
* remaining for the crux: the Mayer–Vietoris input "some component of `VA ∩ VB` has finite
  `T`-orbit" (unavailable in Mathlib), together with `component_meets_of_no_crux` from session 28.
-/

/-! ### Session 32: the period lemma collapses to ONE elementary planar claim

While trying to prove *simplify to simple* myself, I found that it (and "simple loops are graphs",
and the graph case, and the Jordan input) are all **not needed** for the period lemma.  The whole
thing reduces to the following statement about a single path:

```
path_meets_translate:  p > 0, m ≥ 2, γ : ℝ → ℝ × ℝ continuous,
                       (∀ s, γ (s + 1) = ((γ s).1 + m * p, (γ s).2))
                  ⟹  ∃ s t : ℝ, γ s = ((γ t).1 + p, (γ t).2)
```

i.e. *a `T^m`-equivariant curve in the plane meets its own `p`-translate* (equivalently: the lift of
a degree-`m` loop of the cylinder meets the lift of its half-shift).  It is **false for `m = 1`**
(the horizontal line `s ↦ (p*s, 0)`), so `m ≥ 2` is essential.

**Why this suffices.**  Let `C` be open, connected, `T^m`-invariant with `C ∩ T C = ∅`.  Pick
`z ∈ C`; since `C` is open and connected in `ℝ²` it is path connected, so there is a path in `C`
from `z` to `T^m z`; extend it `T^m`-equivariantly to `γ`.  Then `γ (ℝ) ⊆ C` (by `T^m`-invariance)
and `γ s = γ t + (p,0)` gives `γ s ∈ C ∩ T C = ∅` — contradiction.  **No embeddedness, no Jordan,
no graph, no `simple_loop_graph`.**  So the two statements queued in session 31, and the analytic
graph case of session 29, are no longer on the critical path (they remain true and are kept).

**Proof sketch of `path_meets_translate`** (first-crossing heights + crosscut order).  Put
`f s := (γ s).1`, `a := f 0`, and let `τ_j` be the first time `f` reaches `a + j*p`; set
`P_j := γ (τ_j) = (a + j*p, β_j)`.  In the strip `Σ_j = {a + j*p < x < a + (j+1)*p}` the two
sub-paths `γ|[τ_j, τ_{j+1}]` and `(γ|[τ_{j-1}, τ_j]) + (p,0)` join its two boundary lines and are
disjoint by hypothesis; two disjoint crosscuts of a strip joining the two boundary lines cannot swap
their vertical order, so `sign (β_{j+1} - β_j) = sign (β_j - β_{j-1})` for every `j ∈ ℤ`.  Hence all
increments `β_{j+1} - β_j` have one sign, while `β_{j+m} = β_j` makes them sum to `0` over a period
— contradiction.  The only planar input is the crosscut-order (rectangle separation) fact, for which
the commons already has `Commons.Topology.Crossing.*` and
`Commons.Topology.Jordan.top_bottom_continuum_meets_left_right_path`.

**The same claim in the form in which the crossing lemmas apply.**  With `σ₀ := γ|[0,1]` (a path
from `A := γ 0` to `A + (m*p, 0)`) and `σ₁ := σ₀ + (p,0)` (from `A + (p,0)` to `A + ((m+1)*p, 0)`),
the claim is exactly `σ₀ ∩ σ₁ ≠ ∅`: two paths in the plane, each spanning horizontally by `m*p`,
offset from each other by `p < m*p`, must meet.  This is the standard "two spanning curves cross"
statement, for which `Commons.Topology.Crossing.crossing_lemma_square` /
`crossing_lemma_rect_path` are the natural tools (via the first-crossing heights `h_k` of `σ₀` on the
vertical lines `x = A.1 + k*p`, using `σ₁ ∩ {x = A.1 + (k+1)*p} = (σ₀ ∩ {x = A.1 + k*p}) + (p,0)`).

**Status of the fleet queue:** `request_lemma` still refuses (seven attempts; "the team is busy
right now and you have no running children").  Staged payloads, ready to send verbatim:
session 31's `embedded_circle_of_shift_invariant` (now superseded) and `path_meets_translate`
(the critical path).
-/

/-! ### Session 31: *simplify to simple* — statement written up and queued; consumer side proved

The fleet queue refused five attempts (`request_lemma` kept answering "the team is busy right now
and you have no running children"), so the statement is recorded here verbatim, ready to be sent at
`Topology/Strip/embedded_circle_of_shift_invariant` the moment an agent is free:

```
theorem embedded_circle_of_shift_invariant {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 0 < m)
    {C : Set (ℝ × ℝ)} (hCop : IsOpen C) (hCconn : IsConnected C)
    (hCinv : ∀ q : ℝ × ℝ, q ∈ C ↔ ((q.1 + m * p, q.2) ∈ C))
    (hdisj : ∀ q : ℝ × ℝ, q ∈ C → (q.1 + p, q.2) ∉ C) :
    ∃ γ : ℝ → ℝ × ℝ, Continuous γ ∧ (∀ s : ℝ, γ (s + 1) = ((γ s).1 + m * p, (γ s).2)) ∧
      (∀ s : ℝ, γ s ∈ C) ∧
      (∀ s t : ℝ, 0 ≤ s → s < 1 → 0 ≤ t → t < 1 → ∀ j : ℤ,
        γ s = ((γ t).1 + ((j * (m : ℤ) : ℤ) : ℝ) * p, (γ t).2) → j = 0 ∧ s = t)
```

i.e. *a nontrivial free homotopy class of loops in an open connected surface has an embedded
representative*, with the non-triviality supplied by connectedness of the `m`-fold preimage `C`.
`hdisj` is not needed for the geometric conclusion; it is part of the intended application.  The
`m = 1` analogue of the *existence of a crossing* (not of embeddedness) is
`component_invariant_iff_exists_crossing`.

**Consumer side, proved this session.**  `band_inter_translate_nonempty_of_periodic`: if
`h : ℝ → ℝ` is continuous and periodic of period `m*p` (`p > 0`, `m ≥ 2`) and `ε > 0`, then some
point of the graph of `h` lies within `ε` of the graph of its `p`-shift
(`∃ q, |q.2 - h q.1| < ε ∧ |q.2 - h (q.1 + p)| < ε`).  This is the shape in which the graph case
(`exists_add_p_eq_of_periodic`) is consumed by the period lemma: the embedded circle from the
statement above is a graph `θ ↦ (θ, h θ)` with `h` `(m*p)`-periodic (`simple_loop_graph`), its
disjointness from its `p`-translate forces `h (θ + p) ≠ h θ` for all `θ`, and this corollary says
that is impossible.
-/

/-! ### Session 30: step (1) (connected ⟺ degree-one loop) in covering/path form — proved

Three permanent lemmas, all green:

* `Tmap_image_connectedComponentIn` — `T` maps the component of `z` in a `T`-invariant set onto the
  component of `T z`;
* `component_invariant_iff_exists_crossing` — the component `C = connectedComponentIn W z` of a
  `T`-invariant open `W` is `T`-invariant (`T '' C = C`) **iff** `C` contains a point joined to its
  translate *inside* `C`.  This is the elementary form of "`C` is connected ⟺ the corresponding
  component of the quotient contains a loop of degree one": `T '' C = C` says `C` is a full preimage
  of its image, and a path in `C` from `q` to `T q` projects to a degree-one loop;
* `mem_Ess_iff_component_invariant` — consequently `z ∈ Ess p W` (for `W` open and `T`-invariant)
  iff the component of `z` in `W` is `T`-invariant; i.e. `Ess p W` is *exactly* the union of the
  `T`-invariant components of `W` (the docstring claims this; it is now a theorem).

**What step (1) still owes:** "simplify to simple".  Given `T^m C = C` with `C ∩ T C = ∅`, one needs
a path in `C` from `q` to `T^m q` that is injective modulo `T^m` (equivalently: a generator loop in
the open connected `Ĉ ⊆ A_m` can be realised by an embedded circle).  This is a classification
statement for loops in a surface (the core of a covering of the annulus), not an analytic one; the
`m = 1` case is what `component_invariant_iff_exists_crossing` supplies.
-/

/-! ### Session 29: the graph case of the period lemma is PROVED (in the file below)

`exists_add_p_eq_of_periodic` (and its `j`-general form `exists_period_translate_eq`) is exactly the
graph case of the period lemma, and the proof is much cheaper than the "rank function" route:

if `h` is `m*p`-periodic (`m ≥ 2`) and `h (x + p) ≠ h x` for all `x`, then `ψ x = h (x+p) - h x` is
continuous and nowhere zero on the connected line, hence of constant sign; but the telescoping sum
`Σ_{j<m} ψ (x + j*p) = h (x + m*p) - h x = 0` has `m ≥ 2` terms of one strict sign — contradiction.
(So the `j = 1` instance alone already fails.)

**The remaining chain for the full period lemma.**  Let `C` be a connected component of a
`T`-invariant open `W ⊆ Ω` with `C ∩ T C = ∅` and `T^m C = C`.  Writing `C = π_m^{-1}(Ĉ)` for `Ĉ`
open connected in the `m`-fold annulus `A_m`, the two remaining inputs are:

1. (**generator loops**) `C` connected ⟺ `Ĉ` contains a loop of degree `1` in `A_m`; and such a loop
   can be replaced (inside `Ĉ`) by a *simple* one;
2. (**simple loops are graphs**) a simple closed curve in an annulus of degree `±1` is a graph over
   the base circle — i.e. an elementary "degree `∈ {−1, 0, 1}`" statement for simple closed curves in
   an annulus.

Given (1) and (2): `γ ⊆ Ĉ` simple of degree `1`, say `γ = {(θ, h θ)}` with `h` an `m*p`-periodic
continuous function; disjointness `Ĉ ∩ σĈ = ∅` gives `h (θ + p) ≠ h θ` for all `θ`, contradicting
`exists_add_p_eq_of_periodic`.  With (**MV**, still unavailable) this yields the crux.

**Correct formulation of step (2)** (note: the parameter lives in `[0,1)`, and the window condition
must be read *modulo* `p` — a degree-one loop need not meet a fixed window `[x, x+p)`; e.g.
`s ↦ (x - 2p + s*p, 0)` has `γ (s+1) = γ s + (p,0)` and never meets `[x, x+p)`).  For `p > 0` and
`γ : ℝ → ℝ × ℝ` continuous with `γ (s+1) = γ s + (p,0)` and injective on `[0,1)` modulo integer
translates (`γ s = γ t + (j*p,0)` with `s, t ∈ [0,1)` forces `j = 0 ∧ s = t`), one has, for every
`x`,

`∃! s : ℝ, s ∈ Set.Ico 0 1 ∧ ∃ j : ℤ, (γ s).1 = x + j * p`.

That is: a degree-one simple closed curve in the cylinder meets each meridian exactly once, so it is
the graph `θ ↦ (θ, h θ)` of a continuous `p`-periodic `h`.  The uniqueness half needs the Jordan
curve theorem: two sub-arcs of `γ` between repeated meetings of one meridian, together with their
translates, enclose both an inside and an outside piece, forcing `γ s = γ t + (j*p,0)` with `j ≠ 0`.
Together with the `j = 1` graph form (`exists_add_p_eq_of_periodic`) this closes the period lemma up
to the "generator loops can be simplified" step (1).
-/

/-- **The graph case of the period lemma, in its sharp `j = 1` form.**

If `h : ℝ → ℝ` is continuous and periodic of period `m * p` with `p > 0` and `m ≥ 2`, then
`h (x + p) = h x` for some `x`: the `p`-progression of values cannot be strictly monotone in `x`.

Indeed `ψ x = h (x + p) - h x` is continuous and nowhere zero, hence of constant sign on the
connected line `ℝ`, while `Σ_{j<m} ψ (x + j*p) = h (x + m*p) - h x = 0` telescopes.

This is the input needed for the corresponding `T`-invariant "band" `{|y - h x| < ε}`: if `h` is
`m*p`-periodic and `h (x+p) ≠ h x` for all `x`, then the band and its `p`-translate are disjoint,
so the band cannot be a component of a `T`-invariant open set whose `m`-th translate is itself. -/
theorem exists_add_p_eq_of_periodic {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 2 ≤ m)
    {h : ℝ → ℝ} (hc : Continuous h) (hper : ∀ x : ℝ, h (x + (m : ℝ) * p) = h x) :
    ∃ x : ℝ, h (x + p) = h x := by
  by_contra hcon
  have hne : ∀ x : ℝ, h (x + p) - h x ≠ 0 := fun x hx => hcon ⟨x, sub_eq_zero.mp hx⟩
  have hsign : (∀ x : ℝ, 0 < h (x + p) - h x) ∨ (∀ x : ℝ, h (x + p) - h x < 0) := by
    by_contra hbad
    push_neg at hbad
    obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hbad
    have h1 : h (x₁ + p) - h x₁ < 0 := lt_of_le_of_ne hx₁ (hne x₁)
    have h2 : 0 < h (x₂ + p) - h x₂ := lt_of_le_of_ne hx₂ (hne x₂).symm
    have hcontc : Continuous fun x : ℝ => h (x + p) - h x :=
      (hc.comp (continuous_id.add continuous_const)).sub hc
    have hIVT : (0 : ℝ) ∈ (fun x : ℝ => h (x + p) - h x) '' Set.Icc x₁ x₂ ∨
        (0 : ℝ) ∈ (fun x : ℝ => h (x + p) - h x) '' Set.Icc x₂ x₁ := by
      rcases le_total x₁ x₂ with hle | hle
      · exact Or.inl ((intermediate_value_Icc (f := fun x : ℝ => h (x + p) - h x) hle
          hcontc.continuousOn) ⟨h1.le, h2.le⟩)
      · exact Or.inr ((intermediate_value_Icc' (f := fun x : ℝ => h (x + p) - h x) hle
          hcontc.continuousOn) ⟨h1.le, h2.le⟩)
    rcases hIVT with ⟨x₀, -, hx₀⟩ | ⟨x₀, -, hx₀⟩
    · exact hne x₀ hx₀
    · exact hne x₀ hx₀
  have htel : ∑ j ∈ Finset.range m, (h (p + (j : ℝ) * p) - h (0 + (j : ℝ) * p))
      = h (0 + (m : ℝ) * p) - h (0 + ((0 : ℕ) : ℝ) * p) := by
    rw [← Finset.sum_range_sub (fun j : ℕ => h (0 + (j : ℝ) * p)) m]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hcast : 0 + ((j + 1 : ℕ) : ℝ) * p = p + (j : ℝ) * p := by push_cast; ring
    rw [hcast]
  have hzero : h (0 + (m : ℝ) * p) - h (0 + ((0 : ℕ) : ℝ) * p) = 0 := by
    rw [hper 0]; simp
  have hnonempty : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  rcases hsign with hpos | hneg
  · have hsum : 0 < ∑ j ∈ Finset.range m, (h (p + (j : ℝ) * p) - h (0 + (j : ℝ) * p)) :=
      Finset.sum_pos (fun j _ => by
        have hh := hpos (0 + (j : ℝ) * p)
        rwa [show 0 + (j : ℝ) * p + p = p + (j : ℝ) * p by ring] at hh) hnonempty
    rw [htel, hzero] at hsum
    exact lt_irrefl (0 : ℝ) hsum
  · have hsum : (∑ j ∈ Finset.range m, (h (p + (j : ℝ) * p) - h (0 + (j : ℝ) * p))) < 0 :=
      Finset.sum_neg (fun j _ => by
        have hh := hneg (0 + (j : ℝ) * p)
        rwa [show 0 + (j : ℝ) * p + p = p + (j : ℝ) * p by ring] at hh) hnonempty
    rw [htel, hzero] at hsum
    exact lt_irrefl (0 : ℝ) hsum

/-- **Geometric form of the graph case: a periodic band cannot avoid its own translate.**

Let `h : ℝ → ℝ` be continuous and periodic of period `m*p` with `p > 0`, `m ≥ 2`, and let `ε > 0`.
Then some point of the graph of `h` is at height `< ε` from the graph of the `p`-shift of `h`:

`∃ q, |q.2 - h q.1| < ε ∧ |q.2 - h (q.1 + p)| < ε`.

Equivalently: the band `{q | |q.2 - h q.1| < ε}` around the graph (a `T`-invariant open set when `h`
is `p`-periodic, and here `(m*p)`-periodic) meets its own `p`-translate.  This is what the
"graph case" of the period lemma consumes: it forbids a graph band from being a component of a
`T`-invariant open set whose `m`-th translate is itself and which avoids its `p`-translate. -/
theorem band_inter_translate_nonempty_of_periodic {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 2 ≤ m)
    {h : ℝ → ℝ} (hc : Continuous h) (hper : ∀ x : ℝ, h (x + (m : ℝ) * p) = h x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ × ℝ, |q.2 - h q.1| < ε ∧ |q.2 - h (q.1 + p)| < ε := by
  obtain ⟨x, hx⟩ := exists_add_p_eq_of_periodic hp hm hc hper
  refine ⟨(x, h x), ?_, ?_⟩
  · simpa using hε
  · have : h (x + p) = h x := hx
    rw [this]
    simpa using hε

/-- **Existence half of "degree-one simple loops in a cylinder are graphs".**

If `γ : ℝ → ℝ × ℝ` is continuous with `γ (s+1) = γ s + (p,0)` (`p > 0`), then for every `x` some
point of the loop lies on the meridian `x + pℤ`: `∃ s ∈ [0,1), ∃ j : ℤ, (γ s).1 = x + j * p`.

Proof: `g s = (γ s).1 - x` is continuous with `g 1 = g 0 + p`, so by the intermediate value theorem
`g` attains every value in `[g 0, g 0 + p]`; taking `k = ⌈g 0 / p⌉` gives `k*p ∈ [g 0, g 0 + p)`;
if the point found has `s = 1`, use `s = 0` and `j = k - 1` instead.

(Note the `mod p` in the conclusion is necessary: `s ↦ (x - 2p + s*p, 0)` satisfies the shift
relation and never meets the fixed window `[x, x+p)`.) -/
theorem exists_int_mul_eq_of_period_shift {p : ℝ} (hp : 0 < p) {γ : ℝ → ℝ × ℝ}
    (hc : Continuous γ) (heq : ∀ s : ℝ, γ (s + 1) = ((γ s).1 + p, (γ s).2)) (x : ℝ) :
    ∃ s : ℝ, s ∈ Set.Ico 0 1 ∧ ∃ j : ℤ, (γ s).1 = x + j * p := by
  have hg : Continuous fun s : ℝ => (γ s).1 - x := (continuous_fst.comp hc).sub continuous_const
  have h1 : (γ 1).1 - x = ((γ 0).1 - x) + p := by
    have h : (γ 1).1 = (γ 0).1 + p := by simpa using congrArg Prod.fst (heq 0)
    rw [h]; ring
  set g : ℝ → ℝ := fun s => (γ s).1 - x with hgdef
  have hg1 : g 1 = g 0 + p := h1
  set k : ℤ := ⌈g 0 / p⌉ with hkdef
  have hk1 : g 0 ≤ (k : ℝ) * p := by
    have h := Int.le_ceil (g 0 / p)
    have hk : g 0 / p ≤ (k : ℝ) := by simpa [hkdef] using h
    calc g 0 = (g 0 / p) * p := by rw [div_mul_cancel₀ _ (ne_of_gt hp)]
      _ ≤ (k : ℝ) * p := mul_le_mul_of_nonneg_right hk (le_of_lt hp)
  have hk2 : (k : ℝ) * p < g 0 + p := by
    have h := Int.ceil_lt_add_one (g 0 / p)
    have hk : (k : ℝ) < g 0 / p + 1 := by simpa [hkdef] using h
    calc (k : ℝ) * p < (g 0 / p + 1) * p := mul_lt_mul_of_pos_right hk hp
      _ = g 0 + p := by rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul]
  have hmem : (k : ℝ) * p ∈ Set.Icc (g 0) (g 1) := by
    rw [hg1]; exact ⟨hk1, le_of_lt hk2⟩
  obtain ⟨s, hsI, hsg⟩ := (intermediate_value_Icc (a := (0:ℝ)) (b := 1) (by norm_num)
      hg.continuousOn) hmem
  have hsg' : (γ s).1 - x = (k : ℝ) * p := hsg
  rcases eq_or_lt_of_le hsI.2 with hs1 | hs1
  · -- `s = 1`: shift back to `0`
    refine ⟨0, ⟨le_rfl, zero_lt_one⟩, k - 1, ?_⟩
    have : (γ (1:ℝ)).1 - x = (k : ℝ) * p := by rw [← hs1]; exact hsg'
    have h0 : (γ 1).1 - x = ((γ 0).1 - x) + p := h1
    have : (γ 0).1 - x = (k : ℝ) * p - p := by linarith
    have : (γ 0).1 = x + ((k : ℝ) - 1) * p := by linarith
    have hcast : (k : ℝ) - 1 = ((k - 1 : ℤ) : ℝ) := by push_cast; ring
    rw [hcast] at this
    exact this
  · exact ⟨s, ⟨hsI.1, hs1⟩, k, by linarith⟩

/-- **The `j`-general form of the graph case of the period lemma** (immediate from the `j = 1`
form). -/
theorem exists_period_translate_eq {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 2 ≤ m)
    {h : ℝ → ℝ} (hc : Continuous h) (hper : ∀ x : ℝ, h (x + (m : ℝ) * p) = h x) :
    ∃ x : ℝ, ∃ j : ℕ, 1 ≤ j ∧ j < m ∧ h (x + (j : ℝ) * p) = h x := by
  obtain ⟨x, hx⟩ := exists_add_p_eq_of_periodic hp hm hc hper
  exact ⟨x, 1, le_rfl, by omega, by simpa using hx⟩

/-- **Integer-period-shifts of a row.**  Every row of the affine interpolation is equivariant under
arbitrary integer powers of `T`. -/
lemma rowMap_add_int {p : ℝ} {γA γB : ℝ → ℝ × ℝ}
    (hAper : ∀ s : ℝ, γA (s + p) = Tmap p (γA s))
    (hBper : ∀ s : ℝ, γB (s + p) = Tmap p (γB s)) (s t : ℝ) (n : ℤ) :
    rowMap γA γB (s + (n : ℝ) * p) t = Tz p n (rowMap γA γB s t) := by
  have hf : ∀ σ : ℝ, rowMap γA γB (σ + p) t
      = ((rowMap γA γB σ t).1 + p, (rowMap γA γB σ t).2) := fun σ => by
    rw [rowMap_equivariant hAper hBper σ t]
    rfl
  have h := prod_add_mul_int_of_period (p := p) (f := fun σ => rowMap γA γB σ t) hf s n
  have : ((rowMap γA γB s t).1 + (n : ℝ) * p, (rowMap γA γB s t).2)
      = Tz p n (rowMap γA γB s t) := rfl
  rw [this] at h
  exact h

/-- **Iterating the `T`-invariance of a set.**  If `V` is invariant under the unit shift `Tmap p`,
then it is invariant under every integer power `Tz p n`. -/
lemma Tz_mem_iff {p : ℝ} {V : Set (ℝ × ℝ)}
    (hperV : ∀ q : ℝ × ℝ, q ∈ V ↔ Tmap p q ∈ V) (n : ℤ) (q : ℝ × ℝ) :
    Tz p n q ∈ V ↔ q ∈ V := by
  have h1 : ∀ x : ℝ × ℝ, Tz p (1 : ℤ) x ∈ V ↔ x ∈ V := by
    intro x
    simpa [Tz, Tmap] using (hperV x).symm
  have hnat : ∀ m : ℕ, ∀ x : ℝ × ℝ, Tz p (m : ℤ) x ∈ V ↔ x ∈ V := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        have hcast : (((k : ℕ) + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        have hsplit : Tz p ((k : ℤ) + 1) x = Tz p (k : ℤ) (Tz p 1 x) := Tz_add p (k : ℤ) 1 x
        rw [hcast, hsplit, ih, h1]
  rcases lt_or_ge n 0 with hn | hn
  · have hpos : (0 : ℤ) ≤ -n := by omega
    have hcast : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg hpos
    have h := hnat ((-n).toNat) (Tz p n q)
    rw [hcast] at h
    have hcomp : Tz p (-n) (Tz p n q) = q := by
      rw [← Tz_add, neg_add_cancel, Tz_zero]
    rw [hcomp] at h
    exact h.symm
  · have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn
    have h := hnat n.toNat q
    rw [hcast] at h
    exact h

/-- **Integer translates of a `T`-invariant set.**  `Tz`-shifts of joinable points stay
joinable. -/
lemma joinedIn_Tz {p : ℝ} {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (k : ℤ) {x y : ℝ × ℝ} (h : JoinedIn W x y) :
    JoinedIn W (Tz p k x) (Tz p k y) := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ.map (continuous_Tz p k), fun u => (Tz_mem_iff hW k (γ u)).mpr (hγ u)⟩

/-- **Degrees add.**  If a `T`-invariant set joins `z` to `T^k z` and to `T^l z`, then it joins `z`
to `T^{k+l} z` (concatenate the second path with the `T^k`-translate of the first).  This is the
elementary "monodromy is a homomorphism" fact that any homological treatment of the crux uses. -/
lemma joinedIn_Tz_add {p : ℝ} {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    {z : ℝ × ℝ} {k l : ℤ} (hk : JoinedIn W z (Tz p k z)) (hl : JoinedIn W z (Tz p l z)) :
    JoinedIn W z (Tz p (k + l) z) := by
  have h2 : JoinedIn W (Tz p k z) (Tz p k (Tz p l z)) := joinedIn_Tz hW k hl
  rw [← Tz_add] at h2
  exact hk.trans h2

/-- **Negation of degrees.**  If a `T`-invariant set joins `z` to `T^k z`, it also joins `z` to
`T^{-k} z` (reverse the path and translate it back).  With `joinedIn_Tz_add` this says that the
monodromy degrees `{k : z ~ T^k z}` form an additive subgroup of `ℤ`, i.e. the fibre of the covering
`W → W/T` over `z` is a coset of the subgroup of "returning" degrees. -/
lemma joinedIn_Tz_neg {p : ℝ} {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    {z : ℝ × ℝ} {k : ℤ} (hk : JoinedIn W z (Tz p k z)) :
    JoinedIn W z (Tz p (-k) z) := by
  have hrev : JoinedIn W (Tz p k z) z := ⟨hk.choose.symm, fun u => hk.choose_spec _⟩
  have htrans := joinedIn_Tz hW (-k) hrev
  have hz1 : Tz p (-k) (Tz p k z) = z := by rw [← Tz_add, neg_add_cancel, Tz_zero]
  rwa [hz1] at htrans

/-- **`Tz`-shifts map components onto components.**  The `ℤ`-iterate of the component transport. -/
lemma Tz_image_connectedComponentIn_nat {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (n : ℕ) {z : ℝ × ℝ} (hz : z ∈ W) :
    Tz p (n : ℤ) '' connectedComponentIn W z = connectedComponentIn W (Tz p (n : ℤ) z) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hzW : Tz p ((k : ℤ)) z ∈ W := (Tz_mem_iff hW (k : ℤ) z).mpr hz
      rw [show (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 by push_cast; ring]
      have hstep : Tz p ((k : ℤ) + 1) = Tmap p ∘ Tz p (k : ℤ) := by
        funext q
        exact (Tmap_Tz p (k : ℤ) q).symm
      rw [hstep, Set.image_comp, ih]
      exact Tmap_image_connectedComponentIn hW hzW

/-- **`Tz`-shifts map components onto components** (all integer shifts). -/
lemma Tz_image_connectedComponentIn {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (k : ℤ) {z : ℝ × ℝ} (hz : z ∈ W) :
    Tz p k '' connectedComponentIn W z = connectedComponentIn W (Tz p k z) := by
  rcases lt_or_ge k 0 with hk | hk
  · have hnk : (0 : ℤ) ≤ -k := by omega
    have hkz : Tz p k z ∈ W := (Tz_mem_iff hW k z).mpr hz
    have h1 := Tz_image_connectedComponentIn_nat hW ((-k).toNat) hkz
    rw [show ((((-k).toNat : ℕ) : ℤ)) = -k from Int.toNat_of_nonneg hnk] at h1
    have h2 : Tz p (-k) (Tz p k z) = z := by rw [← Tz_add, neg_add_cancel, Tz_zero]
    rw [h2] at h1
    have h3 : Tz p k '' (Tz p (-k) '' connectedComponentIn W (Tz p k z))
        = Tz p k '' connectedComponentIn W z := by rw [h1]
    rw [← Set.image_comp] at h3
    have hid : (Tz p k ∘ Tz p (-k)) = id := by
      funext q
      show Tz p k (Tz p (-k) q) = q
      rw [← Tz_add, add_neg_cancel, Tz_zero]
    rw [hid, Set.image_id] at h3
    exact h3.symm
  · have hcast : k = ((k.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hk).symm
    rw [hcast]
    exact Tz_image_connectedComponentIn_nat hW k.toNat hz

/-- **The period statement: a connected `T^m`-invariant open set meets its own `p`-translate.**

Let `p > 0`, `m ≥ 2`, and let `C ⊆ ℝ × ℝ` be open and connected, invariant under the `m`-fold shift
`(x,y) ↦ (x + m*p, y)`.  Then `C` cannot avoid its `p`-translate: some point of `C` translates by
`(p,0)` into `C`.

This is the statement that a component of a translation-invariant open subset of the strip cannot
have period `m ≥ 2` while missing its own `p`-translate.  The proof is a direct application of the
commons result `Commons.Topology.Strip.path_meets_translate` (a `T^m`-equivariant plane curve meets
its own `p`-translate when `m ≥ 2`): a path in `C` from a point `z` to `T^m z` extends
equivariantly (through `Htilde`) to such a curve, whose two points that differ by `(p,0)` must both
lie in `C` by `T^m`-invariance. -/
theorem period_statement {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 2 ≤ m)
    {C : Set (ℝ × ℝ)} (hCop : IsOpen C) (hCconn : IsConnected C)
    (hCinv : ∀ q : ℝ × ℝ, q ∈ C ↔ ((q.1 + m * p, q.2) ∈ C)) :
    ¬ (∀ q : ℝ × ℝ, q ∈ C → (q.1 + p, q.2) ∉ C) := by
  intro hdisj
  haveI : LocallyPathConnectedSpace (ℝ × ℝ) := inferInstance
  obtain ⟨z, hzC⟩ := hCconn.nonempty
  set u : ℝ × ℝ := ((z.1 + m * p, z.2)) with hudef
  have huC : u ∈ C := (hCinv z).mp hzC
  have hpc : IsPathConnected C := (hCop.isConnected_iff_isPathConnected).mp hCconn
  obtain ⟨γ0, hγ0⟩ := hpc.joinedIn z hzC u huC
  set H : ℝ × ℝ → ℝ × ℝ := fun st => (γ0 ⟨clim st.1, clim_mem st.1⟩ : ℝ × ℝ) with hHdef
  have hHc : Continuous H := by
    rw [hHdef]
    exact γ0.continuous.comp
      (Continuous.subtype_mk (continuous_clim.comp continuous_fst) _)
  have hsub1 : (⟨clim (1:ℝ), clim_mem (1:ℝ)⟩ : unitInterval) = 1 :=
    Subtype.ext clim_one
  have hsub0 : (⟨clim (0:ℝ), clim_mem (0:ℝ)⟩ : unitInterval) = 0 :=
    Subtype.ext clim_zero
  have hHper : ∀ t : ℝ, H (1, t) = Tmap ((m : ℝ) * p) (H (0, t)) := by
    intro t
    have h1 : H (1, t) = u := by
      have hγ1 : (γ0 ⟨clim (1:ℝ), clim_mem (1:ℝ)⟩ : ℝ × ℝ) = γ0 1 :=
        congrArg (fun x : unitInterval => (γ0 x : ℝ × ℝ)) hsub1
      rw [hHdef]
      exact hγ1.trans γ0.target
    have h0 : H (0, t) = z := by
      have hγ0' : (γ0 ⟨clim (0:ℝ), clim_mem (0:ℝ)⟩ : ℝ × ℝ) = γ0 0 :=
        congrArg (fun x : unitInterval => (γ0 x : ℝ × ℝ)) hsub0
      rw [hHdef]
      exact hγ0'.trans γ0.source
    rw [h1, h0, hudef]
    rfl
  set γ : ℝ → ℝ × ℝ := fun s => Htilde ((m : ℝ) * p) H (s, 0) with hγdef
  have hγc : Continuous γ := by
    rw [hγdef]
    exact (continuous_Htilde hHc hHper).comp (continuous_id.prodMk continuous_const)
  have hγper : ∀ s : ℝ, γ (s + 1) = ((γ s).1 + m * p, (γ s).2) := by
    intro s
    have h := Htilde_add_one (p := (m : ℝ) * p) (H := H) hHper (s := s) (t := 0)
    have h2 : γ (s + 1) = Tmap ((m : ℝ) * p) (γ s) := by
      rw [hγdef]
      exact h
    rw [h2]
    rfl
  obtain ⟨s, t, hst⟩ := Commons.Topology.Strip.path_meets_translate hp hm hγc hγper
  have hTzmem : ∀ (k : ℤ) (q : ℝ × ℝ), q ∈ C ↔ Tz ((m:ℝ)*p) k q ∈ C :=
    fun k q => (Tz_mem_iff (p := (m:ℝ)*p) (V := C) (fun q => hCinv q) k q).symm
  have hγ_inC : ∀ s : ℝ, γ s ∈ C := by
    intro s
    have hEq : γ s = Tz ((m:ℝ)*p) ⌊s⌋ (H (s - (⌊s⌋ : ℤ), 0)) := by
      rw [hγdef]; rfl
    rw [hEq]
    refine (hTzmem ⌊s⌋ _).mp ?_
    rw [hHdef]
    exact hγ0 _
  exact hdisj (γ t) (hγ_inC t) (hst ▸ hγ_inC s)

/-- **A component with finite `T`-orbit contains a genuine `T`-crossing.**

Let `W` be `T`-invariant and open, `z ∈ W`, and let the component `C = connectedComponentIn W z` be
invariant under the `k`-fold shift for some `k ≥ 2`.  Then `C` contains a point joined to its
translate *inside* `C`.

This is the component-level form of `period_statement`: the contrapositive says that a component of a
`T`-invariant open set which contains no `T`-crossing must have infinite `T`-orbit, i.e. its
`T`-orbit is `1` or `∞`. -/
theorem component_crossing_of_period {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (hWop : IsOpen W) {z : ℝ × ℝ} (hz : z ∈ W)
    {k : ℕ} (hk : 2 ≤ k)
    (hper : ∀ q : ℝ × ℝ, q ∈ connectedComponentIn W z ↔
      ((q.1 + (k : ℝ) * p, q.2) ∈ connectedComponentIn W z)) :
    ∃ q ∈ connectedComponentIn W z,
      JoinedIn (connectedComponentIn W z) q (Tmap p q) := by
  haveI : LocallyPathConnectedSpace (ℝ × ℝ) := inferInstance
  have hCop : IsOpen (connectedComponentIn W z) := hWop.connectedComponentIn
  have hCconn : IsConnected (connectedComponentIn W z) :=
    ⟨⟨z, mem_connectedComponentIn hz⟩, isPreconnected_connectedComponentIn⟩
  have hnot := Commons.Topology.Strip.period_statement (p := p) hp hk hCop hCconn hper
  push Not at hnot
  obtain ⟨q, hqC, hTqC⟩ := hnot
  have hpc : IsPathConnected (connectedComponentIn W z) :=
    (hCop.isConnected_iff_isPathConnected).mp hCconn
  exact ⟨q, hqC, hpc.joinedIn q hqC (Tmap p q) hTqC⟩

/-- **No crossing ⟹ infinite `T`-orbit.**  The contrapositive of `component_crossing_of_period`,
i.e. the "orbit is `1` or `∞`" statement in the form in which the crux's failure hypothesis is
stated: if a component `C = connectedComponentIn W z` of a `T`-invariant open set `W` contains no
point joined to its translate *inside* `C`, then no non-trivial `Tz`-translate of a point of `C` lies
in `C`. -/
theorem orbit_infinite_of_no_crossing {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (hWop : IsOpen W) {z : ℝ × ℝ} (hz : z ∈ W)
    (hnocross : ¬ ∃ q ∈ connectedComponentIn W z,
      JoinedIn (connectedComponentIn W z) q (Tmap p q)) :
    ∀ k : ℤ, k ≠ 0 → ∀ q ∈ connectedComponentIn W z, Tz p k q ∉ connectedComponentIn W z := by
  intro k hk q hq hqk
  have h2 : Tz p k q ∈ connectedComponentIn W (Tz p k z) := by
    rw [← Tz_image_connectedComponentIn hW k hz]
    exact ⟨q, hq, rfl⟩
  have heq : connectedComponentIn W (Tz p k z) = connectedComponentIn W z :=
    (connectedComponentIn_eq h2).trans (connectedComponentIn_eq hqk).symm
  have hcomp : Tz p k '' connectedComponentIn W z = connectedComponentIn W z := by
    rw [Tz_image_connectedComponentIn hW k hz, heq]
  have hcross : ∃ q' ∈ connectedComponentIn W z,
      JoinedIn (connectedComponentIn W z) q' (Tmap p q') := by
    rcases eq_or_ne k 1 with h1 | h1
    · subst h1
      have hTz1 : Tz p (1 : ℤ) = Tmap p := by
        funext x
        simp [Tz, Tmap]
      rw [hTz1] at hcomp
      exact (component_invariant_iff_exists_crossing hW hWop hz).mp hcomp
    · rcases eq_or_ne k (-1) with hm1 | hm1
      · subst hm1
        have hT : Tmap p '' connectedComponentIn W z = connectedComponentIn W z := by
          have h3 : Tmap p '' (Tz p (-1) '' connectedComponentIn W z)
              = Tmap p '' connectedComponentIn W z := by rw [hcomp]
          rw [← Set.image_comp] at h3
          have hid : (Tmap p ∘ Tz p (-1)) = id := by
            funext x
            show Tmap p (Tz p (-1) x) = x
            rw [Tmap_Tz]
            simp
          rw [hid, Set.image_id] at h3
          exact h3.symm
        exact (component_invariant_iff_exists_crossing hW hWop hz).mp hT
      · set m : ℕ := k.natAbs with hmdef
        have hmcast : ((m : ℤ)) = k ∨ ((m : ℤ)) = -k := by
          rw [hmdef]
          rcases Int.natAbs_eq k with h | h
          · exact Or.inl h.symm
          · exact Or.inr (by rw [h]; simp)
        have hm2 : 2 ≤ m := by
          have h1' : 2 ≤ k ∨ k ≤ -2 := by omega
          rw [hmdef]
          rcases h1' with h | h
          · have hc : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg (by omega)
            omega
          · rw [← Int.natAbs_neg k]
            have hc : ((-k).natAbs : ℤ) = -k := Int.natAbs_of_nonneg (by omega)
            omega
        have hmcomp : Tz p ((m : ℤ)) '' connectedComponentIn W z = connectedComponentIn W z := by
          rcases hmcast with hcast | hcast
          · rw [hcast]; exact hcomp
          · rw [hcast]
            have h3 : Tz p (-k) '' (Tz p k '' connectedComponentIn W z)
                = Tz p (-k) '' connectedComponentIn W z := by rw [hcomp]
            rw [← Set.image_comp] at h3
            have hid : (Tz p (-k) ∘ Tz p k) = id := by
              funext x
              show Tz p (-k) (Tz p k x) = x
              rw [← Tz_add, neg_add_cancel, Tz_zero]
            rw [hid, Set.image_id] at h3
            exact h3.symm
        have hinj : Function.Injective (Tz p ((m : ℤ))) := by
          intro x y hxy
          have hc := congrArg (fun w => Tz p (-(m : ℤ)) w) hxy
          simpa [← Tz_add, neg_add_cancel, Tz_zero] using hc
        have hmem : ∀ q' : ℝ × ℝ,
            Tz p ((m : ℤ)) q' ∈ connectedComponentIn W z ↔ q' ∈ connectedComponentIn W z := by
          intro q'
          constructor
          · intro h
            rw [← hmcomp] at h
            obtain ⟨q'', hq'', hqq''⟩ := h
            have hqq : q'' = q' := hinj hqq''
            rwa [hqq] at hq''
          · intro h
            rw [← hmcomp]
            exact ⟨q', h, rfl⟩
        have hper : ∀ q' : ℝ × ℝ, q' ∈ connectedComponentIn W z ↔
            ((q'.1 + (m : ℝ) * p, q'.2) ∈ connectedComponentIn W z) := by
          intro q'
          have hTz : Tz p ((m : ℤ)) q' = ((q'.1 + (m : ℝ) * p, q'.2)) := rfl
          rw [← hTz]
          exact (hmem q').symm
        exact component_crossing_of_period hp hW hWop hz hm2 hper
  exact hnocross hcross

/-- **The monodromy degree set of a `T`-invariant set at a point.**

For a `T`-invariant `W` and `z ∈ W`, the *degrees* `k ∈ ℤ` for which `z` can be joined to `T^k z`
inside `W` form an additive subgroup of `ℤ` (`retDeg_zero_mem`, `retDeg_add_mem`, `retDeg_neg_mem`);
equivalently, the fibre of the covering `W → W/T` over the class of `z` is a coset of this
subgroup. -/
def retDeg (p : ℝ) (W : Set (ℝ × ℝ)) (z : ℝ × ℝ) : Set ℤ :=
  {k : ℤ | JoinedIn W z (Tz p k z)}

lemma retDeg_zero_mem {p : ℝ} {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    {z : ℝ × ℝ} (hz : z ∈ W) : (0 : ℤ) ∈ retDeg p W z := by
  rw [retDeg, Set.mem_setOf_eq, Tz_zero]
  exact JoinedIn.refl hz

lemma retDeg_add_mem {p : ℝ} {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    {z : ℝ × ℝ} {k l : ℤ} (hk : k ∈ retDeg p W z) (hl : l ∈ retDeg p W z) :
    k + l ∈ retDeg p W z := by
  rw [retDeg, Set.mem_setOf_eq] at hk hl ⊢
  exact joinedIn_Tz_add hW hk hl

lemma retDeg_neg_mem {p : ℝ} {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    {z : ℝ × ℝ} {k : ℤ} (hk : k ∈ retDeg p W z) : -k ∈ retDeg p W z := by
  rw [retDeg, Set.mem_setOf_eq] at hk ⊢
  exact joinedIn_Tz_neg hW hk

@[simp] lemma mem_retDeg {p : ℝ} {W : Set (ℝ × ℝ)} {z : ℝ × ℝ} {k : ℤ} :
    k ∈ retDeg p W z ↔ JoinedIn W z (Tz p k z) := Iff.rfl

/-- **The monodromy subgroup is constant on path components.**  If `x, y ∈ W` are joined inside a
`T`-invariant `W`, then `retDeg p W x = retDeg p W y`: the degree set is a *stabilizer*, so it is
carried unchanged along any path in `W`.

This is the base-point transport of the Mayer–Vietoris layer: transporting the non-trivial monodromy
of `VA` (from `hwindA`) and of `VB` (from `hwindB`) to a common base point is exactly what the
obligation needs, and here is the part of that transport that is available for free — conjugation by
the connecting path. -/
theorem retDeg_eq_of_joinedIn {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {x y : ℝ × ℝ} (h : JoinedIn W x y) :
    retDeg p W x = retDeg p W y := by
  ext k
  rw [mem_retDeg, mem_retDeg]
  constructor
  · intro hk
    exact h.symm.trans (hk.trans (joinedIn_Tz hW k h))
  · intro hk
    exact h.trans (hk.trans (joinedIn_Tz hW k h.symm))

/-- **The monodromy subgroup is invariant under the deck transformation.**  Translating the base
point by `Tz p j` does not change the degree set. -/
theorem retDeg_Tz {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (j : ℤ) (z : ℝ × ℝ) :
    retDeg p W (Tz p j z) = retDeg p W z := by
  ext k
  rw [mem_retDeg, mem_retDeg]
  constructor
  · intro hk
    have h := joinedIn_Tz hW (-j) hk
    have e1 : Tz p (-j) (Tz p j z) = z := by rw [← Tz_add, neg_add_cancel, Tz_zero]
    have e2 : Tz p (-j) (Tz p k (Tz p j z)) = Tz p k z := by
      rw [← Tz_add, ← Tz_add]
      congr 1
      ring
    rwa [e1, e2] at h
  · intro hk
    have h := joinedIn_Tz hW j hk
    have e2 : Tz p j (Tz p k z) = Tz p k (Tz p j z) := by
      rw [← Tz_add, ← Tz_add]
      congr 1
      ring
    rwa [e2] at h

/-- **The monodromy form of the crux.**  `1` lies in the degree set of `W` at `z` exactly when `z`
is an *essential* point of `W`, i.e. when `z` is joined to its own translate `T z` inside `W`.
Hence the conclusion of `crux_Z_meet` is precisely: at a common point `z ∈ VA ∩ VB` the two degree
sets of `VA` and of `VB` share the element `1`. -/
lemma mem_retDeg_one_iff {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {z : ℝ × ℝ} (hz : z ∈ W) :
    (1 : ℤ) ∈ retDeg p W z ↔ z ∈ Ess p W := by
  rw [mem_retDeg, mem_Ess]
  have h1 : Tz p (1 : ℤ) z = Tmap p z := by simp [Tz, Tmap]
  rw [h1]
  exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩

/-- **Monotonicity of the degree set.**  A join inside `W` is a join inside any `V ⊇ W`. -/
lemma retDeg_mono {p : ℝ} {W V : Set (ℝ × ℝ)} (hWV : W ⊆ V) {z : ℝ × ℝ} :
    retDeg p W z ⊆ retDeg p V z := by
  intro k hk
  rw [mem_retDeg] at hk ⊢
  exact hk.mono hWV

/-- **The two cosets of the crux.**  At a point `z` of `VA ∩ VB` the degree set of the intersection
is contained in the intersection of the two degree sets contributed by `VA` and by `VB`.  The crux
says that this sandwich is not sufficient on its own: the two larger degree sets share the element
`1` at a suitable `z` (`hwindA`, `hwindB`), while the conclusion demands `1 ∈ retDeg p (VA ∩ VB) ·`. -/
lemma retDeg_inter_subset {p : ℝ} {VA VB : Set (ℝ × ℝ)} {z : ℝ × ℝ} :
    retDeg p (VA ∩ VB) z ⊆ retDeg p VA z ∩ retDeg p VB z :=
  Set.subset_inter (retDeg_mono Set.inter_subset_left) (retDeg_mono Set.inter_subset_right)

/-! ### The monodromy layer, and exactly where the crux sits in it (session 25)

For a `T`-invariant `W` and `z ∈ W`, `retDeg p W z = {k : ℤ | z ~ T^k z in W}` is an additive
subgroup of `ℤ` (closure under `0`, `+`, `−` is `retDeg_zero_mem`, `retDeg_add_mem`,
`retDeg_neg_mem`), and `mem_retDeg_one_iff` identifies the crux's notion of an essential point with
the membership `1 ∈ retDeg p W z`:

  `z ∈ Ess p W ↔ (1 : ℤ) ∈ retDeg p W z`.

So the crux says: at a common point `z ∈ VA ∩ VB`, the two degree sets — the "two cosets" — share
the element `1`.  What is *formal* is only the monotonicity `retDeg_inter_subset`:
`retDeg p (VA ∩ VB) z ⊆ retDeg p VA z ∩ retDeg p VB z`, i.e. the degree set of the intersection is
*smaller* than either.  Going the other way — from `1 ∈ retDeg p VA z` and `1 ∈ retDeg p VB z` at a
common `z` (which is what `hwindA`/`hwindB` provide, via their two `T`-crossings) to
`1 ∈ retDeg p (VA ∩ VB) z` (the crux) — is exactly the Mayer–Vietoris input, and it is the remaining
gap of the file.  Nothing about the subgroup structure alone can supply it (the inclusion goes the
wrong way); the missing ingredient is the *existence* of a common point where both degrees are `1`,
and that is what the homological argument produces. -/


/-- **Existence of an integer translate in one period.** -/
lemma exists_add_int_mul_mem_Icc {p : ℝ} (hp : 0 < p) (s : ℝ) :
    ∃ k : ℤ, s + (k : ℝ) * p ∈ Set.Icc (0:ℝ) p := by
  refine ⟨-⌊s / p⌋, ?_, ?_⟩
  · have hle : (⌊s / p⌋ : ℝ) * p ≤ s := by
      have h1 : (⌊s / p⌋ : ℝ) ≤ s / p := Int.floor_le (s / p)
      have h2 := mul_le_mul_of_nonneg_right h1 hp.le
      rwa [div_mul_cancel₀ s (ne_of_gt hp)] at h2
    have hcast : ((-⌊s / p⌋ : ℤ) : ℝ) = -((⌊s / p⌋ : ℤ) : ℝ) := by push_cast; ring
    rw [hcast]
    nlinarith [hle]
  · have hlt : s < ((⌊s / p⌋ : ℝ) + 1) * p := by
      have h1 : s / p < (⌊s / p⌋ : ℝ) + 1 := Int.lt_floor_add_one (s / p)
      have h2 := (div_lt_iff₀ hp).mp h1
      linarith [h2]
    have hcast : ((-⌊s / p⌋ : ℤ) : ℝ) = -((⌊s / p⌋ : ℤ) : ℝ) := by push_cast; ring
    rw [hcast]
    nlinarith [hlt]

/-- **Reduction to one period.**  For a `T`-invariant set `V`, whether *some* point of the row
through `t` misses `V` is decided on a single period `[0,p]`. -/
lemma exists_rowMap_notMem_iff_Icc {p : ℝ} (hp : 0 < p) {V : Set (ℝ × ℝ)}
    (hperV : ∀ q : ℝ × ℝ, q ∈ V ↔ Tmap p q ∈ V)
    {γA γB : ℝ → ℝ × ℝ}
    (hAper : ∀ s : ℝ, γA (s + p) = Tmap p (γA s))
    (hBper : ∀ s : ℝ, γB (s + p) = Tmap p (γB s)) (t : ℝ) :
    (∃ s : ℝ, rowMap γA γB s t ∉ V) ↔
      (∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ V) := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := exists_add_int_mul_mem_Icc hp s
    refine ⟨s + (k : ℝ) * p, hk, ?_⟩
    rw [rowMap_add_int hAper hBper s t k]
    intro hmem
    exact hs ((Tz_mem_iff hperV k (rowMap γA γB s t)).mp hmem)
  · rintro ⟨s, -, h⟩
    exact ⟨s, h⟩

/-- **Rows lie in the strip.** -/
lemma rowMap_mem_strip {a b : ℝ} {γA γB : ℝ → ℝ × ℝ}
    (hA : ∀ s : ℝ, γA s ∈ stripS a b) (hB : ∀ s : ℝ, γB s ∈ stripS a b) (s t : ℝ) :
    rowMap γA γB s t ∈ stripS a b :=
  (convex_stripS a b) (hA s) (hB s)
    (a := 1 - clim t) (b := clim t)
    (by linarith [(clim_mem t).2]) (by linarith [(clim_mem t).1]) (by ring)

/-- **A good row closes the crux.**  If the row through `t` lies entirely in `VA ∩ VB`, then it is
a genuine `T`-crossing inside `VA ∩ VB`, so its initial point is an essential point of both `VA`
and `VB`. -/
theorem crux_of_good_row {p : ℝ}
    {VA VB : Set (ℝ × ℝ)} (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    {γA γB : ℝ → ℝ × ℝ} (hAc : Continuous γA) (hBc : Continuous γB)
    (hAper : ∀ s : ℝ, γA (s + p) = Tmap p (γA s))
    (hBper : ∀ s : ℝ, γB (s + p) = Tmap p (γB s))
    (t : ℝ) (hgood : ∀ s : ℝ, rowMap γA γB s t ∈ VA ∩ VB) :
    ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB := by
  have hmk : Continuous fun u : Set.Icc (0:ℝ) 1 => (p * (u : ℝ), t) :=
    Continuous.prodMk (continuous_const.mul continuous_subtype_val) continuous_const
  have hcont : Continuous fun u : Set.Icc (0:ℝ) 1 => rowMap γA γB (p * (u : ℝ)) t :=
    (continuous_rowMap hAc hBc).comp hmk
  have hsrc : rowMap γA γB (p * ((0 : Set.Icc (0:ℝ) 1) : ℝ)) t = rowMap γA γB 0 t := by
    simp
  have htgt : rowMap γA γB (p * ((1 : Set.Icc (0:ℝ) 1) : ℝ)) t = Tmap p (rowMap γA γB 0 t) := by
    have h := rowMap_equivariant (p := p) hAper hBper 0 t
    simpa using h
  refine ⟨rowMap γA γB 0 t, ⟨(hgood 0).1, ?_⟩, ⟨(hgood 0).2, ?_⟩⟩
  · exact ⟨{ toFun := fun u : Set.Icc (0:ℝ) 1 => rowMap γA γB (p * (u : ℝ)) t,
              continuous_toFun := hcont, source' := hsrc, target' := htgt },
      fun u => (hgood (p * (u : ℝ))).1⟩
  · exact ⟨{ toFun := fun u : Set.Icc (0:ℝ) 1 => rowMap γA γB (p * (u : ℝ)) t,
              continuous_toFun := hcont, source' := hsrc, target' := htgt },
      fun u => (hgood (p * (u : ℝ))).2⟩

/-- **Easy case of the crux.**  If one of the two `T`-crossings lies in the *other* open set, then
the row through `0` (resp. `1`) is a good row and the crux follows.  Hence the crux only has
content when `γ_A` meets `Ω \ VB` and `γ_B` meets `Ω \ VA`. -/
theorem crux_of_crossing_subset {p : ℝ}
    {VA VB : Set (ℝ × ℝ)} (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    {γA γB : ℝ → ℝ × ℝ} (hAc : Continuous γA) (hBc : Continuous γB)
    (hAper : ∀ s : ℝ, γA (s + p) = Tmap p (γA s))
    (hBper : ∀ s : ℝ, γB (s + p) = Tmap p (γB s))
    (hA : ∀ s : ℝ, γA s ∈ VA) (hB : ∀ s : ℝ, γB s ∈ VB)
    (hcase : (∀ s : ℝ, γA s ∈ VB) ∨ (∀ s : ℝ, γB s ∈ VA)) :
    ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB := by
  rcases hcase with h | h
  · refine crux_of_good_row hperA hperB hAc hBc hAper hBper 0 fun s => ?_
    rw [rowMap_zero]
    exact ⟨hA s, h s⟩
  · refine crux_of_good_row hperA hperB hAc hBc hAper hBper 1 fun s => ?_
    rw [rowMap_one]
    exact ⟨h s, hB s⟩

/-! ### One-period form, and closedness of the set of bad parameters

Only one period `[0,p]` of a row matters (the row is `T`-closed), so the good-row criterion can be
stated with an interval hypothesis — this is the form in which the parameter set is *compact* and
hence the "bad" set of parameters is closed. -/

/-- **A good row on one period closes the crux.**  If the part of the row through `t` over `[0,p]`
lies in `VA ∩ VB` then that part is already a `T`-crossing inside `VA ∩ VB`. -/
theorem crux_of_good_row_Icc {p : ℝ} (hp : 0 < p)
    {VA VB : Set (ℝ × ℝ)} (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    {γA γB : ℝ → ℝ × ℝ} (hAc : Continuous γA) (hBc : Continuous γB)
    (hAper : ∀ s : ℝ, γA (s + p) = Tmap p (γA s))
    (hBper : ∀ s : ℝ, γB (s + p) = Tmap p (γB s))
    (t : ℝ) (hgood : ∀ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∈ VA ∩ VB) :
    ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (0:ℝ) p := ⟨le_rfl, hp.le⟩
  have hmk : Continuous fun u : Set.Icc (0:ℝ) 1 => (p * (u : ℝ), t) :=
    Continuous.prodMk (continuous_const.mul continuous_subtype_val) continuous_const
  have hcont : Continuous fun u : Set.Icc (0:ℝ) 1 => rowMap γA γB (p * (u : ℝ)) t :=
    (continuous_rowMap hAc hBc).comp hmk
  have hsrc : rowMap γA γB (p * ((0 : Set.Icc (0:ℝ) 1) : ℝ)) t = rowMap γA γB 0 t := by simp
  have htgt : rowMap γA γB (p * ((1 : Set.Icc (0:ℝ) 1) : ℝ)) t = Tmap p (rowMap γA γB 0 t) := by
    have h := rowMap_equivariant (p := p) hAper hBper 0 t
    simpa using h
  have hmemp : ∀ u : Set.Icc (0:ℝ) 1, p * (u : ℝ) ∈ Set.Icc (0:ℝ) p := fun u =>
    ⟨mul_nonneg hp.le u.2.1, by nlinarith [u.2.2, hp.le]⟩
  refine ⟨rowMap γA γB 0 t, ⟨(hgood 0 h0mem).1, ?_⟩, ⟨(hgood 0 h0mem).2, ?_⟩⟩
  · exact ⟨{ toFun := fun u : Set.Icc (0:ℝ) 1 => rowMap γA γB (p * (u : ℝ)) t,
              continuous_toFun := hcont, source' := hsrc, target' := htgt },
      fun u => (hgood (p * (u : ℝ)) (hmemp u)).1⟩
  · exact ⟨{ toFun := fun u : Set.Icc (0:ℝ) 1 => rowMap γA γB (p * (u : ℝ)) t,
              continuous_toFun := hcont, source' := hsrc, target' := htgt },
      fun u => (hgood (p * (u : ℝ)) (hmemp u)).2⟩

/-- **The set of bad parameters is closed.**  The parameters `t ∈ [0,1]` for which one period of the
row through `t` misses the open set `VA` form a closed set (it is the projection of a closed subset
of the compact box `[0,p] × [0,1]`). -/
lemma isClosed_badRow {p : ℝ} (hp : 0 < p) {VA : Set (ℝ × ℝ)} (hVA : IsOpen VA)
    {γA γB : ℝ → ℝ × ℝ} (hAc : Continuous γA) (hBc : Continuous γB) :
    IsClosed {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧
      ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VA} := by
  have hopen : IsOpen ((fun q : ℝ × ℝ => rowMap γA γB q.1 q.2) ⁻¹' VA) :=
    hVA.preimage (continuous_rowMap hAc hBc)
  have hclosed : IsClosed ({q : ℝ × ℝ | q.1 ∈ Set.Icc (0:ℝ) p ∧ q.2 ∈ Set.Icc (0:ℝ) 1} ∩
      ((fun q : ℝ × ℝ => rowMap γA γB q.1 q.2) ⁻¹' VA)ᶜ) :=
    (isClosed_Icc.prod isClosed_Icc).inter hopen.isClosed_compl
  have hKc : IsCompact ({q : ℝ × ℝ | q.1 ∈ Set.Icc (0:ℝ) p ∧ q.2 ∈ Set.Icc (0:ℝ) 1} ∩
      ((fun q : ℝ × ℝ => rowMap γA γB q.1 q.2) ⁻¹' VA)ᶜ) :=
    IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) hclosed
      (by rintro q ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩)
  have himg : (Prod.snd : ℝ × ℝ → ℝ) ''
        ({q : ℝ × ℝ | q.1 ∈ Set.Icc (0:ℝ) p ∧ q.2 ∈ Set.Icc (0:ℝ) 1} ∩
          ((fun q : ℝ × ℝ => rowMap γA γB q.1 q.2) ⁻¹' VA)ᶜ)
      = {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧
          ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VA} := by
    ext t
    constructor
    · rintro ⟨q, ⟨⟨hq1, hq2⟩, hq3⟩, rfl⟩
      exact ⟨hq2, q.1, hq1, hq3⟩
    · rintro ⟨ht, s, hs, hne⟩
      exact ⟨(s, t), ⟨⟨hs, ht⟩, hne⟩, rfl⟩
  rw [← himg]
  exact (hKc.image continuous_snd).isClosed

/-- **If no row is good then some row meets both complementary closed sets.**  Suppose every row
fails to lie in `VA ∩ VB`, and suppose moreover that the two *endpoint* rows are genuinely
one-sided: the row through `0` (i.e. `γ_A`) meets `Ω \ VB` and the row through `1` (i.e. `γ_B`)
meets `Ω \ VA`.  Then there is a parameter `t ∈ [0,1]` whose row meets both `Ω \ VA` and
`Ω \ VB`.

This is the point-set half of the crux: it uses only that the parameter set is an interval (so the
two closed sets of "bad parameters" for `VA` and for `VB`, which together cover `[0,1]`, must
intersect), and no homology.  The remaining content after this lemma is that the obtained row
cannot meet both complements (or, equivalently, the crux itself). -/
theorem exists_row_meets_both {p : ℝ} (hp : 0 < p)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    {γA γB : ℝ → ℝ × ℝ} (hAc : Continuous γA) (hBc : Continuous γB)
    (hall : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VA ∩ VB)
    (hAZero : ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s 0 ∉ VB)
    (hBOne : ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s 1 ∉ VA) :
    ∃ t ∈ Set.Icc (0:ℝ) 1,
      (∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VA) ∧
      (∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VB) := by
  set A₁ : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) 1 ∧
    ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VA} with hA₁
  set A₂ : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) 1 ∧
    ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VB} with hA₂
  have hc₁ : IsClosed A₁ := by rw [hA₁]; exact isClosed_badRow hp hVA hAc hBc
  have hc₂ : IsClosed A₂ := by rw [hA₂]; exact isClosed_badRow hp hVB hAc hBc
  have hsub : Set.Icc (0:ℝ) 1 ⊆ A₁ ∪ A₂ := by
    intro t ht
    obtain ⟨s, hs, hne⟩ := hall t ht
    rcases not_and_or.mp hne with h | h
    · exact Or.inl ⟨ht, s, hs, h⟩
    · exact Or.inr ⟨ht, s, hs, h⟩
  have hzero : (0 : ℝ) ∈ A₂ := ⟨⟨le_rfl, zero_le_one⟩, hAZero⟩
  have hone : (1 : ℝ) ∈ A₁ := ⟨⟨zero_le_one, le_rfl⟩, hBOne⟩
  have hne : (Set.Icc (0:ℝ) 1 ∩ (A₁ ∩ A₂)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hsplit := (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_Icc (a := (0:ℝ)) (b := 1))) A₁ A₂ hc₁ hc₂ hsub hemp
    rcases hsplit with h | h
    · have hmem : (0 : ℝ) ∈ Set.Icc (0:ℝ) 1 ∩ (A₁ ∩ A₂) :=
        ⟨⟨le_rfl, zero_le_one⟩, h ⟨le_rfl, zero_le_one⟩, hzero⟩
      rw [hemp] at hmem
      exact absurd hmem (Set.notMem_empty 0)
    · have hmem : (1 : ℝ) ∈ Set.Icc (0:ℝ) 1 ∩ (A₁ ∩ A₂) :=
        ⟨⟨zero_le_one, le_rfl⟩, hone, h ⟨zero_le_one, le_rfl⟩⟩
      rw [hemp] at hmem
      exact absurd hmem (Set.notMem_empty 1)
  obtain ⟨t, ht, htA⟩ := hne
  exact ⟨t, ht, htA.1.2, htA.2.2⟩

/-- **The crux reduces to "some row meets both complements".**

Let `VA, VB` be `T`-invariant, `γ_A ⊆ VA`, `γ_B ⊆ VB` be two `T`-crossings (written in their
periodic form).  If the crux's conclusion fails, then — combining

* `crux_of_good_row_Icc` (no row can lie in `VA ∩ VB` over a period) with
* `crux_of_crossing_subset` (the easy case fails, so the endpoint rows are one-sided) and
* `exists_rowMap_notMem_iff_Icc` (the one-period reduction of the `T`-invariant sets `VA`, `VB`),

the dichotomy `exists_row_meets_both` applies and produces a parameter whose row meets *both*
complements `Ω \ VA` and `Ω \ VB`.

So the whole crux is reduced to the impossibility of that configuration — which is where
Denne's `prop:homology` (the Mayer–Vietoris surjectivity) enters. -/
theorem not_crux_imp_exists_row_meets_both {p : ℝ} (hp : 0 < p)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    {γA γB : ℝ → ℝ × ℝ} (hAc : Continuous γA) (hBc : Continuous γB)
    (hAper : ∀ s : ℝ, γA (s + p) = Tmap p (γA s))
    (hBper : ∀ s : ℝ, γB (s + p) = Tmap p (γB s))
    (hA : ∀ s : ℝ, γA s ∈ VA) (hB : ∀ s : ℝ, γB s ∈ VB)
    (hnot : ¬ ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB) :
    ∃ t ∈ Set.Icc (0:ℝ) 1,
      (∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VA) ∧
      (∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VB) := by
  classical
  have hnogood : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s t ∉ VA ∩ VB := by
    intro t _
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hnot (crux_of_good_row_Icc hp hperA hperB hAc hBc hAper hBper t hcon)
  have hAZero : ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s 0 ∉ VB := by
    by_contra hcon
    have hnotex : ¬ ∃ s : ℝ, rowMap γA γB s 0 ∉ VB :=
      (exists_rowMap_notMem_iff_Icc hp hperB hAper hBper 0).not.mpr hcon
    have hAin : ∀ s : ℝ, γA s ∈ VB := fun s => by
      have hmem : rowMap γA γB s 0 ∈ VB :=
        not_not.mp fun hs => hnotex ⟨s, hs⟩
      simpa [rowMap_zero] using hmem
    exact hnot (crux_of_crossing_subset hperA hperB hAc hBc hAper hBper hA hB (Or.inl hAin))
  have hBOne : ∃ s ∈ Set.Icc (0:ℝ) p, rowMap γA γB s 1 ∉ VA := by
    by_contra hcon
    have hnotex : ¬ ∃ s : ℝ, rowMap γA γB s 1 ∉ VA :=
      (exists_rowMap_notMem_iff_Icc hp hperA hAper hBper 1).not.mpr hcon
    have hBin : ∀ s : ℝ, γB s ∈ VA := fun s => by
      have hmem : rowMap γA γB s 1 ∈ VA :=
        not_not.mp fun hs => hnotex ⟨s, hs⟩
      simpa [rowMap_one] using hmem
    exact hnot (crux_of_crossing_subset hperA hperB hAc hBc hAper hBper hA hB (Or.inr hBin))
  exact exists_row_meets_both hp hVA hVB hAc hBc hnogood hAZero hBOne

/-! ### State of the row/column branch (session 21)

Proved here, in order, and all usable downstream:

* `clim` / `rowMap` (+ `continuous_rowMap`, `rowMap_equivariant`, `rowMap_mem_strip`,
  `rowMap_zero`, `rowMap_one`): the affine *row map* is continuous, every row is a `T`-crossing that
  stays in the strip, and `rowMap · 0 = γ_A`, `rowMap · 1 = γ_B`;
* `crux_of_good_row` and `crux_of_good_row_Icc`: a row lying in `VA ∩ VB` (over a period) is a
  `T`-crossing inside `VA ∩ VB`, so the crux holds;
* `crux_of_crossing_subset`: **the easy case** — if one of the two `T`-crossings lies in the other
  open set, the crux holds;
* `isClosed_badRow`: the parameters `t ∈ [0,1]` whose row (over a period) misses an *open* set form
  a closed set (projection of a closed subset of the compact box `[0,p] × [0,1]`);
* `exists_row_meets_both`: **the dichotomy** — if no row is good and the two endpoint rows are
  one-sided, then some row meets both `Ω \ VA` and `Ω \ VB`.

* `prod_add_mul_nat_of_period`, `prod_add_mul_int_of_period`, `rowMap_add_int`: the
  *integer-periodicity reduction* — `rowMap γA γB (s + n * p) t = Tz p n (rowMap γA γB s t)` for
  `n : ℤ` (proved by iterating `rowMap_equivariant` through the general lemmas on `ℝ → ℝ × ℝ`;
  these two are reusable independently of this file).

* `Tz_mem_iff`: the `T`-invariance of a set is inherited by all integer powers `Tz p n`;
* `exists_add_int_mul_mem_Icc`: every real has an integer translate in `[0,p]` (Archimedean);
* `exists_rowMap_notMem_iff_Icc`: the **one-period reduction** for a `T`-invariant set `V`,
  `(∃ s, rowMap · s t ∉ V) ↔ (∃ s ∈ [0,p], rowMap · s t ∉ V)`;
* `not_crux_imp_exists_row_meets_both`: **the reduction chain is closed at the point-set level** —
  if the crux's conclusion fails, then the easy case fails (so the endpoint rows are one-sided,
  by the one-period reduction) and no row is good (by `crux_of_good_row_Icc`), so
  `exists_row_meets_both` produces `t ∈ [0,1]` whose row meets *both* `Ω \ VA` and `Ω \ VB`.

The entire crux is therefore reduced to the impossibility of that last configuration: a single row
which is a `T`-crossing yet meets both complements of the two open sets.  That is exactly the point
at which Denne's `prop:homology` — the Mayer–Vietoris surjectivity
`H₁(S \ (A ∪ B)) → H₁(S \ A) ⊕ H₁(S \ B) → H₁(S)`, i.e. an elementary substitute for it — is
required, and it is the remaining gap of the file. -/

/-! ## Sessions 12–16 summary of the state of the reduction

**Session 12 (sharp reduction).**  The crux follows from the existence of a continuous `p`-periodic
`u` with `(s, u s) ∈ VA ∩ VB` for every real `s` (`crux_of_periodic_graph`), and the target follows
from that in one line (`annulus_essential_intersection_of_periodic_graph`); the engine is
`graph_periodic_translate`.

**Session 13 (crossing dichotomy).**  With `α ⊆ VA`, `β ⊆ VB` the two `T`-crossings and
`H (s,t) = (1-t) α s + t β s`, put `τ s` for the first exit from `VA` and `σ s` for the last entry to
`VB` along the segment (both `p`-periodic).  The exit curve `c s = H (s,τ s)` is a `T`-crossing in
`VB` and the entry curve `d s = H (s,σ s)` is one in `VA`; if they meet then Janiszewski finishes
the crux (`joinedIn_inter_of_joinedIn_strip`); if the order of `τ` and `σ` flips then they meet.  So
only two configurations remain: `τ > σ` everywhere, or `τ < σ` everywhere.

**Session 13b/16 (the `τ > σ` regime: proved).**  `isPreconnected_of_convex_fibres` +
`translate_path_of_periodic_corridor` show that any open `T`-invariant `G ⊆ VA ∩ VB` with nonempty
convex fibres closes the crux; and `corridor_isOpen_of_extent_bounds` proves that the corridor
`{q : σ q.1 < q.2 < τ q.1}` is open from the two tube-lemma computations, which is exactly the
instantiation `lo := σ`, `hi := τ`.  (Session 15 corrected the semicontinuities: `τ` is lower and
`σ` upper semicontinuous.)

**Sessions 13c/14 (the `τ < σ` regime: the remaining gap).**  There the corridor `(σ,τ)` is empty
and what is needed is (Obligation O): *some* `T`-invariant family of fibre-components of
`VA ∩ VB` *is open* — since such a family is automatically convex-fibred and the engine finishes.
The canonical candidates are the pieces just below `τ` (`U_τ`, fibres `(α_s,τ_s)`) and just above
`σ` (`U_σ`, fibres `(σ_s,β_s)`), plus any middle family; the fibre-component toolkit of session 14c
(`fibre_window_subset_component`, `fibre_window_eq_component`,
`fibre_overlapping_windows_same_component`, `fibre_window_centres_same_component`) supplies their
nonempty convex fibres and the consistency of the window-to-component assignment.  The obstruction
is the *pinch*: gap points of a fibre can accumulate at an endpoint `{α s₀, τ s₀}` of a piece, so
openness of `D` alone cannot discharge (Obligation O). -/

/-! **SKETCH OF THE SELECTION ARGUMENT (session 18), with the case analysis the machinery now
supplies.**  In the cylinder setting the fibres are `A_s := {t : H (s,t) ∈ VA}` and
`B_s := {t : H (s,t) ∈ VB}`, with `0 ∈ A_s`, `1 ∈ B_s`, and — once the cover `VA ∪ VB = strip` is
available, as it is in the crux — `A_s ∪ B_s ⊇ [0,1]`.  The extents are

  `τ s := sSup {t : ∀ t' < t, H (s,t') ∈ VA}`  (first exit from `VA`),
  `σ s := sInf {t : ∀ t' > t, H (s,t') ∈ VB}`  (last entry to `VB`),

and everything the machinery proves about them transfers verbatim, because its inputs are exactly the
three structural facts `[0, τ s) ⊆ A_s`, `(σ s, 1] ⊆ B_s` and the two room statements.  Case by case:

| configuration | what is proved | lemma |
|---|---|---|
| `σ s < τ s` for all `s` | the corridor `{q : σ q.1 < q.2 < τ q.1}` is open | `corridor_isOpen_of_extent_bounds` |
| order of `σ`, `τ` flips | the exit curve `H (·, τ ·)` and entry curve `H (·, σ ·)` meet | (IVT on the extents) |
| `τ < σ`, `τ` continuous at `s₀` | `[t₀, τ s) ⊆ VA_s ∩ VB_s` near `s₀` | `ico_persists_of_continuous_exit` |
| `τ < σ`, `τ` up-jumps at `s₀` | same, on the low side, from the limit `τ⁻` | `ico_persists_of_upjump` + `exists_exit_room_of_tendsto` + `exists_upper_bound_of_tendsto` + `lsc_stays_above` |
| `τ < σ`, `σ` continuous at `s₀` | `(σ s, t₀] ⊆ VA_s ∩ VB_s` near `s₀` | `ioc_persists_of_continuous_entry` |
| `τ < σ`, `σ` down-jumps at `s₀` | same, mirrored | `ioc_persists_of_bounded_entry` + `exists_entry_room_of_tendsto` + `exists_lower_bound_of_tendsto` |

So the *covering* half of the selection — the fact that the fibre of `VA ∩ VB` contains a definite
interval around every point of either canonical piece, on a neighbourhood — is now fully discharged
except inside a jump range.  What the selection statement still needs, and what is deliberately
**not** attempted here, is

1. **the seam extension of `H`**: `H` is only *twisted* periodic (`H (1,t) = T (H (0,t))`), whereas
   every lemma above is a statement about a `T`-equivariant configuration on all of `ℝ`.  Extending
   `H̃ (s,t) := (Tmap p)^j (H (s - j, t))` for `s - j ∈ [0,1)` is the first step of any application of
   the table to the cylinder, and it is pure bookkeeping (well-definedness at the seam by induction
   on `j` from `hHper`, continuity by gluing);
2. **the global descent** from per-point lower semicontinuity of a canonical piece family to the
   family itself being open (parked);
3. **the pinch inside a jump range**: the points strictly inside a jump range are where the τ-piece
   family is provably *not* lower semicontinuous, so those have to be reached by the σ-side or a
   middle family (parked).

Items 2 and 3 are the two parked obligations; item 1 is the mechanical prerequisite, and it is the
next thing to write.

**Session 20: the barrier lemma and the corrected shape of the remaining gap.**

The *abstract* form of the selection problem — "`P, Q` open, `p`-periodic in `s`, `P ∪ Q = ℝ²`,
`ℝ × {0} ⊆ P`, `ℝ × {1} ⊆ Q`, and `P ∩ Q` has no `T`-crossing" — is **false**, because that datum
does not determine a homotopy `H`: the "spiral tower" `K = (ℝ × {0}) ∪ ⋃_{m∈ℤ} W_m ∪ (ℝ × {1})`
with `W_m = {x = log (y/(1-y)) + m}` together with `P = ℝ² \ (ℝ × {1})`,
`Q = ℝ² \ (⋃_m W_m ∪ ℝ × {0})` satisfies all of them while `P ∩ Q` is the disjoint union of the
`T`-permuted "channels" `{g(y) + m < s < g(y) + m + 1}` and carries no `T`-crossing.  So an argument
of the shape "sweep + barrier lemma" does **not** suffice on the nose; the residual statement below
must therefore be stated for the *actual* `H` of the crux (affine interpolation of the two
`T`-crossings), whose row structure is much more rigid.

What the barrier lemma *does* give (and what is new here) is the following clean dichotomy.  Put
`K := ([0,p] × [0,1]) \ (P ∩ Q)`; by `Commons.Topology.Strip.barrier_bottom_top_of_no_left_right`
(applied to `K`, which is closed in the box, `p`-periodic and never spans), if `K` met every
left–right path in the box then `K` would contain a preconnected `C` meeting both rows `{q.2 = 0}`
and `{q.2 = 1}`.  But `K = (K ∩ Pᶜ) ⊔ (K ∩ Qᶜ)` is a disjoint union of two closed sets (here
`hcover` is used: `P ∪ Q = univ`), so such a preconnected `C` lies inside `Pᶜ` or inside `Qᶜ`, and
both alternatives are impossible because `ℝ × {0} ⊆ P` and `ℝ × {1} ⊆ Q`.  Hence the barrier lemma
supplies a left–right path `λ ⊆ P ∩ Q` from `(0,t₀)` to `(p,t₁)`.  The residual difficulty is then
exactly the *mismatch* `t₀ ≠ t₁`: closing `λ` up at the seam needs the vertical arc
`{0} × [t₀,t₁] ⊆ P ∩ Q`, which is not automatic (it fails in the spiral tower above).  This
mismatch is where the crux genuinely needs the homology argument of Denne's `prop:homology` (the
Mayer–Vietoris surjectivity `H₁(S \ (A ∪ B)) → H₁(S \ A)`); it is the same content as the
`τ/σ`-jump pinch listed above, seen from the other side.

**Sharpening of the mismatch (seam-slice dichotomy).**  In the crux, `p`-periodicity of `P ∩ Q`
(supplied by `hperA`/`hperB` together with the twisted periodicity of `H`) upgrades "closing `λ`
up" to a purely one-dimensional statement: if `t₀` and `t₁` lie in the same component of the *seam
slice* `S := {t ∈ [0,1] | interp (z_A, z_B, t) ∈ VA ∩ VB}`, then the seam path from `(0,t₀)` to
`(0,t₁)` lies in `P ∩ Q`, and concatenating `λ` with its translate closes up into a genuine
`T`-crossing in `P ∩ Q` (and hence, via `H`, in `VA ∩ VB`).  So the residual case is exactly: `t₀`
and `t₁` in *different* components of `S`; equivalently the straight segment `[z_A, z_B]` meets
`F_A ∪ F_B`.  This is as far as the point-set (barrier/Jordan) tools in the commons reach; the
remaining step is Denne's homology argument.

**Cylinder selection lemma (the remaining gap, alternative form).**

Let `P = H⁻¹ VA` and `Q = H⁻¹ VB` be the pull-backs of the two open sets along a homotopy `H` of the
cylinder which is *twisted periodic*, `H (1,t) = T (H (0,t))`, maps the bottom edge into `VA` and the
top edge into `VB` and stays inside the strip.  Then there is a continuous `u` with `u 1 = u 0` (a
"periodic" selection) whose graph lies in the overlap `P ∩ Q`.

Equivalently: the closed `1`-periodic set `K := (ℝ × [0,1]) ∖ (P ∩ Q)`, whose vertical fibres are
never all of `[0,1]`, admits a continuous periodic graph avoiding it — the point-set substitute for
Denne's `prop:homology` (Mayer–Vietoris).

**Status (session 34).**  This interface has been **removed**.  A continuous periodic selection of
that kind was a point-set substitute for Denne's `prop:homology` whose truth was never established,
and it is no longer on the critical path: `crux_Z_meet` is now proved from `mv_obligation` (the
Mayer–Vietoris obligation) via `crux_of_finite_orbit_component`, so the file's single remaining
`sorry` sits on the true gap.  All the fibre/`τ`/`σ` machinery developed on this route remains in the
file as proved material. -/
/-- **A `T`-invariant component of `VA` that misses `VB` forces `VA` to be the whole strip.**

Let `VA, VB` be open `T`-invariant subsets of the strip `Ω = stripS a b` with `VA ∪ VB = Ω`, and let
`C` be the component of a point `z ∈ VA`.  If `C ∩ VB = ∅`, then `C` is a non-empty clopen subset of
the connected strip `Ω`, hence `Ω ⊆ C ⊆ VA` and `VA = Ω`.

Equivalently: **when the crux's conclusion fails, every `T`-invariant component of `VA` meets
`VB`** (and symmetrically).  This is the "rigidity" of the no-crux case: the reason the missing
Mayer–Vietoris input cannot be replaced by a component-counting argument alone.

Proof.  `C ⊆ Ω \ VB` and `Ω \ VB ⊆ VA` (since `VA ∪ VB = Ω`), so `closure C ∩ Ω ⊆ VA ∪ (Ω∖VA)`; if
`x ∈ closure C ∩ Ω` is outside `VA` then `x ∈ VB`, and `VB` being a neighbourhood of `x` meets `C`,
contradicting `C ⊆ Ω \ VB`.  Hence `x ∈ VA`, and a path-connected neighbourhood of `x` inside the
open set `VA` meets `C`, which puts `x` in the same component as `z`. -/
theorem eq_stripS_of_component_disjoint {p a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    {z : ℝ × ℝ} (hz : z ∈ VA)
    (hdisj : connectedComponentIn VA z ∩ VB = ∅) : VA = stripS a b := by
  classical
  haveI : LocallyPathConnectedSpace (ℝ × ℝ) := inferInstance
  have hVA_sub : VA ⊆ stripS a b := by rw [← hcover]; exact subset_union_left
  have hCVA : connectedComponentIn VA z ⊆ VA := connectedComponentIn_subset VA z
  have hCΩ : connectedComponentIn VA z ⊆ stripS a b := hCVA.trans hVA_sub
  have hCopen : IsOpen (connectedComponentIn VA z) := hVA.connectedComponentIn
  have hCFB : connectedComponentIn VA z ⊆ (stripS a b) \ VB := by
    intro q hq
    refine ⟨hCΩ hq, fun hqVB => ?_⟩
    have hmem : q ∈ connectedComponentIn VA z ∩ VB := ⟨hq, hqVB⟩
    rw [hdisj] at hmem
    exact hmem
  have hclVA : closure (connectedComponentIn VA z) ∩ VA ⊆ connectedComponentIn VA z := by
    intro x hx
    obtain ⟨hxcl, hxVA⟩ := hx
    obtain ⟨N, ⟨hNnhds, hNpc⟩, hNsub⟩ :=
      (LocallyPathConnectedSpace.path_connected_basis x).mem_iff.mp (hVA.mem_nhds hxVA)
    obtain ⟨y, hyN, hyC⟩ := mem_closure_iff_nhds.mp hxcl N hNnhds
    have hjoin : JoinedIn VA y x :=
      (hNpc.joinedIn y hyN x (mem_of_mem_nhds hNnhds)).mono hNsub
    have hx' : x ∈ connectedComponentIn VA y := mem_connectedComponentIn_of_joinedIn hjoin
    have heq : connectedComponentIn VA y = connectedComponentIn VA z :=
      (connectedComponentIn_eq hyC).symm
    rwa [heq] at hx'
  have hclΩ : closure (connectedComponentIn VA z) ∩ stripS a b ⊆ connectedComponentIn VA z := by
    intro x hx
    by_cases hxVA : x ∈ VA
    · exact hclVA ⟨hx.1, hxVA⟩
    · exfalso
      have hxVB : x ∈ VB := by
        rcases hcover ▸ hx.2 with h | h
        · exact absurd h hxVA
        · exact h
      obtain ⟨w, hwVB, hwC⟩ := mem_closure_iff_nhds.mp hx.1 VB (hVB.mem_nhds hxVB)
      exact (hCFB hwC).2 hwVB
  have hsub : stripS a b ⊆ connectedComponentIn VA z ∪ (closure (connectedComponentIn VA z))ᶜ := by
    intro q hq
    by_cases hqc : q ∈ connectedComponentIn VA z
    · exact Or.inl hqc
    · exact Or.inr (fun hqcl => hqc (hclΩ ⟨hqcl, hq⟩))
  rcases (convex_stripS a b).isPreconnected.subset_or_subset hCopen
      isClosed_closure.isOpen_compl
      (Disjoint.mono_left subset_closure (disjoint_compl_right (a := closure (connectedComponentIn VA z))))
      hsub with h | h
  · exact Subset.antisymm hVA_sub (h.trans hCVA)
  · exfalso
    exact (h (hVA_sub hz)) (subset_closure (mem_connectedComponentIn hz))

/-- **Rigidity of the no-crux case: every `T`-invariant component of `VA` meets `VB`.**

If some component of `VA` missed `VB`, `eq_stripS_of_component_disjoint` forces `VA = stripS a b`,
and then `hwindB` alone produces the conclusion of the crux (the strip is convex, so the crossing
point of `VB` is joined to its translate inside the whole strip, hence inside `VA`).  So under the
failure of the crux each such component meets `VB` — and symmetrically.  This is the reduction that
isolates the missing Mayer–Vietoris input: it must show that two `T`-invariant components (one of
`VA`, one of `VB`), which can be assumed to meet the *other* set, actually meet each other. -/
theorem component_meets_of_no_crux {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z))
    (hnocrux : ¬ ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB)
    {z : ℝ × ℝ} (hz : z ∈ VA) : (connectedComponentIn VA z ∩ VB).Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hVAeq : VA = stripS a b :=
    eq_stripS_of_component_disjoint hVA hVB hperA hperB hcover hz hemp
  obtain ⟨w, hwB, hjoinB⟩ := hwindB
  have hwV : w ∈ stripS a b := by
    rw [← hcover]; exact Or.inr hwB
  have hjoinA : JoinedIn VA w (Tmap p w) := by
    rw [hVAeq]
    exact joinedIn_of_convex (convex_stripS a b) hwV (Tmap_mem_strip hwV)
  have hwVA : w ∈ VA := by rw [hVAeq]; exact hwV
  exact hnocrux ⟨w, ⟨hwVA, hjoinA⟩, ⟨hwB, hjoinB⟩⟩


/-- **The Mayer–Vietoris obligation, stated at the crux interface, and its reduction to the crux.**

*The obligation* (`hmv`): for `T`-invariant open `VA`, `VB` there is a point of `VA ∩ VB` joined
inside `VA ∩ VB` to some *positive* integer translate of itself.  This is exactly what the
Mayer–Vietoris / winding argument supplies ("some component of `VA ∩ VB` has non-zero winding",
equivalently finite `T`-orbit), and it is the only missing input: not available in Mathlib, since
van Kampen / Mayer–Vietoris for the fundamental group is not.

*The reduction* (proved here): the obligation implies the crux.  Given `q ∈ VA ∩ VB` with
`q ~ T^m q` inside `VA ∩ VB` for some `m ≥ 1`:

* `m = 1`: the crossing `q ~ T q` lies in `VA ∩ VB`, so `q ∈ Ess p VA ∩ Ess p VB`;
* `m ≥ 2`: the component `C = connectedComponentIn (VA ∩ VB) q` satisfies `T^m C = C` (by
  `Tz_image_connectedComponentIn`), so `component_crossing_of_period` produces a point of `C` joined
  to its translate inside `C ⊆ VA ∩ VB`, whence again `Ess p VA ∩ Ess p VB ≠ ∅`.

So the crux is reduced to the obligation alone — no surface topology, Jordan, or embeddeness input
remains (those were eliminated in sessions 29–33). -/
theorem crux_of_finite_orbit_component {p : ℝ} (hp : 0 < p)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hmv : ∃ q ∈ VA ∩ VB, ∃ m : ℤ, 1 ≤ m ∧ JoinedIn (VA ∩ VB) q (Tz p m q)) :
    ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB := by
  obtain ⟨q, hqW, m, hm1, hmjoin⟩ := hmv
  have hWinv : ∀ q : ℝ × ℝ, q ∈ VA ∩ VB ↔ Tmap p q ∈ VA ∩ VB := by
    intro q
    show (q ∈ VA ∧ q ∈ VB) ↔ (Tmap p q ∈ VA ∧ Tmap p q ∈ VB)
    rw [hperA q, hperB q]
  rcases eq_or_lt_of_le hm1 with h1 | h2
  · -- `m = 1`: the crossing already lies in `VA ∩ VB`
    have hmjoin' : JoinedIn (VA ∩ VB) q (Tmap p q) := by
      have h1' : m = 1 := h1.symm
      rw [h1'] at hmjoin
      simpa [Tz, Tmap] using hmjoin
    exact ⟨q, ⟨hqW.1, hmjoin'.mono Set.inter_subset_left⟩,
      ⟨hqW.2, hmjoin'.mono Set.inter_subset_right⟩⟩
  · -- `m ≥ 2`: the orbit of the component is finite, so it contains a genuine crossing
    set W : Set (ℝ × ℝ) := VA ∩ VB with hWdef
    have hqW' : q ∈ W := hqW
    have hWop : IsOpen W := hVA.inter hVB
    have hTm : Tz p m q ∈ connectedComponentIn W q := mem_connectedComponentIn_of_joinedIn hmjoin
    have hcomp : Tz p m '' connectedComponentIn W q = connectedComponentIn W q := by
      rw [Tz_image_connectedComponentIn hWinv m hqW']
      exact (connectedComponentIn_eq hTm).symm
    have hinj : Function.Injective (Tz p m) := by
      intro x y hxy
      have hc := congrArg (fun w => Tz p (-m) w) hxy
      simpa [← Tz_add, neg_add_cancel, Tz_zero] using hc
    have hmem : ∀ q' : ℝ × ℝ,
        Tz p m q' ∈ connectedComponentIn W q ↔ q' ∈ connectedComponentIn W q := by
      intro q'
      constructor
      · intro h
        rw [← hcomp] at h
        obtain ⟨q'', hq'', heq⟩ := h
        have hqq : q'' = q' := hinj heq
        rwa [hqq] at hq''
      · intro h
        rw [← hcomp]
        exact ⟨q', h, rfl⟩
    have hper' : ∀ q' : ℝ × ℝ, q' ∈ connectedComponentIn W q ↔
        ((q'.1 + ((m.toNat : ℕ) : ℝ) * p, q'.2) ∈ connectedComponentIn W q) := by
      intro q'
      have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
      have hcastR : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast hcast
      rw [hcastR]
      have hTz : Tz p m q' = ((q'.1 + (m : ℝ) * p, q'.2)) := rfl
      rw [← hTz]
      exact (hmem q').symm
    have hm2 : 2 ≤ m.toNat := by omega
    obtain ⟨q', hq'C, hjoinC⟩ :=
      component_crossing_of_period hp hWinv hWop hqW' hm2 hper'
    have hq'W : q' ∈ W := connectedComponentIn_subset W q hq'C
    have hsubL : connectedComponentIn W q ⊆ VA :=
      (connectedComponentIn_subset W q).trans Set.inter_subset_left
    have hsubR : connectedComponentIn W q ⊆ VB :=
      (connectedComponentIn_subset W q).trans Set.inter_subset_right
    exact ⟨q', ⟨hq'W.1, hjoinC.mono hsubL⟩, ⟨hq'W.2, hjoinC.mono hsubR⟩⟩

/-- **The `m = 1` instance of the Mayer–Vietoris obligation is *equivalent* to the crux.**

For `T`-invariant open `VA, VB` covering the strip `Ω = stripS a b`, the crux's conclusion
`∃ z, z ∈ Ess p VA ∧ z ∈ Ess p VB` holds **iff** some point of `VA ∩ VB` is joined to its own
`T`-translate inside `VA ∩ VB`.

* (`⟹`) a point `z ∈ Ess p VA ∩ Ess p VB` is joined to `T z` inside `VA` and inside `VB`, so
  Janiszewski in the simply connected strip (`joinedIn_inter_of_joinedIn_strip`) puts the join
  inside `VA ∩ VB`;
* (`⟸`) a join inside `VA ∩ VB` is a join inside each of `VA`, `VB`.

So the obligation of `mv_obligation` is exactly the crux with the conclusion moved from `Ess` to
`VA ∩ VB` — and by `component_crossing_of_period` the same holds for the `m ≥ 2` instances. -/
theorem mv_one_iff_crux {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b) :
    (∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB) ↔
      (∃ q ∈ VA ∩ VB, JoinedIn (VA ∩ VB) q (Tmap p q)) := by
  constructor
  · rintro ⟨z, hzA, hzB⟩
    have hzW : z ∈ VA ∩ VB := ⟨ess_subset p VA hzA, ess_subset p VB hzB⟩
    have hTzW : Tmap p z ∈ VA ∩ VB := ⟨(hperA z).mp hzW.1, (hperB z).mp hzW.2⟩
    exact ⟨z, hzW,
      joinedIn_inter_of_joinedIn_strip hab hVA hVB hcover hzW hTzW hzA.2 hzB.2⟩
  · rintro ⟨q, hqW, hjoin⟩
    exact ⟨q, ⟨hqW.1, hjoin.mono Set.inter_subset_left⟩,
      ⟨hqW.2, hjoin.mono Set.inter_subset_right⟩⟩

/-- **What the failure hypothesis hands you.**  If the crux fails, then for *every* point
`q ∈ VA ∩ VB` the component of `q` in `VA ∩ VB` has infinite `T`-orbit: `Tz p k q` is in that
component only for `k = 0`.

This is the input of the construction that must contradict `period_statement` (a connected
`T^m`-invariant open set, `m ≥ 2`, always meets its `p`-translate).  Proof: a component of `VA ∩ VB`
containing a crossing would give, by `mv_one_iff_crux`, the crux; so no component has a crossing, and
`orbit_infinite_of_no_crossing` applies. -/
theorem not_crux_components_infinite_orbit {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hfail : ¬ ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB)
    {q : ℝ × ℝ} (hq : q ∈ VA ∩ VB) (k : ℤ) (hk : k ≠ 0) :
    Tz p k q ∉ connectedComponentIn (VA ∩ VB) q := by
  have hWinv : ∀ q : ℝ × ℝ, q ∈ VA ∩ VB ↔ Tmap p q ∈ VA ∩ VB := by
    intro q
    show (q ∈ VA ∧ q ∈ VB) ↔ (Tmap p q ∈ VA ∧ Tmap p q ∈ VB)
    rw [hperA q, hperB q]
  have hWop : IsOpen (VA ∩ VB) := hVA.inter hVB
  have hnocross : ¬ ∃ q' ∈ connectedComponentIn (VA ∩ VB) q,
      JoinedIn (connectedComponentIn (VA ∩ VB) q) q' (Tmap p q') := by
    rintro ⟨q', hq', hjoin⟩
    have hsub : connectedComponentIn (VA ∩ VB) q ⊆ VA ∩ VB :=
      connectedComponentIn_subset (VA ∩ VB) q
    have : ∃ q'' ∈ VA ∩ VB, JoinedIn (VA ∩ VB) q'' (Tmap p q'') :=
      ⟨q', hsub hq', hjoin.mono hsub⟩
    exact hfail ((mv_one_iff_crux hp hab hVA hVB hperA hperB hcover).mpr this)
  exact orbit_infinite_of_no_crossing hp hWinv hWop hq hnocross k hk q
    (mem_connectedComponentIn hq)

/-- **The deck-group dictionary.**  For a `T`-invariant open `W`, `z ∈ W` and `m : ℤ`, the
component `C = connectedComponentIn W z` is `T^m`-invariant (that is, `Tz p m '' C = C`) if and only
if `m` is a monodromy degree at `z`, i.e. `z` is joined to `Tz p m z` inside `W`.

Equivalently: the `T`-orbit of a component is exactly the index of the monodromy subgroup
`retDeg p W z` in `ℤ`.  A component therefore has finite `T`-orbit `m ≥ 1` exactly when
`retDeg p W z = mℤ`; in particular "every component of `W` has infinite orbit" is exactly
"`retDeg p W q = {0}` for every `q ∈ W`". -/
theorem Tz_image_component_iff_mem_retDeg {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (hWop : IsOpen W) {z : ℝ × ℝ} (hz : z ∈ W)
    (m : ℤ) :
    Tz p m '' connectedComponentIn W z = connectedComponentIn W z ↔
      JoinedIn W z (Tz p m z) := by
  haveI : LocallyPathConnectedSpace (ℝ × ℝ) := inferInstance
  constructor
  · intro h
    have hzm : Tz p m z ∈ connectedComponentIn W z := by
      rw [← h]; exact ⟨z, mem_connectedComponentIn hz, rfl⟩
    have hpc : IsPathConnected (connectedComponentIn W z) :=
      (hWop.connectedComponentIn.isConnected_iff_isPathConnected).mp
        ⟨⟨z, mem_connectedComponentIn hz⟩, isPreconnected_connectedComponentIn⟩
    exact (hpc.joinedIn z (mem_connectedComponentIn hz) (Tz p m z) hzm).mono
      (connectedComponentIn_subset W z)
  · intro hjoin
    have hzm : Tz p m z ∈ connectedComponentIn W z := mem_connectedComponentIn_of_joinedIn hjoin
    rw [Tz_image_connectedComponentIn hW m hz]
    exact (connectedComponentIn_eq hzm).symm

/-- **The failure hypothesis in monodromy form.**  If the crux fails, then the monodromy subgroup of
`VA ∩ VB` at every point is trivial: there is no non-zero `k` with `q ~ Tz p k q` inside
`VA ∩ VB`.  This is `not_crux_components_infinite_orbit` read through the deck-group dictionary. -/
theorem not_crux_retDeg_eq_bot {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hfail : ¬ ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB)
    {q : ℝ × ℝ} (hq : q ∈ VA ∩ VB) {k : ℤ} (hk : k ∈ retDeg p (VA ∩ VB) q) : k = 0 := by
  by_contra hk0
  exact not_crux_components_infinite_orbit hp hab hVA hVB hperA hperB hcover hfail hq k hk0
    (mem_connectedComponentIn_of_joinedIn hk)


/-- **The connecting-map statement, in a form where only `VA` and `VB` appear.**

The Mayer–Vietoris obligation is *equivalent* to: some point of `VA ∩ VB` carries the same non-zero
translate-crossing in `VA` and in `VB`.  The forward direction is immediate (`VA ∩ VB` is inside both
sets); the converse is exactly Janiszewski in the simply connected strip
(`joinedIn_inter_of_joinedIn_strip`), which turns a crossing in `VA` and a crossing in `VB` at a
common point into a crossing of the intersection.

So the missing layer — the connecting map of van Kampen / Mayer–Vietoris — has to produce, from the
two non-trivial monodromies of `VA` and `VB` (supplied by `hwindA`, `hwindB`), a *common* point where
both are non-trivial.  In `retDeg` language: `∃ q ∈ VA ∩ VB, (retDeg p VA q ∩ retDeg p VB q) ≠ {0}`,
with the two monodromies being constant on path components (`retDeg_eq_of_joinedIn`) — i.e. the
`T`-invariant components of `VA` and of `VB` have to meet. -/
theorem mv_obligation_iff_common_crossing {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b) :
    (∃ q ∈ VA ∩ VB, ∃ m : ℤ, 1 ≤ m ∧ JoinedIn (VA ∩ VB) q (Tz p m q)) ↔
      (∃ q ∈ VA ∩ VB, ∃ m : ℤ, 1 ≤ m ∧ JoinedIn VA q (Tz p m q) ∧
        JoinedIn VB q (Tz p m q)) := by
  constructor
  · rintro ⟨q, hqW, m, hm, hjoin⟩
    exact ⟨q, hqW, m, hm, hjoin.mono Set.inter_subset_left,
      hjoin.mono Set.inter_subset_right⟩
  · rintro ⟨q, hqW, m, hm, hA, hB⟩
    have hTmW : Tz p m q ∈ VA ∩ VB := ⟨hA.target_mem, hB.target_mem⟩
    exact ⟨q, hqW, m, hm,
      joinedIn_inter_of_joinedIn_strip hab hVA hVB hcover hqW hTmW hA hB⟩

/-! ### SESSION 45: what was removed, and why the "straight-wall" refutation is invalid

The "wall existence" statement that used to be proved-towards here,

  `K ⊆ Ω` closed in `Ω`, `T`-invariant, no translate crossing in `Ω \ K`  ⟹  `∃ C ⊆ K`
  preconnected with `a, b ∈ closure (heights '' C)`,

is **not** used by this file any more: the derivation of `mv_obligation` from it has been removed,
so the file's single `sorry` now sits on `mv_obligation` itself.  The reason for removing it is that
the statement is *not established* — it is refuted by the "spiral tower" family recorded in
`Work/Topology/Strip/two_closed_crossing_of_annulus.lean` §(G1) (three horizontal lines plus two
families of walls that are *graphs escaping to infinity* at the level lines), while a naive variant
with **straight** walls is *not* a counterexample; see the caution in the status block at the top of
this file, and `wall_conclusion_of_preconnected_meets_every_level` below for the easy reason: a
connected `K` meeting every level line always witnesses the conclusion, so any counterexample must
be disconnected, and any check must be made on the actual components of `K`. -/

/-- **A preconnected `K` meeting every level line witnesses the wall conclusion.**  Hence any
counterexample to the wall statement must have `K` disconnected (and the naive "straight wall"
families are automatically connected, since the closure of each straight wall meets the level line
separating the two bands). -/
theorem wall_conclusion_of_preconnected_meets_every_level {a b : ℝ} (hab : a < b)
    {K : Set (ℝ × ℝ)} (hKpre : IsPreconnected K)
    (hlev : ∀ y : ℝ, a < y → y < b → ∃ x : ℝ, (x, y) ∈ K) :
    ∃ C : Set (ℝ × ℝ), C ⊆ K ∧ IsPreconnected C ∧
      a ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) ∧
      b ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) := by
  have hsub : Set.Ioo a b ⊆ (fun q : ℝ × ℝ => q.2) '' K := by
    rintro y ⟨h1, h2⟩
    obtain ⟨x, hx⟩ := hlev y h1 h2
    exact ⟨(x, y), hx, rfl⟩
  have hcl : Set.Icc a b ⊆ closure ((fun q : ℝ × ℝ => q.2) '' K) := by
    rw [← closure_Ioo (ne_of_lt hab)]
    exact closure_mono hsub
  exact ⟨K, subset_rfl, hKpre, hcl ⟨le_rfl, hab.le⟩, hcl ⟨hab.le, le_rfl⟩⟩

/-- **The easy case of the crux: an essential component contained in the overlap.**

Let `z ∈ Ess p VA` and `C = connectedComponentIn VA z`.  If `C ⊆ VA ∩ VB` then the crux's
conclusion holds: every point of `C` is essential for `VA` (`connectedComponentIn_subset_Ess`), and
the crossing through such a point stays inside the connected set `C`, hence inside `VB`.

Together with `eq_stripS_of_component_disjoint` (a component of `VA` missing `VB` forces
`VA = stripS a b`, whence `hwindB` gives the crux) this shows: in the remaining case of the crux
the essential component `C` of `VA` *straddles* the two pieces `VA ∩ VB` and `VA \ VB` of `VA`
(and symmetrically for `VB`). -/
theorem crux_of_component_subset_inter {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    {z : ℝ × ℝ} (hz : z ∈ Ess p VA)
    (hsub : connectedComponentIn VA z ⊆ VA ∩ VB) :
    ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB := by
  have hzW : z ∈ VA := ess_subset p VA hz
  refine ⟨z, hz, ?_⟩
  have hzVB : z ∈ VB := (hsub (mem_connectedComponentIn hzW)).2
  obtain ⟨γ, hγ⟩ := hz.2
  have hrange : Set.range γ ⊆ connectedComponentIn VA z :=
    IsPreconnected.subset_connectedComponentIn (isPreconnected_range γ.continuous)
      ⟨0, γ.source⟩ (by rintro q ⟨u, rfl⟩; exact hγ u)
  have hγV : ∀ t, γ t ∈ VB := fun t => (hsub (hrange ⟨t, rfl⟩)).2
  exact ⟨hzVB, ⟨γ, hγV⟩⟩

/-- **The level dichotomy.**  If the whole level line `{q.2 = y}` of the strip avoids `VA ∩ VB`,
then it misses `VA` entirely or misses `VB` entirely.  On that line the two sets `VAᶜ`, `VBᶜ` are
disjoint closed sets covering the line (they cover it because the line lies in `VA ∪ VB`), and the
line is connected. -/
theorem level_subset_compl_left_or_right {a b : ℝ} {VA VB : Set (ℝ × ℝ)} {y : ℝ}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hy : a < y ∧ y < b)
    (hcover : VA ∪ VB = stripS a b)
    (hdisj : ∀ x : ℝ, ((x, y) : ℝ × ℝ) ∉ VA ∩ VB) :
    (∀ x : ℝ, ((x, y) : ℝ × ℝ) ∉ VA) ∨ (∀ x : ℝ, ((x, y) : ℝ × ℝ) ∉ VB) := by
  set C₁ : Set ℝ := {x : ℝ | ((x, y) : ℝ × ℝ) ∉ VA} with hC₁
  set C₂ : Set ℝ := {x : ℝ | ((x, y) : ℝ × ℝ) ∉ VB} with hC₂
  have hc₁ : IsClosed C₁ := by
    rw [hC₁]
    exact (hVA.isClosed_compl).preimage (by fun_prop :
      Continuous (fun x : ℝ => ((x, y) : ℝ × ℝ)))
  have hc₂ : IsClosed C₂ := by
    rw [hC₂]
    exact (hVB.isClosed_compl).preimage (by fun_prop :
      Continuous (fun x : ℝ => ((x, y) : ℝ × ℝ)))
  have hsub : (Set.univ : Set ℝ) ⊆ C₁ ∪ C₂ := by
    intro x _
    have hx : ((x, y) : ℝ × ℝ) ∈ stripS a b := by rw [stripS_iff]; exact hy
    have hxu : ((x, y) : ℝ × ℝ) ∈ VA ∪ VB := by rw [hcover]; exact hx
    rcases hxu with h | h
    · exact Or.inr (fun hb => hdisj x ⟨h, hb⟩)
    · exact Or.inl (fun ha => hdisj x ⟨ha, h⟩)
  have hdisj' : (Set.univ : Set ℝ) ∩ (C₁ ∩ C₂) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and] at hx
    obtain ⟨hx₁, hx₂⟩ := hx
    have hxu : ((x, y) : ℝ × ℝ) ∈ VA ∪ VB := by
      rw [hcover, stripS_iff]; exact hy
    rcases hxu with h | h
    · exact hx₁ h
    · exact hx₂ h
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_univ C₁ C₂
      hc₁ hc₂ hsub hdisj') with h | h
  · exact Or.inl (fun x => h (Set.mem_univ x))
  · exact Or.inr (fun x => h (Set.mem_univ x))

/-- **Closing up.**  A path in the free region `Ω \ K` from the point `(0, y₀)` to the meridian
`{x = p}` at height `y₁` forces `K` to meet the vertical segment at `x = p` between the two
heights: otherwise the vertical segment could be appended, producing a translate crossing inside
`Ω \ K`. -/
theorem vertical_segment_meets_of_joinedIn {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {K : Set (ℝ × ℝ)}
    (hno : ∀ z : ℝ × ℝ, z ∈ stripS a b \ K →
      ¬ JoinedIn (stripS a b \ K) z (Tmap p z))
    {y₀ y₁ : ℝ} (hy₀ : ((0:ℝ), y₀) ∈ stripS a b \ K)
    (hjoin : JoinedIn (stripS a b \ K) ((0:ℝ), y₀) ((p:ℝ), y₁)) :
    ∃ y : ℝ, (min y₀ y₁ ≤ y ∧ y ≤ max y₀ y₁) ∧ ((p:ℝ), y) ∈ K := by
  by_contra hcon
  have hjoin' : JoinedIn (stripS a b \ K) ((0:ℝ), y₀) ((p:ℝ), y₁) := hjoin
  obtain ⟨γ, hγ⟩ := hjoin
  have hy₀s : ((0:ℝ), y₀) ∈ stripS a b := hy₀.1
  have hy₁s : ((p:ℝ), y₁) ∈ stripS a b := by
    have h := hγ 1
    rw [γ.target] at h
    exact h.1
  have hy0lo : a < y₀ := (stripS_iff.mp hy₀s).1
  have hy0hi : y₀ < b := (stripS_iff.mp hy₀s).2
  have hy1lo : a < y₁ := (stripS_iff.mp hy₁s).1
  have hy1hi : y₁ < b := (stripS_iff.mp hy₁s).2
  have hvert : JoinedIn (stripS a b \ K) ((p:ℝ), y₁) ((p:ℝ), y₀) := by
    refine ⟨{ toFun := fun t : Set.Icc (0:ℝ) 1 => ((p:ℝ), (1 - (t : ℝ)) * y₁ + (t : ℝ) * y₀)
              continuous_toFun := by fun_prop
              source' := by simp
              target' := by simp }, ?_⟩
    intro t
    have ht : (t : ℝ) ∈ Set.Icc (0:ℝ) 1 := t.2
    have hle₁ : min y₀ y₁ ≤ (1 - (t:ℝ)) * y₁ + (t:ℝ) * y₀ := by
      nlinarith [ht.1, ht.2, min_le_left y₀ y₁, min_le_right y₀ y₁]
    have hle₂ : (1 - (t:ℝ)) * y₁ + (t:ℝ) * y₀ ≤ max y₀ y₁ := by
      nlinarith [ht.1, ht.2, le_max_left y₀ y₁, le_max_right y₀ y₁]
    exact ⟨⟨lt_of_lt_of_le (lt_min hy0lo hy1lo) hle₁,
            lt_of_le_of_lt hle₂ (max_lt hy0hi hy1hi)⟩,
           fun hmem => hcon ⟨_, ⟨hle₁, hle₂⟩, hmem⟩⟩
  have hcross : JoinedIn (stripS a b \ K) ((0:ℝ), y₀) (Tmap p ((0:ℝ), y₀)) := by
    have h : JoinedIn (stripS a b \ K) ((0:ℝ), y₀) ((p:ℝ), y₀) := JoinedIn.trans hjoin' hvert
    simpa [Tmap] using h
  exact hno _ hy₀ hcross

/-! ### A concrete lead for the missing Mayer–Vietoris input (session 45)

The commons already contains Mayer–Vietoris for the ℤ/2 (co)homology of *simplicial complexes*
(`Commons.AlgebraicTopology.SimplicialComplex.mayer_vietoris`,
`Commons.AlgebraicTopology.SimplicialComplex.mayer_vietoris_cohomology`, and
`Commons.AlgebraicTopology.Cohomology.mayer_vietoris` for simplicial sets).  For the crux it is
enough to work with ℤ/2 coefficients:

* an essential loop of the annulus has non-zero class in `H₁(·; ℤ/2)` (its degree is odd);
* if `a ∈ H₁(VA; ℤ/2)` and `b ∈ H₁(VB; ℤ/2)` are the classes of the two essential loops supplied by
  `hwindA`, `hwindB`, then both map to the generator of `H₁(Ω; ℤ/2) ≅ ℤ/2`, hence `a + b ↦ 0`;
* Mayer–Vietoris exactness `H₁(VA ∩ VB; ℤ/2) → H₁(VA; ℤ/2) ⊕ H₁(VB; ℤ/2) → H₁(Ω; ℤ/2)` therefore
  produces `c ∈ H₁(VA ∩ VB; ℤ/2)` mapping to `(a, b)`, and `c ≠ 0` since `a ≠ 0`;
* a loop of odd degree in `VA ∩ VB` yields a translate crossing inside `VA ∩ VB` by
  `component_crossing_of_period` (order-`k` ⟹ order-`1`, proved above), which is the crux.

So the only link missing from the commons is the comparison between the singular (or Čech) homology
of these open subsets of the plane and that of a simplicial model of the annulus and its pieces; the
Mayer–Vietoris exactness itself is already available for the model. -/


/-! ### SESSION 45 (continued): the concrete Mayer–Vietoris content, and it is proved

`sweep_of_crossings` below is the **elementary** form of the Mayer–Vietoris input: the straight-line
(sweep) interpolation between a translate crossing lying in `VA` and one lying in `VB` produces a
one-parameter family of translate crossings (convexity of the strip plus affinity of the
translation), and whenever the interpolated crossing is contained in neither `VA` nor `VB` it still
"touches" the overlap `VA ∩ VB` (its range is preconnected and meets both `VA \ VB` and
`VB \ VA`).  Consequently the crux is *reduced* to the statement that, for the sweep between any
two crossings, the set of parameters `s` for which the interpolated crossing is contained in `VA` or
in `VB` covers the whole interval — and the two constituent sets are open in the parameter interval
(their complements are the continuous images of the closed sets `F⁻¹(VAᶜ)`, `F⁻¹(VBᶜ)` under the
projection from the compact square, hence closed).  That is the remaining homological content in its
most concrete form. -/


theorem sweep_of_crossings {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hcover : VA ∪ VB = {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    {γA γB : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hA : ∀ t, γA t ∈ VA) (hB : ∀ t, γB t ∈ VB)
    (hTA : γA (1 : Set.Icc (0:ℝ) 1) = ((γA (0 : Set.Icc (0:ℝ) 1)).1 + p,
      (γA (0 : Set.Icc (0:ℝ) 1)).2))
    (hTB : γB (1 : Set.Icc (0:ℝ) 1) = ((γB (0 : Set.Icc (0:ℝ) 1)).1 + p,
      (γB (0 : Set.Icc (0:ℝ) 1)).2)) :
    ∃ G : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ℝ × ℝ),
      (∀ s t, G (s, t) ∈ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) ∧
      (∀ s, G (s, 1) = ((G (s, 0)).1 + p, (G (s, 0)).2)) ∧
      (∀ t, G (0, t) = γA t) ∧ (∀ t, G (1, t) = γB t) ∧
      (∀ s, (∃ t, G (s, t) ∉ VA) → (∃ t, G (s, t) ∉ VB) → ∃ t, G (s, t) ∈ VA ∩ VB) := by
  set F : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 → ℝ × ℝ :=
    fun u => ((1 - (u.1 : ℝ)) * (γA u.2).1 + (u.1 : ℝ) * (γB u.2).1,
              (1 - (u.1 : ℝ)) * (γA u.2).2 + (u.1 : ℝ) * (γB u.2).2) with hF
  have hFc : Continuous F := by rw [hF]; fun_prop
  have hFstrip : ∀ s t, F (s, t) ∈ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b} := by
    intro s t
    have h1 : (γA t).2 ∈ Set.Ioo a b := by
      have h : γA t ∈ VA ∪ VB := Or.inl (hA t)
      rw [hcover] at h; exact h
    have h2 : (γB t).2 ∈ Set.Ioo a b := by
      have h : γB t ∈ VA ∪ VB := Or.inr (hB t)
      rw [hcover] at h; exact h
    have hs1 : (0:ℝ) ≤ (s : ℝ) := s.2.1
    have hs2 : (0:ℝ) ≤ 1 - (s : ℝ) := by linarith [s.2.2]
    have hcombo : (1 - (s:ℝ)) • (γA t).2 + (s:ℝ) • (γB t).2 ∈ Set.Ioo a b :=
      convex_Ioo a b h1 h2 hs2 hs1 (by ring)
    rw [hF]
    simpa [smul_eq_mul] using hcombo
  have hFcross : ∀ s, F (s, 1) = ((F (s, 0)).1 + p, (F (s, 0)).2) := by
    intro s
    simp only [hF]
    rw [hTA, hTB]
    ext <;> ring
  have hF0 : ∀ t, F (0, t) = γA t := by
    intro t
    rw [hF]
    simp
  have hF1 : ∀ t, F (1, t) = γB t := by
    intro t
    rw [hF]
    simp
  have hFmeet : ∀ s, (∃ t, F (s, t) ∉ VA) → (∃ t, F (s, t) ∉ VB) →
      ∃ t, F (s, t) ∈ VA ∩ VB := by
    intro s hAs hBs
    by_contra hcon
    push_neg at hcon
    have hcont : Continuous fun t : Set.Icc (0:ℝ) 1 => F (s, t) :=
      hFc.comp (continuous_const.prodMk continuous_id)
    have hmemΩ : ∀ t : Set.Icc (0:ℝ) 1, F (s, t) ∈ VA ∪ VB := by
      intro t
      have h : F (s, t) ∈ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b} := hFstrip s t
      rwa [hcover]
    set T₁ : Set (Set.Icc (0:ℝ) 1) := {t | F (s, t) ∉ VA} with hT₁
    set T₂ : Set (Set.Icc (0:ℝ) 1) := {t | F (s, t) ∉ VB} with hT₂
    have hc₁ : IsClosed T₁ := by
      rw [hT₁]; exact (isClosed_compl_iff.mpr hVA).preimage hcont
    have hc₂ : IsClosed T₂ := by
      rw [hT₂]; exact (isClosed_compl_iff.mpr hVB).preimage hcont
    have hsub : (Set.univ : Set (Set.Icc (0:ℝ) 1)) ⊆ T₁ ∪ T₂ := by
      intro t _
      by_cases h : F (s, t) ∈ VA
      · refine Or.inr (fun hb => ?_)
        exact hcon t ⟨h, hb⟩
      · exact Or.inl h
    have hdisj : (Set.univ : Set (Set.Icc (0:ℝ) 1)) ∩ (T₁ ∩ T₂) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro t ht
      simp only [Set.mem_inter_iff, Set.mem_univ, true_and, hT₁, hT₂,
        Set.mem_ofPred_eq] at ht
      obtain ⟨h1, h2⟩ := ht
      rcases hmemΩ t with h | h
      · exact h1 h
      · exact h2 h
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_univ
        T₁ T₂ hc₁ hc₂ hsub hdisj) with h | h
    · obtain ⟨tB, htB⟩ := hBs
      have h1 : F (s, tB) ∉ VA := by
        have hh := h (Set.mem_univ tB)
        rwa [hT₁] at hh
      rcases hmemΩ tB with h2 | h2
      · exact h1 h2
      · exact htB h2
    · obtain ⟨tA, htA⟩ := hAs
      have h1 : F (s, tA) ∉ VB := by
        have hh := h (Set.mem_univ tA)
        rwa [hT₂] at hh
      rcases hmemΩ tA with h2 | h2
      · exact htA h2
      · exact h1 h2
  exact ⟨⟨F, hFc⟩, hFstrip, hFcross, hF0, hF1, hFmeet⟩



/-- **The parameter set of a sweep is open.**  For a continuous `G` on the square `I × I` and an
open `V`, the set of parameters `s` for which the whole partial map `t ↦ G (s,t)` lies in `V` is
open: the image of the fixed-time slice is compact and contained in `V`, so it has positive distance
from the complement of `V`, and Heine–Cantor on the compact square makes that distance uniform in `s`.

This is the bookkeeping that makes the two parameter sets of the sweep reduction open, so that a
cover of the parameter interval forces them to intersect. -/
theorem isOpen_forall_mem_of_continuous
    {G : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ℝ × ℝ)} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    IsOpen {s : Set.Icc (0:ℝ) 1 | ∀ t : Set.Icc (0:ℝ) 1, G (s, t) ∈ V} := by
  haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  haveI : CompactSpace (Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1) := inferInstance
  have huc : UniformContinuous G := CompactSpace.uniformContinuous_of_continuous G.continuous
  rw [Metric.isOpen_iff]
  intro s₀ hs₀
  have hcont₀ : Continuous fun t : Set.Icc (0:ℝ) 1 => G (s₀, t) :=
    G.continuous.comp (continuous_const.prodMk continuous_id)
  have hKcpt : IsCompact ((fun t : Set.Icc (0:ℝ) 1 => G (s₀, t)) '' Set.univ) :=
    isCompact_univ.image hcont₀
  have hKV : ((fun t : Set.Icc (0:ℝ) 1 => G (s₀, t)) '' Set.univ) ⊆ V := by
    rintro y ⟨t, -, rfl⟩
    exact hs₀ t
  obtain ⟨ε, hεpos, hε⟩ := hKcpt.exists_cthickening_subset_open hV hKV
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc (ε/2) (by linarith)
  refine ⟨δ, hδpos, fun s hs => ?_⟩
  rw [Metric.mem_ball, dist_comm] at hs
  intro t
  have h1 : dist (G (s, t)) (G (s₀, t)) < ε/2 :=
    hδ (by
      have h2 : dist (s, t) (s₀, t) = dist s s₀ := by
        rw [Prod.dist_eq, max_eq_left (by simp)]
      rw [h2, dist_comm]
      exact hs)
  have hmem : G (s₀, t) ∈ (fun t : Set.Icc (0:ℝ) 1 => G (s₀, t)) '' Set.univ :=
    ⟨t, trivial, rfl⟩
  refine hε (Metric.closedBall_subset_cthickening hmem ε ?_)
  rw [Metric.mem_closedBall]
  linarith

/-- **The last mile of the sweep reduction.**  Let `G` be a sweep on the square which sends the left
edge onto a translate crossing lying in `VA` and the right edge onto one lying in `VB`, and whose
every vertical slice is again a translate crossing (`G (s,1) = Tmap p (G (s,0))`).  If every
parameter `s` has its slice contained in `VA` or in `VB` (the *covering claim* for the sweep), then
some slice is a translate crossing inside `VA ∩ VB`.

Proof: the two parameter sets `{s | slice ⊆ VA}` and `{s | slice ⊆ VB}` are open (previous lemma);
they cover the interval, and they contain the endpoints `0` resp. `1`; hence, if they were disjoint,
`isPreconnected_univ.subset_or_subset` would put the whole interval in one of them, contradicting the
endpoint membership of the other.  The common parameter is a slice lying in `VA ∩ VB` and, being a
translate crossing, yields an element of the overlap joined to its translate inside the overlap. -/
theorem exists_crossing_of_sweep_covering {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB)
    {γA γB : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} (hA : ∀ t, γA t ∈ VA) (hB : ∀ t, γB t ∈ VB)
    {G : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hG0 : ∀ t, G ((0 : Set.Icc (0:ℝ) 1), t) = γA t)
    (hG1 : ∀ t, G ((1 : Set.Icc (0:ℝ) 1), t) = γB t)
    (hcross : ∀ s, G (s, 1) = Tmap p (G (s, 0)))
    (hcov : ∀ s, (∀ t, G (s, t) ∈ VA) ∨ (∀ t, G (s, t) ∈ VB)) :
    ∃ q : ℝ × ℝ, q ∈ VA ∩ VB ∧ JoinedIn (VA ∩ VB) q (Tmap p q) := by
  set S₁ : Set (Set.Icc (0:ℝ) 1) := {s | ∀ t, G (s, t) ∈ VA} with hS₁
  set S₂ : Set (Set.Icc (0:ℝ) 1) := {s | ∀ t, G (s, t) ∈ VB} with hS₂
  have h1 : IsOpen S₁ := isOpen_forall_mem_of_continuous hVA
  have h2 : IsOpen S₂ := isOpen_forall_mem_of_continuous hVB
  have hmem0 : (0 : Set.Icc (0:ℝ) 1) ∈ S₁ := by
    intro t
    rw [hG0]
    exact hA t
  have hmem1 : (1 : Set.Icc (0:ℝ) 1) ∈ S₂ := by
    intro t
    rw [hG1]
    exact hB t
  have hsub : (Set.univ : Set (Set.Icc (0:ℝ) 1)) ⊆ S₁ ∪ S₂ := by
    intro s _; exact hcov s
  have hmeet : (S₁ ∩ S₂).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hdisj : Disjoint S₁ S₂ := by
      rw [Set.disjoint_iff_inter_eq_empty]; exact hcon
    have hpre : IsPreconnected (Set.univ : Set (Set.Icc (0:ℝ) 1)) := isPreconnected_univ
    rcases hpre.subset_or_subset h1 h2 hdisj hsub with h | h
    · exact Set.disjoint_left.mp hdisj (h (Set.mem_univ 1)) hmem1
    · exact Set.disjoint_left.mp hdisj hmem0 (h (Set.mem_univ 0))
  obtain ⟨s, hs1, hs2⟩ := hmeet
  refine ⟨G (s, 0), ⟨hs1 0, hs2 0⟩, ?_⟩
  refine ⟨⟨⟨fun t => G (s, t), ?_⟩, ?_, ?_⟩, fun t => ⟨hs1 t, hs2 t⟩⟩
  · exact G.continuous.comp (continuous_const.prodMk continuous_id)
  · rfl
  · exact hcross s







/-- **The configuration of the square pulled back through a sweep** (the first move on the trace
lemma).  Writing `P := F ⁻¹' (Ω \\ VA)` and `Q := F ⁻¹' (Ω \\ VB)` (where `Ω = stripS a b`):

* `P` and `Q` are closed in the square (preimages of the closed sets `VAᶜ`, `VBᶜ`, using that `F`
  takes values in `Ω`);
* `P ∩ Q = ∅` (a point outside both `VA` and `VB` would be outside `VA ∪ VB = Ω`);
* the **bottom edge** `{0} × I` (which is `γA ⊆ VA`) misses `P`, and the **top edge** `{1} × I`
  (which is `γB ⊆ VB`) misses `Q`.

So the square carries two disjoint closed sets, the bottom edge avoiding one of them, the top edge
avoiding the other, and the open complement `U = F ⁻¹' (VA ∩ VB)` forming the rest of the square — the
configuration to which the trace lemma applies. -/
theorem sweep_square_configuration {a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hcover : VA ∪ VB = stripS a b)
    {F : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hFstrip : ∀ s t, F (s, t) ∈ stripS a b)
    {γA γB : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hF0 : ∀ t, F ((0 : Set.Icc (0:ℝ) 1), t) = γA t)
    (hF1 : ∀ t, F ((1 : Set.Icc (0:ℝ) 1), t) = γB t)
    (hA : ∀ t, γA t ∈ VA) (hB : ∀ t, γB t ∈ VB) :
    IsClosed (F ⁻¹' (stripS a b \ VA)) ∧ IsClosed (F ⁻¹' (stripS a b \ VB)) ∧
      Disjoint (F ⁻¹' (stripS a b \ VA)) (F ⁻¹' (stripS a b \ VB)) ∧
      (∀ t : Set.Icc (0:ℝ) 1, F ((0 : Set.Icc (0:ℝ) 1), t) ∈ VA) ∧
      (∀ t : Set.Icc (0:ℝ) 1, F ((1 : Set.Icc (0:ℝ) 1), t) ∈ VB) ∧
      (∀ t : Set.Icc (0:ℝ) 1, (((0 : Set.Icc (0:ℝ) 1), t) : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1)
        ∉ F ⁻¹' (stripS a b \ VA)) ∧
      (∀ t : Set.Icc (0:ℝ) 1, (((1 : Set.Icc (0:ℝ) 1), t) : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1)
        ∉ F ⁻¹' (stripS a b \ VB)) := by
  have hpre : ∀ V : Set (ℝ × ℝ), F ⁻¹' (stripS a b \ V) = F ⁻¹' (Vᶜ) := by
    intro V
    ext u
    simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_compl_iff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨hFstrip u.1 u.2, h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpre VA]; exact (isClosed_compl_iff.mpr hVA).preimage F.continuous
  · rw [hpre VB]; exact (isClosed_compl_iff.mpr hVB).preimage F.continuous
  · rw [Set.disjoint_left]
    intro u huA huB
    rw [hpre VA] at huA
    rw [hpre VB] at huB
    rcases (show F u ∈ VA ∪ VB by rw [hcover]; exact hFstrip u.1 u.2) with h | h
    · exact huA h
    · exact huB h
  · intro t; rw [hF0]; exact hA t
  · intro t; rw [hF1]; exact hB t
  · intro t
    rw [hpre VA]
    intro h
    exact h (by rw [hF0]; exact hA t)
  · intro t
    rw [hpre VB]
    intro h
    exact h (by rw [hF1]; exact hB t)

/-- **The pairing's separation property.**  Pulling the no-crossing hypothesis back through the
sweep: if two points `u`, `v` of the square have `F`-images in the overlap `W` related by the
translation, then **no** path inside `F ⁻¹' W` joins `u` to `v`.

Indeed, such a path would push forward along the continuous `F` to a path inside `W` from `F u` to
`F v = T (F u)`, contradicting `hno`.  This is the exact input that the trace lemma of the boundary
cycle consumes. -/
theorem no_path_in_preimage_of_translate {p : ℝ} {W : Set (ℝ × ℝ)}
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q))
    {F : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    {u v : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1}
    (hu : F u ∈ W) (hv : F v = Tmap p (F u)) :
    ¬ JoinedIn (F ⁻¹' W) u v := by
  rintro ⟨γ, hγ⟩
  refine hno (F u) hu ?_
  rw [← hv]
  exact ⟨γ.map F.continuous, fun t => hγ t⟩

/-- **The overlap step.**  If a slice of a sweep is *mixed* — it has a point outside `VA` and a point
outside `VB` — then it must meet the overlap `VA ∩ VB`.

Indeed, putting `T₁ := {t | F (s,t) ∉ VA}` and `T₂ := {t | F (s,t) ∉ VB}`: both are closed in the
parameter interval (`VA`, `VB` are open and the slice is continuous), they cover the interval (a point
of the slice lies in `Ω = VA ∪ VB`), they are disjoint (a point outside both would lie outside
`VA ∪ VB`), and the mixing hypothesis makes both non-empty.  A preconnected interval cannot be the
disjoint union of two non-empty closed sets; contradiction.

So a mixed slice always carries an overlap point, and that is the point at which the hypothesis `hno`
acts (no translate crossing lives inside the overlap). -/
theorem mixed_slice_meets_inter {a b : ℝ} {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hcover : VA ∪ VB = stripS a b)
    {F : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hFstrip : ∀ s t, F (s, t) ∈ stripS a b)
    {s : Set.Icc (0:ℝ) 1}
    (hmix : (∃ t, F (s, t) ∉ VA) ∧ (∃ t, F (s, t) ∉ VB)) :
    ∃ t, F (s, t) ∈ VA ∩ VB := by
  by_contra hcon
  push_neg at hcon
  have hcont : Continuous fun t : Set.Icc (0:ℝ) 1 => F (s, t) :=
    F.continuous.comp (continuous_const.prodMk continuous_id)
  set T₁ : Set (Set.Icc (0:ℝ) 1) := {t | F (s, t) ∉ VA} with hT₁
  set T₂ : Set (Set.Icc (0:ℝ) 1) := {t | F (s, t) ∉ VB} with hT₂
  have hc₁ : IsClosed T₁ := by
    rw [hT₁]; exact (isClosed_compl_iff.mpr hVA).preimage hcont
  have hc₂ : IsClosed T₂ := by
    rw [hT₂]; exact (isClosed_compl_iff.mpr hVB).preimage hcont
  have hsub : (Set.univ : Set (Set.Icc (0:ℝ) 1)) ⊆ T₁ ∪ T₂ := by
    intro t _
    by_cases h : F (s, t) ∈ VA
    · refine Or.inr (fun hb => ?_)
      exact hcon t ⟨h, hb⟩
    · exact Or.inl h
  have hdisj : (Set.univ : Set (Set.Icc (0:ℝ) 1)) ∩ (T₁ ∩ T₂) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, hT₁, hT₂, Set.mem_ofPred_eq] at ht
    obtain ⟨h1, h2⟩ := ht
    rcases (show F (s, t) ∈ VA ∪ VB by rw [hcover]; exact hFstrip s t) with h | h
    · exact h1 h
    · exact h2 h
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_univ : IsPreconnected (Set.univ : Set (Set.Icc (0:ℝ) 1)))
      T₁ T₂ hc₁ hc₂ hsub hdisj) with h | h
  · obtain ⟨t₂, ht₂⟩ := hmix.2
    have h1 : F (s, t₂) ∉ VA := by
      have := h (Set.mem_univ t₂)
      rwa [hT₁] at this
    rcases (show F (s, t₂) ∈ VA ∪ VB by rw [hcover]; exact hFstrip s t₂) with hh | hh
    · exact h1 hh
    · exact ht₂ hh
  · obtain ⟨t₁, ht₁⟩ := hmix.1
    have h1 : F (s, t₁) ∉ VB := by
      have := h (Set.mem_univ t₁)
      rwa [hT₂] at this
    rcases (show F (s, t₁) ∈ VA ∪ VB by rw [hcover]; exact hFstrip s t₁) with hh | hh
    · exact ht₁ hh
    · exact h1 hh

/-- **The "bad locus" of a sweep is closed** (first component).  The set of points of the square at
which the slice lies outside the open set `VA` is the preimage of the closed set `VAᶜ` under the
continuous map `F`. -/
theorem isClosed_sweep_outside_left {VA : Set (ℝ × ℝ)} (hVA : IsOpen VA)
    {F : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ℝ × ℝ)} :
    IsClosed {u : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 | F u ∉ VA} :=
  (isClosed_compl_iff.mpr hVA).preimage F.continuous

/-- **The set of "mixed" parameters is closed.**  A parameter `s` is *mixed* when its slice is
contained in neither `VA` nor `VB`, i.e. when some time has the slice outside `VA` and some time has
it outside `VB`.  This set is closed in the parameter interval: each of the two conjuncts is the
complement of the corresponding parameter set, which is open by `isOpen_forall_mem_of_continuous`.

`sweep_cover_claim` says precisely that this closed set is empty. -/
theorem isClosed_mixed_params {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    {F : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ℝ × ℝ)} :
    IsClosed {s : Set.Icc (0:ℝ) 1 | (∃ t, F (s, t) ∉ VA) ∧ (∃ t, F (s, t) ∉ VB)} := by
  have h1 : IsClosed {s : Set.Icc (0:ℝ) 1 | ∃ t, F (s, t) ∉ VA} := by
    have heq : {s : Set.Icc (0:ℝ) 1 | ∃ t, F (s, t) ∉ VA}
        = {s : Set.Icc (0:ℝ) 1 | ∀ t, F (s, t) ∈ VA}ᶜ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_forall]
    rw [heq]
    exact (isOpen_forall_mem_of_continuous hVA).isClosed_compl
  have h2 : IsClosed {s : Set.Icc (0:ℝ) 1 | ∃ t, F (s, t) ∉ VB} := by
    have heq : {s : Set.Icc (0:ℝ) 1 | ∃ t, F (s, t) ∉ VB}
        = {s : Set.Icc (0:ℝ) 1 | ∀ t, F (s, t) ∈ VB}ᶜ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_forall]
    rw [heq]
    exact (isOpen_forall_mem_of_continuous hVB).isClosed_compl
  exact h1.inter h2

/-- **Endpoint type-pairing of a sweep.**  Since `T` preserves a `T`-invariant set, the two ends of
every slice of a sweep have the same type: `F (s,0) ∈ KA ↔ F (s,1) ∈ KA`.  Applied to
`KA = Ω ∖ VA` and to `KB = Ω ∖ VB` this is the coherence of the family of covers `(T_s, T'_s)` of the
parameter interval: each slice starts and ends in the same one of the three types
`VA ∖ VB`, `VB ∖ VA`, `VA ∩ VB`. -/
theorem sweep_endpoint_pairing {p : ℝ} {KA : Set (ℝ × ℝ)}
    (hKA : ∀ q : ℝ × ℝ, q ∈ KA ↔ Tmap p q ∈ KA)
    {F : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hFcross : ∀ s, F (s, 1) = Tmap p (F (s, 0))) (s : Set.Icc (0:ℝ) 1) :
    F (s, (0 : Set.Icc (0:ℝ) 1)) ∈ KA ↔ F (s, (1 : Set.Icc (0:ℝ) 1)) ∈ KA := by
  rw [hFcross s]
  exact hKA (F (s, (0 : Set.Icc (0:ℝ) 1)))

/-! ### The trace lemma of the square (statement only — an unverified target)

The reduction of the crux to a statement about a square is now complete in its *inputs* (all proved):
with `P := F ⁻¹' (Ω \ VA)`, `Q := F ⁻¹' (Ω \ VB)` (disjoint closed in `I × I`), `U := F ⁻¹' (VA ∩ VB)`
(the open complement), and the edges `E₀ = {0} × I ⊆ VA`, `E₁ = {1} × I ⊆ VB` (so `E₀ ∩ P = ∅`,
`E₁ ∩ Q = ∅`, and the two edges are type-matched by `sweep_endpoint_pairing`), the remaining statement
is:

  **trace lemma.**  For every continuous `F : I × I → Ω` with `F (s,1) = T (F (s,0))` for all `s`,
  `F (0,·) ⊆ VA`, `F (1,·) ⊆ VB` and `hno` (no translate crossing inside `VA ∩ VB`), there exist
  `u v : I × I` with `F u ∈ VA ∩ VB`, `F v = T (F u)` and a path in `I × I` inside `F ⁻¹' (VA ∩ VB)`
  joining `u` to `v`.

**Consequence for the plan (no extra intermediate target).**  Since the square abstraction fails and is
not repaired abstractly (see below), and since adding the sweep hypothesis back to it yields exactly
`VA`, `VB`, `F`, `hno` — i.e. the statement `sweep_cover_claim` itself — there is *no* intermediate
target left between the configuration lemmas proved this run and the claim.  Any further attack should
be phrased *inside* `sweep_cover_claim`, with the `T`-invariance of the walls and the sweep structure
as explicit hypotheses, rather than beside it.

**Why the naive limit argument for union-closedness fails (and what it must use).**  Suppose
`sₙ → s` with each slice in `VA` or in `VB`, and suppose the limit slice `F s` is mixed.  The
pointwise limit of sets inside an *open* set need not stay inside it — e.g. `VA = {y < 1/2}` with
slices at heights `1/2 - 1/n` lying in `VA` and the limit slice at height `1/2` lying in neither — so
the convergence alone gives only that the exit points of the limit slice lie in the **boundary**
`∂VA` resp. `∂VB`.  Both boundaries are `T`-invariant (they are the boundaries of `T`-invariant open
sets), so the usable lever is: the mixed limit slice meets `∂VA` and `∂VB`, and the corresponding
half-space structure of these `T`-invariant closed sets is what the argument must consume.  This is
recorded so that the next attempt starts from "the exit points are boundary points, and the boundaries
are `T`-invariant", rather than from a naive limit argument that cannot work.

**A sharper equivalent form of the residual.**  The mixing locus is closed (`isClosed_mixed_params`)
and the endpoint slices lie in `VA` resp. in `VB`, so `0` and `1` lie outside it.  Hence the claim
follows as soon as the mixing locus is also *open*: a clopen subset of the connected interval which
avoids `0` must be empty.  So the residual is equivalently

  **the mixing locus of a sweep is open**  (equivalently, the set of parameters whose slice is
  contained in `VA` or in `VB` is closed).

Note where the difficulty sits in this form: each of the two parameter sets is *separately* open
(`isOpen_forall_mem_of_continuous`); what is missing is closedness of their **union** — and the square
counterexample below shows that this cannot hold for an arbitrary configuration of two closed sets in
the square.  So this form of the residual localises exactly the place where `T`-invariance of the
walls together with the sweep structure must be consumed.

**Caution: the four conditions alone do NOT suffice** (a counterexample, found before committing to
the target).  In the square take `P := {u | 1/4 ≤ u.1 ≤ 1/3}` and `Q := {u | 2/3 ≤ u.1 ≤ 3/4}`: both
are closed, they are disjoint, `E₀ ∩ P = ∅` (as `P ⊆ {s ≥ 1/4}`) and `E₁ ∩ Q = ∅` (as
`Q ⊆ {s ≤ 3/4}`).  Yet the complement `U` has no connected subset meeting both edges: the component
of `U` containing `E₀` is `{s < 1/4}`, which misses `E₁`.  So the "connected trace from edge to edge"
statement is **false** for the abstract configuration, and a proof of the trace lemma must use the
*swept* structure of `P` and `Q` (they are pullbacks of the `T`-invariant walls `Ω \ VA`, `Ω \ VB`,
and `F` is a sweep, not an arbitrary map) — or, equivalently, use the homological input directly.
This is the same lesson as the refuted wall statement: the configuration that the crux reaches is
strictly richer than its combinatorial shadow, and the extra structure (T-invariance plus the sweep)
is exactly what the argument has to consume.

Equivalently (contrapositively) the four structural conditions above are *inconsistent* with `hno`.
The statement is recorded here rather than as a `sorry`: it has not been verified to follow from
exactly those hypotheses, and an unverified target with a `sorry` is debt — but the inputs are all
proved, so it is a well-posed next target.  The first move is already in the file
(`sweep_square_configuration` sets up `P`, `Q` and the edge conditions; `no_path_in_preimage_of_translate`
turns `hno` into the separation property of the `T`-pairing on `U`). -/

/-! ### Session 47, piece 1: the sheet index (the discrete half of the potential `Ψ`)

The §(H1) mechanism recorded above asks for a continuous `Ψ` on the strip with `Ψ (T q) = Ψ q + 1`
whose level sets are the walls, and the crossing argument it feeds.  The *discrete* half of that
potential is the following: under `hno` the components ("sheets") of `W` are permuted freely by `T`,
so choosing one sheet per `T`-orbit gives a locally constant `ℤ`-valued index on `W`, constant on
components, with `ind (T q) = ind q + 1`.  The within-cell coordinate `φ` (with `Ψ = ind + φ`) and
the crossing argument are the remaining pieces. -/
variable {p : ℝ} {W : Set (ℝ × ℝ)}

/-- The "same `T`-orbit of sheets" relation on `W`. -/
def wSheetRel (p : ℝ) (W : Set (ℝ × ℝ)) (q q' : ℝ × ℝ) : Prop :=
  ∃ k : ℤ, Tz p k q' ∈ connectedComponentIn W q

/-- The relation `wSheetRel` is a setoid on `W`. -/
def wSheetSetoid (p : ℝ) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) : Setoid ↥W where
  r q q' := wSheetRel p W (q : ℝ × ℝ) (q' : ℝ × ℝ)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro q
      exact ⟨0, by rw [Tz_zero]; exact mem_connectedComponentIn q.2⟩
    · intro q q' h
      obtain ⟨k, hk⟩ := h
      refine ⟨-k, ?_⟩
      have h1 : (q' : ℝ × ℝ) ∈ connectedComponentIn W (Tz p (-k) (q : ℝ × ℝ)) := by
        have hmem : Tz p (-k) (Tz p k (q' : ℝ × ℝ))
            ∈ Tz p (-k) '' connectedComponentIn W (q : ℝ × ℝ) := ⟨_, hk, rfl⟩
        rwa [Tz_image_connectedComponentIn hW (-k) q.2, ← Tz_add, neg_add_cancel, Tz_zero] at hmem
      rw [← connectedComponentIn_eq h1]
      exact mem_connectedComponentIn ((Tz_mem_iff hW (-k) (q : ℝ × ℝ)).mpr q.2)
    · intro q q' q'' h h'
      obtain ⟨k, hk⟩ := h
      obtain ⟨m, hm⟩ := h'
      refine ⟨k + m, ?_⟩
      have h1 : Tz p k (Tz p m (q'' : ℝ × ℝ)) ∈ Tz p k '' connectedComponentIn W (q' : ℝ × ℝ) :=
        ⟨_, hm, rfl⟩
      rw [Tz_image_connectedComponentIn hW k q'.2, ← connectedComponentIn_eq hk, ← Tz_add] at h1
      exact h1

/-- A chosen sheet in each `T`-orbit. -/
noncomputable def wSheetRep (p : ℝ) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) : Quotient (wSheetSetoid p hW) → ↥W :=
  fun c => Classical.choose (Quotient.exists_rep c)

lemma wSheetRep_spec (p : ℝ) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (c : Quotient (wSheetSetoid p hW)) :
    Quotient.mk _ (wSheetRep p hW c) = c :=
  Classical.choose_spec (Quotient.exists_rep c)

/-- Existence of the index: every point of `W` is a `Tz`-translate of the chosen sheet of its orbit. -/
lemma sheetIndex_exists (p : ℝ) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (q : ↥W) :
    ∃ k : ℤ, Tz p k ((wSheetRep p hW (Quotient.mk _ q) : ↥W) : ℝ × ℝ)
      ∈ connectedComponentIn W (q : ℝ × ℝ) := by
  have hc : Quotient.mk (wSheetSetoid p hW) (wSheetRep p hW (Quotient.mk _ q)) = Quotient.mk _ q := by
    rw [wSheetRep_spec]
  obtain ⟨k, hk⟩ := Quotient.exact hc
  -- hk : Tz p k (q : ℝ×ℝ) ∈ connectedComponentIn W (wSheetRep ...)
  refine ⟨-k, ?_⟩
  have h1 : (q : ℝ × ℝ)
      ∈ connectedComponentIn W (Tz p (-k) ((wSheetRep p hW (Quotient.mk _ q) : ↥W) : ℝ × ℝ)) := by
    have hmem : Tz p (-k) (Tz p k (q : ℝ × ℝ))
        ∈ Tz p (-k) '' connectedComponentIn W
            ((wSheetRep p hW (Quotient.mk _ q) : ↥W) : ℝ × ℝ) := ⟨_, hk, rfl⟩
    rwa [Tz_image_connectedComponentIn hW (-k) (wSheetRep p hW (Quotient.mk _ q)).2,
      ← Tz_add, neg_add_cancel, Tz_zero] at hmem
  rw [← connectedComponentIn_eq h1]
  exact mem_connectedComponentIn ((Tz_mem_iff hW (-k) _).mpr (wSheetRep p hW (Quotient.mk _ q)).2)

/-- **The sheet index**: a `ℤ`-valued function on `W`, constant on components and equivariant with
`T` up to `+1`. -/
noncomputable def sheetIndex (p : ℝ) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (q : ↥W) : ℤ :=
  Classical.choose (sheetIndex_exists p hW q)

lemma sheetIndex_spec (p : ℝ) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (q : ↥W) :
    Tz p (sheetIndex p hW q) ((wSheetRep p hW (Quotient.mk _ q) : ↥W) : ℝ × ℝ)
      ∈ connectedComponentIn W (q : ℝ × ℝ) :=
  Classical.choose_spec (sheetIndex_exists p hW q)

/-- Uniqueness of the index: this is where `hno` enters. -/
lemma sheetIndex_unique {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (hWop : IsOpen W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q)) (q : ↥W) {k : ℤ}
    (hk : Tz p k ((wSheetRep p hW (Quotient.mk _ q) : ↥W) : ℝ × ℝ)
      ∈ connectedComponentIn W (q : ℝ × ℝ)) :
    k = sheetIndex p hW q := by
  set R : ℝ × ℝ := ((wSheetRep p hW (Quotient.mk _ q) : ↥W) : ℝ × ℝ) with hR
  by_contra hne
  have h2 : Tz p (sheetIndex p hW q) R ∈ connectedComponentIn W (q : ℝ × ℝ) := sheetIndex_spec p hW q
  have heq : connectedComponentIn W (Tz p k R) = connectedComponentIn W (q : ℝ × ℝ) :=
    (connectedComponentIn_eq hk).symm
  have h3 : Tz p (sheetIndex p hW q) R ∈ connectedComponentIn W (Tz p k R) := by
    rw [heq]; exact h2
  have heq2 : Tz p (sheetIndex p hW q - k) (Tz p k R) = Tz p (sheetIndex p hW q) R := by
    rw [← Tz_add, sub_add_cancel]
  have h4 : Tz p (sheetIndex p hW q - k) (Tz p k R) ∈ connectedComponentIn W (Tz p k R) := by
    rw [heq2]; exact h3
  set z : ℝ × ℝ := Tz p k R with hz
  have hzW : z ∈ W := (Tz_mem_iff hW k _).mpr (wSheetRep p hW (Quotient.mk _ q)).2
  have hnonzero : sheetIndex p hW q - k ≠ 0 := fun h0 => hne (by omega)
  have hnocross : ¬ ∃ q' ∈ connectedComponentIn W z,
      JoinedIn (connectedComponentIn W z) q' (Tmap p q') := by
    rintro ⟨q', hq', hj⟩
    exact hno q' (connectedComponentIn_subset W z hq') (hj.mono (connectedComponentIn_subset W z))
  have hnot := orbit_infinite_of_no_crossing (p := p) hp hW hWop hzW hnocross
    (sheetIndex p hW q - k) hnonzero (Tz p k R) (mem_connectedComponentIn hzW)
  exact hnot h4


/-- The class of `T q` is the class of `q`. -/
lemma wSheetRel_translate {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {q : ℝ × ℝ} (hq : q ∈ W) :
    wSheetRel p W (Tmap p q) q := by
  refine ⟨1, ?_⟩
  have h1 : Tz p 1 q = Tmap p q := by
    apply Prod.ext <;> simp [Tz, Tmap]
  rw [h1]
  exact mem_connectedComponentIn ((hW q).mp hq)

/-- **The sheet index exists**: a locally constant `ℤ`-valued function on `W`, constant on the
components of `W` and shifting by `+1` under `T`. -/
theorem exists_sheet_index_aei {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hWop : IsOpen W) (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q)) :
    ∃ ind : ℝ × ℝ → ℤ,
      (∀ q : ℝ × ℝ, q ∈ W → ind (Tmap p q) = ind q + 1) ∧
      (∀ q q' : ℝ × ℝ, q ∈ W → q' ∈ W → JoinedIn W q q' → ind q = ind q') := by
  classical
  have hcls_eq : ∀ q q' : ↥W, JoinedIn W (q : ℝ × ℝ) (q' : ℝ × ℝ) →
      Quotient.mk (wSheetSetoid p hW) q = Quotient.mk (wSheetSetoid p hW) q' := by
    intro q q' h
    refine Quotient.sound ⟨0, ?_⟩
    rw [Tz_zero]
    exact mem_connectedComponentIn_of_joinedIn h
  have key : ∀ q q' : ↥W, JoinedIn W (q : ℝ × ℝ) (q' : ℝ × ℝ) →
      sheetIndex p hW q = sheetIndex p hW q' := by
    intro q q' h
    have hmem : (q' : ℝ × ℝ) ∈ connectedComponentIn W (q : ℝ × ℝ) :=
      mem_connectedComponentIn_of_joinedIn h
    have heq : connectedComponentIn W (q : ℝ × ℝ) = connectedComponentIn W (q' : ℝ × ℝ) :=
      connectedComponentIn_eq hmem
    have hrep : wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) q)
        = wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) q') := by
      rw [hcls_eq q q' h]
    have hspec := sheetIndex_spec p hW q
    rw [heq, hrep] at hspec
    exact sheetIndex_unique (p := p) hp hW hWop hno q' hspec
  have hequiv : ∀ (q : ℝ × ℝ) (hq : q ∈ W),
      sheetIndex p hW ⟨Tmap p q, (hW q).mp hq⟩ = sheetIndex p hW ⟨q, hq⟩ + 1 := by
    intro q hq
    have hTq : Tmap p q ∈ W := (hW q).mp hq
    have hcls : Quotient.mk (wSheetSetoid p hW) ⟨Tmap p q, hTq⟩
        = Quotient.mk (wSheetSetoid p hW) ⟨q, hq⟩ := by
      refine Quotient.sound ?_
      exact wSheetRel_translate hW hq
    have hrep : wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨Tmap p q, hTq⟩)
        = wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨q, hq⟩) := by rw [hcls]
    have hspec := sheetIndex_spec p hW ⟨q, hq⟩
    have hstep : Tmap p (Tz p (sheetIndex p hW ⟨q, hq⟩)
        ((wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨q, hq⟩) : ↥W) : ℝ × ℝ))
        = Tz p (sheetIndex p hW ⟨q, hq⟩ + 1)
          ((wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨q, hq⟩) : ↥W) : ℝ × ℝ) :=
      Tmap_Tz p _ _
    have hmem2 : Tz p (sheetIndex p hW ⟨q, hq⟩ + 1)
        ((wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨q, hq⟩) : ↥W) : ℝ × ℝ)
        ∈ connectedComponentIn W (Tmap p q) := by
      rw [← Tmap_image_connectedComponentIn hW hq]
      exact ⟨_, hspec, hstep⟩
    rw [← hrep] at hmem2
    exact (sheetIndex_unique (p := p) hp hW hWop hno ⟨Tmap p q, hTq⟩ hmem2).symm
  refine ⟨fun q => if hq : q ∈ W then sheetIndex p hW ⟨q, hq⟩ else 0, ?_, ?_⟩
  · intro q hq
    have hTq : Tmap p q ∈ W := (hW q).mp hq
    show (if h : Tmap p q ∈ W then sheetIndex p hW ⟨Tmap p q, h⟩ else 0)
        = (if h : q ∈ W then sheetIndex p hW ⟨q, h⟩ else 0) + 1
    rw [dif_pos hTq, dif_pos hq]
    exact hequiv q hq
  · intro q q' hq hq' h
    show (if h₁ : q ∈ W then sheetIndex p hW ⟨q, h₁⟩ else 0)
        = (if h₂ : q' ∈ W then sheetIndex p hW ⟨q', h₂⟩ else 0)
    rw [dif_pos hq, dif_pos hq']
    exact key ⟨q, hq⟩ ⟨q', hq'⟩ h


/-- **A `T`-equivariant continuous function blocks translate crossings through its integer levels.**

If `Ψ` is continuous with `Ψ (T q) = Ψ q + 1`, and `VA` avoids all integer values of `Ψ`, then no
translate crossing lies inside `VA`: along a `T`-crossing the value of `Ψ` changes by `1`, so it must
cross an integer level, which is forbidden. -/
theorem no_crossing_of_potential_avoids_integers {p : ℝ}
    {Ψ : ℝ × ℝ → ℝ} (hΨc : Continuous Ψ)
    (hΨT : ∀ q : ℝ × ℝ, Ψ (Tmap p q) = Ψ q + 1)
    {VA : Set (ℝ × ℝ)} (hΨ : ∀ q ∈ VA, ∀ n : ℤ, Ψ q ≠ (n : ℝ))
    {z : ℝ × ℝ} (hz : z ∈ VA) : ¬ JoinedIn VA z (Tmap p z) := by
  rintro ⟨γ, hγ⟩
  have hcont : Continuous fun t : Set.Icc (0:ℝ) 1 => Ψ (γ t) := hΨc.comp γ.continuous
  have h0 : Ψ (γ 0) = Ψ z := by rw [γ.source]
  have h1 : Ψ (γ 1) = Ψ z + 1 := by
    rw [γ.target, hΨT]
  have hnotint : Ψ z ≠ ((⌈Ψ z⌉ : ℤ) : ℝ) := hΨ z hz ⌈Ψ z⌉
  have hgt : Ψ z < ((⌈Ψ z⌉ : ℤ) : ℝ) := by
    by_contra hcon
    simp only [not_lt] at hcon
    have hle : ((⌈Ψ z⌉ : ℤ) : ℝ) ≤ Ψ z := hcon
    have hge : Ψ z ≤ ((⌈Ψ z⌉ : ℤ) : ℝ) := by
      have := Int.le_ceil (Ψ z)
      exact_mod_cast this
    exact hnotint (le_antisymm hge hle)
  have hpre : IsPreconnected (Set.univ : Set (Set.Icc (0:ℝ) 1)) := isPreconnected_univ
  have hsub := hpre.intermediate_value (Set.mem_univ (0 : Set.Icc (0:ℝ) 1))
    (Set.mem_univ (1 : Set.Icc (0:ℝ) 1)) hcont.continuousOn
  have hmem : ((⌈Ψ z⌉ : ℤ) : ℝ) ∈ Set.Icc (Ψ (γ 0)) (Ψ (γ 1)) := by
    rw [h0, h1]
    exact ⟨le_of_lt hgt, le_of_lt (Int.ceil_lt_add_one (Ψ z))⟩
  obtain ⟨t, -, ht⟩ := hsub hmem
  exact hΨ (γ t) (hγ t) ⌈Ψ z⌉ ht


/-! ### Session 49, seam (i): the cell coordinate and the potential on `W`

Standing on the sheet index (`exists_sheet_index_aei`) this adds the within-cell coordinate and the
resulting potential on the free region: `cellPotential p a b hW q = ind q + (q.2 - a)/(b - a)`,
continuous on `W`, `T`-equivariant (`Ψ (T q) = Ψ q + 1`), taking no integer value on `W`, and
normalised so that `Ψ q - ind q ∈ (0,1)`.  The two remaining seams are the extension across
`K ∩ Ω` and the preconnectedness of the level sets. -/

/-- The index is constant on components. -/
lemma sheetIndex_eq_of_joinedIn {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hWop : IsOpen W) (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q))
    {q q' : ↥W} (h : JoinedIn W (q : ℝ × ℝ) (q' : ℝ × ℝ)) :
    sheetIndex p hW q = sheetIndex p hW q' := by
  have hmem : (q' : ℝ × ℝ) ∈ connectedComponentIn W (q : ℝ × ℝ) :=
    mem_connectedComponentIn_of_joinedIn h
  have heq : connectedComponentIn W (q : ℝ × ℝ) = connectedComponentIn W (q' : ℝ × ℝ) :=
    connectedComponentIn_eq hmem
  have hrel : wSheetRel p W (q : ℝ × ℝ) (q' : ℝ × ℝ) := ⟨0, by rw [Tz_zero]; exact hmem⟩
  have hcls : Quotient.mk (wSheetSetoid p hW) q = Quotient.mk (wSheetSetoid p hW) q' :=
    Quotient.sound hrel
  have hrep : wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) q)
      = wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) q') := by rw [hcls]
  have hspec := sheetIndex_spec p hW q
  rw [heq, hrep] at hspec
  exact sheetIndex_unique (p := p) hp hW hWop hno q' hspec

/-- The index shifts by `+1` under `T`. -/
lemma sheetIndex_translate {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hWop : IsOpen W) (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q)) (q : ↥W) :
    sheetIndex p hW ⟨Tmap p (q : ℝ × ℝ), (hW (q : ℝ × ℝ)).mp q.2⟩ = sheetIndex p hW q + 1 := by
  have hTq : Tmap p (q : ℝ × ℝ) ∈ W := (hW (q : ℝ × ℝ)).mp q.2
  have hcls : Quotient.mk (wSheetSetoid p hW) ⟨Tmap p (q : ℝ × ℝ), hTq⟩
      = Quotient.mk (wSheetSetoid p hW) ⟨(q : ℝ × ℝ), q.2⟩ := by
    refine Quotient.sound ?_
    exact wSheetRel_translate hW q.2
  have hrep : wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨Tmap p (q : ℝ × ℝ), hTq⟩)
      = wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨(q : ℝ × ℝ), q.2⟩) := by rw [hcls]
  have hspec := sheetIndex_spec p hW ⟨(q : ℝ × ℝ), q.2⟩
  have hstep : Tmap p (Tz p (sheetIndex p hW ⟨(q : ℝ × ℝ), q.2⟩)
      ((wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨(q : ℝ × ℝ), q.2⟩) : ↥W) : ℝ × ℝ))
      = Tz p (sheetIndex p hW ⟨(q : ℝ × ℝ), q.2⟩ + 1)
        ((wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨(q : ℝ × ℝ), q.2⟩) : ↥W) : ℝ × ℝ) :=
    Tmap_Tz p _ _
  have hmem2 : Tz p (sheetIndex p hW ⟨(q : ℝ × ℝ), q.2⟩ + 1)
      ((wSheetRep p hW (Quotient.mk (wSheetSetoid p hW) ⟨(q : ℝ × ℝ), q.2⟩) : ↥W) : ℝ × ℝ)
      ∈ connectedComponentIn W (Tmap p (q : ℝ × ℝ)) := by
    rw [← Tmap_image_connectedComponentIn hW q.2]
    exact ⟨_, hspec, hstep⟩
  rw [← hrep] at hmem2
  exact (sheetIndex_unique (p := p) hp hW hWop hno ⟨Tmap p (q : ℝ × ℝ), hTq⟩ hmem2).symm

/-- The index is locally constant on `W`. -/
lemma sheetIndex_eventually_eq {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hWop : IsOpen W) (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q)) (q : ↥W) :
    ∃ δ > 0, ∀ (q' : ℝ × ℝ) (hq' : q' ∈ W), dist q' (q : ℝ × ℝ) < δ →
      sheetIndex p hW ⟨q', hq'⟩ = sheetIndex p hW q := by
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hWop (q : ℝ × ℝ) q.2
  refine ⟨δ, hδ, ?_⟩
  intro q' hq' hlt
  have hq'ball : q' ∈ Metric.ball (q : ℝ × ℝ) δ := by rwa [Metric.mem_ball]
  have hjoin : JoinedIn W (q : ℝ × ℝ) q' :=
    (joinedIn_of_convex (convex_ball (q : ℝ × ℝ) δ) (Metric.mem_ball_self hδ) hq'ball).mono
      hδsub
  exact sheetIndex_eq_of_joinedIn (p := p) hp hWop hW hno
    (q := ⟨q', hq'⟩) (q' := ⟨(q : ℝ × ℝ), q.2⟩) hjoin.symm

/-- **The cell potential on the free region**: the sheet index plus the normalised height. -/
noncomputable def cellPotential (p a b : ℝ) {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) (q : ℝ × ℝ) : ℝ := by
  classical
  exact if hq : q ∈ W then (sheetIndex p hW ⟨q, hq⟩ : ℝ) + (q.2 - a) / (b - a) else 0

lemma cellPotential_of_mem {p a b : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {q : ℝ × ℝ} (hq : q ∈ W) :
    cellPotential p a b hW q = (sheetIndex p hW ⟨q, hq⟩ : ℝ) + (q.2 - a) / (b - a) := by
  classical
  rw [cellPotential, dif_pos hq]

lemma cellPotential_sub_index {p a b : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) {q : ℝ × ℝ} (hq : q ∈ W) :
    cellPotential p a b hW q - (sheetIndex p hW ⟨q, hq⟩ : ℝ) = (q.2 - a) / (b - a) := by
  rw [cellPotential_of_mem hW hq]; ring

lemma cellPotential_add_one {p a b : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hWop : IsOpen W) (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q)) {q : ℝ × ℝ} (hq : q ∈ W) :
    cellPotential p a b hW (Tmap p q) = cellPotential p a b hW q + 1 := by
  have hTq : Tmap p q ∈ W := (hW q).mp hq
  rw [cellPotential_of_mem hW hTq, cellPotential_of_mem hW hq]
  have hshift := sheetIndex_translate (p := p) hp hWop hW hno ⟨q, hq⟩
  have hsub : (⟨Tmap p q, hTq⟩ : ↥W) = ⟨Tmap p q, (hW q).mp hq⟩ := rfl
  rw [hsub, hshift]
  have hT2 : (Tmap p q).2 = q.2 := rfl
  rw [hT2]
  push_cast
  ring

lemma cellPotential_not_int {p a b : ℝ} (hab : a < b) {W : Set (ℝ × ℝ)}
    (hWsub : W ⊆ stripS a b) (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    {q : ℝ × ℝ} (hq : q ∈ W) (n : ℤ) : cellPotential p a b hW q ≠ (n : ℝ) := by
  rw [cellPotential_of_mem hW hq]
  intro hcon
  have hb := hWsub hq
  have hh0 : 0 < (q.2 - a) / (b - a) := div_pos (by linarith [hb.1]) (by linarith)
  have hh1 : (q.2 - a) / (b - a) < 1 := by rw [div_lt_one (by linarith)]; linarith [hb.2]
  have hint : ((n - sheetIndex p hW ⟨q, hq⟩ : ℤ) : ℝ) = (q.2 - a) / (b - a) := by
    push_cast; linarith
  have hm0 : (0 : ℝ) < ((n - sheetIndex p hW ⟨q, hq⟩ : ℤ) : ℝ) := by rw [hint]; exact hh0
  have hm1 : ((n - sheetIndex p hW ⟨q, hq⟩ : ℤ) : ℝ) < 1 := by rw [hint]; exact hh1
  have h0 : (0 : ℤ) < n - sheetIndex p hW ⟨q, hq⟩ := by exact_mod_cast hm0
  have h1 : n - sheetIndex p hW ⟨q, hq⟩ < 1 := by exact_mod_cast hm1
  omega

lemma cellPotential_continuousAt {p a b : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hWop : IsOpen W) (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q)) {q : ℝ × ℝ} (hq : q ∈ W) :
    ContinuousAt (cellPotential p a b hW) q := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hWop q hq
  obtain ⟨δ, hδ, hev⟩ := sheetIndex_eventually_eq (p := p) hp hWop hW hno ⟨q, hq⟩
  have hcont : ContinuousAt
      (fun q' : ℝ × ℝ => (sheetIndex p hW ⟨q, hq⟩ : ℝ) + (q'.2 - a) / (b - a)) q := by
    fun_prop
  refine hcont.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds q (lt_min hε hδ)] with q' hq'
  have hd : dist q' q < min ε δ := Metric.mem_ball.mp hq'
  have hq'W : q' ∈ W :=
    hεsub (Metric.mem_ball.mpr (lt_of_lt_of_le hd (min_le_left _ _)))
  rw [cellPotential_of_mem hW hq'W]
  rw [hev q' hq'W (lt_of_lt_of_le hd (min_le_right _ _))]

/-- **Seam (i): the cell coordinate, packaged.**  There is a potential `Ψ` on the free region `W`,
continuous there, equivariant with `T` up to `+1`, taking no integer value on `W`, and normalised so
that `Ψ q` sits between the consecutive integers around `ind q`. -/
theorem exists_potential_on_free_region {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W : Set (ℝ × ℝ)} (hWop : IsOpen W) (hWsub : W ⊆ stripS a b)
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q)) :
    ∃ Ψ : ℝ × ℝ → ℝ,
      (∀ q ∈ W, ContinuousAt Ψ q) ∧
      (∀ q ∈ W, Ψ (Tmap p q) = Ψ q + 1) ∧
      (∀ q ∈ W, ∀ n : ℤ, Ψ q ≠ (n : ℝ)) ∧
      (∀ q ∈ W, ∃ k : ℤ, Ψ q - (k : ℝ) ∈ Set.Ioo 0 1) := by
  refine ⟨cellPotential p a b hW,
    fun q hq => cellPotential_continuousAt hp hWop hW hno hq,
    fun q hq => cellPotential_add_one hp hWop hW hno hq,
    fun q hq n => cellPotential_not_int hab hWsub hW hq n,
    fun q hq => ⟨sheetIndex p hW ⟨q, hq⟩, ?_⟩⟩
  rw [cellPotential_sub_index hW hq]
  have hb := hWsub hq
  exact ⟨div_pos (by linarith [hb.1]) (by linarith), by
    rw [div_lt_one (by linarith)]; linarith [hb.2]⟩


/-! ### Session 51, seam (ii): the behaviour of the cell coordinate at a wall

On a sheet (an open preconnected subset of `W`) the cell potential is `ind(C)` plus the normalised
height, so it has a well-defined limit `ind(C) + (q₀.2 - a)/(b - a)` at every point `q₀` of the
strip.  That pins down how the cell coordinate behaves as one approaches a wall point from inside
a sheet; the remaining content of seam (ii) is the *compatibility* of these limits between the two
sheets adjacent to a wall (brick 2 below is the equal-index case). -/

/-- The index is constant on an open preconnected subset of `W` (a "sheet"). -/
lemma sheetIndex_eq_on_of_isOpen_isPreconnected {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hWop : IsOpen W) (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q))
    {C : Set (ℝ × ℝ)} (hCopen : IsOpen C) (hCpc : IsPreconnected C) (hCne : C.Nonempty)
    (hCW : C ⊆ W) {x y : ℝ × ℝ} (hx : x ∈ C) (hy : y ∈ C) :
    sheetIndex p hW ⟨x, hCW hx⟩ = sheetIndex p hW ⟨y, hCW hy⟩ := by
  have hCconn : IsConnected C := ⟨hCne, hCpc⟩
  have hpc : IsPathConnected C := (hCopen.isConnected_iff_isPathConnected).mp hCconn
  have hjoin : JoinedIn C x y := hpc.joinedIn x hx y hy
  exact sheetIndex_eq_of_joinedIn (p := p) hp hWop hW hno (hjoin.mono hCW)

/-- **Seam (ii), brick 1: the cell coordinate extends continuously to the boundary of a sheet.**

On a sheet `C` (an open preconnected subset of `W`) the cell potential is `ind(C) + height`, where
`ind(C)` is the (constant) sheet index of `C`; hence its limit at every point `q₀` of the strip is
`ind(C) + (q₀.2 - a)/(b - a)`.  This pins down the behaviour of the cell coordinate as one approaches
a wall point from inside a sheet; what remains for seam (ii) is the *compatibility* of these limits
between the different sheets adjacent to a wall. -/
theorem cellPotential_tendsto_of_preconnected {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W : Set (ℝ × ℝ)} (hWop : IsOpen W) (hWsub : W ⊆ stripS a b)
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q))
    {C : Set (ℝ × ℝ)} (hCopen : IsOpen C) (hCpc : IsPreconnected C) (hCne : C.Nonempty)
    (hCW : C ⊆ W) {q₁ : ℝ × ℝ} (hq₁ : q₁ ∈ C) {q₀ : ℝ × ℝ} (hq₀ : q₀ ∈ stripS a b) :
    Tendsto (cellPotential p a b hW) (𝓝[C] q₀)
      (𝓝 ((sheetIndex p hW ⟨q₁, hCW hq₁⟩ : ℝ) + (q₀.2 - a) / (b - a))) := by
  have hcont : ContinuousAt
      (fun q : ℝ × ℝ => (sheetIndex p hW ⟨q₁, hCW hq₁⟩ : ℝ) + (q.2 - a) / (b - a)) q₀ := by
    fun_prop
  have happly : ∀ q ∈ C, cellPotential p a b hW q
      = (sheetIndex p hW ⟨q₁, hCW hq₁⟩ : ℝ) + (q.2 - a) / (b - a) := by
    intro q hq
    rw [cellPotential_of_mem hW (hCW hq)]
    rw [sheetIndex_eq_on_of_isOpen_isPreconnected (p := p) hp hWop hW hno hCopen hCpc hCne hCW
      hq₁ hq]
  have hev : (fun q => cellPotential p a b hW q) =ᶠ[𝓝[C] q₀]
      (fun q : ℝ × ℝ => (sheetIndex p hW ⟨q₁, hCW hq₁⟩ : ℝ) + (q.2 - a) / (b - a)) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact happly q hq
  exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm

/-- **Seam (ii), brick 2: adjacent sheets of equal index have the same boundary behaviour.**

If two sheets `C`, `C' ⊆ W` carry the same sheet index, then the limits of the cell potential at a
common strip point `q₀` agree — the equal-index case of the compatibility needed to glue the cell
coordinate across a wall. -/
theorem cellPotential_tendsto_eq_of_same_index {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W : Set (ℝ × ℝ)} (hWop : IsOpen W) (hWsub : W ⊆ stripS a b)
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q))
    {C C' : Set (ℝ × ℝ)} (hCop : IsOpen C) (hCpc : IsPreconnected C) (hCne : C.Nonempty)
    (hCW : C ⊆ W) (hCop' : IsOpen C') (hCpc' : IsPreconnected C') (hCne' : C'.Nonempty)
    (hCW' : C' ⊆ W) {q₁ : ℝ × ℝ} (hq₁ : q₁ ∈ C) {q₁' : ℝ × ℝ} (hq₁' : q₁' ∈ C')
    (hidx : sheetIndex p hW ⟨q₁, hCW hq₁⟩ = sheetIndex p hW ⟨q₁', hCW' hq₁'⟩)
    {q₀ : ℝ × ℝ} (hq₀ : q₀ ∈ stripS a b) :
    (sheetIndex p hW ⟨q₁, hCW hq₁⟩ : ℝ) + (q₀.2 - a) / (b - a)
      = (sheetIndex p hW ⟨q₁', hCW' hq₁'⟩ : ℝ) + (q₀.2 - a) / (b - a) := by
  rw [hidx]


/-- **Seam (iii), brick 1: the level sets of the cell potential are `T`-permuted.**

Inside `W` the level set of the cell potential at `c` is carried by `T` onto the level set at `c + 1`
— the `T`-structure that the assembly lemma (`one_side_no_crossing_of_potential`) uses to force the
"side" of the walls to be independent of the level. -/
lemma cellPotential_levelSet_translate {p a b : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hWop : IsOpen W) (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q)) (c : ℝ) :
    Tmap p '' ({q : ℝ × ℝ | q ∈ W ∧ cellPotential p a b hW q = c})
      = {q : ℝ × ℝ | q ∈ W ∧ cellPotential p a b hW q = c + 1} := by
  ext q
  constructor
  · rintro ⟨q', ⟨hq'W, hq'⟩, rfl⟩
    refine ⟨(hW q').mp hq'W, ?_⟩
    rw [cellPotential_add_one (p := p) (a := a) (b := b) hp hWop hW hno hq'W, hq']
  · rintro ⟨hqW, hq⟩
    set Tp : ℝ × ℝ := (q.1 - p, q.2) with hTp
    have hT : Tmap p Tp = q := by
      rw [hTp]; ext <;> simp [Tmap]
    have hTpW : Tp ∈ W := (hW Tp).mpr (by rw [hT]; exact hqW)
    refine ⟨Tp, ⟨hTpW, ?_⟩, hT⟩
    have hstep := cellPotential_add_one (p := p) (a := a) (b := b) hp hWop hW hno hTpW
    rw [hT] at hstep
    linarith


/-- Closure of a `Tz`-translate. -/
lemma Tz_image_closure (p : ℝ) (k : ℤ) (S : Set (ℝ × ℝ)) :
    Tz p k '' closure S = closure (Tz p k '' S) := by
  have hpt : ∀ q : ℝ × ℝ, Homeomorph.addRight (((k : ℝ) * p, 0) : ℝ × ℝ) q = Tz p k q := by
    intro q
    ext <;> simp [Homeomorph.addRight, Tz]
  have he : (Homeomorph.addRight (((k : ℝ) * p, 0) : ℝ × ℝ)) = fun q : ℝ × ℝ => Tz p k q :=
    funext hpt
  have h := (Homeomorph.addRight (((k : ℝ) * p, 0) : ℝ × ℝ)).image_closure S
  rw [he] at h
  exact h

/-- **Seam (ii), brick 3: the boundary data of the cell coordinate is `T`-equivariant.**

If a sheet `C` accumulates at `q₀`, then its `T`-image accumulates at `T q₀` (`Tz_image_closure`), the
sheet index shifts by one and the height is unchanged, so the value the cell coordinate must take at
`T q₀` from `T '' C` is the value at `q₀` shifted by `1`.  This is the `T`-equivariance of the gluing
data for sheets of *different* index: iterating, the compatibility at a wall only has to be checked
on one period. -/
theorem cellPotential_tendsto_image {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W : Set (ℝ × ℝ)} (hWop : IsOpen W) (hWsub : W ⊆ stripS a b)
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hno : ∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q))
    {C : Set (ℝ × ℝ)} (hCop : IsOpen C) (hCpc : IsPreconnected C) (hCne : C.Nonempty)
    (hCW : C ⊆ W) {q₁ : ℝ × ℝ} (hq₁ : q₁ ∈ C) {q₀ : ℝ × ℝ} (hq₀ : q₀ ∈ stripS a b) :
    Tendsto (cellPotential p a b hW) (𝓝[Tmap p '' C] (Tmap p q₀))
      (𝓝 ((sheetIndex p hW ⟨Tmap p q₁, (hW q₁).mp (hCW hq₁)⟩ : ℝ)
        + (q₀.2 - a) / (b - a))) := by
  have himage_open : IsOpen (Tmap p '' C) := by
    have hpre : Tmap p '' C = (fun q : ℝ × ℝ => (q.1 - p, q.2)) ⁻¹' C := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [Tmap] using hx
      · intro hq
        exact ⟨(q.1 - p, q.2), hq, by simp [Tmap]⟩
    rw [hpre]
    exact hCop.preimage (continuous_Tmap_inv p)
  have himage_pc : IsPreconnected (Tmap p '' C) :=
    hCpc.image _ (continuous_Tmap p).continuousOn
  have himage_ne : (Tmap p '' C).Nonempty := hCne.image _
  have himage_sub : Tmap p '' C ⊆ W := by
    rintro q ⟨x, hx, rfl⟩
    exact (hW x).mp (hCW hx)
  have hmem : Tmap p q₁ ∈ Tmap p '' C := ⟨q₁, hq₁, rfl⟩
  have hmain := cellPotential_tendsto_of_preconnected (p := p) (a := a) (b := b) hp hab
    hWop hWsub hW hno himage_open himage_pc himage_ne himage_sub hmem (q₀ := Tmap p q₀) hq₀
  simpa [Tmap] using hmain


/-! ### Session 50: the crux reduced to a single construction (the potential)

With the cell coordinate of seam (i) in hand, the last assembly step is now formal: *if* a continuous
`T`-equivariant potential exists which is integer-free on `W = VA ∩ VB` and whose level sets are
preconnected and lie in the strip, *then* the cover has a translate crossing.  The level sets are
permuted by `T` (`T '' {Ψ = n} = {Ψ = n+1}`), each lies on one side of the cover
(`⊆ VAᶜ` or `⊆ VBᶜ`, by the disjoint-closed-sets splitting, since they lie in the strip), the side is
`T`-invariant, and the levels are `ℤ`-indexed, so either every level set lies in `VAᶜ` — whence `VA`
avoids every integer value of `Ψ` and `no_crossing_of_potential_avoids_integers` kills all crossings
inside `VA` — or every level set lies in `VBᶜ`.  This is `one_side_no_crossing_of_potential` below.

So the whole residual is the *existence* of that potential, stated as `exists_equivariant_potential`
below.  Note the form: what the assembly consumes is preconnectedness of the *parts inside the strip*
of the level sets (`levelSet Ψ n ∩ stripS a b`), not their containment in the strip — and that is the
form the first concrete construction satisfies: `exists_potential_of_free_graph` proves that if some
continuous graph `y ↦ (u y, y)` in the strip avoids `W`, then `Ψ (x,y) = (x - u y)/p` is a potential,
its level sets meeting the strip in graphs over `y`. -/
/-- The level set of the potential at the integer `n`. -/
def levelSet (Ψ : ℝ × ℝ → ℝ) (n : ℤ) : Set (ℝ × ℝ) := {q : ℝ × ℝ | Ψ q = (n : ℝ)}

lemma mem_levelSet {Ψ : ℝ × ℝ → ℝ} {n : ℤ} {q : ℝ × ℝ} :
    q ∈ levelSet Ψ n ↔ Ψ q = (n : ℝ) := Iff.rfl

/-- **If the potential exists, one of the two sets carries no translate crossing.**  The
level sets of a `T`-equivariant potential are permuted by `T` and their parts inside the strip,
being preconnected, lie on one side of the cover; the side is `T`-invariant and the levels are
`ℤ`-indexed, so one side holds them all, and the potential then blocks every crossing there. -/
theorem one_side_no_crossing_of_potential {p a b : ℝ}
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    {Ψ : ℝ × ℝ → ℝ} (hΨc : Continuous Ψ)
    (hΨT : ∀ q : ℝ × ℝ, Ψ (Tmap p q) = Ψ q + 1)
    (hΨW : ∀ q ∈ VA ∩ VB, ∀ n : ℤ, Ψ q ≠ (n : ℝ))
    (hΨpre : ∀ n : ℤ, IsPreconnected (levelSet Ψ n ∩ stripS a b)) :
    (∀ z ∈ VA, ¬ JoinedIn VA z (Tmap p z)) ∨ (∀ z ∈ VB, ¬ JoinedIn VB z (Tmap p z)) := by
  classical
  have hsubA : VA ⊆ stripS a b := hcover ▸ subset_union_left
  have hsubB : VB ⊆ stripS a b := hcover ▸ subset_union_right
  -- step 1: each level set inside the strip lies on one side
  have hside : ∀ n : ℤ,
      levelSet Ψ n ∩ stripS a b ⊆ VAᶜ ∨ levelSet Ψ n ∩ stripS a b ⊆ VBᶜ := by
    intro n
    have hsub : levelSet Ψ n ∩ stripS a b ⊆ VAᶜ ∪ VBᶜ := by
      rintro q ⟨hq, -⟩
      by_cases hA : q ∈ VA
      · by_cases hB : q ∈ VB
        · exact absurd (mem_levelSet.mp hq) (hΨW q ⟨hA, hB⟩ n)
        · exact Or.inr hB
      · exact Or.inl hA
    have hdisj : (levelSet Ψ n ∩ stripS a b) ∩ (VAᶜ ∩ VBᶜ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro q ⟨⟨hq, hqs⟩, ⟨hA, hB⟩⟩
      have : q ∈ (VA ∪ VB)ᶜ := by
        simp only [Set.mem_compl_iff, Set.mem_union, not_or]
        exact ⟨hA, hB⟩
      rw [hcover] at this
      exact this hqs
    exact isPreconnected_iff_subset_of_disjoint_closed.mp (hΨpre n) VAᶜ VBᶜ
      hVA.isClosed_compl hVB.isClosed_compl hsub hdisj
  -- step 2: the side is `T`-invariant
  have hstep : ∀ n : ℤ,
      (levelSet Ψ n ∩ stripS a b ⊆ VAᶜ) ↔ (levelSet Ψ (n + 1) ∩ stripS a b ⊆ VAᶜ) := by
    intro n
    constructor
    · intro h q hq
      have hq1 : Ψ q = ((n : ℝ) + 1) := by
        have := mem_levelSet.mp hq.1
        push_cast at this
        exact this
      have hpre : (q.1 - p, q.2) ∈ levelSet Ψ n ∩ stripS a b := by
        refine ⟨?_, by simpa [stripS] using hq.2⟩
        rw [mem_levelSet]
        have hh := hΨT (q.1 - p, q.2)
        simp only [Tmap] at hh
        have hqeq : ((q.1 - p) + p, q.2) = q := by ext <;> ring
        rw [hqeq] at hh
        linarith
      have hmem := h hpre
      intro hcon
      exact hmem ((hperA ((q.1 - p, q.2) : ℝ × ℝ)).mpr (by simpa [Tmap] using hcon))
    · intro h q hq
      have h2 : Tmap p q ∈ levelSet Ψ (n + 1) ∩ stripS a b := by
        refine ⟨?_, by simpa [stripS, Tmap] using hq.2⟩
        rw [mem_levelSet, hΨT, mem_levelSet.mp hq.1]
        push_cast; ring
      have hmem := h h2
      intro hcon
      exact hmem ((hperA q).mp hcon)
  -- step 3: the side is constant in the level
  have hconst : ∀ n : ℤ,
      (levelSet Ψ 0 ∩ stripS a b ⊆ VAᶜ) ↔ (levelSet Ψ n ∩ stripS a b ⊆ VAᶜ) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ j ih => rw [← hstep j]; exact ih
    | pred j ih =>
        rw [hstep (-(j : ℤ) - 1)]
        convert ih using 2
        ring_nf
  -- step 4: conclude
  by_cases h0 : levelSet Ψ 0 ∩ stripS a b ⊆ VAᶜ
  · left
    refine fun z hz => no_crossing_of_potential_avoids_integers (p := p) hΨc hΨT ?_ hz
    intro q hq n hcon
    have hA : levelSet Ψ n ∩ stripS a b ⊆ VAᶜ := (hconst n).mp h0
    exact hA ⟨show q ∈ levelSet Ψ n from hcon, hsubA hq⟩ hq
  · right
    refine fun z hz => no_crossing_of_potential_avoids_integers (p := p) hΨc hΨT ?_ hz
    intro q hq n hcon
    have hAn : ¬ (levelSet Ψ n ∩ stripS a b ⊆ VAᶜ) := fun h => h0 ((hconst n).mpr h)
    have hB : levelSet Ψ n ∩ stripS a b ⊆ VBᶜ := (hside n).resolve_left hAn
    exact hB ⟨show q ∈ levelSet Ψ n from hcon, hsubB hq⟩ hq


/-- **A spanning graph blocks translate crossings.**

If `K` is `T`-invariant and contains the graph of a continuous `g` over the whole strip, then no
translate crossing stays inside `Kᶜ` and inside the strip: along a crossing `γ` from `z` to `T z` the
continuous function `t ↦ (γ t).1 - g (γ t).2` changes by exactly `p`, so by the intermediate value
theorem it takes a value `m * p` (`m : ℤ`); at that time the crossing point equals
`Tz p m (g y, y) ∈ K`.

This is the `⇐` direction of the duality between "no crossing in the complement" and "the complement
contains a transversal graph": it shows that supplying a free graph (as
`exists_potential_of_free_graph` does) is *exactly* a way of certifying that `W` contains no crossing
in the strip.  It is the reason `exists_potential_of_free_graph` is useful, and it is the half of the
duality that is provable without any covering-space input. -/
theorem spanning_graph_blocks_translate_path {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {K : Set (ℝ × ℝ)} (hperK : ∀ q : ℝ × ℝ, q ∈ K ↔ Tmap p q ∈ K)
    {g : ℝ → ℝ} (hg : Continuous g) (hgraph : ∀ y ∈ Set.Ioo a b, (g y, y) ∈ K) :
    ∀ z : ℝ × ℝ, z ∈ stripS a b → z ∉ K →
      ¬ ∃ γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ), γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, (γ t).2 ∈ Set.Ioo a b) ∧ ∀ t, γ t ∉ K := by
  intro z hz hzK
  rintro ⟨γ, hγ0, hγ1, hγstrip, hγK⟩
  set Φ : Set.Icc (0:ℝ) 1 → ℝ := fun t => (γ t).1 - g (γ t).2 with hΦdef
  have hΦc : Continuous Φ := by
    rw [hΦdef]
    exact (continuous_fst.comp γ.continuous).sub
      (hg.comp (continuous_snd.comp γ.continuous))
  have h0 : Φ 0 = z.1 - g z.2 := by rw [hΦdef]; simp [hγ0]
  have h1 : Φ 1 = z.1 - g z.2 + p := by rw [hΦdef]; simp [hγ1]; ring
  set c : ℝ := z.1 - g z.2 with hc
  set m : ℤ := ⌈c / p⌉ with hm
  have hle : c ≤ (m : ℝ) * p := by
    have h1' : c / p ≤ ((m : ℤ) : ℝ) := by
      rw [hm]; exact Int.le_ceil (c / p)
    calc c = (c / p) * p := by field_simp
      _ ≤ (m : ℝ) * p := by
          exact mul_le_mul_of_nonneg_right h1' (le_of_lt hp)
  have hlt : (m : ℝ) * p < c + p := by
    have h2 : ((m : ℤ) : ℝ) < c / p + 1 := by
      rw [hm]; exact Int.ceil_lt_add_one (c / p)
    have h3 : (m : ℝ) * p < (c / p + 1) * p := mul_lt_mul_of_pos_right h2 hp
    have h4 : (c / p + 1) * p = c + p := by field_simp
    linarith [h3, h4.le, h4.ge]
  have hmem : ((m : ℝ) * p) ∈ Set.Icc (Φ 0) (Φ 1) := by
    rw [h0, h1]
    exact ⟨hle, by linarith⟩
  have hpre : IsPreconnected (Set.univ : Set (Set.Icc (0:ℝ) 1)) := isPreconnected_univ
  have hsub := hpre.intermediate_value (Set.mem_univ (0 : Set.Icc (0:ℝ) 1))
    (Set.mem_univ (1 : Set.Icc (0:ℝ) 1)) hΦc.continuousOn
  obtain ⟨t, -, ht⟩ := hsub hmem
  have hy : (γ t).2 ∈ Set.Ioo a b := hγstrip t
  have hkey : γ t = Tz p m (g (γ t).2, (γ t).2) := by
    have hx : (γ t).1 = g (γ t).2 + (m : ℝ) * p := by
      have hΦt : (γ t).1 - g (γ t).2 = (m : ℝ) * p := ht
      linarith
    ext <;> simp [Tz, hx]
  have hmemK : Tz p m (g (γ t).2, (γ t).2) ∈ K :=
    (Tz_mem_iff hperK m (g (γ t).2, (γ t).2)).mpr (hgraph (γ t).2 hy)
  exact hγK t (hkey ▸ hmemK)

/-- **The graph potential.**  If there is a continuous graph `y ↦ (u y, y)` in the strip avoiding `W`,
then `Ψ (x,y) = (x - u y)/p` is a `T`-equivariant potential which is integer-free on `W` and whose
level sets meet the strip in graphs over `y` — hence in preconnected sets.

This is the first concrete construction of the analytic half: it reduces the existence of the
potential to the existence of a *continuous free graph* in the complement of `W`. -/
theorem exists_potential_of_free_graph {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W : Set (ℝ × ℝ)} (hWsub : W ⊆ stripS a b)
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    {u : ℝ → ℝ} (hu : Continuous u) (hfree : ∀ y ∈ Set.Ioo a b, (u y, y) ∉ W) :
    ∃ Ψ : ℝ × ℝ → ℝ, Continuous Ψ ∧
      (∀ q : ℝ × ℝ, Ψ (Tmap p q) = Ψ q + 1) ∧
      (∀ q ∈ W, ∀ n : ℤ, Ψ q ≠ (n : ℝ)) ∧
      (∀ n : ℤ, IsPreconnected ({q : ℝ × ℝ | Ψ q = (n : ℝ)} ∩ stripS a b)) := by
  refine ⟨fun q => (q.1 - u q.2) / p, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro q
    have hpne : p ≠ 0 := ne_of_gt hp
    simp only [Tmap]
    field_simp
    ring
  · intro q hq n hcon
    -- `q = Tz p n (u q.2, q.2)`, so `(u q.2, q.2) ∈ W` by `T`-invariance
    have hpne : p ≠ 0 := ne_of_gt hp
    have hx : q.1 = u q.2 + (n : ℝ) * p := by
      have := (div_eq_iff hpne).mp hcon
      linarith
    have hpre : (u q.2, q.2) ∈ W := by
      have h2 : Tz p n (u q.2, q.2) = q := by
        ext <;> simp [Tz, hx, mul_comm]
      have h1 : Tz p n (u q.2, q.2) ∈ W := by rw [h2]; exact hq
      exact (Tz_mem_iff hW n (u q.2, q.2)).mp h1
    exact hfree q.2 ⟨(hWsub hq).1, (hWsub hq).2⟩ hpre
  · intro n
    have himg : {q : ℝ × ℝ | (q.1 - u q.2) / p = (n : ℝ)} ∩ stripS a b
        = (fun y : ℝ => (u y + (n : ℝ) * p, y)) '' Set.Ioo a b := by
      ext q
      constructor
      · rintro ⟨hq, hqs⟩
        refine ⟨q.2, hqs, ?_⟩
        have hpne : p ≠ 0 := ne_of_gt hp
        have hx : q.1 = u q.2 + (n : ℝ) * p := by
          have := (div_eq_iff hpne).mp hq
          linarith
        ext <;> simp [hx]
      · rintro ⟨y, hy, rfl⟩
        constructor
        · have hpne : p ≠ 0 := ne_of_gt hp
          show (u y + (n : ℝ) * p - u y) / p = (n : ℝ)
          field_simp
          ring
        · exact hy
    rw [himg]
    have hcont : Continuous fun y : ℝ => (u y + (n : ℝ) * p, y) :=
      (hu.add continuous_const).prodMk continuous_id
    exact (isPreconnected_Ioo.image _ hcont.continuousOn)


/-! ### Session 54: why the residual is the *potential* and not a free graph

The single `sorry` of this file is `exists_equivariant_potential` (a `T`-equivariant potential `Ψ`).
This session clarified the shape of that residual and recorded the following.

* **The free-graph form is strictly stronger.**  `exists_potential_of_free_graph` builds `Ψ` from a
  continuous graph `y ↦ (u y, y)` inside `K = stripS a b \\ W`.  The converse fails: the level sets of
  the potential need not be graphs.  For example `W = {q | q.1 \\notin pℤ} ∩ stripS a b` (so
  `K = (pℤ × (a,b))`) has the potential `Ψ q = q.1 / p`, whose level sets are *vertical lines*.
  Accordingly `spanning_graph_blocks_translate_path` (proved above) shows that a free graph in `K`
  certifies `hno`, and it is a *sufficient* certificate, not an equivalent one.

* **The "minimal wall" argument for the potential is exactly the crux.**  For a wall `K = Ω \\ W`
  (`hno`) the standard Zorn argument that a *minimal* sub-wall is preconnected needs the two-set
  statement "if `A`, `B` are closed `T`-invariant with essential complements, then so is `A ∪ B`" —
  i.e. Denne's Mayer–Vietoris cancellation, which is the crux (or `mv_obligation`) itself.  So the
  potential is *not* easier than Mayer–Vietoris, and "minimality plus Janiszewski" cannot be used to
  prove it; this is the precise sense in which `exists_equivariant_potential` is the right residual.

* **What the potential really is.**  `Ψ` exists iff `K` contains a `T`-orbit `{L n}` of closed
  preconnected sets with `T (L n) = L (n+1)` and `⋃ n, L n ⊆ K` — a *ladder of walls*.  Conversely, by
  the intermediate value theorem, every such `L n` blocks every crossing (along a crossing `Ψ` runs
  from `Ψ z` to `Ψ z + 1`, so it meets an integer level).  Both the spiral example (`L n` = the graph
  of `log (y/(1-y)) + n p`) and the vertical-line example (`L n = {n p} × (a,b)`) are ladders.

* **A failed counterexample to the free-graph form.**  Let `a < b/2 < b` and
  `W := ((ℝ \\ (ℤ ∪ (1/2 + ℤ))) × (a, b/2)) ∪ ((ℝ \\ ((1/4 + ℤ) ∪ (3/4 + ℤ))) × (b/2, b))`
  (`p = 1`).  This `W` has *no* free graph: a continuous `u` with `(u y, y) ∉ W` would have to be
  locally constant with values in `ℤ ∪ (1/2 + ℤ)` below `b/2` and in `(1/4 + ℤ) ∪ (3/4 + ℤ)` above
  `b/2`, which is impossible by continuity at `y = b/2`.  But `hno` *fails* for this `W`: its "rooms"
  can be woven through (e.g. the crossing from `(0.1, b/4)` to `(1.1, b/4)` can be threaded around the
  lattice lines).  This is the mechanism by which `hno` excludes such ladders: a "lattice jump" is
  always avoidable by a path, hence never a wall. -/

/-! #### Where the residual sits (routes for the next stretch)

* **Route 1 — Mayer–Vietoris (Denne's proof).** `mv_obligation` above is *exactly* the statement that
  in the quotient annulus the exact sequence
  `H₁(VA ∩ VB) → H₁(VA) ⊕ H₁(VB) → H₁(S)` (for the open cover `{VA, VB}` of the annulus `S`)
  lifts the pair `(α, -β)` of degree-one classes to `H₁(VA ∩ VB)`.  It is TRUE (Pannwitz 1933 /
  Kuperberg 1994; Denne, `prop:homology`), and the reduction of the crux to it is
  `crux_of_finite_orbit_component`.  What is missing in Mathlib is 2-set Mayer–Vietoris for singular
  homology (or a groupoid van Kampen); the commons has simplicial-complex Mayer–Vietoris in
  cohomology (`Commons.AlgebraicTopology.SimplicialComplex.mayer_vietoris_cohomology`), which is not
  yet connected to singular homology of open plane sets.

* **Route 2 — the potential.**  `exists_equivariant_potential` below.  As recorded above, the
  minimal-wall route to it is *circular* (it needs the two-set statement, i.e. Route 1/3), so it has
  to be constructed directly; the ladder characterization
  `{L n}` closed preconnected, `T (L n) = L (n+1)`, `⋃ n, L n ⊆ K` is what has to be produced.

* **Route 3 — two-set Janiszewski for translate-crossings.**  The square analogue is *proved* in the
  commons (`Commons.Topology.Jordan.janiszewski_lines`, with `continuum_cut` and
  `exists_minimal_separating_lines`), by encoding "there is a top-to-bottom continuum avoiding `S`"
  as joinedness of two *fixed* cone tips.  The obstruction for the annulus is exactly that a
  translate-crossing has a *variable* basepoint (`z ↝ T z` for arbitrary `z`), so that encoding is
  unavailable; reconciling the basepoints is the same content as Route 1. -/

/-! ### First step of the ladder construction: a potential is exactly a ladder of walls -/

/-- **The level sets of an equivariant potential form a ladder of walls.**

Let `Ψ` be continuous and `T`-equivariant (`Ψ (T q) = Ψ q + 1`) and integer-free on `W`.  Then:

* the level sets in the strip form a single `T`-orbit:
  `T '' (levelSet Ψ n ∩ stripS a b) = levelSet Ψ (n+1) ∩ stripS a b`;
* every integer level avoids `W`: `levelSet Ψ n ∩ stripS a b ⊆ Wᶜ`;
* **every path in the strip from a point to its translate meets some integer level**: for
  `γ 0 = z`, `γ 1 = (z.1 + p, z.2)` with `(γ t).2 ∈ (a,b)`, there are `n` and `t` with
  `γ t ∈ levelSet Ψ n ∩ stripS a b`.  (Intermediate value theorem: `Ψ ∘ γ` runs from `Ψ z` to
  `Ψ z + 1`, hence takes the value `⌈Ψ z⌉`.)

Together with `∀ n, IsPreconnected (levelSet Ψ n ∩ stripS a b)` (the last hypothesis of
`exists_equivariant_potential`) this says precisely that the level sets are a *ladder of walls*
`{L n}`: closed (as level sets of a continuous map), preconnected (hypothesis),
`T (L n) = L (n+1)` (first bullet), `⋃ n, L n ⊆ K` (second bullet, with `K = stripS a b \\ W`), and
every translate crossing meets some `L n` (third bullet).  This is the purely geometric form of the
residual, and it is the form in which the ladder should be constructed directly. -/
theorem levelSet_ladder_of_equivariant_potential {p a b : ℝ}
    {W : Set (ℝ × ℝ)} {Ψ : ℝ × ℝ → ℝ} (hΨc : Continuous Ψ)
    (hΨT : ∀ q : ℝ × ℝ, Ψ (Tmap p q) = Ψ q + 1)
    (hΨfree : ∀ q ∈ W, ∀ n : ℤ, Ψ q ≠ (n : ℝ)) :
    (∀ n : ℤ, Tmap p '' (levelSet Ψ n ∩ stripS a b) = levelSet Ψ (n+1) ∩ stripS a b) ∧
    (∀ n : ℤ, levelSet Ψ n ∩ stripS a b ⊆ (W : Set (ℝ × ℝ))ᶜ) ∧
    (∀ (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)) (z : ℝ × ℝ),
      γ 0 = z → γ 1 = (z.1 + p, z.2) → (∀ t, (γ t).2 ∈ Set.Ioo a b) →
      ∃ n : ℤ, ∃ t : Set.Icc (0:ℝ) 1, γ t ∈ levelSet Ψ n ∩ stripS a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩
      obtain ⟨hq'l, hq's⟩ := hq'
      refine ⟨?_, ?_⟩
      · rw [mem_levelSet] at hq'l ⊢
        rw [hΨT, hq'l]
        push_cast
        ring
      · rw [stripS_iff] at hq's ⊢
        simpa [Tmap] using hq's
    · intro hq
      obtain ⟨hql, hqs⟩ := hq
      refine ⟨(q.1 - p, q.2), ⟨?_, ?_⟩, ?_⟩
      · rw [mem_levelSet] at hql ⊢
        have hTm : Tmap p (q.1 - p, q.2) = q := by ext <;> simp [Tmap]
        have hT := hΨT (q.1 - p, q.2)
        rw [hTm, hql] at hT
        push_cast at hT
        linarith
      · rw [stripS_iff] at hqs ⊢
        simpa using hqs
      · ext <;> simp [Tmap]
  · intro n q hq hqW
    obtain ⟨hql, -⟩ := hq
    rw [mem_levelSet] at hql
    exact hΨfree q hqW n hql
  · intro γ z hγ0 hγ1 hγstrip
    have hcont : Continuous fun t : Set.Icc (0:ℝ) 1 => Ψ (γ t) := hΨc.comp γ.continuous
    have h0 : Ψ (γ 0) = Ψ z := by rw [hγ0]
    have h1 : Ψ (γ 1) = Ψ z + 1 := by rw [hγ1]; simpa [Tmap] using hΨT z
    have hmem : (((⌈Ψ z⌉ : ℤ)) : ℝ) ∈ Set.Icc (Ψ (γ 0)) (Ψ (γ 1)) := by
      refine ⟨?_, ?_⟩
      · rw [h0]; exact Int.le_ceil (Ψ z)
      · rw [h1]; linarith [Int.ceil_lt_add_one (Ψ z)]
    have hpre : IsPreconnected (Set.univ : Set (Set.Icc (0:ℝ) 1)) := isPreconnected_univ
    have hsub := hpre.intermediate_value (Set.mem_univ (0 : Set.Icc (0:ℝ) 1))
      (Set.mem_univ (1 : Set.Icc (0:ℝ) 1)) hcont.continuousOn
    obtain ⟨t, -, ht⟩ := hsub hmem
    exact ⟨⌈Ψ z⌉, t, by rw [mem_levelSet]; exact ht, by rw [stripS_iff]; exact hγstrip t⟩

/-! ### The ladder pieces, named, and their mechanical properties

`ladderSet Ψ a b n` is the `n`-th piece of the ladder that `levelSet_ladder_of_equivariant_potential`
extracts from an equivariant potential: the `n`-th integer level set of `Ψ` inside the strip.  This
bundle collects everything about the pieces that does *not* use the hard (crossing) condition: they
lie in the strip, they avoid `W` (and so `⋃ n, L n ⊆ K`), they form one `T`-orbit, they are closed
*in the strip*, distinct pieces are disjoint, and preconnectedness is exactly the residual's last
hypothesis.  Only `crossing_meets_ladderSet` is the genuinely hard condition. -/

/-- The `n`-th piece of the ladder: the `n`-th integer level set of `Ψ` inside the strip. -/
def ladderSet (Ψ : ℝ × ℝ → ℝ) (a b : ℝ) (n : ℤ) : Set (ℝ × ℝ) :=
  levelSet Ψ n ∩ stripS a b

lemma ladderSet_subset_strip (Ψ : ℝ × ℝ → ℝ) (a b : ℝ) (n : ℤ) :
    ladderSet Ψ a b n ⊆ stripS a b := fun _ h => h.2

/-- Each ladder piece avoids `W`: integer levels of an integer-free potential. -/
lemma ladderSet_subset_compl {a b : ℝ} {W : Set (ℝ × ℝ)} {Ψ : ℝ × ℝ → ℝ}
    (hΨfree : ∀ q ∈ W, ∀ n : ℤ, Ψ q ≠ (n : ℝ)) (n : ℤ) :
    ladderSet Ψ a b n ⊆ (W : Set (ℝ × ℝ))ᶜ := by
  rintro q ⟨hql, -⟩ hqW
  exact hΨfree q hqW n hql

/-- **The whole ladder misses `W`**, i.e. `⋃ n, L n ⊆ K` with `K = stripS a b \\ W`. -/
lemma iUnion_ladderSet_subset_compl {a b : ℝ} {W : Set (ℝ × ℝ)} {Ψ : ℝ × ℝ → ℝ}
    (hΨfree : ∀ q ∈ W, ∀ n : ℤ, Ψ q ≠ (n : ℝ)) :
    (⋃ n : ℤ, ladderSet Ψ a b n) ⊆ (W : Set (ℝ × ℝ))ᶜ := by
  intro q hq
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hq
  exact ladderSet_subset_compl (a := a) (b := b) (W := W) hΨfree n hn

/-- **The ladder pieces form one `T`-orbit**: `T (L n) = L (n+1)`. -/
lemma ladderSet_translate {p a b : ℝ} {Ψ : ℝ × ℝ → ℝ}
    (hΨT : ∀ q : ℝ × ℝ, Ψ (Tmap p q) = Ψ q + 1) (n : ℤ) :
    Tmap p '' ladderSet Ψ a b n = ladderSet Ψ a b (n+1) := by
  ext q
  constructor
  · rintro ⟨q', hq', rfl⟩
    obtain ⟨hq'l, hq's⟩ := hq'
    refine ⟨?_, ?_⟩
    · rw [mem_levelSet] at hq'l ⊢
      rw [hΨT, hq'l]
      push_cast
      ring
    · rw [stripS_iff] at hq's ⊢
      simpa [Tmap] using hq's
  · intro hq
    obtain ⟨hql, hqs⟩ := hq
    refine ⟨(q.1 - p, q.2), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_levelSet] at hql ⊢
      have hTm : Tmap p (q.1 - p, q.2) = q := by ext <;> simp [Tmap]
      have hT := hΨT (q.1 - p, q.2)
      rw [hTm, hql] at hT
      push_cast at hT
      linarith
    · rw [stripS_iff] at hqs ⊢
      simpa using hqs
    · ext <;> simp [Tmap]

/-- **Each ladder piece is closed in the strip** (`levelSet Ψ n` is closed in the plane and the
strip is the ambient subtype). -/
lemma isClosed_preimage_ladderSet {Ψ : ℝ × ℝ → ℝ} (hΨc : Continuous Ψ) (a b : ℝ) (n : ℤ) :
    IsClosed (Subtype.val ⁻¹' ladderSet Ψ a b n : Set ↥(stripS a b)) := by
  have h : IsClosed (levelSet Ψ n) := isClosed_eq hΨc continuous_const
  have h2 : IsClosed (Subtype.val ⁻¹' (levelSet Ψ n) : Set ↥(stripS a b)) :=
    h.preimage continuous_subtype_val
  convert h2 using 1
  ext q
  simp [ladderSet]

/-- Distinct ladder pieces are disjoint (they are distinct level sets). -/
lemma ladderSet_disjoint {a b : ℝ} {Ψ : ℝ × ℝ → ℝ} {m n : ℤ} (hmn : m ≠ n) :
    Disjoint (ladderSet Ψ a b m) (ladderSet Ψ a b n) := by
  rw [Set.disjoint_left]
  rintro q ⟨hqm, -⟩ ⟨hqn, -⟩
  rw [mem_levelSet] at hqm hqn
  have hcast : (m : ℝ) = (n : ℝ) := by rw [← hqm, hqn]
  exact hmn (Int.cast_injective hcast)

/-- Preconnectedness of the ladder pieces is exactly the last hypothesis of the residual. -/
lemma isPreconnected_ladderSet {Ψ : ℝ × ℝ → ℝ} {a b : ℝ} {n : ℤ}
    (hΨpre : IsPreconnected (levelSet Ψ n ∩ stripS a b)) :
    IsPreconnected (ladderSet Ψ a b n) := hΨpre

/-- **The crossing condition, in ladder language.**  Every path in the strip from a point to its
translate meets some ladder piece.  This is the only remaining (hard) condition. -/
lemma crossing_meets_ladderSet {p a b : ℝ} {Ψ : ℝ × ℝ → ℝ} (hΨc : Continuous Ψ)
    (hΨT : ∀ q : ℝ × ℝ, Ψ (Tmap p q) = Ψ q + 1)
    {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} {z : ℝ × ℝ}
    (hγ0 : γ 0 = z) (hγ1 : γ 1 = (z.1 + p, z.2)) (hγstrip : ∀ t, (γ t).2 ∈ Set.Ioo a b) :
    ∃ n : ℤ, ∃ t : Set.Icc (0:ℝ) 1, γ t ∈ ladderSet Ψ a b n := by
  have h := (levelSet_ladder_of_equivariant_potential (p := p) (a := a) (b := b)
    (W := (∅ : Set (ℝ × ℝ))) (Ψ := Ψ) hΨc hΨT
    (by intro q hq; exact absurd hq (Set.notMem_empty q))).2.2 γ z hγ0 hγ1 hγstrip
  simpa [ladderSet] using h

/-! #### The wall statement to aim at (dispatched to the fleet)

The extension step needs the local coherence of the sheet classes at a point of `K`.  Stated in
commons form (no file-specific definitions) this is:

```
theorem wall_local_two_sheet_classes {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W : Set (ℝ × ℝ)} (hWop : IsOpen W)
    (hWsub : W ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    (hno : ∀ z : ℝ × ℝ, z ∈ W → ¬ JoinedIn W z (z.1 + p, z.2))
    {κ : ℝ × ℝ} (hκs : a < κ.2 ∧ κ.2 < b) (hκW : κ ∉ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q q' q'' : ℝ × ℝ, q ∈ W → q' ∈ W → q'' ∈ W →
      dist q κ < ε → dist q' κ < ε → dist q'' κ < ε →
      (∃ k : ℤ, (q'.1 + k * p, q'.2) ∈ connectedComponentIn W q) ∨
      (∃ k : ℤ, (q''.1 + k * p, q''.2) ∈ connectedComponentIn W q) ∨
      (∃ k : ℤ, (q''.1 + k * p, q''.2) ∈ connectedComponentIn W q')
```

#### The first sub-lemma of the wall statement (also dispatched)

The easy half of the near-`κ` class structure is that *local* components refine sheet classes: the
component of `q` in the small open set `W ∩ B(κ,ε)` is a connected subset of `W`, hence lies in the
component of `q` in `W` itself, hence every point of it is in the sheet class of `q` (with `k = 0`):

```
theorem local_component_subset_sheet_class {p ε : ℝ} (hp : 0 < p)
    {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    {κ q : ℝ × ℝ} (hq : q ∈ W) (hqε : q ∈ Metric.ball ﻿κ ε) :
    connectedComponentIn (W ∩ Metric.ball κ ε) q ⊆
      {q' : ℝ × ℝ | ∃ k : ℤ, (q'.1 + k * p, q'.2) ∈ connectedComponentIn W q}
```

**Caution (corrected, session 57): "at most two *local components*" is FALSE, so the implication
above is one-way and the local count is *not* the remaining content of
`wall_local_two_sheet_classes`.**  Counterexample: in the strip with `p = 1` take the `T`-invariant
grid `K = ⋃_k ({k} × (a,b) ∪ (ℝ × {y₀}))` with `a < y₀ < b`.  `K` is a wall (every crossing must
cross some line `x = k`, and every horizontal level is blocked), yet at the crossing point
`κ = (0, y₀) ∈ K` the set `W ∩ B(κ,ε)` has **four** components for every `ε > 0` (the four
quadrants).  What *is* true there is the class statement: the two upper quadrants are related by `T`
(indeed `T ((-1,0)×(y₀,∞)) = (0,1)×(y₀,∞)`), as are the two lower ones, while no upper quadrant is
related to a lower one (every `T`-translate preserves the sign of `q.2 - y₀`).  So exactly **two**
sheet classes meet `κ`.

Hence the class statement genuinely needs a *global* argument — comparing the components of `W`
through the local pieces — and cannot be reduced to a local count.  `local_component_subset_sheet_class`
remains a valid (one-way) tool; its converse-strength reading is refuted by the grid above.

("at most two sheet classes meet `κ`": of any three points of `W` close to `κ`, two lie in the same
sheet class, i.e. some `T`-translate of one lies in the component of `W` through the other.)  This is
the local form of the index coherence that the extension of `ind` across `K` needs; it is *not*
assumed anywhere in this file, and it is the statement the fleet has been handed. -/

/-- **Local components refine sheet classes** (the first sub-lemma of the wall statement).

Let `W` be `T`-invariant.  For `q ∈ W` and any radius `ε`, the component of `q` in the small open set
`W ∩ B(κ,ε)` is a connected subset of `W` containing `q`, hence lies in the component of `q` in `W`
itself; so every point of it lies in the sheet class of `q` (with `k = 0`).  Consequently "at most two
sheet classes meet `κ`" (the target `wall_local_two_sheet_classes`) follows from the purely local
statement "at most two components of `W ∩ B(κ,ε)` for small `ε`". -/
theorem local_component_subset_sheet_class {p ε : ℝ} (hp : 0 < p)
    {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    {κ q : ℝ × ℝ} (hq : q ∈ W) (hqε : q ∈ Metric.ball κ ε) :
    connectedComponentIn (W ∩ Metric.ball κ ε) q ⊆
      {q' : ℝ × ℝ | ∃ k : ℤ, (q'.1 + k * p, q'.2) ∈ connectedComponentIn W q} := by
  intro q' hq'
  refine ⟨0, ?_⟩
  have hmem : q ∈ W ∩ Metric.ball κ ε := ⟨hq, hqε⟩
  have hpre : IsPreconnected (connectedComponentIn (W ∩ Metric.ball κ ε) q) :=
    isPreconnected_connectedComponentIn
  have hsub : connectedComponentIn (W ∩ Metric.ball κ ε) q ⊆ W :=
    (connectedComponentIn_subset _ _).trans Set.inter_subset_left
  have hkey := hpre.subset_connectedComponentIn (mem_connectedComponentIn hmem) hsub
  simpa using hkey hq'

/-! #### Sketch of (ii): the class statement at a wall point

Goal: for `κ ∈ K = (stripS a b) \\ W`, at most two sheet classes meet `κ`.  Per the correction above
the local count is *not* enough, so the argument must be global.  The shape:

1. **Local pieces.**  For small `ε` every point of `W` near `κ` lies in a component of the open set
   `W ∩ B(κ,ε)`, and by `local_component_subset_sheet_class` its class is the class of that component.
   So the local components near `κ` are an upper bound for the classes, and the classes are the images
   of these finitely-many-under-`T` pieces (the grid shows the bound can be strict: 4 pieces, 2 classes).

2. **Where the difficulty sits.**  Deciding whether two local components `C`, `C'` are in the same
   class means asking whether some `T`-translate of `C'` lies in the *same component of `W`* as `C` —
   a global question, since a sheet may wander arbitrarily far from `κ` before returning.  The grid
   example shows this is genuinely global: the two upper quadrants are related only through the sheet
   that passes around the wall, and no local computation can see that.

3. **Where `hno` is spent.**  If three classes met `κ`, take `q, q', q'' ∈ W` close to `κ` in three
   different classes.  Near `κ` the wall forces the local pieces to meet in a nested way, and the
   *only* obstruction to joining two of them inside `W` is the wall itself; assembling q ↝ q' and
   q' ↝ q'' through the pieces adjacent to `κ` and closing up with the `T`-translates would produce a
   path in `W` from a point to its translate — which `hno` forbids.  Making this step precise *is* the
   remaining work: it must convert "three classes at `κ`" into an explicit `hno`-violating path.

**Status.**  Steps 1 is proved (`local_component_subset_sheet_class`); steps 2–3 are not.  The statement
`wall_local_two_sheet_classes` remains the fleet's target, and the grid example above should be kept in
mind as the sanity check for any proposed proof of it (it is a true instance, with 4 local pieces and
2 classes). -/

/-- **The grid test.**  If `W` misses a whole horizontal level `ℝ × {y₀}`, then the sheet-class
relation cannot cross that level: related points of `W` lie on the same side of `y₀`.

Proof: the second coordinate is continuous and the component of `q` in `W` is preconnected, so by the
intermediate value theorem a pair of related points on opposite sides would force a point of `W` at
height exactly `y₀` — excluded by the hypothesis.

This is the test case recorded above for `wall_local_two_sheet_classes`: for the `T`-invariant grid
`K = ⋃_k ({k p} × (a,b) ∪ ℝ × {y₀})` the complement misses the level `y₀`, so the sheet classes are
confined to the two open half planes (two classes), even though `W ∩ B(κ,ε)` has four components at
the crossing `κ = (0, y₀)`. -/
theorem sheet_class_same_side_of_unmet_level {p y₀ : ℝ} (hp : 0 < p)
    {W : Set (ℝ × ℝ)} (hlevel : ∀ x : ℝ, (x, y₀) ∉ W)
    {q q' : ℝ × ℝ} (hq : q ∈ W)
    (hrel : ∃ k : ℤ, (q'.1 + k * p, q'.2) ∈ connectedComponentIn W q) :
    (q.2 - y₀) * (q'.2 - y₀) > 0 := by
  obtain ⟨k, hk⟩ := hrel
  set q'' : ℝ × ℝ := (q'.1 + k * p, q'.2) with hq''def
  have hk' : q'' ∈ connectedComponentIn W q := hk
  have hqmem : q ∈ connectedComponentIn W q := mem_connectedComponentIn hq
  have hsub : connectedComponentIn W q ⊆ W := connectedComponentIn_subset W q
  have hq₂ : q.2 ≠ y₀ := fun h => hlevel q.1 (by rw [← h]; exact hq)
  have hq''₂ : q''.2 ≠ y₀ := fun h => hlevel q''.1 (by rw [← h]; exact hsub hk')
  have hq''snd : q''.2 = q'.2 := rfl
  have hpre : IsPreconnected (connectedComponentIn W q) := isPreconnected_connectedComponentIn
  have hcont : ContinuousOn (fun z : ℝ × ℝ => z.2) (connectedComponentIn W q) :=
    continuous_snd.continuousOn
  have key : ∀ a b : ℝ × ℝ, a ∈ connectedComponentIn W q → b ∈ connectedComponentIn W q →
      a.2 ≤ y₀ → y₀ ≤ b.2 → False := by
    intro a b ha hb h1 h2
    have hivt := hpre.intermediate_value ha hb hcont
    have hmem : y₀ ∈ Set.Icc (a.2) (b.2) := ⟨h1, h2⟩
    obtain ⟨z, hz, hzx⟩ := hivt hmem
    refine hlevel z.1 ?_
    have hzz : z = (z.1, y₀) := by ext <;> simp [hzx]
    rw [← hzz]
    exact hsub hz
  by_contra hcon
  have hcon' : (q.2 - y₀) * (q'.2 - y₀) ≤ 0 := not_lt.mp hcon
  have hstraddle : (q.2 < y₀ ∧ y₀ < q'.2) ∨ (q'.2 < y₀ ∧ y₀ < q.2) := by
    rcases lt_or_gt_of_ne hq₂ with h1 | h1 <;> rcases lt_or_gt_of_ne hq''₂ with h2 | h2
    · exfalso; nlinarith [hcon']
    · left; exact ⟨h1, by rw [← hq''snd]; exact h2⟩
    · right; exact ⟨by rw [← hq''snd]; exact h2, h1⟩
    · exfalso; nlinarith [hcon']
  rcases hstraddle with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key q q'' hqmem hk' (le_of_lt h1) (le_of_lt (by rwa [hq''snd] at h2))
  · exact key q'' q hk' hqmem (le_of_lt (by rwa [hq''snd] at h1)) (le_of_lt h2)

/-- **A local piece sits in `W` and in the sheet class of its centre** (immediate from
`local_component_subset_sheet_class`): this is the indexing fact that lets the pieces adjacent to `κ`
be fed into the class bookkeeping. -/
lemma mem_W_and_sheet_class_of_mem_local_component {p ε : ℝ} (hp : 0 < p)
    {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    {κ q q' : ℝ × ℝ} (hq : q ∈ W) (hqε : q ∈ Metric.ball κ ε)
    (hq' : q' ∈ connectedComponentIn (W ∩ Metric.ball κ ε) q) :
    q' ∈ W ∧ ∃ k : ℤ, (q'.1 + k * p, q'.2) ∈ connectedComponentIn W q := by
  have hcl := local_component_subset_sheet_class (p := p) (ε := ε) hp hW hq hqε
  exact ⟨(connectedComponentIn_subset (W ∩ Metric.ball κ ε) q).trans Set.inter_subset_left hq',
    hcl hq'⟩

/-- **The local pieces form one `T`-orbit** (the `T`-closure bookkeeping for step 3).

`T` carries the component of `q` in the local piece `W ∩ B(κ,ε)` onto the component of `T q` in the
local piece at `T κ`.  Proof: `T` is the homeomorphism `Homeomorph.addRight (p, 0)`
(`Homeomorph.coe_addRight`), it carries `W ∩ B(κ,ε)` onto `W ∩ B(Tκ, ε)` (`f '' W = W` from
`T`-invariance, `f '' B = B` from `dist (f a) (f b) = dist a b`), and
`Homeomorph.image_connectedComponentIn` transports components along a homeomorphism. -/
theorem local_piece_image_translate {p ε : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) {κ q : ℝ × ℝ}
    (hq : q ∈ W ∩ Metric.ball κ ε) :
    (fun z : ℝ × ℝ => (z.1 + p, z.2)) '' connectedComponentIn (W ∩ Metric.ball κ ε) q
      = connectedComponentIn (W ∩ Metric.ball (κ.1 + p, κ.2) ε) (q.1 + p, q.2) := by
  set f : ℝ × ℝ → ℝ × ℝ := fun z => (z.1 + p, z.2) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    simp only [hf, Prod.mk.injEq] at hab
    exact Prod.ext (by linarith [hab.1]) hab.2
  have hdist_f : ∀ a b : ℝ × ℝ, dist (f a) (f b) = dist a b := by
    intro a b
    have hd : f a - f b = a - b := by
      apply Prod.ext <;> simp [hf] <;> ring
    rw [dist_eq_norm, dist_eq_norm, hd]
  have hball : f '' Metric.ball κ ε = Metric.ball (f κ) ε := by
    ext z
    simp only [Set.mem_image, Metric.mem_ball]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rwa [hdist_f]
    · intro hz
      refine ⟨(z.1 - p, z.2), ?_, ?_⟩
      · rw [← hdist_f (z.1 - p, z.2) κ]
        have hone : f (z.1 - p, z.2) = z := by
          apply Prod.ext
          · simp only [hf]; ring
          · simp only [hf]
        rwa [hone]
      · apply Prod.ext
        · simp only [hf]; ring
        · simp only [hf]
  have hcoe : ⇑(Homeomorph.addRight (p, 0) : ℝ × ℝ ≃ₜ ℝ × ℝ) = f := by
    rw [Homeomorph.coe_addRight]
    ext z <;> simp [hf]
  have hW' : f '' W = W := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact (hW w).mp hw
    · intro hz
      have hz' : ((z.1 - p) + p, z.2) = z := by
        apply Prod.ext <;> simp <;> try ring
      refine ⟨(z.1 - p, z.2), (hW _).mpr (by rw [hz']; exact hz), ?_⟩
      apply Prod.ext
      · simp only [hf]; ring
      · simp only [hf]
  have hmain : f '' (W ∩ Metric.ball κ ε) = W ∩ Metric.ball (f κ) ε := by
    rw [Set.image_inter hfinj, hW', hball]
  have hkey := Homeomorph.image_connectedComponentIn
    (Homeomorph.addRight (p, 0) : ℝ × ℝ ≃ₜ ℝ × ℝ) hq
  rw [hcoe] at hkey
  rw [hmain] at hkey
  simpa [hf] using hkey

/-- **The local pieces are path-connected** (the local-segment ingredient of step 3).

Each piece `connectedComponentIn (W ∩ B(κ,ε)) q` is a component of the *open* set `W ∩ B(κ,ε)`, hence
open, connected and — in `ℝ²` — path-connected.  So any two points of one piece are joined by an arc
that stays inside the piece, and a fortiori inside `W`.  This is the local segment that the step-3
threading starts from. -/
lemma local_piece_path_connected {ε : ℝ} {W : Set (ℝ × ℝ)} (hWop : IsOpen W)
    {κ q : ℝ × ℝ} (hq : q ∈ W ∩ Metric.ball κ ε) :
    IsPathConnected (connectedComponentIn (W ∩ Metric.ball κ ε) q) ∧
    ∀ q' ∈ connectedComponentIn (W ∩ Metric.ball κ ε) q,
      JoinedIn (connectedComponentIn (W ∩ Metric.ball κ ε) q) q q' := by
  have hS : IsOpen (W ∩ Metric.ball κ ε) := hWop.inter Metric.isOpen_ball
  have hCopen : IsOpen (connectedComponentIn (W ∩ Metric.ball κ ε) q) := hS.connectedComponentIn
  have hCconn : IsConnected (connectedComponentIn (W ∩ Metric.ball κ ε) q) :=
    ⟨⟨q, mem_connectedComponentIn hq⟩, isPreconnected_connectedComponentIn⟩
  have hpc : IsPathConnected (connectedComponentIn (W ∩ Metric.ball κ ε) q) :=
    (hCopen.isConnected_iff_isPathConnected).mp hCconn
  exact ⟨hpc, fun q' hq' => hpc.joinedIn q (mem_connectedComponentIn hq) q' hq'⟩

/-- **The two-arc comparison: a local arc and its `T`-translate.**

For `q` in the piece `P = connectedComponentIn (W ∩ B(κ,ε)) q`, the `T`-translate of any arc `γ` in `P`
starts at `T q` and runs inside the corresponding piece at `T κ` (immediate from
`local_piece_image_translate`).

This is the mechanical content of the two-arc comparison, and it makes the *structural* point for
step 3 explicit: the arc and its translate live at *different* basepoints, `κ` and `T κ`.  So the
threading cannot sew a local arc to its own translate locally — the translate is a piece at a
different point of the wall — and the sewing must therefore use the global component structure of `W`,
exactly as the banked refutation (same-class does not imply local joinedness) already predicted. -/
lemma local_arc_image_translate {p ε : ℝ} {W : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) {κ q : ℝ × ℝ}
    (hq : q ∈ W ∩ Metric.ball κ ε) {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} (hγ0 : γ 0 = q)
    (hγ : ∀ t, γ t ∈ connectedComponentIn (W ∩ Metric.ball κ ε) q) :
    (∀ t, (fun z : ℝ × ℝ => (z.1 + p, z.2)) (γ t) ∈
        connectedComponentIn (W ∩ Metric.ball (κ.1 + p, κ.2) ε) (q.1 + p, q.2)) ∧
      (fun z : ℝ × ℝ => (z.1 + p, z.2)) (γ 0) = (q.1 + p, q.2) := by
  have himg := local_piece_image_translate (p := p) (ε := ε) hW hq
  refine ⟨fun t => ?_, by rw [hγ0]⟩
  rw [← himg]
  exact ⟨γ t, hγ t, rfl⟩

/-! #### The Mayer–Vietoris chapter: the one target to aim at, and its acceptance test

The missing fundamental is the *connecting homomorphism* of the two-set cover, together with exactness
of the resulting long sequence.  State it in the form the commons' algebra already supports
(`Commons.AlgebraicTopology.CochainComplex.long_exact_sequence` produces a long exact sequence from a
short exact sequence of cochain complexes; `Commons.AlgebraicTopology.SimplicialComplex.mayer_vietoris`
is the simplicial case):

* **geometric input — the piece not on the shelf.**  For open `U, V` with `U ∪ V = X` and a
  coefficient sheaf `A`, the degreewise sequence of cochain complexes
  `0 → C(U ∪ V) → C(U) ⊕ C(V) → C(U ∩ V) → 0`
  is short exact.  In the Čech/sheaf form this is the two-set sheaf axiom and is algebraic; in the
  singular form it needs the small-chains (barycentric subdivision) argument.  This is the object
  that *forces* a finite-orbit component, and it is exactly what the finite-orbit route was missing.
* **connecting homomorphism.**  The snake-lemma map `δ : H^n (U ∩ V) → H^{n+1} (U ∪ V)` supplied by
  that short exact sequence, plus exactness of the long sequence.
* **acceptance test.**  Instantiate the exactness at `H¹(S)` for the annulus `S` with `U = VA`,
  `V = VB`, `A = B` disjoint closed with `S \ A`, `S \ B` essential: exactness says a pair
  `(α, -β)` with `α`, `β` both of degree one is hit from `H¹(VA ∩ VB)`, so `VA ∩ VB` is essential.
  The geometric half of that test is `crux_of_finite_orbit_component`, already proved; the
  finite-orbit route cannot shortcut it (`orbit_infinite_of_no_crossing` shows every component is
  `T`-free under `hno`). -/

/-! #### Correction (session 63): the Mayer–Vietoris chapter is ALREADY IN MATHLIB

The chapter the note above asked to build exists in Mathlib, in greater generality than needed:

* `Mathlib/CategoryTheory/Sites/MayerVietorisSquare.lean` — `structure MayerVietorisSquare`,
  `bijective_toPullbackObj`, `sheafCondition_of_sheaf`, and
  **`shortComplex_shortExact : S.shortComplex.ShortExact`**: the **two-set short exact sequence**;
* `Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean` — `toBiprod`, `fromBiprod`,
  **`δ` (the connecting homomorphism)**, `sequenceIso`, and **`sequence_exact`**: the long exact
  sequence and its exactness, for a `MayerVietorisSquare` of sheaves, in all degrees;
* `Mathlib/Topology/Sheaves/MayerVietoris.lean` — `mayerVietorisSquare (U V : Opens T)`: the square
  for a **two-set open cover of a topological space**, i.e. exactly the `{VA, VB}` cover shape.

So the MV algebra is *not* the gap.  What actually remains is the **identification layer**: connecting
the concrete degree-one translate-crossing statements of this file (`JoinedIn` in the strip) with
`H' 1`-cohomology of the annulus with coefficients, so that "essential" becomes "non-zero under the
degree map".  That is: cohomology of open plane sets versus degree-one loops, together with
`H¹(annulus, ℤ) ≅ ℤ`.  This now replaces the "build the SES" plan as the honest description of the
frontier. -/

/-! ### Session 66: the potential is FALSE (the residual returns to `mv_obligation`)

The statement that used to sit here (the single `sorry` of the file),

  `exists_equivariant_potential` : for `W` open, `T`-invariant, `W ⊆ stripS a b`, with `hno`
  (no translate crossing inside `W`), there is a continuous `T`-equivariant `Ψ` with
  `Ψ (Tmap p q) = Ψ q + 1`, `Ψ` integer-free on `W`, and `∀ n`, `levelSet Ψ n ∩ stripS a b`
  preconnected,

is **false**.  Counterexample: the two-banded spiral tower of session 65
(`Submission/Work/Topology/Strip/accumulating_refutation_of_no_translate_path.lean`, whose
`AccRefute.tower_hypotheses` is machine-checked, sorry-free and axiom-clean).  Let `p = 1`,
`a = 0`, `b = 2`, `f y = log y - log (1 - y)`, `W_m = {q | 0 < q.2 < 1 ∧ q.1 = f q.2 + m}`,
`W'_m = W_m + (0,1)` (shifted up by one), `K' = {q.2 = 1} ∪ ⋃_m W_m ∪ ⋃_m W'_m` and
`W := stripS 0 2 \ K'`.  Then `W` is open, `T`-invariant, inside the strip, and `hno` holds
(`AccRefute.tower_hypotheses`).

Suppose `Ψ` were a potential.  Each `Λ_n := levelSet Ψ n ∩ stripS 0 2` is preconnected and, since
`Ψ` is integer-free on `W`, `Λ_n ⊆ K'`; also `T '' (Λ_n) = Λ_{n+1}`, so all the `Λ_n` have the same
set of heights.  Now:

* every preconnected `C ⊆ K'` meeting the level `{y = 1/2}` is contained in a **single** wall `W_m`
  (the argument of `AccCE.no_spanning`: the only points of `K2` at height `1/2` are on `⋃_m W_m`,
  and the closed sets `W_{m₀}` and `K2 \ W_{m₀}` — `AccCE.isClosed_W`,
  `AccCE.isClosed_K2_off_W` — separate them, so preconnectedness forces `C ⊆ W_{m₀}`);
* hence either some `Λ_n` lies in a single wall, whence `heights '' Λ_n ⊆ (0,1)`, or no `Λ_n` meets
  the level `1/2`, whence the interval `heights '' Λ_0 ⊆ (0,2)` lies either in `(0,1/2)` or in
  `(1/2,2)` (it is connected, being the image of a preconnected set).

In all three cases some nonempty open horizontal band `Y ⊆ (0,2)` avoids **every** `Λ_n`, hence
avoids `Ψ⁻¹(ℤ)`.  But `Y` is connected and `T`-invariant, so it lies in a single region
`S_j := {j < Ψ < j+1}`; applying `T` gives `Y = T '' Y ⊆ T '' S_j = S_{j+1}`, and
`S_j ∩ S_{j+1} = ∅` — contradiction.  (The tower's bands `(0,1)` and `(1,2)` are glued only by the
accumulation of the walls at the interface `{q.2 = 1}`, and that accumulation is exactly what makes
the level sets unable to separate the *upper* band: the walls of the upper band are the shifts
`W'_m`, which are **not** translates `T^k W_m` of the lower walls, so a `T`-orbit of level sets
cannot serve both bands.)

Consequence: the route
`mv_obligation ⟸ exists_equivariant_potential + one_side_no_crossing_of_potential` is not available,
and the residual of this file is again `mv_obligation` itself.  Note that the potential is *not*
refuted for the special shape `W = VA ∩ VB` arising in the crux — there the extra structure (two open
sets `VA ∪ VB = Ω`, covering) rules out the tower configuration: in the tower no split
`K' = K_A ⊔ K_B` with both `Ω \ K_A` and `Ω \ K_B` open *in `ℝ²`* exists, since the walls of each band
accumulate on the interface line, so that line would have to lie in both closed pieces.  So the
correct statement to prove is the crux itself; `one_side_no_crossing_of_potential` below remains the
(proved) implication that any potential whatsoever yields. -/

/-- **The potential** (FALSE in general — see the session-66 note above; recorded for the refuted
route, and no longer used anywhere in this file).

For `W` open and `T`-invariant with `hno` (no translate crossing inside `W`) there is a continuous
`T`-equivariant `Ψ` which is integer-free on `W` and whose level sets are preconnected and lie in the
strip. -/
def potentialStatement (p a b : ℝ) : Prop :=
  ∀ W : Set (ℝ × ℝ), IsOpen W → W ⊆ stripS a b → (∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W) →
    (∀ q : ℝ × ℝ, q ∈ W → ¬ JoinedIn W q (Tmap p q)) →
    ∃ Ψ : ℝ × ℝ → ℝ, Continuous Ψ ∧
      (∀ q : ℝ × ℝ, Ψ (Tmap p q) = Ψ q + 1) ∧
      (∀ q ∈ W, ∀ n : ℤ, Ψ q ≠ (n : ℝ)) ∧
      (∀ n : ℤ, IsPreconnected (levelSet Ψ n ∩ stripS a b))

/-! ### Piece (ii) of the ladder route: the arithmetic core of the distance-ratio construction

The potential of piece (ii) is built as `Ψ q = N q + φ q` with `φ q := d (q, L (N q)) /
(d (q, L (N q)) + d (q, L (N q + 1)))`.  Two arithmetic facts about this shape are used, and both are
proved here (they are the only places where the `ℤ`-valuedness of `N` and the interval `[0,1]` of the
ratio are consumed). -/

/-- **The integer dichotomy of the distance-ratio potential.**

If `N` is an integer, `φ ∈ [0,1]` and `N + φ = n` with `n` an integer, then either `N = n` and
`φ = 0`, or `N + 1 = n` and `φ = 1`.  Geometrically: if `Ψ = N + φ ∈ (N, N+1)` is an integer `n`,
then `n` must be one of the two rungs bounding the slab of `q`, and `φ` is `0` or `1` accordingly —
i.e. integer values of `Ψ` are attained exactly on the rungs. -/
theorem int_dichotomy_of_add_le (n N : ℤ) {phi : ℝ} (h0 : 0 ≤ phi) (h1 : phi ≤ 1)
    (h : (N : ℝ) + phi = (n : ℝ)) : (N = n ∧ phi = 0) ∨ (N + 1 = n ∧ phi = 1) := by
  have hle : (N : ℝ) ≤ (n : ℝ) := by linarith
  rcases eq_or_lt_of_le hle with heq | hlt
  · left
    have hNn : N = n := by exact_mod_cast heq
    refine ⟨hNn, ?_⟩
    rw [hNn] at h
    linarith
  · right
    have hge : (1 : ℤ) ≤ n - N := by
      have hltZ : N < n := by exact_mod_cast hlt
      omega
    have hle2 : n - N ≤ 1 := by
      have hcast : ((n - N : ℤ) : ℝ) ≤ 1 := by
        have : (n : ℝ) - (N : ℝ) ≤ 1 := by linarith
        push_cast
        linarith
      exact_mod_cast hcast
    have heq2 : n - N = 1 := le_antisymm hle2 hge
    have hN1 : N + 1 = n := by omega
    refine ⟨hN1, ?_⟩
    have hsub : (n : ℝ) - (N : ℝ) = 1 := by
      have hc : ((n - N : ℤ) : ℝ) = 1 := by rw [heq2]; norm_num
      push_cast at hc
      linarith
    linarith

/-- **The cancellation at a rung.**  Approaching a rung `L n` from the slab below (`N = n-1`) the
ratio `φ` tends to `1`, so `Ψ = N + φ → (n-1) + 1 = n`; approaching from the slab above (`N = n`) it
tends to `0`, so `Ψ → n + 0 = n`.  The two one-sided jumps of `φ` cancel, which is why `Ψ` is
continuous although `φ` cannot be (a `T`-invariant `φ` constant on each rung would have a single
boundary value and could never match both limits). -/
theorem cast_pred_add_one (n : ℤ) : ((n : ℝ) - 1) + 1 = (n : ℝ) := by ring

/-! ### Piece (ii), the distance ratio: the (φ)-toolkit

The potential of piece (ii) is `Ψ q = N q + φ q` with `N` the rung number and
`φ q = d (q, L (N q)) / (d (q, L (N q)) + d (q, L (N q + 1)))` the *distance ratio* of the two rungs
bounding the slab of `q`.  The lemmas below are the complete analytic toolkit for `φ`: `T`-invariance
of the distances to the rungs (so that `Ψ` is `T`-equivariant), the range `[0,1]`, the exact
characterisation of the extreme values `0` and `1` (which is what makes the integer level sets of `Ψ`
the rungs), and continuity wherever the denominator does not vanish.  See the status block at the top
of the file for the full design; the only remaining ingredient is the rung number `N` itself. -/

/-- `Tmap p` is a translation, hence an isometry. -/
lemma isometry_Tmap (p : ℝ) : Isometry (Tmap p) := by
  refine isometry_iff_dist_eq.mpr ?_
  intro a b
  have h : Tmap p a - Tmap p b = a - b := by
    apply Prod.ext <;> simp [Tmap]
  rw [dist_eq_norm, dist_eq_norm, h]

/-- **The distance to the rungs is `T`-equivariant.**  The distance from `T q` to the `(n+1)`-st rung
equals the distance from `q` to the `n`-th rung: the rungs are a `T`-orbit and `T` is an isometry.
This is what makes the distance ratio `T`-invariant and hence `Ψ = N + φ` `T`-equivariant. -/
lemma infDist_Tmap_image {p : ℝ} {L : ℤ → Set (ℝ × ℝ)}
    (hLper : ∀ n, Tmap p '' L n = L (n+1)) (n : ℤ) (q : ℝ × ℝ) :
    Metric.infDist (Tmap p q) (L (n+1)) = Metric.infDist q (L n) := by
  have h := Metric.infDist_image (Φ := Tmap p) (isometry_Tmap p) (x := q) (t := L n)
  rw [hLper n] at h
  exact h

/-- **The distance ratio of two rungs.**  For the two rungs `A`, `B` bounding a slab, this is the
normalised position of a point between them: `0` on `A`, `1` on `B`. -/
noncomputable def rungRatio (A B : Set (ℝ × ℝ)) (q : ℝ × ℝ) : ℝ :=
  Metric.infDist q A / (Metric.infDist q A + Metric.infDist q B)

lemma rungRatio_nonneg (A B : Set (ℝ × ℝ)) (q : ℝ × ℝ) : 0 ≤ rungRatio A B q := by
  have h1 : 0 ≤ Metric.infDist q A := Metric.infDist_nonneg
  have h2 : 0 ≤ Metric.infDist q B := Metric.infDist_nonneg
  simp only [rungRatio]
  exact div_nonneg h1 (by linarith)

lemma rungRatio_le_one (A B : Set (ℝ × ℝ)) (q : ℝ × ℝ) : rungRatio A B q ≤ 1 := by
  have h2 : 0 ≤ Metric.infDist q B := Metric.infDist_nonneg
  by_cases hden : Metric.infDist q A + Metric.infDist q B = 0
  · simp only [rungRatio, hden, div_zero]; norm_num
  · have hpos : 0 < Metric.infDist q A + Metric.infDist q B :=
      lt_of_le_of_ne (by linarith [Metric.infDist_nonneg (x := q) (s := A)]) (Ne.symm hden)
    simp only [rungRatio]
    rw [div_le_one hpos]
    linarith

/-- **The ratio vanishes exactly on the closure of the first rung.** -/
lemma rungRatio_eq_zero {A B : Set (ℝ × ℝ)} (hA : A.Nonempty) (hBne : B.Nonempty) {q : ℝ × ℝ}
    (hB : q ∉ closure B) : rungRatio A B q = 0 ↔ q ∈ closure A := by
  have h2 : 0 < Metric.infDist q B := (Metric.infDist_pos_iff_notMem_closure hBne).mp hB
  have h1 : 0 ≤ Metric.infDist q A := Metric.infDist_nonneg
  have hden : Metric.infDist q A + Metric.infDist q B ≠ 0 := by linarith
  simp only [rungRatio]
  rw [div_eq_zero_iff]
  exact ⟨fun h => (Metric.mem_closure_iff_infDist_zero hA).mpr (h.resolve_right hden),
    fun hq => Or.inl ((Metric.mem_closure_iff_infDist_zero hA).mp hq)⟩

/-- **The ratio equals one exactly on the closure of the second rung.**  Together with
`rungRatio_eq_zero` this is what identifies the integer level sets of `Ψ = N + φ` with the rungs. -/
lemma rungRatio_eq_one {A B : Set (ℝ × ℝ)} (hA : A.Nonempty) (hBne : B.Nonempty) {q : ℝ × ℝ}
    (hA' : q ∉ closure A) : rungRatio A B q = 1 ↔ q ∈ closure B := by
  have h1 : 0 < Metric.infDist q A := (Metric.infDist_pos_iff_notMem_closure hA).mp hA'
  have h2 : 0 ≤ Metric.infDist q B := Metric.infDist_nonneg
  have hden : Metric.infDist q A + Metric.infDist q B ≠ 0 := by linarith
  simp only [rungRatio]
  rw [div_eq_one_iff_eq hden]
  constructor
  · intro h
    have hz : Metric.infDist q B = 0 := by linarith
    exact (Metric.mem_closure_iff_infDist_zero hBne).mpr hz
  · intro hq
    have hz : Metric.infDist q B = 0 := (Metric.mem_closure_iff_infDist_zero hBne).mp hq
    rw [hz, add_zero]

/-- **The distance ratio is continuous wherever its denominator does not vanish.**  (The denominator
vanishes only at points whose distance to *both* rungs is zero, i.e. in `closure A ∩ closure B`; for
the rungs of a ladder this is avoided on the slabs by the separation hypothesis.) -/
lemma continuousOn_rungRatio {A B : Set (ℝ × ℝ)} {s : Set (ℝ × ℝ)}
    (h : ∀ q ∈ s, Metric.infDist q A + Metric.infDist q B ≠ 0) : ContinuousOn (rungRatio A B) s := by
  unfold rungRatio
  exact ContinuousOn.div (Metric.continuous_infDist_pt A).continuousOn
    ((Metric.continuous_infDist_pt A).add (Metric.continuous_infDist_pt B)).continuousOn
    (fun q hq => h q hq)

/-! ### Piece (ii), the rung number `N`: its geometric core

The rung number is `N q :=` the greatest index `n` whose rung `L n` meets the **horizontal left ray**
of `q` (`{(t, q.2) | t < q.1}`).  With the slab convention of the design block this gives
`N = n - 1` on the rung `L n` and `N = n` on the slab between `L n` and `L (n+1)`, which is exactly
what the distance-ratio formula needs.

**Status of the four properties of `N` (session 63, end).**  (1) is *proved*
(`hitsLeftRay_Tmap`, `mem_shift_of_orbit`, `greatest_hitsLeftRay_Tmap`).  For (2) the met-ness half
is proved as `crosscut_meets_level` (a crosscut of the box meets every interior level, from the
extraction lemma `segment_meets_of_crosscut`), and the whole of (2) is *reduced* by
`locallyConstant_of_ray_persistence` to two named geometric inputs: that the ray-hitting set is a
down-set in the index, and that the pair "(the `N q`-th rung meets the ray, the `(N q + 1)`-st does
not)" persists near every point off the rungs.  (3)+(4) (the slab description) rest on the same
extraction lemma and are independent of (2).

The **box-general transport is now in place** (`rungSqBox` and its API, `segment_meets_of_crosscut_box`
for a box `[x₀,x₁] × [a,b]`, and `leftRay_meets_of_box_crosscut`, which converts a box-crosscut whose
right edge sits at `q.1` into the combinatorial relation `∃ z ∈ L, z.2 = q.2 ∧ z.1 < q.1` — the
strictness coming from `q ∉ L`).  With it, the down-set input `horder` reduces further to: *for
`n < m` and a point of `L m` at `x < q.1`, the piece of `L n` inside the box `[q.1 - p, q.1] × [a,b]`
is a crosscut of that box* — the one place where the index ordering `n < m` and the disjointness of
the rungs are consumed.

For the **down-set** input, `down_of_pointwise_ordering` reduces it to the pointwise ordering
"every rung meets every interior level strictly to the left of every point of any later rung"; that
ordering is what `segment_meets_of_crosscut` has to supply, applied in a box whose right edge is at
the point in question — so it needs the *box-general* form of the `rungSq` transport (replace the
normalised first coordinate `2 * q.1 / p - 1` by `2 * (q.1 - x₀) / (x₁ - x₀) - 1`), which is a
mechanical generalisation.

The two lemmas below are the whole algebraic content of the construction: the relation "the `n`-th
rung meets the left ray of `q`" is carried by `T` to the relation at index `n+1`, and consequently a
greatest-index choice is `T`-equivariant.  (The remaining two properties of `N` — local constancy off
the rungs and the slab description near a rung — are geometric: they need the rung to *cross* the ray
transversally, which is what the separation of the rung in the strip provides; the separation itself
comes from `Commons.Topology.Jordan.top_bottom_continuum_meets_left_right_path`.) -/

/-- The `n`-th rung meets the horizontal **left ray** of `q`. -/
def hitsLeftRay (L : ℤ → Set (ℝ × ℝ)) (n : ℤ) (q : ℝ × ℝ) : Prop :=
  ∃ z ∈ L n, z.2 = q.2 ∧ z.1 < q.1

/-- **Membership shift for a `T`-orbit of rungs.**  For a rung family with `Tmap p '' L n = L (n+1)`,
a point lies on the `(n+1)`-st rung exactly when its `T`-preimage lies on the `n`-th rung. -/
lemma mem_shift_of_orbit {p : ℝ} {L : ℤ → Set (ℝ × ℝ)}
    (hLper : ∀ n, Tmap p '' L n = L (n + 1)) (n : ℤ) (z : ℝ × ℝ) :
    z ∈ L (n + 1) ↔ (z.1 - p, z.2) ∈ L n := by
  constructor
  · intro hz
    have h : z ∈ Tmap p '' L n := by rw [hLper n]; exact hz
    rcases h with ⟨w, hw, hwz⟩
    have hw' : w = (z.1 - p, z.2) := by
      apply Prod.ext
      · have := congrArg Prod.fst hwz; simp [Tmap] at this; linarith
      · have := congrArg Prod.snd hwz; simpa [Tmap] using this
    rwa [hw'] at hw
  · intro hz
    rw [← hLper n]
    exact ⟨(z.1 - p, z.2), hz, by apply Prod.ext <;> simp [Tmap] <;> ring⟩

/-- **The left-ray relation is `T`-equivariant.**  The `(n+1)`-st rung meets the left ray of `T q`
exactly when the `n`-th rung meets the left ray of `q`: `T` translates the left ray of `q` onto the
left ray of `T q` and shifts the rungs by one index. -/
lemma hitsLeftRay_Tmap {p : ℝ} {L : ℤ → Set (ℝ × ℝ)}
    (hLper : ∀ n, Tmap p '' L n = L (n + 1)) (n : ℤ) (q : ℝ × ℝ) :
    hitsLeftRay L (n + 1) (Tmap p q) ↔ hitsLeftRay L n q := by
  constructor
  · rintro ⟨z, hz, hz2, hz1⟩
    refine ⟨(z.1 - p, z.2), (mem_shift_of_orbit hLper n z).mp hz, ?_, ?_⟩
    · simpa [Tmap] using hz2
    · simp only [Tmap] at hz1 ⊢; linarith
  · rintro ⟨z, hz, hz2, hz1⟩
    refine ⟨(z.1 + p, z.2), (mem_shift_of_orbit hLper n (z.1 + p, z.2)).mpr ?_, ?_, ?_⟩
    · have : (z.1 + p - p, z.2) = z := by apply Prod.ext <;> simp <;> ring
      rw [this]; exact hz
    · simpa [Tmap] using hz2
    · simp only [Tmap]; linarith

/-- **The rung number is `T`-equivariant.**  If `N q` is the greatest rung index meeting the left ray
of `q`, then `N (T q) = N q + 1`.  This is property (1) of the four properties of `N`. -/
lemma greatest_hitsLeftRay_Tmap {p : ℝ} {L : ℤ → Set (ℝ × ℝ)}
    (hLper : ∀ n, Tmap p '' L n = L (n + 1)) {N : ℝ × ℝ → ℤ}
    (hN : ∀ q : ℝ × ℝ, IsGreatest {n : ℤ | hitsLeftRay L n q} (N q)) (q : ℝ × ℝ) :
    N (Tmap p q) = N q + 1 := by
  have hset : {n : ℤ | hitsLeftRay L n (Tmap p q)} =
      (fun n : ℤ => n + 1) '' {n : ℤ | hitsLeftRay L n q} := by
    ext n
    constructor
    · intro hn
      refine ⟨n - 1, ?_, by ring⟩
      rw [show n = (n - 1) + 1 by ring] at hn
      exact (hitsLeftRay_Tmap hLper (n - 1) q).mp hn
    · rintro ⟨m, hm, rfl⟩
      exact (hitsLeftRay_Tmap hLper m q).mpr hm
  have h1 := hN (Tmap p q)
  have h2 := hN q
  rw [hset] at h1
  have himg : IsGreatest ((fun n : ℤ => n + 1) '' {n : ℤ | hitsLeftRay L n q}) (N q + 1) := by
    constructor
    · exact ⟨N q, h2.1, by ring⟩
    · rintro y ⟨m, hm, rfl⟩
      show m + 1 ≤ N q + 1
      have := h2.2 hm
      omega
  exact h1.unique himg

/-! ### Piece (ii), the extraction lemma: a crosscut of the box blocks every horizontal segment

The rung number is built from the left-ray relation `hitsLeftRay` below, and the *geometric* content
that makes it work — that the ray cannot slip around a rung — is the following fact, extracted here
from `Commons.Topology.Jordan.top_bottom_continuum_meets_left_right_path` by the transposed square
coordinate `rungSq` (real part = `x`-coordinate, imaginary part = height, so "left–right" in the
square becomes "bottom–top" in the strip and the top–bottom continuum becomes the crosscut of the
box).

`segment_meets_of_crosscut`: a preconnected subset `L` of the closed box `[0,p] × [a,b]` meeting both
horizontal sides `{q.2 = a}` and `{q.2 = b}` meets **every** horizontal segment of the box at an
interior height.  This is the hinge for properties (2)–(4) of the rung number: it says a rung of a
ladder is met by the horizontal rays of the points it "separates", with no room to slip around. -/

/-- Transposed square coordinate: real part = normalised `x`-coordinate, imaginary part = height. -/
noncomputable def rungSq (p a b : ℝ) (q : ℝ × ℝ) : ℂ :=
  ((2 * q.1 / p - 1 : ℝ) : ℂ) + ((2 * (q.2 - a) / (b - a) - 1 : ℝ) : ℂ) * Complex.I

lemma rungSq_re (p a b : ℝ) (q : ℝ × ℝ) : (rungSq p a b q).re = 2 * q.1 / p - 1 := by
  simp only [rungSq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

lemma rungSq_im (p a b : ℝ) (q : ℝ × ℝ) : (rungSq p a b q).im = 2 * (q.2 - a) / (b - a) - 1 := by
  simp only [rungSq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

lemma continuous_rungSq (p a b : ℝ) : Continuous (rungSq p a b) := by
  unfold rungSq; fun_prop

lemma rungSq_inj {p a b : ℝ} (hp : p ≠ 0) (hab : b - a ≠ 0) {q q' : ℝ × ℝ}
    (h : rungSq p a b q = rungSq p a b q') : q = q' := by
  have h1 : 2 * q.1 / p - 1 = 2 * q'.1 / p - 1 := by
    have := congrArg Complex.re h; simpa [rungSq_re] using this
  have h2 : 2 * (q.2 - a) / (b - a) - 1 = 2 * (q'.2 - a) / (b - a) - 1 := by
    have := congrArg Complex.im h; simpa [rungSq_im] using this
  have hx : q.1 = q'.1 := by
    have h2' : 2 * q.1 / p = 2 * q'.1 / p := by linarith
    field_simp at h2'
    linarith
  have hy : q.2 = q'.2 := by
    have h3 : 2 * (q.2 - a) / (b - a) = 2 * (q'.2 - a) / (b - a) := by linarith
    rw [div_eq_div_iff hab hab] at h3
    have h4 : 2 * (q.2 - a) = 2 * (q'.2 - a) := mul_right_cancel₀ hab h3
    linarith
  rw [Prod.ext_iff]; exact ⟨hx, hy⟩

lemma rungSq_mem_square {p a b : ℝ} (hp : 0 < p) (hab : a < b) {q : ℝ × ℝ}
    (h1 : 0 ≤ q.1) (h2 : q.1 ≤ p) (h3 : a ≤ q.2) (h4 : q.2 ≤ b) :
    (rungSq p a b q).re ∈ Set.Icc (-1:ℝ) 1 ∧ (rungSq p a b q).im ∈ Set.Icc (-1:ℝ) 1 := by
  have hb : 0 < b - a := sub_pos.mpr hab
  constructor
  · rw [rungSq_re]
    constructor
    · have : 0 ≤ 2 * q.1 / p := div_nonneg (by linarith) hp.le
      linarith
    · have : 2 * q.1 / p ≤ 2 := by rw [div_le_iff₀ hp]; linarith
      linarith
  · rw [rungSq_im]
    constructor
    · have : 0 ≤ 2 * (q.2 - a) / (b - a) := div_nonneg (by linarith) hb.le
      linarith
    · have : 2 * (q.2 - a) / (b - a) ≤ 2 := by rw [div_le_iff₀ hb]; linarith
      linarith

/-- **Extraction: a crosscut of the box blocks every horizontal segment.**

If `L` is a preconnected subset of the closed box `[0,p] × [a,b]` meeting both horizontal sides
`{q.2 = a}` and `{q.2 = b}`, then every horizontal segment of the box at an interior height meets
`L`.  This is `Commons.Topology.Jordan.top_bottom_continuum_meets_left_right_path` transported by
`rungSq` (which reads the `x`-coordinate as the real part and the height as the imaginary part, so that
"left–right" in the square becomes "bottom–top" in the strip and the top–bottom continuum becomes the
crosscut). -/
theorem segment_meets_of_crosscut {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {L : Set (ℝ × ℝ)} (hLsq : ∀ q ∈ L, 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b)
    (hLpre : IsPreconnected L)
    (hLbot : (L ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty)
    (hLtop : (L ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty)
    {y₀ : ℝ} (hy : a < y₀ ∧ y₀ < b) :
    ∃ z ∈ L, z.2 = y₀ ∧ 0 ≤ z.1 ∧ z.1 ≤ p := by
  have hb : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  -- the image of the crosscut in the square
  set C : Set ℂ := rungSq p a b '' L with hC
  have hCsub : C ⊆ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1} := by
    rintro z ⟨q, hq, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hLsq q hq
    exact rungSq_mem_square hp hab h1 h2 h3 h4
  have hCpre : IsPreconnected C :=
    hLpre.image _ (continuous_rungSq p a b).continuousOn
  have hCbot : (C ∩ {z : ℂ | z.im = -1}).Nonempty := by
    obtain ⟨q, hq, hqy⟩ := hLbot
    refine ⟨rungSq p a b q, ⟨⟨q, hq, rfl⟩, ?_⟩⟩
    show (rungSq p a b q).im = -1
    rw [rungSq_im, hqy]; ring
  have hCtop : (C ∩ {z : ℂ | z.im = 1}).Nonempty := by
    obtain ⟨q, hq, hqy⟩ := hLtop
    refine ⟨rungSq p a b q, ⟨⟨q, hq, rfl⟩, ?_⟩⟩
    show (rungSq p a b q).im = 1
    rw [rungSq_im, hqy]
    field_simp
    norm_num
  -- the horizontal segment as a path in the square
  set γ : C(Set.Icc (0:ℝ) 1, ℂ) :=
    ⟨fun t : Set.Icc (0:ℝ) 1 => rungSq p a b ((t : ℝ) * p, y₀),
      (continuous_rungSq p a b).comp (by fun_prop)⟩ with hγdef
  have hγsq : ∀ t, γ t ∈ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1} := by
    intro t
    have ht0 : (0:ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have h1 : (0:ℝ) ≤ (t : ℝ) * p := mul_nonneg ht0 hp.le
    have h2 : (t : ℝ) * p ≤ p := by
      have := mul_le_mul_of_nonneg_right ht1 hp.le
      simpa using this
    show (rungSq p a b ((t : ℝ) * p, y₀)).re ∈ Set.Icc (-1:ℝ) 1 ∧
      (rungSq p a b ((t : ℝ) * p, y₀)).im ∈ Set.Icc (-1:ℝ) 1
    exact rungSq_mem_square hp hab h1 h2 hy.1.le hy.2.le

  have hγ0 : (γ 0).re = -1 := by
    show (rungSq p a b (((0:Set.Icc (0:ℝ) 1) : ℝ) * p, y₀)).re = -1
    rw [rungSq_re]; simp
  have hγ1 : (γ 1).re = 1 := by
    change (rungSq p a b (((1:Set.Icc (0:ℝ) 1) : ℝ) * p, y₀)).re = 1
    rw [rungSq_re]
    have h1 : (((1:Set.Icc (0:ℝ) 1) : ℝ)) = 1 := by simp
    rw [h1, one_mul]
    field_simp
    norm_num

  obtain ⟨t, ht⟩ :=
    Commons.Topology.Jordan.top_bottom_continuum_meets_left_right_path hCsub hCpre hCbot hCtop
      hγsq hγ0 hγ1
  obtain ⟨q, hqL, hqeq⟩ := ht
  have hq : q = ((t : ℝ) * p, y₀) := rungSq_inj hp.ne' hb hqeq
  refine ⟨q, hqL, ?_, ?_, ?_⟩
  · rw [hq]
  · rw [hq, Prod.fst]
    exact mul_nonneg t.2.1 hp.le
  · rw [hq, Prod.fst]
    nlinarith [t.2.2, hp]


/-! #### The box-general transport

The down-set input of [`down_of_pointwise_ordering`] needs the extraction lemma in a box whose right
edge sits at the point in question, not just in `[0,p] × [a,b]`.  The same transposition, with one
affine parameter more, gives it: `rungSqBox x₀ x₁ a b q` normalises the `x`-coordinate over
`[x₀,x₁]` (real part) and the height over `[a,b]` (imaginary part), and then

`segment_meets_of_crosscut_box`: a preconnected subset of the closed box `[x₀,x₁] × [a,b]` meeting
both horizontal sides meets every horizontal segment of that box.

This pays for both remaining consumers: the down-set input `horder` here, and the slab description
(3)+(4). -/

/-- Box-generic transposed square coordinate: real part = `x` normalised over `[x₀,x₁]`,
imaginary part = height normalised over `[a,b]`. -/
noncomputable def rungSqBox (x₀ x₁ a b : ℝ) (q : ℝ × ℝ) : ℂ :=
  ((2 * (q.1 - x₀) / (x₁ - x₀) - 1 : ℝ) : ℂ) +
    ((2 * (q.2 - a) / (b - a) - 1 : ℝ) : ℂ) * Complex.I

lemma rungSqBox_re (x₀ x₁ a b : ℝ) (q : ℝ × ℝ) :
    (rungSqBox x₀ x₁ a b q).re = 2 * (q.1 - x₀) / (x₁ - x₀) - 1 := by
  simp only [rungSqBox, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

lemma rungSqBox_im (x₀ x₁ a b : ℝ) (q : ℝ × ℝ) :
    (rungSqBox x₀ x₁ a b q).im = 2 * (q.2 - a) / (b - a) - 1 := by
  simp only [rungSqBox, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

lemma continuous_rungSqBox (x₀ x₁ a b : ℝ) : Continuous (rungSqBox x₀ x₁ a b) := by
  unfold rungSqBox; fun_prop

lemma rungSqBox_inj {x₀ x₁ a b : ℝ} (hx : x₁ - x₀ ≠ 0) (hb : b - a ≠ 0) {q q' : ℝ × ℝ}
    (h : rungSqBox x₀ x₁ a b q = rungSqBox x₀ x₁ a b q') : q = q' := by
  have h1 : 2 * (q.1 - x₀) / (x₁ - x₀) - 1 = 2 * (q'.1 - x₀) / (x₁ - x₀) - 1 := by
    have := congrArg Complex.re h; simpa [rungSqBox_re] using this
  have h2 : 2 * (q.2 - a) / (b - a) - 1 = 2 * (q'.2 - a) / (b - a) - 1 := by
    have := congrArg Complex.im h; simpa [rungSqBox_im] using this
  have hx1 : q.1 = q'.1 := by
    have h3 : 2 * (q.1 - x₀) / (x₁ - x₀) = 2 * (q'.1 - x₀) / (x₁ - x₀) := by linarith
    rw [div_eq_div_iff hx hx] at h3
    have h4 : 2 * (q.1 - x₀) = 2 * (q'.1 - x₀) := mul_right_cancel₀ hx h3
    linarith
  have hy1 : q.2 = q'.2 := by
    have h3 : 2 * (q.2 - a) / (b - a) = 2 * (q'.2 - a) / (b - a) := by linarith
    rw [div_eq_div_iff hb hb] at h3
    have h4 : 2 * (q.2 - a) = 2 * (q'.2 - a) := mul_right_cancel₀ hb h3
    linarith
  rw [Prod.ext_iff]; exact ⟨hx1, hy1⟩

lemma rungSqBox_mem_square {x₀ x₁ a b : ℝ} (hx : x₀ < x₁) (hab : a < b) {q : ℝ × ℝ}
    (h1 : x₀ ≤ q.1) (h2 : q.1 ≤ x₁) (h3 : a ≤ q.2) (h4 : q.2 ≤ b) :
    (rungSqBox x₀ x₁ a b q).re ∈ Set.Icc (-1:ℝ) 1 ∧
      (rungSqBox x₀ x₁ a b q).im ∈ Set.Icc (-1:ℝ) 1 := by
  have hxd : 0 < x₁ - x₀ := sub_pos.mpr hx
  have hb : 0 < b - a := sub_pos.mpr hab
  constructor
  · rw [rungSqBox_re]
    constructor
    · have : 0 ≤ 2 * (q.1 - x₀) / (x₁ - x₀) := div_nonneg (by linarith) hxd.le
      linarith
    · have : 2 * (q.1 - x₀) / (x₁ - x₀) ≤ 2 := by rw [div_le_iff₀ hxd]; linarith
      linarith
  · rw [rungSqBox_im]
    constructor
    · have : 0 ≤ 2 * (q.2 - a) / (b - a) := div_nonneg (by linarith) hb.le
      linarith
    · have : 2 * (q.2 - a) / (b - a) ≤ 2 := by rw [div_le_iff₀ hb]; linarith
      linarith

/-- **Box-general extraction.** -/
theorem segment_meets_of_crosscut_box {x₀ x₁ a b : ℝ} (hx : x₀ < x₁) (hab : a < b)
    {L : Set (ℝ × ℝ)} (hLsq : ∀ q ∈ L, x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ a ≤ q.2 ∧ q.2 ≤ b)
    (hLpre : IsPreconnected L)
    (hLbot : (L ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty)
    (hLtop : (L ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty)
    {y₀ : ℝ} (hy : a < y₀ ∧ y₀ < b) :
    ∃ z ∈ L, z.2 = y₀ ∧ x₀ ≤ z.1 ∧ z.1 ≤ x₁ := by
  have hxd : x₁ - x₀ ≠ 0 := (sub_pos.mpr hx).ne'
  have hb : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  set C : Set ℂ := rungSqBox x₀ x₁ a b '' L with hC
  have hCsub : C ⊆ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1} := by
    rintro z ⟨q, hq, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hLsq q hq
    exact rungSqBox_mem_square hx hab h1 h2 h3 h4
  have hCpre : IsPreconnected C :=
    hLpre.image _ (continuous_rungSqBox x₀ x₁ a b).continuousOn
  have hCbot : (C ∩ {z : ℂ | z.im = -1}).Nonempty := by
    obtain ⟨q, hq, hqy⟩ := hLbot
    refine ⟨rungSqBox x₀ x₁ a b q, ⟨⟨q, hq, rfl⟩, ?_⟩⟩
    show (rungSqBox x₀ x₁ a b q).im = -1
    rw [rungSqBox_im, hqy]; ring
  have hCtop : (C ∩ {z : ℂ | z.im = 1}).Nonempty := by
    obtain ⟨q, hq, hqy⟩ := hLtop
    refine ⟨rungSqBox x₀ x₁ a b q, ⟨⟨q, hq, rfl⟩, ?_⟩⟩
    show (rungSqBox x₀ x₁ a b q).im = 1
    rw [rungSqBox_im, hqy]
    field_simp
    norm_num
  set γ : C(Set.Icc (0:ℝ) 1, ℂ) :=
    ⟨fun t : Set.Icc (0:ℝ) 1 => rungSqBox x₀ x₁ a b (x₀ + (t : ℝ) * (x₁ - x₀), y₀),
      (continuous_rungSqBox x₀ x₁ a b).comp (by fun_prop)⟩ with hγdef
  have hγsq : ∀ t, γ t ∈ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1} := by
    intro t
    have ht0 : (0:ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have h1 : x₀ ≤ x₀ + (t : ℝ) * (x₁ - x₀) := by
      have := mul_nonneg ht0 (le_of_lt (sub_pos.mpr hx)); linarith
    have h2 : x₀ + (t : ℝ) * (x₁ - x₀) ≤ x₁ := by
      have := mul_le_mul_of_nonneg_right ht1 (le_of_lt (sub_pos.mpr hx))
      nlinarith
    show (rungSqBox x₀ x₁ a b (x₀ + (t : ℝ) * (x₁ - x₀), y₀)).re ∈ Set.Icc (-1:ℝ) 1 ∧
      (rungSqBox x₀ x₁ a b (x₀ + (t : ℝ) * (x₁ - x₀), y₀)).im ∈ Set.Icc (-1:ℝ) 1
    exact rungSqBox_mem_square hx hab h1 h2 hy.1.le hy.2.le
  have hγ0 : (γ 0).re = -1 := by
    show (rungSqBox x₀ x₁ a b (x₀ + ((0:Set.Icc (0:ℝ) 1) : ℝ) * (x₁ - x₀), y₀)).re = -1
    rw [rungSqBox_re]
    simp
  have hγ1 : (γ 1).re = 1 := by
    show (rungSqBox x₀ x₁ a b (x₀ + ((1:Set.Icc (0:ℝ) 1) : ℝ) * (x₁ - x₀), y₀)).re = 1
    have h1 : (((1:Set.Icc (0:ℝ) 1) : ℝ)) = 1 := by simp
    rw [rungSqBox_re, h1, one_mul]
    have h2 : x₀ + (x₁ - x₀) = x₁ := by ring
    rw [h2]
    field_simp
    norm_num
  obtain ⟨t, ht⟩ :=
    Commons.Topology.Jordan.top_bottom_continuum_meets_left_right_path hCsub hCpre hCbot hCtop
      hγsq hγ0 hγ1
  obtain ⟨q, hqL, hqeq⟩ := ht
  have hq : q = (x₀ + (t : ℝ) * (x₁ - x₀), y₀) := rungSqBox_inj hxd hb hqeq
  refine ⟨q, hqL, ?_, ?_, ?_⟩
  · rw [hq]
  · rw [hq]
    have := mul_nonneg t.2.1 (le_of_lt (sub_pos.mpr hx)); linarith
  · rw [hq]
    have := mul_le_mul_of_nonneg_right t.2.2 (le_of_lt (sub_pos.mpr hx))
    nlinarith
/-- **A crosscut of the box meets every interior level.**  Immediate from `segment_meets_of_crosscut`
applied to the horizontal segment at that level.  Together with the observation that the crossing
point cannot be the point `q` itself when `q` lies off the rungs, this is the "met-ness" half of
property (2) of the rung number. -/
theorem crosscut_meets_level {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {L : Set (ℝ × ℝ)} (hLsq : ∀ q ∈ L, 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b)
    (hLpre : IsPreconnected L)
    (hLbot : (L ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty)
    (hLtop : (L ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty)
    {y₀ : ℝ} (hy : a < y₀ ∧ y₀ < b) :
    (L ∩ {q : ℝ × ℝ | q.2 = y₀}).Nonempty := by
  obtain ⟨z, hz, hz2, -, -⟩ :=
    segment_meets_of_crosscut hp hab hLsq hLpre hLbot hLtop hy
  exact ⟨z, hz, hz2⟩

/-- **Property (2) of the rung number, reduced to its two geometric inputs.**

If `N` is the greatest rung index meeting the left ray of `q`, the ray-hitting set is a *down-set* in
the index (if the `m`-th rung meets the ray then so does every earlier rung), and the pair "the
`N q`-th rung meets the ray, the `(N q + 1)`-st does not" *persists* in a neighbourhood of every point
`q` off the rungs, then `N` is locally constant off the rungs.

The two hypotheses are exactly what the geometry has to supply: the persistence of the met pair comes
from `segment_meets_of_crosscut` (the rung is met by the horizontal rays of the points it separates,
with the crossing point strictly to the left of the base point because the base point lies off the
rungs), and the down-set property from the ordering of the rungs along the ray. -/
theorem locallyConstant_of_ray_persistence {L : ℤ → Set (ℝ × ℝ)} {N : ℝ × ℝ → ℤ}
    (hN : ∀ q : ℝ × ℝ, IsGreatest {n : ℤ | hitsLeftRay L n q} (N q))
    (hdown : ∀ (q : ℝ × ℝ) (n m : ℤ), hitsLeftRay L n q → m ≤ n → hitsLeftRay L m q)
    (hpers : ∀ q : ℝ × ℝ, (∀ n : ℤ, q ∉ L n) → ∃ ε : ℝ, 0 < ε ∧ ∀ q' : ℝ × ℝ, dist q q' < ε →
      hitsLeftRay L (N q) q' ∧ ¬ hitsLeftRay L (N q + 1) q') :
    ∀ q : ℝ × ℝ, (∀ n : ℤ, q ∉ L n) → ∃ ε : ℝ, 0 < ε ∧ ∀ q' : ℝ × ℝ, dist q q' < ε →
      N q' = N q := by
  intro q hq
  obtain ⟨ε, hε, h⟩ := hpers q hq
  refine ⟨ε, hε, fun q' hq' => ?_⟩
  obtain ⟨h1, h2⟩ := h q' hq'
  have hge : IsGreatest {n : ℤ | hitsLeftRay L n q'} (N q) := by
    refine ⟨h1, fun m hm => ?_⟩
    by_contra hmc
    have hle : N q + 1 ≤ m := by omega
    exact h2 (hdown q' m (N q + 1) hm hle)
  exact (hN q').unique hge

/-- **From a box-crosscut to the left-ray relation.**

If the rung `L` (or a piece of it) is a crosscut of the box `[q.1 - p, q.1] × [a,b]` whose right
edge sits exactly at `q.1`, and `q` itself lies off `L`, then `L` meets the left ray of `q`: the
box-general extraction hands back a point of `L` on the horizontal segment at height `q.2` with
`x ≤ q.1`, and it cannot be at `x = q.1` — that would be `q` itself, which is off `L`.  This is the
step that converts the geometry of the rungs into the combinatorial relation `hitsLeftRay`, and it is
the engine behind the down-set property. -/
theorem leftRay_meets_of_box_crosscut {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {L : Set (ℝ × ℝ)} {q : ℝ × ℝ}
    (hSsub : ∀ z ∈ L, q.1 - p ≤ z.1 ∧ z.1 ≤ q.1 ∧ a ≤ z.2 ∧ z.2 ≤ b)
    (hSpre : IsPreconnected L)
    (hSbot : (L ∩ {z : ℝ × ℝ | z.2 = a}).Nonempty)
    (hStop : (L ∩ {z : ℝ × ℝ | z.2 = b}).Nonempty)
    (hq : a < q.2 ∧ q.2 < b) (hqL : q ∉ L) :
    ∃ z ∈ L, z.2 = q.2 ∧ z.1 < q.1 := by
  obtain ⟨z, hzL, hz2, -, hz1hi⟩ :=
    segment_meets_of_crosscut_box (by linarith : q.1 - p < q.1) hab hSsub hSpre hSbot hStop hq
  refine ⟨z, hzL, hz2, ?_⟩
  rcases lt_or_eq_of_le hz1hi with h | h
  · exact h
  · exfalso
    have hzq : z = q := by rw [Prod.ext_iff]; exact ⟨h, hz2⟩
    exact hqL (hzq ▸ hzL)

/-- **The down-set property of the rung number, from a pointwise ordering of the rungs.**

If every rung meets every interior level strictly to the left of every point of any *later* rung,
then the set of rung indices meeting the left ray of a point is a down-set in the index: if the
`m`-th rung meets the ray and `n ≤ m`, so does the `n`-th.  This is the first of the two geometric
inputs of `locallyConstant_of_ray_persistence`.

The pointwise ordering is what the extraction lemma supplies: it is the statement that a rung is met
by the horizontal rays of the points lying on its right, with room to spare — obtained from
`segment_meets_of_crosscut` applied in a box whose right edge is at the point in question. -/
theorem down_of_pointwise_ordering {a b : ℝ} {L : ℤ → Set (ℝ × ℝ)}
    (horder : ∀ (n m : ℤ), n < m → ∀ w ∈ L m, ∀ y : ℝ, a < y → y < b →
      ∃ z ∈ L n, z.2 = y ∧ z.1 < w.1)
    {q : ℝ × ℝ} (hy : a < q.2 ∧ q.2 < b) {n m : ℤ}
    (hm : hitsLeftRay L m q) (hnm : n ≤ m) : hitsLeftRay L n q := by
  obtain ⟨w, hwL, hw2, hw1⟩ := hm
  rcases eq_or_lt_of_le hnm with h | h
  · subst h; exact ⟨w, hwL, hw2, hw1⟩
  · obtain ⟨z, hzL, hz2, hz1⟩ := horder n m h w hwL q.2 hy.1 hy.2
    exact ⟨z, hzL, hz2, lt_trans hz1 hw1⟩

/-- **IDEA AA implies the residual potential.**

If the closed complement `stripS a b \ W` of the free region contains a *continuous crosscut graph*
`y ↦ (u y, y)`, then the equivariant potential of `exists_equivariant_potential` exists
(`exists_potential_of_free_graph`) — and hence, by the chain proved in this file, so does the crux
and the target.  This is the precise sense in which IDEA AA (see the status block at the top of the
file) is a *sufficient* form of the remaining gap. -/
theorem exists_potential_of_crosscut_graph {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W : Set (ℝ × ℝ)} (hWsub : W ⊆ stripS a b)
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    (hcross : ∃ u : ℝ → ℝ, Continuous u ∧ ∀ y ∈ Set.Ioo a b, (u y, y) ∉ W) :
    ∃ Ψ : ℝ × ℝ → ℝ, Continuous Ψ ∧
      (∀ q : ℝ × ℝ, Ψ (Tmap p q) = Ψ q + 1) ∧
      (∀ q ∈ W, ∀ n : ℤ, Ψ q ≠ (n : ℝ)) ∧
      (∀ n : ℤ, IsPreconnected (levelSet Ψ n ∩ stripS a b)) := by
  obtain ⟨u, hu, hfree⟩ := hcross
  obtain ⟨Ψ, hΨc, hΨT, hΨfree, hΨpre⟩ :=
    exists_potential_of_free_graph hp hab hWsub hW hu hfree
  exact ⟨Ψ, hΨc, hΨT, hΨfree, fun n => by
    have := hΨpre n
    simpa only [levelSet] using this⟩


/-! ### The covering claim for the sweep — the single remaining statement

Everything above is proved; the whole crux now rests on the following one statement about a cover of
the parameter interval by two open sets.  For the sweep `F` between a translate crossing lying in
`VA` and one lying in `VB` (as produced by `sweep_of_crossings`), and assuming there is **no**
translate crossing inside `VA ∩ VB`, every parameter's slice is contained in `VA` or in `VB`.

Its role: `exists_crossing_of_sweep_covering` turns this claim plus the openness lemma into a
translate crossing inside `VA ∩ VB`, contradicting the hypothesis — i.e. the claim is *equivalent*
to `mv_obligation` (and hence to the crux) once the sweep is inserted.  So the claim is exactly the
Mayer–Vietoris content, in the most concrete form we have found: a statement about an open cover of
`[0,1]` by the two parameter sets `{s | slice ⊆ VA}` and `{s | slice ⊆ VB}`.

The shape of the proof (from the half-wall probe): a slice that is contained in neither set must
meet the overlap, and — with no crossing living inside the overlap — the "T-transport" of that
meeting point along the slice has no room to close up; the slice is then forced into one of the two
sets.

**The boundary cycle of the sweep (the concrete target for the two-parameter step).**  Write
`F : I × I → Ω` for the sweep.  Its four sides are: the given crossings `γA = F (0,·) ⊆ VA` and
`γB = F (1,·) ⊆ VB` on the horizontal sides, and the two parameter paths `ρ₀ = F (·,0)` and
`ρ₁ = F (·,1)` on the vertical sides — and `ρ₁ = T ρ₀`, because `F (s,1) = T (F (s,0))` for every
`s`.  Hence the boundary of the square carries the 1-cycle
`γA - γB + ρ₀ - T ρ₀`, whose annulus homology class is `0` (it is the boundary of the image of the
square, which lies in the simply connected `Ω`).  The two-parameter step is precisely the statement
that some part of that cycle can be pushed into `VA ∩ VB`: in the half-wall template it is the "flat"
piece where the `up` phase of `γA` and the `down` phase of `γB` cancel, and that piece is a genuine
translate crossing inside `VA ∩ VB`.  A proof of `sweep_cover_claim` should therefore be phrased as
a statement about this boundary cycle, not about a single slice.

**The boundary relation in path form (the composite path to carry).**  With `ρ₀ = F (·,0)`,
`ρ₁ = F (·,1) = T ρ₀`, `γA = F (0,·)`, `γB = F (1,·)`, the boundary of the square traversed once gives
the closed path `γA ∗ ρ₁ ∗ γB⁻¹ ∗ ρ₀⁻¹` based at `γA 0`, and — because it bounds the image of the
square inside the convex (hence simply connected) strip — it is null-homotopic.  Equivalently, in path
form:

  `γA ~ ρ₀ ∗ γB ∗ (T ρ₀)⁻¹`  (rel endpoints, from `γA 0` to `T (γA 0)`).

This is the precise sense in which "the `up` motion of `γA`, transported, is the `down` motion of
`γB`": the two given crossings differ by the parameter paths and their `T`-translate.

**The flat set, and the step to aim at.**  Let `flat F := {s | ∀ t, F (s,t) ∈ VA ∩ VB}` be the set of
parameters whose slice is a translate crossing inside the overlap.  Two remarks about it:
* `flat F ≠ ∅` would give the crux *directly* (a slice contained in `VA ∩ VB` is a translate crossing
  inside the overlap), and it is *stronger* than `sweep_cover_claim` — the claim only asks every slice
  to lie in one of the two sets, and the crux does not require the crossing inside `VA ∩ VB` to be one
  of the sweep's slices.  So `flat F ≠ ∅` is a *template*, not the goal: use it to see the mechanism
  (in the half-wall template `1/2 ∈ flat F`), but do not demand it in general.
* the step to aim at is the cancellation itself: the `up` motion of `γA` and the `down` motion of `γB`
  must cancel at some parameter, and at the cancellation point the slice is flat, i.e. lies in the
  overlap.  In the half-wall template this is exactly where the interpolation keeps the height inside
  the wall gap.

**The cancellation step restated as a one-dimensional statement about covers.**  For each parameter
`s`, put `T_s := F_s⁻¹(VA)` and `T'_s := F_s⁻¹(VB)`, the (open) sets of times at which the slice lies
in `VA` resp. in `VB`.  They are open and cover `I`.  Because the two ends of every slice have the
same type (`F (s,1) = T (F (s,0))` and `T` preserves `VA` and `VB`), each slice starts and ends in the
same one of `VA \ VB`, `VB \ VA`, `VA ∩ VB`.  `sweep_cover_claim` is then exactly:

  *for every `s`, one of `T_s`, `T'_s` is all of `I` — i.e. the cover of the parameter interval by the
  two sets never "mixes" into a proper pair, although at `s = 0` it is `VA` that covers and at
  `s = 1` it is `VB`.*

In this form the claim is visibly a two-parameter statement: it says that a family of covers of `I`
that *starts* trivial-of-type-`A` and *ends* trivial-of-type-`B` can never pass through a genuinely
mixed cover.  The endpoint type-pairing above is what makes the family "coherent", and `hno` is the
only hypothesis available to forbid the mixing.  This is the form in which the cancellation should be
attacked; the one-parameter closing-up (below) cannot see it, because within a single slice the type
pattern is unconstrained.

**Why the assembly lemma needs the second parameter (second negative finding).**  With the overlap
point `w = F (s,t_w) ∈ VA ∩ VB` in hand (from `mixed_slice_meets_inter`) and `hno` available at `w`,
one would like to close the argument on the single slice.  It cannot be done: `hno` forbids paths
*inside* `VA ∩ VB` from `w` to `T w`, and the only paths at hand are sub-arcs of the slice.  Because
the slice is mixed, one of the two sub-arcs of the slice from `w` (forwards to `F (s,1) = T (F (s,0))`
or backwards to `F (s,0)`) has its first exit from `VA ∩ VB` into `VA \ VB` or into `VB \ VA`; the
endpoint pairing only tells us that the two *ends* of the slice agree in type, not that either
sub-arc stays in the overlap.  So no path inside `VA ∩ VB` is constructible from one slice's data,
and the assembly must genuinely use the second parameter — the image of the square, i.e. the
boundary cycle `γA - γB + ρ₀ - T ρ₀` above, whose vanishing annulus class is the only thing available
that can force an overlap path to exist.  This is the same gap that defeated the one-parameter
closing-up and the flat-set target, now located exactly at the assembly step.

**A negative finding on the first attempted brick (worth recording).**  The *one-parameter* closing-up
of a slice at a point of `VA ∩ VB` is a path from that point to its translate built from the slice and
its `T`-translate; asking that it meet `Ω \ (VA ∩ VB)` just re-derives the hypothesis `hno` itself
("no translate crossing is contained in `VA ∩ VB`"), because the closing-up is assembled from the
slice and its translate.  Hence the gluing step cannot be a one-parameter statement: it must use the
*second* parameter, i.e. compare two slices of the sweep (or the sweep with the convexity homotopy
linking them), which is exactly where the Mayer–Vietoris content lives.  A slice that avoids `VA`

**Session 46: the structure of the residual, and two new tools from the commons.**  This session
re-derived the residual from scratch and fixed its *shape*; the shape is what the next attack needs.

*First, the statement of `mv_obligation` is TRUE and the missing input is exactly the rank inequality
of Mayer–Vietoris.*  For open `U, V ⊆ A` (the quotient annulus) with `U ∪ V = A` one has
`rank H₁(U) + rank H₁(V) ≤ rank H₁(U ∩ V) + rank H₁(A) = rank H₁(U ∩ V) + 1`; since `rank H₁ ≥ 1`
is the same as "contains an essential loop", `U, V` essential forces `U ∩ V` essential.  Also
checked: the hypotheses of the target are exactly Denne's except that Denne additionally assumes the
two closed sets to miss neighbourhoods of the two boundary components; the extra strength in our
statement is genuine and the argument above does not use the extra hypothesis.

*Second, the residual has an equivalent form purely in terms of components — the cleanest target so
far.*  Work in the strip `Ω = stripS a b`, so the lifted sets are `VA, VB` themselves and
`W = VA ∩ VB`.  Assume `hno`: no translate crossing inside `W`.  Then

 * every component of `W` is `T`-free (its `T`-orbit is infinite), so the components are permuted
   freely by `T`; each component `C` is a *sheet*;
 * if `E` is a component of `VA` (resp. of `VB`) containing a sheet `C`, then either `T E = E`
   (equivalently `E ⊇ W`, because `T W = W` and the set of sheets inside `E` is a nonempty
   `T`-invariant family), or `E ∩ W = C` — the **sheet dichotomy**;
 * consequently `VA` is essential iff some component `E` of `VA` with `T E = E` meets `W`, and the
   crux is equivalent to: *there is a sheet `C` whose `VA`-component and `VB`-component are both
   `T`-periodic*.  If both are, then any point of `C` is joined to its translate inside each of
   `VA`, `VB` (both components are open, connected and `T`-invariant), and Janiszewski
   (`joinedIn_inter_of_joinedIn_strip`) upgrades this to a translate crossing inside `W`.

So, without any homology, the residual is the **meeting statement**: *under `hno`, every `T`-periodic
component of `VA` meets `W`* (and the same for `VB`).  The "thick-wall" examples (`VA = {y < f}`,
`VB = {y > g}` with `f, g` periodic and `f > g`) satisfy it, because there `W` is a band and its
components are not `T`-free — those examples are exactly the ones in which `hno` fails.

*Third, a new tool available in the commons for the meeting statement.*
`Commons.Topology.Covering.section_of_monodromy_eq_self(_weak)` says that a covering with trivial
monodromy at a point has a *global section*.  Applied to the covering `π : Ω → A` restricted over an
open `T`-invariant `V ⊆ Ω` (i.e. to `V → V/T`, whose deck group is `ℤ`) this yields the equivalence

  `V` has no translate crossing  ⟺  `π` admits a continuous section `σ : V → V` (`π ∘ σ = id`)

(`⟸`: a section carries a loop of degree `d` in `V/T` to a closed path of degree `0` in `Ω`, so no
loop of degree `≠ 0` exists; `⟹`: the monodromy of `V → V/T` is trivial and the section lemma
applies, `V` being open in the plane, hence locally path connected).  This converts "no crossing"
hypotheses into *existence of a section*, i.e. into "the cover untwists" — the form in which the
meeting statement should be attacked, since the sheet dichotomy says that the `VA`-component of a
sheet is either the "untwisted" piece `C ∪ (⊂ VA \ VB)` or the "twisted" piece `⊇ W`.

*Fourth, what the transition analysis gives (and where it stops).*  For the sweep
`δ_s = (1-s) γA + s γB` between a translate crossing `γA ⊆ VA` and `γB ⊆ VB`, the parameter sets
`G_A = {s : δ_s ⊆ VA}` and `G_B = {s : δ_s ⊆ VB}` are open (`isOpen_forall_mem_of_continuous`) and
`0 ∈ G_A`, `1 ∈ G_B`; so `sweep_cover_claim` follows from `G_A ∪ G_B = [0,1]` by connectedness of
`[0,1]`.  If `s₀` is a "transition" point (bad, with `G_A` on the left and `G_B` on the right), then
`δ_{s₀} ∩ (Ω \ VA) ⊆ ∂VA` and `δ_{s₀} ∩ (Ω \ VB) ⊆ ∂VB`; equivalently the limiting slice lies in
`cl VA ∩ cl VB` and meets both `∂VA` and `∂VB`.  Both boundaries are `T`-invariant (`∂VA ⊆ VB`,
`∂VB ⊆ VA`), so a transition produces a *translate crossing inside `∂VA ∪ ∂VB`* — but that is not a
contradiction by itself (a translation path may run inside the union of the two boundaries), which is
exactly where the transition analysis stops.  Note also that `sweep_cover_claim` as stated carries no
hypothesis on the end slices; its intended uses go through `sweep_of_crossings`, which supplies
`F (0,·) = γA ⊆ VA` and `F (1,·) = γB ⊆ VB`, and those are the hypotheses the connectedness argument
needs (`0 ∈ G_A`, `1 ∈ G_B`)

**Session 47: the potential route, and the crossing argument it feeds.**

*Piece 1 is done* (`exists_sheet_index_aei`, proved in the source just above): under `hno` there is a
locally constant `ℤ`-valued index on `W` with `ind (T q) = ind q + 1` and `ind` constant on
components.  Its construction is the one anticipated above: the components of `W` are permuted
freely by `T` (hno), the `T`-orbits of components are the classes of the setoid `wSheetSetoid`, a
choice of representative sheet per orbit gives `wSheetRep`, and `ind q` is the unique `k` with
`Tz p k (wSheetRep [q]) ∈ connectedComponentIn W q`; existence is the class relation, uniqueness is
`orbit_infinite_of_no_crossing`.

*Piece 2 (open) is the potential proper.*  The required object is

  `Ψ : Ω → ℝ` continuous, `Ψ (T q) = Ψ q + 1`, `Ψ q ∉ ℤ` for `q ∈ W`, and every level set
  `{Ψ = n}` preconnected (hence a "wall": `T {Ψ = n} = {Ψ = n+1}` and, each level set being a
  preconnected subset of `Ω` contained in `VAᶜ ∪ VBᶜ` with
  `{Ψ = n} ∩ (VAᶜ ∩ VBᶜ) ⊆ Ωᶜ = ∅`, the disjoint-closed-sets splitting puts *all* the level sets on
  one side: either every `{Ψ = n} ⊆ VAᶜ` or every `{Ψ = n} ⊆ VBᶜ`).

*Piece 3a is also done* (`no_crossing_of_potential_avoids_integers`, proved in the source above):
if `Ψ` is continuous, `Ψ (T q) = Ψ q + 1`, and `VA` avoids the integer values of `Ψ`, then `VA`
contains no translate crossing.  The proof is the intermediate value theorem on the `Ψ`-image of the
crossing, which runs from `Ψ z` to `Ψ z + 1` and so must take the value `⌈Ψ z⌉`.

*Reformulation of Piece 2.*  Every continuous `Ψ` with `Ψ (T q) = Ψ q + 1` has the form
`Ψ q = (q.1 + g q)/p` with `g` continuous and `T`-invariant (`g := p * Ψ q - q.1`), and conversely.
So Piece 2 is equivalent to: *there is a `T`-invariant continuous `g : Ω → ℝ` with
`(q.1 + g q)/p ∉ ℤ` for all `q ∈ W`* — i.e. the "shifted projection" `q ↦ q.1 + g q` (mod `p`)
must avoid the meridian orbit `pℤ` on `W`.  In the simplest configurations `g ≡ 0` already works
(whenever `W` misses the vertical lines `{x ∈ pℤ}`), and the examples in which `hno` holds (the
"room and wall" pictures) always admit a `g` built cell by cell; making that construction uniform
enough to be a Lean term is the remaining engineering.  Note also that no compactness of the level
sets is needed anywhere: the crossing argument (Piece 3a) uses only continuity and equivariance.


*Therefore the crux follows from Piece 2 alone*, with no further argument: the level sets `{Ψ = n}`
are preconnected subsets of `Ω` contained in `VAᶜ ∪ VBᶜ` and disjoint from `VAᶜ ∩ VBᶜ` (they lie in
`Ω`), so each lies in `VAᶜ` or in `VBᶜ`; `T {Ψ = n} = {Ψ = n + 1}` and `VAᶜ`, `VBᶜ` are
`T`-invariant, so the side is the same for every `n`; hence *every* integer value of `Ψ` is missed by
`VA` (if the level sets lie in `VAᶜ`) or by `VB`, and Piece 3a contradicts `hwindA` (resp. `hwindB`).


*Piece 3 (the crossing argument, given Piece 2).*  Suppose all the level sets lie in `VAᶜ` (the other
case is symmetric).  A `T`-crossing `γ ⊆ VA` has `Ψ (γ 1) = Ψ (γ 0) + 1`, and `Ψ (γ 0) ∉ ℤ` because
`γ 0 ∈ VA` and `{Ψ ∈ ℤ} ⊆ VAᶜ`; by the intermediate value theorem `γ` must meet the level set
`{Ψ = ⌈Ψ (γ 0)⌉} ⊆ VAᶜ`, contradicting `γ ⊆ VA`.  So `hno` is impossible, which is exactly the crux
in the form "no translate crossing in `W` cannot happen".  Note that this argument uses *one* of the
two `T`-crossings (the one inside the side that avoided all the walls), and that the level sets need
not be contained in a compact region: only preconnectedness and `⊆ Ω` are used.

So the whole residual is now: **Piece 2** — and the natural seams for it are: (i) build the
within-cell coordinate `φ : W → (0,1)` (`T`-invariant, `Ψ = ind + φ` on `W`); (ii) extend `Ψ` across
`K ∩ Ω` along the level sets, using that the two sheets adjacent to a wall point must receive the
same index; (iii) preconnectedness of the level sets.
therefore has to be caught by `VB` only by an argument that moves *between* slices. -/

/-! ## The chain-to-path extractor (`exists_directed_path_of_flow`)

The final step of the interface-chain route to `mv_obligation` recorded in the STATUS block above:
a finite integral flow on a digraph from `x` to `y` contains a directed path from `x` to `y` all of
whose edges carry non-zero flow.  Applied to the interface `1`-chain of a grid subdivision (whose
boundary is the translate discrepancy `Tz - z`), it produces an honest path in `VA ∩ VB` from a
point to its translate, i.e. `mv_obligation`.  Proved here `sorry`-free and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`). -/

section FlowExtraction


variable {m : ℕ}

/-- Sum of a function modified in one coordinate. -/
lemma sum_update_eq (w : Fin m → ℕ) (i0 : Fin m) (c : ℕ) (S : Finset (Fin m)) :
    (∑ i ∈ S, ((Function.update w i0 c) i : ℤ))
      = (∑ i ∈ S, (w i : ℤ)) + (if i0 ∈ S then ((c : ℤ) - (w i0 : ℤ)) else 0) := by
  by_cases h : i0 ∈ S
  · rw [if_pos h, ← Finset.add_sum_erase _ (fun i => ((Function.update w i0 c) i : ℤ)) h]
    have h2 : (∑ i ∈ S.erase i0, ((Function.update w i0 c) i : ℤ))
        = ∑ i ∈ S.erase i0, (w i : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne]
      exact (Finset.mem_erase.mp hi).1
    rw [h2, Function.update_self]
    rw [← Finset.add_sum_erase _ (fun i => (w i : ℤ)) h]
    ring
  · rw [if_neg h, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne]
    intro hc
    exact h (hc ▸ hi)

/-- Lowering one coordinate by `1` lowers the sum by `1` (when it is positive there). -/
lemma sum_update_sub (w : Fin m → ℕ) (i0 : Fin m) (hw : 0 < w i0) (S : Finset (Fin m)) :
    (∑ i ∈ S, ((Function.update w i0 (w i0 - 1)) i : ℤ))
      = (∑ i ∈ S, (w i : ℤ)) - (if i0 ∈ S then 1 else 0) := by
  rw [sum_update_eq]
  by_cases h : i0 ∈ S
  · rw [if_pos h, if_pos h]
    have hcast : (((w i0 - 1 : ℕ)) : ℤ) = (w i0 : ℤ) - 1 := by omega
    rw [hcast]; ring
  · rw [if_neg h, if_neg h]; ring

/-- Total flow after lowering one coordinate. -/
lemma sum_univ_update_sub (w : Fin m → ℕ) (i0 : Fin m) (hw : 0 < w i0) :
    (∑ i : Fin m, (Function.update w i0 (w i0 - 1)) i) = (∑ i : Fin m, w i) - 1 := by
  have h := sum_update_sub (m := m) w i0 hw Finset.univ
  rw [if_pos (Finset.mem_univ i0)] at h
  have h1 : ((∑ i : Fin m, (Function.update w i0 (w i0 - 1)) i : ℕ) : ℤ)
      = ∑ i : Fin m, ((Function.update w i0 (w i0 - 1)) i : ℤ) := by push_cast; rfl
  have h2 : ((∑ i : Fin m, w i : ℕ) : ℤ) = ∑ i : Fin m, (w i : ℤ) := by push_cast; rfl
  have h3 : ((∑ i : Fin m, (Function.update w i0 (w i0 - 1)) i : ℕ) : ℤ)
      = ((∑ i : Fin m, w i : ℕ) : ℤ) - 1 := by
    rw [h1, h2]; exact h
  have hw1 : 1 ≤ ∑ i : Fin m, w i := by
    have := Finset.single_le_sum (fun x _ => Nat.zero_le (w x)) (Finset.mem_univ i0)
    omega
  omega

/-- Rewriting a sum of `ite`s as a sum over a filter. -/
lemma sum_ite_filter {m : ℕ} (f : Fin m → ℤ) (p : Fin m → Prop) [DecidablePred p] :
    (∑ i : Fin m, if p i then f i else 0) = ∑ i ∈ Finset.univ.filter p, f i := by
  rw [Finset.sum_filter]

/-- **Flow decomposition (graph form).**  A finite integral flow on a directed multigraph on
`Fin n`, with source `x` and sink `y` (`x ≠ y`), contains a directed path from `x` to `y` along
edges of non-zero flow. -/
theorem exists_directed_path_of_flow {n m : ℕ} (e : Fin m → Fin n × Fin n) (w : Fin m → ℕ)
    (x y : Fin n) (hxy : x ≠ y)
    (hflow : ∀ v : Fin n,
      (∑ i : Fin m, if (e i).1 = v then (w i : ℤ) else 0)
        - (∑ i : Fin m, if (e i).2 = v then (w i : ℤ) else 0)
        = (if v = x then (1 : ℤ) else 0) - (if v = y then (1 : ℤ) else 0)) :
    ∃ (l : List (Fin m)) (h : l ≠ []), (∀ i ∈ l, w i ≠ 0) ∧
      (e (l.head h)).1 = x ∧ (e (l.getLast h)).2 = y ∧
      l.IsChain (fun i j => (e i).2 = (e j).1) := by
  classical
  suffices key : ∀ T : ℕ, ∀ (x y : Fin n) (w : Fin m → ℕ), x ≠ y →
      (∑ i : Fin m, w i) ≤ T →
      (∀ v : Fin n,
        (∑ i : Fin m, if (e i).1 = v then (w i : ℤ) else 0)
          - (∑ i : Fin m, if (e i).2 = v then (w i : ℤ) else 0)
          = (if v = x then (1 : ℤ) else 0) - (if v = y then (1 : ℤ) else 0)) →
      ∃ (l : List (Fin m)) (h : l ≠ []), (∀ i ∈ l, w i ≠ 0) ∧
        (e (l.head h)).1 = x ∧ (e (l.getLast h)).2 = y ∧
        l.IsChain (fun i j => (e i).2 = (e j).1) from
    key (∑ i : Fin m, w i) x y w hxy le_rfl hflow
  intro T
  induction T with
  | zero =>
      intro x y w hxy hT hf
      exfalso
      have hall : ∀ i, w i = 0 := by
        intro i
        by_contra h
        have hpos : 0 < w i := Nat.pos_of_ne_zero h
        have h1 : w i ≤ ∑ j : Fin m, w j :=
          Finset.single_le_sum (fun a _ => Nat.zero_le (w a)) (Finset.mem_univ i)
        omega
      have hx0 := hf x
      rw [if_pos rfl, if_neg hxy] at hx0
      simp only [hall, Nat.cast_zero, ite_self, Finset.sum_const_zero, sub_zero] at hx0
      exact one_ne_zero hx0.symm
  | succ T ih =>
      intro x y w hxy hT hf
      by_cases hzero : ∀ i, w i = 0
      · exfalso
        have hx0 := hf x
        rw [if_pos rfl, if_neg hxy] at hx0
        simp only [hzero, Nat.cast_zero, ite_self, Finset.sum_const_zero, sub_zero] at hx0
        exact one_ne_zero hx0.symm
      · push Not at hzero
        have hout1 : (1 : ℤ) ≤ ∑ i : Fin m, if (e i).1 = x then (w i : ℤ) else 0 := by
          have hx0 := hf x
          rw [if_pos rfl, if_neg hxy] at hx0
          have hnn : 0 ≤ ∑ i : Fin m, if (e i).2 = x then (w i : ℤ) else 0 :=
            Finset.sum_nonneg (fun i _ => by split_ifs <;> simp)
          linarith
        obtain ⟨i0, hi0s, hi0w⟩ : ∃ i, (e i).1 = x ∧ 0 < w i := by
          by_contra hcon
          push Not at hcon
          have hle : (∑ i : Fin m, if (e i).1 = x then (w i : ℤ) else 0) ≤ 0 := by
            apply Finset.sum_nonpos
            intro i _
            by_cases h : (e i).1 = x
            · rw [if_pos h]
              have := hcon i h
              omega
            · rw [if_neg h]
          omega
        rcases eq_or_ne (e i0).2 y with hty | hty
        · refine ⟨[i0], by simp, ?_, ?_, ?_, List.isChain_singleton _⟩
          · intro i hi; simp at hi; subst hi; exact Nat.pos_iff_ne_zero.mp hi0w
          · simp [hi0s]
          · simp [hty]
        · set w' : Fin m → ℕ := Function.update w i0 (w i0 - 1) with hw'
          have hsum' : (∑ i : Fin m, w' i) ≤ T := by
            rw [hw', sum_univ_update_sub w i0 hi0w]
            omega
          have hflow' : ∀ v : Fin n,
              (∑ i : Fin m, if (e i).1 = v then (w' i : ℤ) else 0)
                - (∑ i : Fin m, if (e i).2 = v then (w' i : ℤ) else 0)
                = (if v = (e i0).2 then (1 : ℤ) else 0)
                  - (if v = y then (1 : ℤ) else 0) := by
            intro v
            have hA : (∑ i : Fin m, if (e i).1 = v then (w' i : ℤ) else 0)
                = (∑ i : Fin m, if (e i).1 = v then (w i : ℤ) else 0)
                  - (if (e i0).1 = v then 1 else 0) := by
              rw [sum_ite_filter (fun i : Fin m => (w' i : ℤ)) (fun i => (e i).1 = v),
                sum_ite_filter (fun i : Fin m => (w i : ℤ)) (fun i => (e i).1 = v)]
              have hthis := sum_update_sub (m := m) w i0 hi0w
                (Finset.univ.filter (fun i : Fin m => (e i).1 = v))
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hthis
              rw [← hthis]
            have hB : (∑ i : Fin m, if (e i).2 = v then (w' i : ℤ) else 0)
                = (∑ i : Fin m, if (e i).2 = v then (w i : ℤ) else 0)
                  - (if (e i0).2 = v then 1 else 0) := by
              rw [sum_ite_filter (fun i : Fin m => (w' i : ℤ)) (fun i => (e i).2 = v),
                sum_ite_filter (fun i : Fin m => (w i : ℤ)) (fun i => (e i).2 = v)]
              have hthis := sum_update_sub (m := m) w i0 hi0w
                (Finset.univ.filter (fun i : Fin m => (e i).2 = v))
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hthis
              rw [← hthis]
            rw [hA, hB, hi0s]
            have hexp : (∑ i : Fin m, if (e i).1 = v then (w i : ℤ) else 0)
                  - (if x = v then (1 : ℤ) else 0)
                  - ((∑ i : Fin m, if (e i).2 = v then (w i : ℤ) else 0)
                    - (if (e i0).2 = v then (1 : ℤ) else 0))
                = ((∑ i : Fin m, if (e i).1 = v then (w i : ℤ) else 0)
                    - (∑ i : Fin m, if (e i).2 = v then (w i : ℤ) else 0))
                  - (if x = v then (1 : ℤ) else 0) + (if (e i0).2 = v then (1 : ℤ) else 0) := by
              ring
            rw [hexp, hf v]
            have key1 : (if x = v then (1 : ℤ) else 0) = (if v = x then (1 : ℤ) else 0) := by
              by_cases h : v = x
              · rw [if_pos h.symm, if_pos h]
              · rw [if_neg (fun hh : x = v => h hh.symm), if_neg h]
            have key2 : (if (e i0).2 = v then (1 : ℤ) else 0)
                = (if v = (e i0).2 then (1 : ℤ) else 0) := by
              by_cases h : v = (e i0).2
              · rw [if_pos h.symm, if_pos h]
              · rw [if_neg (fun hh : (e i0).2 = v => h hh.symm), if_neg h]
            rw [key1, key2]
            ring
          obtain ⟨l, hl, hne, hsrc, htgt, hchain⟩ := ih (e i0).2 y w' hty hsum' hflow'
          refine ⟨i0 :: l, by simp, ?_, ?_, ?_, ?_⟩
          · intro i hi
            rw [List.mem_cons] at hi
            rcases hi with rfl | hi
            · exact Nat.pos_iff_ne_zero.mp hi0w
            · by_cases hii : i = i0
              · subst hii; exact Nat.pos_iff_ne_zero.mp hi0w
              · have h := hne i hi
                rw [hw', Function.update_of_ne hii] at h
                exact h
          · simp [hi0s]
          · rw [List.getLast_cons hl]; exact htgt
          · obtain ⟨b, tl, rfl⟩ : ∃ b tl, l = b :: tl := by
              cases l with
              | nil => exact absurd rfl hl
              | cons b tl => exact ⟨b, tl, rfl⟩
            refine List.isChain_cons_cons.mpr ⟨?_, hchain⟩
            rw [List.head_cons] at hsrc
            exact hsrc.symm

/-- Concatenating the paths of a directed path in a graph. -/
theorem joinedIn_of_chain {X : Type*} [TopologicalSpace X] {n m : ℕ} (P : Fin n → X)
    (e : Fin m → Fin n × Fin n) (σ : (i : Fin m) → Path (P (e i).1) (P (e i).2)) {W : Set X}
    (hσW : ∀ i t, σ i t ∈ W) :
    ∀ (i : Fin m) (l : List (Fin m)) (b : Fin n),
      (i :: l).IsChain (fun i j => (e i).2 = (e j).1) →
      (∀ k, (i :: l).getLast? = some k → (e k).2 = b) →
      JoinedIn W (P (e i).1) (P b) := by
  intro i l
  induction l generalizing i with
  | nil =>
      intro b _ hb
      have h1 : (e i).2 = b := hb i (by simp)
      exact h1 ▸ (show JoinedIn W (P (e i).1) (P (e i).2) from ⟨σ i, hσW i⟩)
  | cons j l' ih =>
      intro b hchain hb
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hij, hchain'⟩ := hchain
      have hb' : ∀ k, (j :: l').getLast? = some k → (e k).2 = b := by
        intro k hk
        exact hb k (by rw [List.getLast?_cons_cons]; exact hk)
      have hrec : JoinedIn W (P (e j).1) (P b) := ih j b hchain' hb'
      exact JoinedIn.trans (show JoinedIn W (P (e i).1) (P (e i).2) from ⟨σ i, hσW i⟩)
        (hij.symm ▸ hrec)

/-- Chain form of the extraction: a flow from `x` to `y` in a graph whose edges are realised by
paths in `W` gives a join in `W`. -/
theorem joinedIn_of_flow {X : Type*} [TopologicalSpace X] {n m : ℕ} (P : Fin n → X)
    (e : Fin m → Fin n × Fin n) (σ : (i : Fin m) → Path (P (e i).1) (P (e i).2)) {W : Set X}
    (hσW : ∀ i t, σ i t ∈ W) (w : Fin m → ℕ) (x y : Fin n) (hxy : x ≠ y)
    (hflow : ∀ v : Fin n,
      (∑ i : Fin m, if (e i).1 = v then (w i : ℤ) else 0)
        - (∑ i : Fin m, if (e i).2 = v then (w i : ℤ) else 0)
        = (if v = x then (1 : ℤ) else 0) - (if v = y then (1 : ℤ) else 0)) :
    JoinedIn W (P x) (P y) := by
  obtain ⟨l, hl, hne, hsrc, htgt, hchain⟩ := exists_directed_path_of_flow e w x y hxy hflow
  obtain ⟨i, l', rfl⟩ : ∃ i l', l = i :: l' := by
    cases l with
    | nil => exact absurd rfl hl
    | cons i l' => exact ⟨i, l', rfl⟩
  have hhead : (e i).1 = x := by
    rw [List.head_cons] at hsrc; exact hsrc
  have hlast : ∀ k, (i :: l').getLast? = some k → (e k).2 = y := by
    intro k hk
    have hkl : (i :: l').getLast hl = k := by
      have h1 : (i :: l').getLast? = some ((i :: l').getLast hl) :=
        List.getLast?_eq_getLast hl
      rw [h1] at hk
      exact Option.some.inj hk
    rw [← hkl]
    exact htgt
  have hjoin : JoinedIn W (P (e i).1) (P y) :=
    joinedIn_of_chain P e σ hσW i l' y hchain hlast
  rw [hhead] at hjoin
  exact hjoin

end FlowExtraction


/-! ## The square map of two translate paths, and its grid decomposition

The geometric input of the interface-chain route to `mv_obligation` recorded in the STATUS block.
For two paths `γ, δ : [0,1] → Ω` the **square map** `squareMap γ δ (t,s) = (1-s)•γ t + s•δ t`
interpolates linearly between them (possible because the strip is convex).  Its two `t`-edges are
`γ` (at `s = 0`) and `δ` (at `s = 1`), and its `s`-edges join `γ 0` to `δ 0` and `γ 1` to `δ 1`.

The decisive property is `squareMap_T`: if `γ` and `δ` each join a point to its `T`-translate,
then the `t = 1` edge of the square is the `T`-translate of the `t = 0` edge — the square
**descends to a map of the cylinder** `S¹ × I`.  This is precisely what makes the left and right
edges of the grid cancel in the quotient annulus `Ω/T` (whereas in the lifted picture `Ω` they do
not, `σ` versus `Tσ`), which is why the interface chain must be read in the annulus/cylinder.

`exists_grid_of_squareMap` then subdivides the square into an `n × n` grid of cells each carried by
`VA` or by `VB`, by the commons' `exists_grid_decomposition_of_open_cover`.
-/

/-- The closed unit interval, as a type. -/
abbrev UnitSeg : Type := Set.Icc (0 : ℝ) 1

lemma zero_mem_seg : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩

lemma one_mem_seg : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩

/-- The convex interpolation ("square map") of two paths `γ, δ : [0,1] → ℝ × ℝ`; the first
coordinate is the `γ`/`δ` parameter, the second the interpolation parameter. -/
noncomputable def squareMap (γ δ : C(UnitSeg, ℝ × ℝ)) : C(UnitSeg × UnitSeg, ℝ × ℝ) where
  toFun q := (1 - (q.2 : ℝ)) • γ ⟨q.1, q.1.2⟩ + (q.2 : ℝ) • δ ⟨q.1, q.1.2⟩
  continuous_toFun := by fun_prop

lemma squareMap_apply (γ δ : C(UnitSeg, ℝ × ℝ)) (t s : UnitSeg) :
    squareMap γ δ (t, s) = (1 - (s : ℝ)) • γ t + (s : ℝ) • δ t := rfl

lemma squareMap_fst_zero (γ δ : C(UnitSeg, ℝ × ℝ)) (s : UnitSeg) :
    squareMap γ δ (⟨0, zero_mem_seg⟩, s) = (1 - (s : ℝ)) • γ ⟨0, zero_mem_seg⟩
      + (s : ℝ) • δ ⟨0, zero_mem_seg⟩ := rfl

lemma squareMap_snd_zero (γ δ : C(UnitSeg, ℝ × ℝ)) (t : UnitSeg) :
    squareMap γ δ (t, ⟨0, zero_mem_seg⟩) = γ t := by
  rw [squareMap_apply]; simp

lemma squareMap_snd_one (γ δ : C(UnitSeg, ℝ × ℝ)) (t : UnitSeg) :
    squareMap γ δ (t, ⟨1, one_mem_seg⟩) = δ t := by
  rw [squareMap_apply]; simp

/-- **The cylinder relation.**  If `γ` and `δ` both join a point to its `T`-translate, then the
`t = 1` edge of the square is the `T`-translate of its `t = 0` edge. -/
lemma squareMap_T {p : ℝ} (γ δ : C(UnitSeg, ℝ × ℝ))
    (hγ : γ ⟨1, one_mem_seg⟩ = Tmap p (γ ⟨0, zero_mem_seg⟩))
    (hδ : δ ⟨1, one_mem_seg⟩ = Tmap p (δ ⟨0, zero_mem_seg⟩)) (s : UnitSeg) :
    squareMap γ δ (⟨1, one_mem_seg⟩, s) = Tmap p (squareMap γ δ (⟨0, zero_mem_seg⟩, s)) := by
  rw [squareMap_fst_zero, squareMap_apply, hγ, hδ]
  simp only [Tmap_apply]
  ext <;> simp <;> ring

lemma squareMap_mem_strip {a b : ℝ} (γ δ : C(UnitSeg, ℝ × ℝ))
    (hγ : ∀ t, γ t ∈ stripS a b) (hδ : ∀ t, δ t ∈ stripS a b) (q : UnitSeg × UnitSeg) :
    squareMap γ δ q ∈ stripS a b := by
  rw [squareMap_apply]
  have h := convex_stripS a b
  have hs0 : (0 : ℝ) ≤ (q.2 : ℝ) := q.2.2.1
  have hs1 : (q.2 : ℝ) ≤ 1 := q.2.2.2
  exact h (hγ _) (hδ _) (by linarith) (by linarith) (by ring)

/-- **Grid decomposition of the square map**: the square subdivides into an `n × n` grid of cells,
each carried by `VA` or by `VB`. -/
theorem exists_grid_of_squareMap {a b : ℝ} {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hcover : VA ∪ VB = stripS a b) (γ δ : C(UnitSeg, ℝ × ℝ))
    (hγ : ∀ t, γ t ∈ VA) (hδ : ∀ t, δ t ∈ VB) :
    ∃ (n : ℕ) (_ : 0 < n) (c : Fin n → Fin n → Bool) (u : Fin (n + 1) → UnitSeg),
      u 0 = ⟨0, zero_mem_seg⟩ ∧ u (Fin.last n) = ⟨1, one_mem_seg⟩ ∧ Monotone u ∧
      ∀ (i j : Fin n),
        ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ),
          squareMap γ δ s ∈ (if c i j = true then VB else VA) := by
  have hsubA : VA ⊆ stripS a b := hcover ▸ subset_union_left
  have hsubB : VB ⊆ stripS a b := hcover ▸ subset_union_right
  have hH : ∀ q : UnitSeg × UnitSeg, squareMap γ δ q ∈ VA ∪ VB := by
    intro q
    rw [hcover]
    exact squareMap_mem_strip γ δ (fun t => hsubA (hγ t)) (fun t => hsubB (hδ t)) q
  exact Commons.Topology.Homotopy.exists_grid_decomposition_of_open_cover hVA hVB hH


/-! ### The grid of the square map: vertices and edges

The combinatorial layer of the interface-chain route.  `gridVert γ δ u i j = F (u i) (u j)` are the
vertices of the grid (where `F = squareMap γ δ`), and `gridT`/`gridS` are the edges of the grid as
explicit paths in `Ω`: `gridT u i j` runs in the `t`-direction (from `gridVert i.castSucc j` to
`gridVert i.succ j`) and `gridS u i j` in the `s`-direction (from `gridVert i j.castSucc` to
`gridVert i j.succ`).  Because the square map is built from the *grid's own* subdivision points, the
consecutive edges of the grid share their endpoints *definitionally*, which is what makes the
bookkeeping of the interface chain exact (no transport anywhere).
-/

instance instZeroUnitSeg : Zero UnitSeg := ⟨⟨0, zero_mem_seg⟩⟩

instance instOneUnitSeg : One UnitSeg := ⟨⟨1, one_mem_seg⟩⟩

@[simp] lemma unitSeg_zero_coe : ((0 : UnitSeg) : ℝ) = 0 := rfl

@[simp] lemma unitSeg_one_coe : ((1 : UnitSeg) : ℝ) = 1 := rfl

/-- The convex combination of two points of the unit interval, in the unit interval. -/
def segPt (a b s : UnitSeg) : UnitSeg :=
  ⟨(1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ), by
    have ha := a.2; have hb := b.2; have hs := s.2
    refine ⟨?_, ?_⟩ <;> nlinarith [ha.1, ha.2, hb.1, hb.2, hs.1, hs.2]⟩

@[simp] lemma segPt_zero (a b : UnitSeg) : segPt a b 0 = a := by
  apply Subtype.ext
  simp [segPt]

@[simp] lemma segPt_one (a b : UnitSeg) : segPt a b 1 = b := by
  apply Subtype.ext
  simp [segPt]

lemma continuous_segPt (a b : UnitSeg) : Continuous (segPt a b) := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun s : UnitSeg => (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ)
  fun_prop

/-- The vertices of the grid. -/
noncomputable def gridVert (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i j : Fin (n + 1)) : ℝ × ℝ := squareMap γ δ (u i, u j)

/-- The `s`-direction grid edge at `t`-index `i`. -/
noncomputable def gridS (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin (n + 1)) (j : Fin n) : C(UnitSeg, ℝ × ℝ) where
  toFun s := squareMap γ δ (u i, segPt (u j.castSucc) (u j.succ) s)
  continuous_toFun := (squareMap γ δ).continuous.comp
    (Continuous.prodMk continuous_const (continuous_segPt _ _))

/-- The `t`-direction grid edge at `s`-index `j`. -/
noncomputable def gridT (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin n) (j : Fin (n + 1)) : C(UnitSeg, ℝ × ℝ) where
  toFun s := squareMap γ δ (segPt (u i.castSucc) (u i.succ) s, u j)
  continuous_toFun := (squareMap γ δ).continuous.comp
    (Continuous.prodMk (continuous_segPt _ _) continuous_const)

lemma gridS_apply (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin (n + 1)) (j : Fin n) (s : UnitSeg) :
    gridS γ δ u i j s = squareMap γ δ (u i, segPt (u j.castSucc) (u j.succ) s) := rfl

lemma gridT_apply (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin n) (j : Fin (n + 1)) (s : UnitSeg) :
    gridT γ δ u i j s = squareMap γ δ (segPt (u i.castSucc) (u i.succ) s, u j) := rfl

lemma gridS_zero (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin (n + 1)) (j : Fin n) :
    gridS γ δ u i j 0 = gridVert γ δ u i j.castSucc := by
  rw [gridS_apply]; simp [gridVert]

lemma gridS_one (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin (n + 1)) (j : Fin n) :
    gridS γ δ u i j 1 = gridVert γ δ u i j.succ := by
  rw [gridS_apply]; simp [gridVert]

lemma gridT_zero (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin n) (j : Fin (n + 1)) :
    gridT γ δ u i j 0 = gridVert γ δ u i.castSucc j := by
  rw [gridT_apply]; simp [gridVert]

lemma gridT_one (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin n) (j : Fin (n + 1)) :
    gridT γ δ u i j 1 = gridVert γ δ u i.succ j := by
  rw [gridT_apply]; simp [gridVert]

/-- The `s`-direction grid edge as a path. -/
noncomputable def gridSPath (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin (n + 1)) (j : Fin n) : Path (gridVert γ δ u i j.castSucc) (gridVert γ δ u i j.succ) :=
  { toFun := gridS γ δ u i j
    continuous_toFun := (gridS γ δ u i j).continuous
    source' := gridS_zero γ δ u i j
    target' := gridS_one γ δ u i j }

/-- The `t`-direction grid edge as a path. -/
noncomputable def gridTPath (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i : Fin n) (j : Fin (n + 1)) : Path (gridVert γ δ u i.castSucc j) (gridVert γ δ u i.succ j) :=
  { toFun := gridT γ δ u i j
    continuous_toFun := (gridT γ δ u i j).continuous
    source' := gridT_zero γ δ u i j
    target' := gridT_one γ δ u i j }


/-- **The boundary cycle of the `(i,j)`-cell of the grid**, as a path
`vert(i,j) → vert(i+1,j) → vert(i+1,j+1) → vert(i,j+1) → vert(i,j)`.  This is the object whose
`F`-images are the cell boundaries of the interface-chain construction. -/
noncomputable def cellCycle (γ δ : C(UnitSeg, ℝ × ℝ)) {n : ℕ} (u : Fin (n + 1) → UnitSeg)
    (i j : Fin n) : Path (gridVert γ δ u i.castSucc j.castSucc) (gridVert γ δ u i.castSucc j.castSucc) :=
  (gridTPath γ δ u i j.castSucc).trans
    ((gridSPath γ δ u i.succ j).trans
      (((gridTPath γ δ u i j.succ).symm).trans ((gridSPath γ δ u i.castSucc j).symm)))


/-! ### The interface coefficients `±`(incidence with `A`-cells)

The cell boundary `cellCycle i j` decomposes, in the orientation convention of `grid_assembly`'s
`cellBnd`, as

  `∂(cell i j) = + gridT i j.castSucc + gridS i.succ j - gridT i j.succ - gridS i.castSucc j`,

i.e. *bottom (running in the `t`-direction, `+`), right (running in the `s`-direction, `+`),
top (`-`), left (`-`)*.  Summing over the `A`-cells (those with `c i j = false`) leaves, on an
interior edge, the *difference* of the two adjacent cells' `A`-indicators — the interior edges
cancel in pairs — and on the square's boundary edges the indicator of the single adjacent cell.
That is exactly what `coeffT` and `coeffS` below compute: `±(incidence with `A`-cells)`.

Because the grid's edges are read off the grid's own subdivision points, the two adjacent cells of
an interior edge are canonically `⟨q.val - 1, ·⟩` and `⟨q.val, ·⟩` (for a `t`-edge at `s`-index `q`)
and `⟨p.val - 1, ·⟩` and `⟨p.val, ·⟩` (for an `s`-edge at `t`-index `p`), so these coefficients are
pure `Fin (n+1)` arithmetic.
-/

section InterfaceCoefficients

variable {n : ℕ}

/-- Labelling of the cells of an `n × n` grid: `c i j = false` means the cell `(i,j)` is carried by
`VA`, `c i j = true` that it is carried by `VB` (the convention of the commons'
`exists_grid_decomposition_of_open_cover`). -/
abbrev Lab (n : ℕ) : Type := Fin n → Fin n → Bool

/-- `A`-indicator of the `(i,j)`-cell. -/
def isA (c : Lab n) (i j : Fin n) : ℤ := if c i j = false then 1 else 0

@[simp] lemma isA_false (c : Lab n) (i j : Fin n) (h : c i j = false) : isA c i j = 1 := by
  rw [isA, if_pos h]

@[simp] lemma isA_true (c : Lab n) (i j : Fin n) (h : c i j = true) : isA c i j = 0 := by
  rw [isA, if_neg (by simp [h])]

lemma isA_nonneg (c : Lab n) (i j : Fin n) : 0 ≤ isA c i j := by
  rw [isA]; split_ifs <;> norm_num

lemma isA_le_one (c : Lab n) (i j : Fin n) : isA c i j ≤ 1 := by
  rw [isA]; split_ifs <;> norm_num

lemma isA_ne_zero_iff (c : Lab n) (i j : Fin n) : isA c i j ≠ 0 ↔ c i j = false := by
  rw [isA]; split_ifs with h h <;> simp [h]

/-- **The `±`(incidence with `A`-cells)` coefficient of the `t`-edge `gridT i q` in `∂Σ_A`.**
The first summand is the contribution of the cell below the edge (its bottom side, `+1`), the
second that of the cell above (its top side, `-1`); on the square's boundary the corresponding
summand is absent. -/
noncomputable def coeffT (c : Lab n) (i : Fin n) (q : Fin (n + 1)) : ℤ :=
  (if h : q.val < n then isA c i ⟨q.val, h⟩ else 0)
    - (if h : 1 ≤ q.val then isA c i ⟨q.val - 1, by omega⟩ else 0)

/-- **The `±`(incidence with `A`-cells)` coefficient of the `s`-edge `gridS p j` in `∂Σ_A`.**
The first summand is the contribution of the cell on the left of the edge (its right side, `+1`),
the second that of the cell on the right (its left side, `-1`). -/
noncomputable def coeffS (c : Lab n) (p : Fin (n + 1)) (j : Fin n) : ℤ :=
  (if h : 1 ≤ p.val then isA c ⟨p.val - 1, by omega⟩ j else 0)
    - (if h : p.val < n then isA c ⟨p.val, h⟩ j else 0)

/-- Interior `t`-edges: the two adjacent cells are both present. -/
lemma coeffT_interior (c : Lab n) (i : Fin n) {q : Fin (n + 1)} (h1 : 1 ≤ q.val) (h2 : q.val < n) :
    coeffT c i q = isA c i ⟨q.val, h2⟩ - isA c i ⟨q.val - 1, by omega⟩ := by
  unfold coeffT
  rw [dif_pos h2, dif_pos h1]

/-- Bottom boundary of the square (`q.val = 0`): only the cell above the edge is adjacent. -/
lemma coeffT_bot (c : Lab n) (i : Fin n) {q : Fin (n + 1)} (h0 : q.val = 0) (hn : 0 < n) :
    coeffT c i q = isA c i ⟨0, hn⟩ := by
  unfold coeffT
  have hq : (⟨q.val, by omega⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext h0
  rw [dif_pos (by omega : q.val < n), dif_neg (by omega : ¬ 1 ≤ q.val), hq]
  simp

/-- Top boundary of the square (`q.val = n`): only the cell below the edge is adjacent. -/
lemma coeffT_top (c : Lab n) (i : Fin n) {q : Fin (n + 1)} (h0 : q.val = n) (hn : 0 < n) :
    coeffT c i q = - isA c i ⟨n - 1, by omega⟩ := by
  unfold coeffT
  have hq : (⟨q.val - 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  rw [dif_neg (by omega : ¬ q.val < n), dif_pos (by omega : 1 ≤ q.val), hq]
  simp

/-- Interior-edge support: if the coefficient does not vanish then exactly one adjacent cell is an
`A`-cell. -/
lemma coeffT_interior_support (c : Lab n) (i : Fin n) {q : Fin (n + 1)}
    (h1 : 1 ≤ q.val) (h2 : q.val < n)
    (h : coeffT c i q ≠ 0) :
    (isA c i ⟨q.val, h2⟩ = 1 ∧ isA c i ⟨q.val - 1, by omega⟩ = 0)
      ∨ (isA c i ⟨q.val, h2⟩ = 0 ∧ isA c i ⟨q.val - 1, by omega⟩ = 1) := by
  rw [coeffT_interior c i h1 h2] at h
  have hb := isA_nonneg c i ⟨q.val, h2⟩
  have hb' := isA_nonneg c i ⟨q.val - 1, by omega⟩
  have hc := isA_le_one c i ⟨q.val, h2⟩
  have hc' := isA_le_one c i ⟨q.val - 1, by omega⟩
  omega

lemma coeffS_interior (c : Lab n) (p : Fin (n + 1)) (j : Fin n) (h1 : 1 ≤ p.val) (h2 : p.val < n) :
    coeffS c p j = isA c ⟨p.val - 1, by omega⟩ j - isA c ⟨p.val, h2⟩ j := by
  unfold coeffS
  rw [dif_pos h1, dif_pos h2]

lemma coeffS_left (c : Lab n) (p : Fin (n + 1)) (j : Fin n) (h0 : p.val = 0) (hn : 0 < n) :
    coeffS c p j = - isA c ⟨0, hn⟩ j := by
  have hq : (⟨p.val, by omega⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext h0
  unfold coeffS
  rw [dif_neg (by omega : ¬ 1 ≤ p.val), dif_pos (by omega : p.val < n), hq]
  simp

lemma coeffS_right (c : Lab n) (p : Fin (n + 1)) (j : Fin n) (h0 : p.val = n) (hn : 0 < n) :
    coeffS c p j = isA c ⟨n - 1, by omega⟩ j := by
  have hq : (⟨p.val - 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  unfold coeffS
  rw [dif_pos (by omega : 1 ≤ p.val), dif_neg (by omega : ¬ p.val < n), hq]
  simp

lemma coeffS_interior_support (c : Lab n) (p : Fin (n + 1)) (j : Fin n)
    (h1 : 1 ≤ p.val) (h2 : p.val < n) (h : coeffS c p j ≠ 0) :
    (isA c ⟨p.val - 1, by omega⟩ j = 1 ∧ isA c ⟨p.val, h2⟩ j = 0)
      ∨ (isA c ⟨p.val - 1, by omega⟩ j = 0 ∧ isA c ⟨p.val, h2⟩ j = 1) := by
  rw [coeffS_interior c p j h1 h2] at h
  have hb := isA_nonneg c ⟨p.val - 1, by omega⟩ j
  have hb' := isA_nonneg c ⟨p.val, h2⟩ j
  have hc := isA_le_one c ⟨p.val - 1, by omega⟩ j
  have hc' := isA_le_one c ⟨p.val, h2⟩ j
  omega


/-! ### The interface chain as an `(edge, coefficient)` family

Row 1 of the interface-chain construction.  `GEdge n` is the edge set of the `n × n` grid — the
`t`-edges (`Fin n × Fin (n+1)`) together with the `s`-edges (`Fin (n+1) × Fin n`) — and `coeff c` is
the coefficient of each edge in `∂Σ_A`, i.e. the value of `±`(incidence with `A`-cells)` computed by
`coeffT`/`coeffS`.  `edgeSrc`/`edgeTgt` record the two vertices of each edge (so that the incidence
bookkeeping of `∂∂Σ_A = 0` becomes a statement about this single function), and `edgePath` records
the edge as a `Path` in `Ω`.

Once the conservation `Σ_{e : src e = v} coeff e = Σ_{e : tgt e = v} coeff e` at every grid vertex is
in place, `coeff` is a *circulation* on the finite graph `(GEdge n, edgeSrc, edgeTgt)`, and it
decomposes into closed walks; each of those lifts to a path in `Ω` (its edges being `F`-images of
grid edges, with `squareMap_T` closing the seam at `i = 0`, `i = n`), and the `joinedIn_of_flow`
extractor consumes the result.
-/

/-- The edge set of the `n × n` grid: `t`-edges (first summand) and `s`-edges (second). -/
abbrev GEdge (n : ℕ) : Type := Sum (Fin n × Fin (n + 1)) (Fin (n + 1) × Fin n)

/-- **The interface chain**: the coefficient of a grid edge in `∂Σ_A`. -/
noncomputable def coeff (c : Lab n) : GEdge n → ℤ
  | Sum.inl iq => coeffT c iq.1 iq.2
  | Sum.inr pj => coeffS c pj.1 pj.2

@[simp] lemma coeff_inl (c : Lab n) (i : Fin n) (q : Fin (n + 1)) :
    coeff c (Sum.inl (i, q)) = coeffT c i q := rfl

@[simp] lemma coeff_inr (c : Lab n) (p : Fin (n + 1)) (j : Fin n) :
    coeff c (Sum.inr (p, j)) = coeffS c p j := rfl

/-- The vertex a grid edge starts at. -/
def edgeSrc : GEdge n → Fin (n + 1) × Fin (n + 1)
  | Sum.inl iq => (iq.1.castSucc, iq.2)
  | Sum.inr pj => (pj.1, pj.2.castSucc)

/-- The vertex a grid edge ends at. -/
def edgeTgt : GEdge n → Fin (n + 1) × Fin (n + 1)
  | Sum.inl iq => (iq.1.succ, iq.2)
  | Sum.inr pj => (pj.1, pj.2.succ)

@[simp] lemma edgeSrc_inl (i : Fin n) (q : Fin (n + 1)) :
    edgeSrc (Sum.inl (i, q) : GEdge n) = (i.castSucc, q) := rfl

@[simp] lemma edgeTgt_inl (i : Fin n) (q : Fin (n + 1)) :
    edgeTgt (Sum.inl (i, q) : GEdge n) = (i.succ, q) := rfl

@[simp] lemma edgeSrc_inr (p : Fin (n + 1)) (j : Fin n) :
    edgeSrc (Sum.inr (p, j) : GEdge n) = (p, j.castSucc) := rfl

@[simp] lemma edgeTgt_inr (p : Fin (n + 1)) (j : Fin n) :
    edgeTgt (Sum.inr (p, j) : GEdge n) = (p, j.succ) := rfl

/-- **Singleton collapse (successor form).** -/
lemma sum_succ_eq (f : Fin n → ℤ) {v : Fin (n + 1)} {a : Fin n} (ha : a.succ = v) :
    (∑ p : Fin n, if p.succ = v then f p else 0) = f a := by
  have key := Finset.sum_eq_single
    (f := fun p : Fin n => if p.succ = v then f p else 0)
    (s := (Finset.univ : Finset (Fin n))) a
    (fun b _ hb => by
      rw [if_neg]
      intro hc
      exact hb (Fin.succ_injective n (hc.trans ha.symm)))
    (fun hmem => absurd (Finset.mem_univ _) hmem)
  rwa [if_pos ha] at key

/-- **Singleton collapse (castSucc form).** -/
lemma sum_castSucc_eq (f : Fin n → ℤ) {v : Fin (n + 1)} {a : Fin n} (ha : a.castSucc = v) :
    (∑ p : Fin n, if p.castSucc = v then f p else 0) = f a := by
  have key := Finset.sum_eq_single
    (f := fun p : Fin n => if p.castSucc = v then f p else 0)
    (s := (Finset.univ : Finset (Fin n))) a
    (fun b _ hb => by
      rw [if_neg]
      intro hc
      exact hb (Fin.castSucc_injective n (hc.trans ha.symm)))
    (fun hmem => absurd (Finset.mem_univ _) hmem)
  rwa [if_pos ha] at key

lemma sum_pair_eq (g : Fin (n + 1) → ℤ) (a : Fin (n + 1)) (v : Fin (n + 1) × Fin (n + 1)) :
    (∑ x : Fin (n + 1), if (a, x) = v then g x else 0) = if a = v.1 then g v.2 else 0 := by
  by_cases h : a = v.1
  · rw [if_pos h]
    have key := Finset.sum_eq_single
      (f := fun x : Fin (n + 1) => if (a, x) = v then g x else 0)
      (s := (Finset.univ : Finset (Fin (n + 1)))) v.2
      (fun b _ hb => by
        rw [if_neg]
        intro hc
        exact hb ((Prod.ext_iff.mp hc).2))
      (fun hmem => absurd (Finset.mem_univ _) hmem)
    have hgoal : (a, v.2) = v := by
      rw [Prod.ext_iff]
      exact ⟨h, rfl⟩
    rw [if_pos hgoal] at key
    exact key
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    intro hx
    exact h ((Prod.ext_iff.mp hx).1)

lemma sum_pair_eq' (g : Fin (n + 1) → ℤ) (b : Fin (n + 1)) (v : Fin (n + 1) × Fin (n + 1)) :
    (∑ x : Fin (n + 1), if (x, b) = v then g x else 0) = if b = v.2 then g v.1 else 0 := by
  by_cases h : b = v.2
  · rw [if_pos h]
    have key := Finset.sum_eq_single
      (f := fun x : Fin (n + 1) => if (x, b) = v then g x else 0)
      (s := (Finset.univ : Finset (Fin (n + 1)))) v.1
      (fun b' _ hb => by
        rw [if_neg]
        intro hc
        exact hb ((Prod.ext_iff.mp hc).1))
      (fun hmem => absurd (Finset.mem_univ _) hmem)
    have hgoal : (v.1, b) = v := by
      rw [Prod.ext_iff]
      exact ⟨rfl, h⟩
    rw [if_pos hgoal] at key
    exact key
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    intro hx
    exact h ((Prod.ext_iff.mp hx).2)

lemma sum_edgeSrc_split (c : Lab n) (v : Fin (n + 1) × Fin (n + 1)) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ i : Fin n, if i.castSucc = v.1 then coeffT c i v.2 else 0)
      + (∑ j : Fin n, if j.castSucc = v.2 then coeffS c v.1 j else 0) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
    simp only [edgeSrc_inl, coeff_inl]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_pair_eq (fun q : Fin (n + 1) => coeffT c i q) i.castSucc v
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [edgeSrc_inr, coeff_inr]
    apply Finset.sum_congr rfl
    intro j _
    exact sum_pair_eq' (fun p : Fin (n + 1) => coeffS c p j) j.castSucc v

lemma sum_edgeTgt_split (c : Lab n) (v : Fin (n + 1) × Fin (n + 1)) :
    (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0)
      = (∑ i : Fin n, if i.succ = v.1 then coeffT c i v.2 else 0)
      + (∑ j : Fin n, if j.succ = v.2 then coeffS c v.1 j else 0) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
    simp only [edgeTgt_inl, coeff_inl]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_pair_eq (fun q : Fin (n + 1) => coeffT c i q) i.succ v
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [edgeTgt_inr, coeff_inr]
    apply Finset.sum_congr rfl
    intro j _
    exact sum_pair_eq' (fun p : Fin (n + 1) => coeffS c p j) j.succ v


/-- **Local circulation, interior vertex.**  At an interior grid vertex the four incident edges'
coefficients cancel (`∂∂Σ_A = 0` at one vertex): the `t`-edge leaving, the `s`-edge leaving, the
`t`-edge arriving and the `s`-edge arriving. -/
lemma circulation_interior (c : Lab n) {vi vj : Fin (n + 1)} (h1 : 1 ≤ vi.val) (h2 : vi.val < n)
    (h3 : 1 ≤ vj.val) (h4 : vj.val < n) :
    coeffT c ⟨vi.val, h2⟩ vj + coeffS c vi ⟨vj.val, h4⟩
      = coeffT c ⟨vi.val - 1, by omega⟩ vj + coeffS c vi ⟨vj.val - 1, by omega⟩ := by
  rw [coeffT_interior c ⟨vi.val, h2⟩ (q := vj) h3 h4, coeffS_interior c vi ⟨vj.val, h4⟩ h1 h2,
    coeffT_interior c ⟨vi.val - 1, by omega⟩ (q := vj) h3 h4,
    coeffS_interior c vi ⟨vj.val - 1, by omega⟩ h1 h2]
  ring

/-- **The circulation at an interior vertex.** -/
lemma sum_succ_eq_zero (f : Fin n → ℤ) {v : Fin (n + 1)} (hv : v.val = 0) :
    (∑ p : Fin n, if p.succ = v then f p else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  intro hc
  have hv' := congrArg Fin.val hc
  simp only [Fin.val_succ] at hv'
  omega

lemma sum_castSucc_eq_zero (f : Fin n → ℤ) {v : Fin (n + 1)} (hv : n ≤ v.val) :
    (∑ p : Fin n, if p.castSucc = v then f p else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  intro hc
  have hv' := congrArg Fin.val hc
  simp only [Fin.val_castSucc] at hv'
  omega

/-- **The circulation at a vertex on the left edge of the square** (`v.1.val = 0`), with `v.2`
interior.  The `t`-edge arriving at `v` does not exist, so its collapse returns `0`. -/
lemma circulation_vertex_left (c : Lab n) {v : Fin (n + 1) × Fin (n + 1)} (hn : 0 < n)
    (h2 : v.1.val = 0) (h3 : 1 ≤ v.2.val) (h4 : v.2.val < n) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  have hleft : (⟨0, hn⟩ : Fin n).castSucc = v.1 := by
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_mk, h2]
  rw [sum_edgeSrc_split, sum_edgeTgt_split,
    sum_castSucc_eq (fun i : Fin n => coeffT c i v.2) hleft,
    sum_castSucc_eq (fun j : Fin n => coeffS c v.1 j)
      (Fin.ext rfl : (⟨v.2.val, h4⟩ : Fin n).castSucc = v.2),
    sum_succ_eq_zero (fun i : Fin n => coeffT c i v.2) h2,
    sum_succ_eq (fun j : Fin n => coeffS c v.1 j)
      (by apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega :
        (⟨v.2.val - 1, by omega⟩ : Fin n).succ = v.2)]
  rw [coeffT_interior c ⟨0, hn⟩ (q := v.2) h3 h4,
    coeffS_left c v.1 ⟨v.2.val, h4⟩ h2 hn,
    coeffS_left c v.1 ⟨v.2.val - 1, by omega⟩ h2 hn]
  ring


/-- **The circulation at a vertex on the right edge of the square** (`v.1.val = n`), with `v.2`
interior.  The `t`-edge leaving `v` does not exist, so its collapse returns `0`. -/
lemma circulation_vertex_right (c : Lab n) {v : Fin (n + 1) × Fin (n + 1)} (hn : 0 < n)
    (h2 : v.1.val = n) (h3 : 1 ≤ v.2.val) (h4 : v.2.val < n) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  have hone : (⟨n - 1, by omega⟩ : Fin n).succ = v.1 := by
    apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega
  rw [sum_edgeSrc_split, sum_edgeTgt_split,
    sum_castSucc_eq_zero (fun i : Fin n => coeffT c i v.2) (by omega : n ≤ v.1.val),
    sum_castSucc_eq (fun j : Fin n => coeffS c v.1 j)
      (Fin.ext rfl : (⟨v.2.val, h4⟩ : Fin n).castSucc = v.2),
    sum_succ_eq (fun i : Fin n => coeffT c i v.2) hone,
    sum_succ_eq (fun j : Fin n => coeffS c v.1 j)
      (by apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega :
        (⟨v.2.val - 1, by omega⟩ : Fin n).succ = v.2)]
  rw [coeffS_right c v.1 ⟨v.2.val, h4⟩ h2 hn,
    coeffT_interior c ⟨n - 1, by omega⟩ (q := v.2) h3 h4,
    coeffS_right c v.1 ⟨v.2.val - 1, by omega⟩ h2 hn]
  ring


/-- **The circulation at a vertex on the bottom edge of the square** (`v.2.val = 0`), with `v.1`
interior.  The `s`-edge arriving at `v` does not exist, so its collapse returns `0`. -/
lemma circulation_vertex_bot (c : Lab n) {v : Fin (n + 1) × Fin (n + 1)} (hn : 0 < n)
    (h1 : 1 ≤ v.1.val) (h2 : v.1.val < n) (h4 : v.2.val = 0) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  have hzero : (⟨0, hn⟩ : Fin n).castSucc = v.2 := by
    apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk, h4]
  rw [sum_edgeSrc_split, sum_edgeTgt_split,
    sum_castSucc_eq (fun i : Fin n => coeffT c i v.2)
      (Fin.ext rfl : (⟨v.1.val, h2⟩ : Fin n).castSucc = v.1),
    sum_castSucc_eq (fun j : Fin n => coeffS c v.1 j) hzero,
    sum_succ_eq (fun i : Fin n => coeffT c i v.2)
      (by apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega :
        (⟨v.1.val - 1, by omega⟩ : Fin n).succ = v.1),
    sum_succ_eq_zero (fun j : Fin n => coeffS c v.1 j) h4]
  rw [coeffT_bot c ⟨v.1.val, h2⟩ h4 hn, coeffT_bot c ⟨v.1.val - 1, by omega⟩ h4 hn,
    coeffS_interior c v.1 ⟨0, hn⟩ h1 h2]
  ring


/-- **The circulation at a vertex on the top edge of the square** (`v.2.val = n`), with `v.1`
interior.  The `s`-edge leaving `v` does not exist, so its collapse returns `0`. -/
lemma circulation_vertex_top (c : Lab n) {v : Fin (n + 1) × Fin (n + 1)} (hn : 0 < n)
    (h1 : 1 ≤ v.1.val) (h2 : v.1.val < n) (h4 : v.2.val = n) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  have hone : (⟨n - 1, by omega⟩ : Fin n).succ = v.2 := by
    apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega
  rw [sum_edgeSrc_split, sum_edgeTgt_split,
    sum_castSucc_eq (fun i : Fin n => coeffT c i v.2)
      (Fin.ext rfl : (⟨v.1.val, h2⟩ : Fin n).castSucc = v.1),
    sum_castSucc_eq_zero (fun j : Fin n => coeffS c v.1 j) (by omega : n ≤ v.2.val),
    sum_succ_eq (fun i : Fin n => coeffT c i v.2)
      (by apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega :
        (⟨v.1.val - 1, by omega⟩ : Fin n).succ = v.1),
    sum_succ_eq (fun j : Fin n => coeffS c v.1 j) hone]
  rw [coeffT_top c ⟨v.1.val, h2⟩ h4 hn, coeffT_top c ⟨v.1.val - 1, by omega⟩ h4 hn,
    coeffS_interior c v.1 ⟨n - 1, by omega⟩ h1 h2]
  ring


/-- **The circulation at the bottom-left corner** (`v.1.val = 0 = v.2.val`): only the `t`-leaving
and the `s`-leaving edges exist, and their coefficients are `I` and `−I`. -/
lemma circulation_vertex_cornerBL (c : Lab n) {v : Fin (n + 1) × Fin (n + 1)} (hn : 0 < n)
    (h2 : v.1.val = 0) (h4 : v.2.val = 0) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  have hcz : (⟨0, hn⟩ : Fin n).castSucc = v.1 := by
    apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk, h2]
  have hcz' : (⟨0, hn⟩ : Fin n).castSucc = v.2 := by
    apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk, h4]
  rw [sum_edgeSrc_split, sum_edgeTgt_split,
    sum_castSucc_eq (fun i : Fin n => coeffT c i v.2) hcz,
    sum_castSucc_eq (fun j : Fin n => coeffS c v.1 j) hcz',
    sum_succ_eq_zero (fun i : Fin n => coeffT c i v.2) h2,
    sum_succ_eq_zero (fun j : Fin n => coeffS c v.1 j) h4]
  rw [coeffT_bot c ⟨0, hn⟩ h4 hn, coeffS_left c v.1 ⟨0, hn⟩ h2 hn]
  ring


/-- **The circulation at the top-left corner** (`v.1.val = 0`, `v.2.val = n`). -/
lemma circulation_vertex_cornerTL (c : Lab n) {v : Fin (n + 1) × Fin (n + 1)} (hn : 0 < n)
    (h2 : v.1.val = 0) (h4 : v.2.val = n) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  have hcz : (⟨0, hn⟩ : Fin n).castSucc = v.1 := by
    apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk, h2]
  have hcn : (⟨n - 1, by omega⟩ : Fin n).succ = v.2 := by
    apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega
  rw [sum_edgeSrc_split, sum_edgeTgt_split,
    sum_castSucc_eq (fun i : Fin n => coeffT c i v.2) hcz,
    sum_castSucc_eq_zero (fun j : Fin n => coeffS c v.1 j) (by omega : n ≤ v.2.val),
    sum_succ_eq_zero (fun i : Fin n => coeffT c i v.2) h2,
    sum_succ_eq (fun j : Fin n => coeffS c v.1 j) hcn]
  rw [coeffT_top c ⟨0, hn⟩ h4 hn, coeffS_left c v.1 ⟨n - 1, by omega⟩ h2 hn]
  ring

/-- **The circulation at the top-right corner** (`v.1.val = n`, `v.2.val = n`). -/
lemma circulation_vertex_cornerTR (c : Lab n) {v : Fin (n + 1) × Fin (n + 1)} (hn : 0 < n)
    (h2 : v.1.val = n) (h4 : v.2.val = n) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  have hcn : (⟨n - 1, by omega⟩ : Fin n).succ = v.1 := by
    apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega
  have hcn' : (⟨n - 1, by omega⟩ : Fin n).succ = v.2 := by
    apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega
  rw [sum_edgeSrc_split, sum_edgeTgt_split,
    sum_castSucc_eq_zero (fun i : Fin n => coeffT c i v.2) (by omega : n ≤ v.1.val),
    sum_castSucc_eq_zero (fun j : Fin n => coeffS c v.1 j) (by omega : n ≤ v.2.val),
    sum_succ_eq (fun i : Fin n => coeffT c i v.2) hcn,
    sum_succ_eq (fun j : Fin n => coeffS c v.1 j) hcn']
  rw [coeffT_top c ⟨n - 1, by omega⟩ h4 hn, coeffS_right c v.1 ⟨n - 1, by omega⟩ h2 hn]
  ring

/-- **The circulation at the bottom-right corner** (`v.1.val = n`, `v.2.val = 0`). -/
lemma circulation_vertex_cornerBR (c : Lab n) {v : Fin (n + 1) × Fin (n + 1)} (hn : 0 < n)
    (h2 : v.1.val = n) (h4 : v.2.val = 0) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  have hcn : (⟨n - 1, by omega⟩ : Fin n).succ = v.1 := by
    apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega
  have hcz : (⟨0, hn⟩ : Fin n).castSucc = v.2 := by
    apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk, h4]
  rw [sum_edgeSrc_split, sum_edgeTgt_split,
    sum_castSucc_eq_zero (fun i : Fin n => coeffT c i v.2) (by omega : n ≤ v.1.val),
    sum_castSucc_eq (fun j : Fin n => coeffS c v.1 j) hcz,
    sum_succ_eq (fun i : Fin n => coeffT c i v.2) hcn,
    sum_succ_eq_zero (fun j : Fin n => coeffS c v.1 j) h4]
  rw [coeffT_bot c ⟨n - 1, by omega⟩ h4 hn, coeffS_right c v.1 ⟨0, hn⟩ h2 hn]
  ring


lemma circulation_vertex_interior (c : Lab n) {v : Fin (n + 1) × Fin (n + 1)}
    (h1 : 1 ≤ v.1.val) (h2 : v.1.val < n) (h3 : 1 ≤ v.2.val) (h4 : v.2.val < n) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  rw [sum_edgeSrc_split, sum_edgeTgt_split,
    sum_castSucc_eq (fun i : Fin n => coeffT c i v.2)
      (Fin.ext rfl : (⟨v.1.val, h2⟩ : Fin n).castSucc = v.1),
    sum_castSucc_eq (fun j : Fin n => coeffS c v.1 j)
      (Fin.ext rfl : (⟨v.2.val, h4⟩ : Fin n).castSucc = v.2),
    sum_succ_eq (fun i : Fin n => coeffT c i v.2)
      (by apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega :
        (⟨v.1.val - 1, by omega⟩ : Fin n).succ = v.1),
    sum_succ_eq (fun j : Fin n => coeffS c v.1 j)
      (by apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega :
        (⟨v.2.val - 1, by omega⟩ : Fin n).succ = v.2)]
  exact circulation_interior c h1 h2 h3 h4





/-- **The circulation at every grid vertex**: `Σ_{e : edgeSrc e = v} coeff e = Σ_{e : edgeTgt e = v}
coeff e`, i.e. `∂∂Σ_A = 0` written on the finite graph `(GEdge n, edgeSrc, edgeTgt)`. -/
lemma circulation_vertex (c : Lab n) (hn : 0 < n) (v : Fin (n + 1) × Fin (n + 1)) :
    (∑ e : GEdge n, if edgeSrc e = v then coeff c e else 0)
      = (∑ e : GEdge n, if edgeTgt e = v then coeff c e else 0) := by
  by_cases h1z : v.1.val = 0
  · by_cases h2z : v.2.val = 0
    · exact circulation_vertex_cornerBL c hn h1z h2z
    · by_cases h2n : v.2.val = n
      · exact circulation_vertex_cornerTL c hn h1z h2n
      · exact circulation_vertex_left c hn h1z (by omega) (by omega)
  · by_cases h1n : v.1.val = n
    · by_cases h2z : v.2.val = 0
      · exact circulation_vertex_cornerBR c hn h1n h2z
      · by_cases h2n : v.2.val = n
        · exact circulation_vertex_cornerTR c hn h1n h2n
        · exact circulation_vertex_right c hn h1n (by omega) (by omega)
    · by_cases h2z : v.2.val = 0
      · exact circulation_vertex_bot c hn (by omega) (by omega) h2z
      · by_cases h2n : v.2.val = n
        · exact circulation_vertex_top c hn (by omega) (by omega) h2n
        · exact circulation_vertex_interior c (by omega) (by omega) (by omega) (by omega)


/-- An orientation flag attached to a grid edge: `false` = the natural orientation, `true` = the
reversed one. -/
abbrev OEdge (n : ℕ) : Type := GEdge n × Bool

/-- The source vertex of an oriented edge. -/
def oSrc : OEdge n → Fin (n + 1) × Fin (n + 1)
  | (e, false) => edgeSrc e
  | (e, true) => edgeTgt e

/-- The target vertex of an oriented edge. -/
def oTgt : OEdge n → Fin (n + 1) × Fin (n + 1)
  | (e, false) => edgeTgt e
  | (e, true) => edgeSrc e

/-- The `ℕ`-valued multiplicity: the coefficient of the oriented edge, truncated at `0`. -/
noncomputable def oMult (c : Lab n) : OEdge n → ℕ
  | (e, false) => (coeff c e).toNat
  | (e, true) => (-coeff c e).toNat

@[simp] lemma oMult_false (c : Lab n) (e : GEdge n) : oMult c (e, false) = (coeff c e).toNat := rfl

@[simp] lemma oMult_true (c : Lab n) (e : GEdge n) : oMult c (e, true) = (-coeff c e).toNat := rfl

/-- **The orientation bridge**: the signed difference of the two multiplicities recovers the
coefficient, so summing `oMult` with the orientation flags reproduces `coeff` (and hence transports
`circulation_vertex` into the flow conservation of the extractor). -/
lemma oMult_sub (c : Lab n) (e : GEdge n) :
    ((oMult c (e, false) : ℤ) - (oMult c (e, true) : ℤ)) = coeff c e := by
  rw [oMult_false, oMult_true]
  by_cases h : 0 ≤ coeff c e
  · rw [Int.toNat_of_nonneg h, Int.toNat_of_nonpos (by omega : -coeff c e ≤ 0)]
    ring
  · rw [Int.toNat_of_nonpos (by omega : coeff c e ≤ 0), Int.toNat_of_nonneg (by omega : 0 ≤ -coeff c e)]
    ring


/-- **The flag-split telescope**: for any condition `S` on grid edges, the signed difference of the
`ℤ`-casts of `oMult` over the two orientation flags is the corresponding sum of `coeff`.  This is the
step that turns `circulation_vertex` (about `coeff`) into a conservation statement about `oMult`:
the `false`-flag contributes `+coeff` and the `true`-flag `−coeff`. -/
lemma oMult_sum_sub (c : Lab n) (S : GEdge n → Prop) [DecidablePred S] :
    (∑ e : GEdge n, if S e then (oMult c (e, false) : ℤ) else 0)
        - (∑ e : GEdge n, if S e then (oMult c (e, true) : ℤ) else 0)
      = ∑ e : GEdge n, if S e then coeff c e else 0 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : S e
  · rw [if_pos h, if_pos h, if_pos h, oMult_sub]
  · rw [if_neg h, if_neg h, if_neg h]
    ring


end InterfaceCoefficients

/-! ### STATUS (session 71): the annulus interface chain is BUILT and PROVED

**What is new and `sorry`-free in this file now** (section `AnnulusChain`, inserted just before
`mv_obligation`): the *annulus* interface chain of the grid subdivision — the chain that the
lifted-square picture cannot see because it needs the two seam columns of the square to be
identified.

* `cpred`/`csucc` (+`cpred_val`, `csucc_val`, `csucc_cpred`, `cpred_csucc`): the cyclic
  `t`-index arithmetic of the annulus grid `Fin n`.
* `AVert n := Fin n × Fin (n + 1)` (annulus vertices: cyclic `t`-index, `s`-level), and
  `AEdge n := (Fin n × Fin (n+1)) ⊕ (Fin n × Fin n)` (the `t`-edges and the `s`-edges).
* `isAv c i v` (the `A`-indicator of the `v`-th cell of column `i`, indexed by a *natural* number so
  that all index matches in the conservation are syntactic), `isAv_of_lt`, `isAv_of_ge`,
  `isAv_nonneg`, `isAv_le_one`, `isAv_ne_zero_iff`.
* `acoef c hn : AEdge n → ℤ` — **the annulus interface chain**:
  `t`-edge `(i,q)` ↦ `[q=0] - (isAv c i q - [q≠0]·isAv c i (q-1))` (i.e. `α - ∂Σ_A` with the
  cyclic `t`-index), and `s`-edge `(i,j)` ↦ `isAv c i j - isAv c (cpred hn i) j`
  (**this is exactly the seam identification**: for `i = 0` the two strip contributions
  `-coeffS c 0 j + coeffS c n j` are summed, which is the cancellation that removes the two "bad"
  seam columns of the strip chain).
* `aSrc`, `aTgt` and the sum evaluations `sum_aSrc_inl`, `sum_aSrc_inr`, `sum_aTgt_inl`,
  `sum_aTgt_inr`, `sum_aSrc_eval`, `sum_aTgt_eval`.
* **`acirculation`** — the chain is a **circulation**: at every vertex `(i,q)`,
  `Σ_{e : aSrc e = v} acoef e = Σ_{e : aTgt e = v} acoef e`.  (The proof is a three-case split on
  `q.val` with `ring`, using `isAv` and the `if`-free index discipline.)

**Remaining plan for the residual `mv_obligation`** (the machinery above is the first layer):

1. **`awind`** (DONE, `sorry`-free, section `AnnulusWinding`): the winding functional
   `awind hn z := Σ_{q : Fin (n+1)} z (t-edge (n-1, q))`, with `awind_add`, `awind_neg`,
   `awind_sub`, the telescoping lemma `sum_fin_telescope`, and **`awind_acoef`**
   (`Σ_q acoef c hn (inl (i,q)) = 1` for every column `i`; hence `awind hn (acoef c hn) = 1`).
   This is the *sheet displacement* of a closed walk: each step's sheet change (`+1` for a forward
   traversal of a `t`-edge with `i = n-1`, `-1` for a backward one, `0` otherwise) equals its
   `awind`-contribution, so `awind (walk as chain) = (the k with lift end = T^k (lift start))`.
2. **Oriented ℕ-flow** (DONE, `sorry`-free, section `AnnulusFlow`): `AOEdge n := AEdge n × Bool`
   with `aoSrc`/`aoTgt` and `aoW e = (acoef e.1).toNat` (forward) resp. `(-acoef e.1).toNat`
   (backward); `aoW_sub` is the identity `(aoW (f,false) : ℤ) - (aoW (f,true) : ℤ) = acoef f`,
   `aoW_sum_sub` its summed form, and **`aoFlow`** is the conservation
   `Σ_{aoSrc e = v} aoW e = Σ_{aoTgt e = v} aoW e` for every vertex `v` (proved from
   `acirculation` by `generalize` + `linarith`, after `Fintype.sum_prod_type`,
   `Fintype.sum_bool` and `Finset.sum_add_distrib`).
   *Remaining plumbing for step 3*: reindex `AOEdge n ≃ Fin m` and `AVert n ≃ Fin nv` (via
   `Fintype.equivFin`, `Fintype.sum_equiv`) to feed `aoFlow` to the extractor's hypothesis.

   **DONE since** (all `sorry`-free): `sum_symm_comp` (reindexing in `.symm` form, so the
   `Fintype.sum_equiv` coherence goal is `rfl` — the `Equiv.symm_apply_apply` fix), `eIdx`, `vIdx`,
   `ef`, `ew`, **`ef_flow`** (section `AnnulusReindex`), **`ef_flow_sub`** (section `AnnulusPeel`:
   peeling one unit off an edge `i₀` gives exactly the extractor's source/sink form with source
   `(ef hn i₀).2` and sink `(ef hn i₀).1`), and **`aStep`/`awindList`** (section `AnnulusWalk`: the
   seam contribution of a step and the winding of a walk).

   **DONE (session 88): the extraction and the peel are also available for an *arbitrary* flow**
   (section `AnnulusWalkGen`): `ef_flow_sub_gen` (the peel with the `Fin`-indexed conservation as a
   hypothesis) and `exists_closed_walk_gen` (the extraction for `W : Fin m → ℕ`, with the walk's
   edges satisfying `W (eIdx hn e) ≠ 0`); plus `update_ne_zero'`.  These are what the mass induction
   below runs on: at each step it peels/re-extracts with the flow that remains after removing the
   walk found so far.
   *`lake build` has `autoImplicit := false`*: every variable used in a statement (in particular
   `hn : 0 < n`) must be declared explicitly, even though `lake env lean <file>` (which uses the
   file's own defaults) accepts implicit ones — `ef_flow_sub_gen`/`exists_closed_walk_gen` need
   `(hn : 0 < n)` written out.
   **DONE (session 98): the chain of a flow.**  Section `AnnulusChainOfFlow`:
   `chainOfA hn A := fun f => (A (f,false) : ℤ) - (A (f,true) : ℤ)`,
   `chainOfFin hn W := fun f => (W (eIdx hn (f,false)) : ℤ) - (W (eIdx hn (f,true)) : ℤ)`,
   `toFin hn A := fun i => A ((eIdx hn).symm i)`, with
   **`chainOfA_aoW`** (`chainOfA hn (aoW c hn) = acoef c hn`, by `oW_sub`),
   **`chainOfFin_toFin`**, **`chainOfFin_ew`** (`chainOfFin hn (ew c hn) = acoef c hn`) and
   **`awind_chainOfFin_ew`** (`awind hn (chainOfFin hn (ew c hn)) = 1`, by `awind_acoef'`) plus
   `awind_chainOfA_aoW`.
   **Two design points for the induction itself, found while writing this** (both must be handled,
   they are not bookkeeping):
   * The walk returned by `exists_closed_walk_gen` may traverse the same edge twice while the flow
     weight there is `1`, so subtracting its `incChain` from an `ℕ`-valued flow can go *negative*.
     The removal step must therefore be carried out on the **`ℤ`-chain** (`chainOfA`, `awind_sub`),
     with the extraction run on the `ℕ`-flow *derived* from the chain (`toFin` of the positive/negative
     parts); the termination measure should then be `∑ f, |c f|` (which the subtraction strictly
     decreases only for a walk without a repeated edge — the honest fix is to use the extractor's
     path and remove it edge-by-edge with `ef_flow_sub_gen`, whose peeled flow stays `ℕ`-valued, so
     the mass `∑ i, W i` decreases by one per peel).
**DONE (session 103): the base of the induction.**  Section `AnnulusInductionBase`:
   **`exists_closed_walk_of_selfloop`** (a self-loop `e₀` with `0 < A e₀` and `aStep hn e₀ ≠ 0` gives
   the closed walk `[e₀]` with `awindList = aStep hn e₀ ≠ 0` — this settles the `n = 1` case
   outright), `chainOfA_eq_zero_of_mass_zero` (all weights zero ⟹ the chain is zero) and
   `awind_zero` (the zero chain has winding zero) — together they discharge the `M = 0` case.
   **DONE (session 108): the step case's opening.**  `exists_zFlow_ne_zero` (a non-zero chain has a
   non-zero derived-flow weight), `ne_zero_of_awind_ne_zero` (non-zero winding ⟹ non-zero chain, from
   `awind_zero`) and **`exists_zFlow_ne_zero_of_awind`** (non-zero winding ⟹ an oriented edge of
   non-zero derived-flow weight — the edge the step case peels).
   **THE INDUCTION STATEMENT (next stretch: this is the only thing left in this layer).**  The target,
   with every dependency now proved, is the strong-induction statement

   `lemma exists_walk_awind_ne_zero (hn : 0 < n) (M : ℕ) :`
   `  ∀ z : AEdge n → ℤ, (∑ f, |z f|) ≤ M →`
   `    (∀ v : AVert n, (∑ e, if aSrc hn e = v then z e else 0)`
   `        = (∑ e, if aTgt hn e = v then z e else 0)) →`
   `    awind hn z ≠ 0 →`
   `    ∃ (L : List (AOEdge n)) (hL : L ≠ []),`
   `      (∀ e ∈ L, 0 < zFlow hn z (eIdx hn e)) ∧`
   `      L.IsChain (fun a b => aoTgt hn a = aoSrc hn b) ∧`
   `      (aoTgt hn (L.getLast hL) = aoSrc hn (L.head hL)) ∧`
   `      awindList hn L ≠ 0`

   proved by induction on `M`, with:
   * `M = 0` ⟹ (sum of `|z f|` = 0 ⟹ `z = 0`) ⟹ `awind hn z = 0` (`awind_zero`), contradiction;
   * otherwise `exists_zFlow_ne_zero_of_awind` gives `e₀` with `zFlow hn z e₀ ≠ 0`; peel it,
     `z₁ := z - stepChain hn e₀` (the `ℤ`-chain form of the peel: `z₁ = chainOfA hn (updated flow)`,
     cf. `chainOfA_update`), so that `awind hn z₁ = awind hn z - aStep hn e₀` by `awind_sub` +
     `awind_stepChain`, and `∑ |z₁ f| ≤ M - 1`;
   * if `awind hn z₁ ≠ 0`: apply the induction hypothesis to `z₁` (weights of the walk are positive
     for `zFlow hn z₁`, hence for `zFlow hn z` since `zFlow` only lowers) and translate back: the walk
     is already the witness;
   * if `awind hn z₁ = 0`: then `aStep hn e₀ = awind hn z ≠ 0`.  Either `e₀` is a self-loop — then
     `[e₀]` is a closed walk with `awindList = aStep hn e₀ ≠ 0` (`exists_closed_walk_of_selfloop`,
     positive weight included) — or it is not, and then either peel `e₀` a second time (this is
     available whenever the derived weight at `e₀` was at least `2`, by `awind_chainOfA_update` applied
     to the peeled chain: the winding returns to `-aStep hn e₀ ≠ 0` and the induction hypothesis
     applies at mass `≤ M - 2`), or the weight at `e₀` was exactly `1`; in the latter case extract a
     walk at `i₀ := eIdx hn e₀` (`zFlow_conservation` → `toFin_flow'` → `exists_closed_walk_gen`,
     whose walk starts at `e₀` by the fourth conjunct); if its `awindList ≠ 0` it is the witness, and if
     `awindList = 0` then `z - incChain hn L` is a circulation of strictly smaller size with
     `awind hn (z - incChain hn L) = awind hn z - 0 = awind hn z ≠ 0` (`awind_sub_incChain`), so the
     induction hypothesis applies to it — this is the only branch that consumes the removal identity.
      **DONE (session 106/107): the `ℤ`-chain ⇄ `ℕ`-flow bridge.**  Section `AnnulusZFlow`:
   `zFlow hn z := fun e => if e.2 then (-(z e.1)).toNat else (z e.1).toNat` (the positive part on the
   forward orientation, the negative part on the backward one — `aoW` with `z` in place of `acoef`),
   **`chainOfA_zFlow`** (`chainOfA hn (zFlow hn z) = z`: passing to the flow and back is *lossless*)
   and **`zFlow_conservation`** (`zFlow hn z` has the `aoSrc`/`aoTgt`-conservation whenever `z` is a
   circulation; proved by the `Fintype.sum_prod_type`/`sum_bool`/`sum_add_distrib` + `generalize` +
   `linarith` pattern of `oFlow`, with the peel identity `(z f).toNat - (-(z f)).toNat = z f` as the
   pointwise input).  With these two, the extraction path for an arbitrary `ℤ`-chain is completely
   paved: `zFlow_conservation` + `toFin_flow'` hand `toFin hn (zFlow hn z)` to
   `exists_closed_walk_gen`, and `chainOfA_zFlow` returns the same chain.
      **DONE (session 105): the removal identity.**  `incChain`/`awind_incChain` were already in place
   (session 96, section `AnnulusIncidence`); what the removal step consumes is their composition
   **`awind_sub_incChain`**:
   `awind hn (z - incChain hn L) = awind hn z - awindList hn L` (one line from `awind_sub` +
   `awind_incChain`).  With `z := chainOfA hn A` this is the whole winding bookkeeping of the
   vanishing-winding step: subtracting a walk from the chain lowers the winding by the walk's winding,
   so a walk with `awindList ≠ 0` is a witness and one with `awindList = 0` leaves the winding
   unchanged, which is exactly what the induction hypothesis needs.
   **Precise shape of what is left.**  The induction should now be stated on **`ℤ`-chains** `z`
   (with the measure `M := ∑ f, |z f|` and the hypothesis `awind hn z ≠ 0`), because the removal
   `z - incChain hn L` stays a `ℤ`-chain without any non-negativity constraint (this is the
   negative-flow issue: a `ℕ`-valued flow peeled by a walk can go negative, whereas the `ℤ`-chain is
   closed under the subtraction).  The extraction runs on the `ℕ`-flow derived from `z` — namely
   `posOf z e := (z e.1).toNat` on the forward orientation and `(-z e.1).toNat` on the backward one,
   i.e. exactly `aoW`-with-`z`-in-place-of-`coef` — whose conservation (`oFlow`'s proof, with `acirculation`
   replaced by the circulation of `z`) and whose peel/transport (`ef_flow_sub_gen`, `toFin_flow'`) are
   already available for an arbitrary flow.  Specialising `z := chainOfA hn (aoW c hn) = acoef c hn`
   (`chainOfA_aoW`, `awind_chainOfA_aoW`) at the end gives the `Fin`-indexed walk that the lift needs.
      **DONE (session 104): the walk's starting edge is exposed.**  `exists_closed_walk_gen` now returns
   a fourth conjunct, **`L.head hL = (eIdx hn).symm i0`** (proved by `simp [List.head_cons]`, since the
   walk is built as `(eIdx hn).symm i0 :: l.map (eIdx hn).symm`).  This is exactly what the surviving
   sub-case needs: applied at `i0 := eIdx hn e₀` the walk starts at `e₀`, so with `awindList_cons`
   (`awindList hn L = aStep hn (L.head hL) + awindList hn L.tail`) its winding reads off as
   `aStep hn e₀ + awindList hn L.tail` with `aStep hn e₀ ≠ 0` — i.e. the walk's winding is that of the
   peeled edge plus the winding of its tail.
      **REFINEMENT of the non-self-loop seam case (found this session; it removes the extraction from
   most of it).**  In the peel dichotomy, when the peeled flow `A₁ = Function.update A e₀ (A e₀ - 1)`
   has `awind hn (chainOfA hn A₁) = 0` one gets `aStep hn e₀ = awind hn (chainOfA hn A) ≠ 0`, so `e₀`
   lies in the seam column.  Then:
   * if `A e₀ ≥ 2`: **peel `e₀` a second time**, `A₂ := Function.update A₁ e₀ (A₁ e₀ - 1)`; by
     `awind_chainOfA_update` (applied to `A₁`, whose weight at `e₀` is `A e₀ - 1 > 0`)
     `awind hn (chainOfA hn A₂) = 0 - aStep hn e₀ ≠ 0`, so the induction hypothesis applies to `A₂`
     (mass `M - 2 < M`); every walk it produces has positive `A₂`-weights, hence positive
     `A`-weights, and is a witness.  **No extraction is needed in this branch.**
   * if `A e₀ = 1`: `A₁ e₀ = 0`, so `e₀` can no longer be peeled; this is the surviving sub-case, and
     here `e₀` is a non-self-loop edge of the seam column (`n ≥ 2`), so `exists_closed_walk_gen` at
     `i₀ := eIdx hn e₀` applied to `toFin hn A` (conservation by `toFin_flow'`, the peel by
     `ef_flow_sub_gen`) yields a walk whose first edge is `e₀`; its winding is
     `aStep hn e₀ + awindList(path)` with `aStep hn e₀ ≠ 0`, and if that winding happens to vanish
     the walk is removed — which is where `incChain`/`awind_incChain` and the sharpened
     "walk-with-non-zero-winding" induction statement are needed.
   So the induction can be run with the **positive statement** ("if `awind (chainOfA A) ≠ 0` then there
   is a walk with positive weights and `awindList ≠ 0`") and the dichotomy above, with the only
   genuinely remaining case being `A e₀ = 1` at a seam-column edge.
   **DONE (session 102): the peel bookkeeping.**  Section `AnnulusPeelChain`:
   **`chainOfA_update`** (`chainOfA hn (Function.update A e₀ (A e₀ - 1)) = chainOfA hn A - stepChain hn e₀`
   for `0 < A e₀`) and **`awind_chainOfA_update`**
   (`awind hn (chainOfA hn (Function.update A e₀ (A e₀ - 1))) = awind hn (chainOfA hn A) - aStep hn e₀`,
   by `awind_sub` + `awind_stepChain`).  These two are the whole arithmetic of the peel case of the
   strong induction: after peeling `e₀` the winding drops by exactly `aStep hn e₀`, so if the peeled
   flow still has non-zero winding the induction hypothesis applies, and if it does not then
   `aStep hn e₀ = awind hn (chainOfA hn A) ≠ 0` — i.e. `e₀` sits in the seam column, which is exactly
   the case where the one-element walk `[e₀]` is available when `e₀` is a self-loop (`n = 1`), and
   otherwise is the case to attack with `exists_closed_walk_gen` on the peeled flow (whose walk then
   contains `e₀`).
   **DONE (session 99): the transport.**  Section `AnnulusToFinFlow`: **`toFin_flow`**
   (`toFin hn A` has the `ef`-indexed conservation whenever `A` has the `aoSrc`/`aoTgt`-indexed one),
   its `(i,q)`-indexed wrapper **`toFin_flow'`** (the form in which `oFlow` supplies the hypothesis),
   and **`ef_flow'`** re-deriving `ef_flow` through it — a consistency check that the transport is
   literally the same argument with `A` in place of `ew c hn` (definitionally
   `toFin hn (aoW c hn) = ew c hn`).
   **Strong induction (the next step, now fully prepared).**  Target: for every `A : AOEdge n → ℕ`
   with the `aoSrc`/`aoTgt`-conservation and `awind hn (chainOfA hn A) ≠ 0`, there is a closed walk
   `L` with `awindList hn L ≠ 0` and every edge of `L` carrying positive `A`-weight.  Proof by strong
   induction on `M := ∑ e, A e`:
   * `M = 0` ⟹ `chainOfA hn A = 0` ⟹ `awind 0 = 0`, contradiction with the hypothesis.
   * `M > 0`: pick `e₀` with `A e₀ ≠ 0`.  If `e₀` is a self-loop with `aStep hn e₀ ≠ 0`, the
     one-element walk `[e₀]` is closed with `awindList = aStep hn e₀ ≠ 0`: done.
   * Otherwise, **peel**: `A₁ := fun e => Function.update A e₀ (A e₀ - 1) e` (still `ℕ`-valued, mass
     `M - 1`, conservation preserved by the `ℤ`-identity behind `ef_flow_sub_gen`, transported with
     `toFin_flow'` applied to `A₁`), and extract a closed walk `L` from `A₁` via
     `exists_closed_walk_gen` (for a non-self-loop `e₀`; if `e₀` is a self-loop with
     `aStep hn e₀ = 0` use the peel with the one-element walk `[e₀]` whose `awindList = 0`, i.e. it
     does not change `awind`).
   * `awind` bookkeeping at each peel: removing the walk `L` means passing from `A` to
     `A - incChain hn L` *in `ℤ`* (see the note above), and
     `awind hn (chainOfA hn A - incChain hn L) = awind hn (chainOfA hn A) - awindList hn L`
     by `incChain_cons`/`awind_incChain` and `awind_sub`.  So if the extracted walk has
     `awindList ≠ 0` we are done, and otherwise the peeled flow again satisfies
     `awind ≠ 0` with strictly smaller mass, so the induction hypothesis applies.  The measure that
     terminates is `∑ e, A e` when peeling *one unit at a time* (`A₁` above), which is why the peel
     is written as a single-edge removal rather than a walk removal.
   * Finally specialise `A := aoW c hn` (`chainOfA_aoW`, `awind_chainOfA_aoW`), then
     `W := ew c hn` (`chainOfFin_ew`, `awind_chainOfFin_ew`), giving the walk with
     `awindList ≠ 0` that the lift needs.
      * `exists_closed_walk_gen` consumes the **`Fin`-indexed** conservation, so an `AOEdge`-form
     conservation must be transported to it: that is the lemma **`toFin_flow`** (`toFin hn A` has the
     `ef`-indexed conservation whenever `A` has the `aoSrc`/`aoTgt`-indexed one), provable by exactly
     the `sum_symm_comp` + `change` + `if_pos`/`if_neg` argument that `ef_flow` uses, with `A` in
     place of `ew c hn`.
      **Mass induction (the next step, precise shape).**  Let
   `chainOfFin W : AEdge n → ℤ := fun f => (W (eIdx hn (f,false)) : ℤ) - (W (eIdx hn (f,true)) : ℤ)`
   (so `chainOfFin (ew c hn) = acoef c hn`, by `aoW_sub` + `Equiv.apply_symm_apply`, and hence
   `awind hn (chainOfFin (ew c hn)) = 1` by `awind_acoef'`).  Claim: for any `W` with the `Fin`-indexed
   conservation and `awind hn (chainOfFin W) ≠ 0` there is a closed walk `L` (nonempty, all
   `W (eIdx hn e) ≠ 0`, `IsChain`, closed) with `awindList hn L ≠ 0`.  Strong induction on
   `∑ i, W i`: if some non-self-loop `i₀` has `W i₀ ≠ 0`, apply `exists_closed_walk_gen`; if the walk
   returned already has `awindList ≠ 0`, done; otherwise remove it (incidence chain
   `incChain hn L : AEdge n → ℤ := fun f => (L.map (fun e => if e.1 = f then (if e.2 then -1 else 1) else 0)).sum`),
   which preserves the conservation, strictly lowers the mass, and preserves `awind` because
   **DONE (session 96): the winding identity.**  Section `AnnulusIncidence`:
   `stepChain hn e := fun f => if e.1 = f then (if e.2 then -1 else 1) else 0`,
   `incChain hn L := fun f => (L.map (fun e => if e.1 = f then (if e.2 then -1 else 1) else 0)).sum`
   (the `1`-chain a walk stands for, with multiplicity), `incChain_nil`, `incChain_cons`
   (`incChain (e :: L) = stepChain e + incChain L`), **`awind_stepChain`**
   (`awind hn (stepChain hn e) = aStep hn e`, by `Finset.sum_eq_single` in the seam-column case and
   `Finset.sum_eq_zero` otherwise) and **`awind_incChain`**
   (`awind hn (incChain hn L) = awindList hn L`, by induction on `L` with `awind_add`).  So removing
   a walk from a flow changes `awind` of the resulting chain by exactly `awindList` of the walk: the
   mass induction now has every ingredient it needs.  (Lean detail that cost a round: the `if`
   condition of `stepChain` mentions the projection `(e).1` unreduced, so the `if_pos`/`if_neg`
   steps need a `change` to the reduced form `Sum.inl (i,q₀) = Sum.inl (⟨n-1,·⟩,q)`; and in the
   `Sum.inr` branch `exact absurd hh (by simp)` closes it.)
   **`awind hn (incChain hn L) = awindList hn L`** (the one identity still to prove: expand `awind`,
   swap the two sums with `Finset.sum_comm`/`List.sum`-to-`Finset` transport, and use the pointwise
   `∑_q (if e.1 = Sum.inl (⟨n-1,·⟩, q) then (if e.2 then -1 else 1) else 0) = aStep hn e`, which is
   `Finset.sum_ite_eq'` on the `Sum.inl` branch and `0` on the `Sum.inr` branch).  If instead `i₀` is
   a self-loop with `aStep hn i₀ ≠ 0`, the one-element walk `[i₀]` is already closed with
   `awindList ≠ 0`; if `aStep hn i₀ = 0`, remove it by the same argument.  Specialise to
   `W := ew c hn` at the end.
   **DONE (session 86): `exists_closed_walk`** (section `AnnulusWalkExtraction`) with the helpers `getLast_map'`, `isChain_map`, `update_ne_zero` — the extractor's path mapped back along `(eIdx hn).symm`, `(eIdx hn).symm i₀` prepended, the chain built by `List.isChain_cons_cons` + `isChain_map`, and the closure by `List.getLast_cons` + `getLast_map'`.  **Session 79 note (the facts its proof needs; kept for the mass-induction step):** the extraction (`exists_closed_walk`) needed
   the API facts the next attempt needs** (all mathematical components are ready, the list API was
   fought to a draw):
   * `List.IsChain` is the **consecutive** form: `List.isChain_cons_cons :
     (a :: b :: l).IsChain R ↔ R a b ∧ (b :: l).IsChain R`; `List.IsChain.imp` lifts a chain along
     an implication.  So for `L := (eIdx hn).symm i₀ :: l.map (eIdx hn).symm` the chain condition is
     `rw [List.isChain_cons_cons]` + `⟨(first link), hchain.imp (fun a b hab => (vIdx hn).injective hab)⟩`.
   * The first link `aoTgt hn ((eIdx hn).symm i₀) = aoSrc hn ((l.map (eIdx hn).symm).head _)` comes
     from the extractor's `(ef hn (l.head hl)).1 = (ef hn i₀).2` via `(vIdx hn).injective` and the
     **definitional** identities `(ef hn i).1 = vIdx hn (aoSrc hn ((eIdx hn).symm i))`,
     `(ef hn i).2 = vIdx hn (aoTgt hn ((eIdx hn).symm i))`, `ew c hn i = aoW c hn ((eIdx hn).symm i)`
     (hence `h0 : ew c hn i₀ ≠ 0` *is literally* `aoW c hn ((eIdx hn).symm i₀) ≠ 0`), plus
     `(l.map f).head = f (l.head)`.
   * `List.getLast_cons` takes **only** the proof `l ≠ []` (`l` and the head implicit):
     `List.getLast_cons (l := l') h`.  `Function.update_of_ne` (not `…update_neq`).  Both
     `(l.map f).head = f (l.head)` and `(l.map f).getLast = f (l.getLast)` are cleanest as local
     helpers proved by `cases l` (the `cons`/`cons cons` cases close by `rfl` after
     `List.getLast_cons`), not by lookup lemmas.
   * The peeled weights only vanish where the original weight vanishes: `Function.update_of_ne` for
     `i ≠ i₀`, and for `i = i₀` the hypothesis `ew i₀ - 1 ≠ 0` yields `ew i₀ ≠ 0`
     (`fun hc => h (by rw [hc]; simp)`).
   * Closure `aoTgt hn (L.getLast hL) = aoSrc hn (L.head hL)`: `List.getLast_cons`, the
     `getLast`-of-map helper, and the extractor's `(ef hn (l.getLast hl)).2 = (ef hn i₀).1` through
     `(vIdx hn).injective`.
3. **Extraction of a closed walk**: pick a non-self-loop oriented edge `i₀` with `oW i₀ ≠ 0`; put
   `w' := w - e_{i₀}`; the extractor applies with `x = (oTgt i₀)` and `y = (oSrc i₀)` and yields a
   directed path from `x` to `y` all of whose edges carry non-zero weight; appending the edge `i₀`
   gives a **closed walk**.  Iterating (subtracting the walk and re-extracting, the total mass
   strictly decreasing, `W` additivity) yields a closed walk with `W ≠ 0`.
4. **The lift**: with the sheet bookkeeping `m ↦ m ± 1` on the seam (a forward `t`-edge with
   `i = n-1` raises the sheet), each step of the walk lifts to the strip path
   `T^m (gridT i q)` resp. `T^m (gridS i j)` (or its reverse), whose endpoint is the strip lift of
   the next vertex; `JoinedIn`-transitivity along the walk gives
   `JoinedIn W (T^{m₀}(gridVert i₀ q₀)) (T^{m₀+W}(gridVert i₀ q₀))`, with `W ≠ 0`.  Reversing if
   `W < 0` gives a point of `W` joined to its `T^m`-translate inside `W`, i.e. `mv_obligation`.
5. **Goodness**: every edge with non-zero `acoef` has its strip realization in `W = VA ∩ VB`:
   interior `t`-edges (labels of the two adjacent cells differ — `isAv` gap), the `α` row
   (`q = 0`: the cell above is `B`), the `β` row (`q = n`: the cell below is `A`, and `δ ⊆ VB`),
   interior `s`-edges (labels differ), and the seam `s`-edge (`i = 0`: the labels of the cells
   `(0,j)` and `(n-1,j)` differ, and `T (gridS 0 j) = gridS n j` via `squareMap_T`, so the
   `T`-invariance transfers the containment).
-/

/-! ### The annulus interface chain (`α - ∂Σ_A` read on the cyclic grid)

The interface chain of the grid subdivision, read in the quotient annulus `Ω/T` instead of the
lifted square: the `t`-index is cyclic (`Fin n`) and the seam `s`-edges of the two boundary columns
are identified, so their two strip contributions *sum* (this is the cancellation that the lifted
square cannot see, and it is exactly what removes the two "bad" seam columns of the strip chain).

`acoef c` is the resulting `1`-chain: `α` (the closed `s = 0` circle, i.e. the translate path `γ`
closed up) minus the annulus boundary `∂Σ_A` of the `A`-cells.  It is a circulation
(`acirculation`) of winding `1`, supported on edges whose strip realizations lie in `VA ∩ VB`; the
extraction/lifting argument then produces a genuine translate path in `VA ∩ VB`. -/

section AnnulusChain

variable {n : ℕ}

/-- The cyclic predecessor in `Fin n` (`n > 0`). -/
def cpred (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨if i.val = 0 then n - 1 else i.val - 1, by split_ifs with h <;> omega⟩

/-- The cyclic successor in `Fin n` (`n > 0`). -/
def csucc (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨if i.val + 1 = n then 0 else i.val + 1, by split_ifs with h <;> omega⟩

lemma cpred_val (hn : 0 < n) (i : Fin n) :
    (cpred hn i).val = (if i.val = 0 then n - 1 else i.val - 1) := rfl

lemma csucc_val (hn : 0 < n) (i : Fin n) :
    (csucc hn i).val = (if i.val + 1 = n then 0 else i.val + 1) := rfl

lemma csucc_cpred (hn : 0 < n) (i : Fin n) : csucc hn (cpred hn i) = i := by
  apply Fin.ext
  rw [csucc_val]
  by_cases h : i.val = 0
  · have hc1 : (cpred hn i).val = n - 1 := by rw [cpred_val, if_pos h]
    rw [hc1, if_pos (by omega : n - 1 + 1 = n)]
    omega
  · have hc1 : (cpred hn i).val = i.val - 1 := by rw [cpred_val, if_neg h]
    rw [hc1, if_neg (by intro hh; have := i.isLt; omega)]
    have := i.isLt
    omega

lemma cpred_csucc (hn : 0 < n) (i : Fin n) : cpred hn (csucc hn i) = i := by
  apply Fin.ext
  rw [cpred_val]
  by_cases h : i.val + 1 = n
  · have hc1 : (csucc hn i).val = 0 := by rw [csucc_val, if_pos h]
    rw [hc1, if_pos rfl]
    omega
  · have hc1 : (csucc hn i).val = i.val + 1 := by rw [csucc_val, if_neg h]
    rw [hc1, if_neg (by intro hh; omega)]
    omega

/-- Annulus vertices: cyclic `t`-index, `s`-level `0..n`. -/
abbrev AVert (n : ℕ) : Type := Fin n × Fin (n + 1)

/-- Annulus edges: `t`-edges (varying `t`, cyclic) and `s`-edges (varying `s`). -/
abbrev AEdge (n : ℕ) : Type := Sum (Fin n × Fin (n + 1)) (Fin n × Fin n)

/-- The `A`-indicator of the `v`-th cell of column `i` (zero outside the range). -/
noncomputable def isAv (c : Lab n) (i : Fin n) (v : ℕ) : ℤ :=
  if h : v < n then isA c i ⟨v, h⟩ else 0

lemma isAv_of_lt (c : Lab n) (i : Fin n) {v : ℕ} (h : v < n) :
    isAv c i v = isA c i ⟨v, h⟩ := by
  rw [isAv, dif_pos h]

lemma isAv_of_ge (c : Lab n) (i : Fin n) {v : ℕ} (h : n ≤ v) : isAv c i v = 0 := by
  rw [isAv, dif_neg (by omega)]

lemma isAv_nonneg (c : Lab n) (i : Fin n) (v : ℕ) : 0 ≤ isAv c i v := by
  rw [isAv]; split_ifs <;> simp [isA_nonneg]

lemma isAv_le_one (c : Lab n) (i : Fin n) (v : ℕ) : isAv c i v ≤ 1 := by
  rw [isAv]; split_ifs with h
  · exact isA_le_one c i ⟨v, h⟩
  · norm_num

lemma isAv_ne_zero_iff (c : Lab n) (i : Fin n) {v : ℕ} (h : v < n) :
    isAv c i v ≠ 0 ↔ c i ⟨v, h⟩ = false := by
  rw [isAv_of_lt c i h, isA_ne_zero_iff]

/-- **The annulus interface chain `α - ∂Σ_A`.** -/
noncomputable def acoef (c : Lab n) (hn : 0 < n) : AEdge n → ℤ
  | Sum.inl (i, q) => (if q.val = 0 then (1 : ℤ) else 0)
      - (isAv c i q.val - (if q.val = 0 then 0 else isAv c i (q.val - 1)))
  | Sum.inr (i, j) => isAv c i j.val - isAv c (cpred hn i) j.val

lemma acoef_inl (c : Lab n) (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    acoef c hn (Sum.inl (i, q)) = (if q.val = 0 then (1 : ℤ) else 0)
      - (isAv c i q.val - (if q.val = 0 then 0 else isAv c i (q.val - 1))) := rfl

lemma acoef_inr (c : Lab n) (hn : 0 < n) (i j : Fin n) :
    acoef c hn (Sum.inr (i, j)) = isAv c i j.val - isAv c (cpred hn i) j.val := rfl

/-- The vertex an annulus edge starts at. -/
def aSrc (hn : 0 < n) : AEdge n → AVert n
  | Sum.inl (i, q) => (i, q)
  | Sum.inr (i, j) => (i, j.castSucc)

/-- The vertex an annulus edge ends at. -/
def aTgt (hn : 0 < n) : AEdge n → AVert n
  | Sum.inl (i, q) => (csucc hn i, q)
  | Sum.inr (i, j) => (i, j.succ)

@[simp] lemma aSrc_inl (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    aSrc hn (Sum.inl (i, q)) = (i, q) := rfl

@[simp] lemma aSrc_inr (hn : 0 < n) (i j : Fin n) :
    aSrc hn (Sum.inr (i, j)) = (i, j.castSucc) := rfl

@[simp] lemma aTgt_inl (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    aTgt hn (Sum.inl (i, q)) = (csucc hn i, q) := rfl

@[simp] lemma aTgt_inr (hn : 0 < n) (i j : Fin n) :
    aTgt hn (Sum.inr (i, j)) = (i, j.succ) := rfl

lemma sum_aSrc_inl (c : Lab n) (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    (∑ x : Fin n × Fin (n + 1),
        if aSrc hn (Sum.inl x) = (i, q) then acoef c hn (Sum.inl x) else 0)
      = acoef c hn (Sum.inl (i, q)) := by
  have h : ∀ x : Fin n × Fin (n + 1),
      (if aSrc hn (Sum.inl x) = (i, q) then acoef c hn (Sum.inl x) else 0)
        = (if x = (i, q) then acoef c hn (Sum.inl x) else 0) := fun x => rfl
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

lemma sum_aSrc_inr (c : Lab n) (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    (∑ y : Fin n × Fin n,
        if aSrc hn (Sum.inr y) = (i, q) then acoef c hn (Sum.inr y) else 0)
      = (if h : q.val < n then acoef c hn (Sum.inr (i, ⟨q.val, h⟩)) else 0) := by
  by_cases hq : q.val < n
  · rw [dif_pos hq]
    have key : ∀ y : Fin n × Fin n,
        (aSrc hn (Sum.inr y) = (i, q)) ↔ (y = (i, ⟨q.val, hq⟩)) := by
      rintro ⟨i', j'⟩
      simp only [aSrc_inr, Prod.mk.injEq]
      constructor
      · rintro ⟨hc, hc2⟩
        have hv : j'.val = q.val := by simpa using congrArg Fin.val hc2
        exact ⟨hc, Fin.ext hv⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, Fin.ext (by simp)⟩
    have h : ∀ y : Fin n × Fin n,
        (if aSrc hn (Sum.inr y) = (i, q) then acoef c hn (Sum.inr y) else 0)
          = (if y = (i, ⟨q.val, hq⟩) then acoef c hn (Sum.inr y) else 0) := by
      intro y; by_cases hy : y = (i, ⟨q.val, hq⟩)
      · rw [if_pos hy, if_pos ((key y).mpr hy)]
      · rw [if_neg hy, if_neg (fun hh => hy ((key y).mp hh))]
    rw [Finset.sum_congr rfl (fun y _ => h y), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  · rw [dif_neg hq]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    intro h
    rcases y with ⟨y1, y2⟩
    simp only [aSrc_inr, Prod.mk.injEq] at h
    obtain ⟨hc, hc2⟩ := h
    have hv : y2.val = q.val := by simpa using congrArg Fin.val hc2
    have := y2.isLt
    omega

lemma sum_aTgt_inl (c : Lab n) (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    (∑ x : Fin n × Fin (n + 1),
        if aTgt hn (Sum.inl x) = (i, q) then acoef c hn (Sum.inl x) else 0)
      = acoef c hn (Sum.inl (cpred hn i, q)) := by
  have h : ∀ x : Fin n × Fin (n + 1),
      (if aTgt hn (Sum.inl x) = (i, q) then acoef c hn (Sum.inl x) else 0)
        = (if x = (cpred hn i, q) then acoef c hn (Sum.inl x) else 0) := by
    intro x; by_cases hx : x = (cpred hn i, q)
    · rw [if_pos hx, if_pos (by rw [hx]; exact Prod.ext (csucc_cpred hn i) rfl)]
    · rw [if_neg hx, if_neg]
      rintro hh
      exact hx (by
        rcases x with ⟨i', q'⟩
        simp only [aTgt_inl, Prod.mk.injEq] at hh
        obtain ⟨hc, hq⟩ := hh
        have hi : i' = cpred hn i := by rw [← cpred_csucc hn i', hc]
        exact Prod.ext hi hq)
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

lemma sum_aTgt_inr (c : Lab n) (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    (∑ y : Fin n × Fin n,
        if aTgt hn (Sum.inr y) = (i, q) then acoef c hn (Sum.inr y) else 0)
      = (if h : 1 ≤ q.val then acoef c hn (Sum.inr (i, ⟨q.val - 1, by omega⟩)) else 0) := by
  by_cases hq : 1 ≤ q.val
  · rw [dif_pos hq]
    have key : ∀ y : Fin n × Fin n,
        (aTgt hn (Sum.inr y) = (i, q)) ↔ (y = (i, ⟨q.val - 1, by omega⟩)) := by
      rintro ⟨i', j'⟩
      simp only [aTgt_inr, Prod.mk.injEq]
      constructor
      · rintro ⟨hc, hc2⟩
        have hv : j'.val + 1 = q.val := by simpa using congrArg Fin.val hc2
        exact ⟨hc, Fin.ext (by simp only [Fin.val_mk]; omega)⟩
      · rintro ⟨rfl, rfl⟩
        refine ⟨rfl, Fin.ext ?_⟩
        simp only [Fin.val_succ, Fin.val_mk]
        omega
    have h : ∀ y : Fin n × Fin n,
        (if aTgt hn (Sum.inr y) = (i, q) then acoef c hn (Sum.inr y) else 0)
          = (if y = (i, ⟨q.val - 1, by omega⟩) then acoef c hn (Sum.inr y) else 0) := by
      intro y; by_cases hy : y = (i, ⟨q.val - 1, by omega⟩)
      · rw [if_pos hy, if_pos ((key y).mpr hy)]
      · rw [if_neg hy, if_neg (fun hh => hy ((key y).mp hh))]
    rw [Finset.sum_congr rfl (fun y _ => h y), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  · rw [dif_neg hq]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    intro h
    rcases y with ⟨y1, y2⟩
    simp only [aTgt_inr, Prod.mk.injEq] at h
    obtain ⟨hc, hc2⟩ := h
    have hv : y2.val + 1 = q.val := by simpa using congrArg Fin.val hc2
    omega

/-- **The source sum** of the annulus chain at a vertex, in `isAv` form. -/
lemma sum_aSrc_eval (c : Lab n) (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    (∑ e : AEdge n, if aSrc hn e = (i, q) then acoef c hn e else 0)
      = (if q.val = 0 then (1 : ℤ) else 0)
        - (isAv c i q.val - (if q.val = 0 then 0 else isAv c i (q.val - 1)))
        + (if h : q.val < n then (isAv c i q.val - isAv c (cpred hn i) q.val) else 0) := by
  rw [Fintype.sum_sum_type, sum_aSrc_inl, sum_aSrc_inr]
  simp only [acoef_inl, acoef_inr, Fin.val_mk]

/-- **The target sum** of the annulus chain at a vertex, in `isAv` form. -/
lemma sum_aTgt_eval (c : Lab n) (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    (∑ e : AEdge n, if aTgt hn e = (i, q) then acoef c hn e else 0)
      = (if q.val = 0 then (1 : ℤ) else 0)
        - (isAv c (cpred hn i) q.val - (if q.val = 0 then 0 else isAv c (cpred hn i) (q.val - 1)))
        + (if h : 1 ≤ q.val then
            (isAv c i (q.val - 1) - isAv c (cpred hn i) (q.val - 1)) else 0) := by
  rw [Fintype.sum_sum_type, sum_aTgt_inl, sum_aTgt_inr]
  simp only [acoef_inl, acoef_inr, Fin.val_mk]

/-- **The annulus interface chain is a circulation.** -/
lemma acirculation (c : Lab n) (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    (∑ e : AEdge n, if aSrc hn e = (i, q) then acoef c hn e else 0)
      = (∑ e : AEdge n, if aTgt hn e = (i, q) then acoef c hn e else 0) := by
  rw [sum_aSrc_eval, sum_aTgt_eval]
  by_cases hq0 : q.val = 0
  · rw [hq0]
    simp only [dif_pos (by omega : (0:ℕ) < n), dif_neg (by omega : ¬ (1:ℕ) ≤ 0)]
    norm_num
  · by_cases hqn : q.val = n
    · rw [hqn]
      simp only [if_neg (by omega : ¬ n = 0), dif_neg (by omega : ¬ n < n),
        dif_pos (by omega : (1:ℕ) ≤ n), isAv_of_ge c i (le_refl n),
        isAv_of_ge c (cpred hn i) (le_refl n)]
      ring
    · rw [dif_pos (by omega : q.val < n), dif_pos (by omega : (1:ℕ) ≤ q.val)]
      simp only [if_neg hq0]
      ring

end AnnulusChain




/-! ### The winding of the annulus interface chain

`awind` is the winding functional of the annulus grid: the net flow of a `1`-chain across the seam
column `t = n - 1`, i.e. across the `t`-edges `(n-1,q) → (0,q)` that wrap around the annulus.  For a
closed walk of the oriented graph it is exactly the number of sheets by which the walk's lift to the
strip is displaced (`T`-displacement), which is why it governs the translate path produced by the
extraction.  The chain `α - ∂Σ_A` has winding `1`: the `α` circle contributes `1`, and the boundary
of the cells telescopes in the `s`-direction. -/

section AnnulusWinding

variable {n : ℕ}

/-- **The winding functional** on the annulus grid. -/
noncomputable def awind (hn : 0 < n) (z : AEdge n → ℤ) : ℤ :=
  ∑ q : Fin (n + 1), z (Sum.inl (⟨n - 1, by omega⟩, q))

lemma awind_add (hn : 0 < n) (z z' : AEdge n → ℤ) :
    awind hn (z + z') = awind hn z + awind hn z' := by
  simp only [awind, Pi.add_apply, Finset.sum_add_distrib]

lemma awind_neg (hn : 0 < n) (z : AEdge n → ℤ) : awind hn (-z) = -awind hn z := by
  simp only [awind, Pi.neg_apply, Finset.sum_neg_distrib]

lemma awind_sub (hn : 0 < n) (z z' : AEdge n → ℤ) :
    awind hn (z - z') = awind hn z - awind hn z' := by
  simp only [awind, Pi.sub_apply, Finset.sum_sub_distrib]

/-- Telescoping over `Fin n`. -/
lemma sum_fin_telescope (f : ℕ → ℤ) (n : ℕ) :
    (∑ i : Fin n, (f i.val - f (i.val + 1))) = f 0 - f n := by
  rw [Fin.sum_univ_eq_sum_range (fun v => f v - f (v + 1))]
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- **The winding of the annulus interface chain is `1`.** -/
lemma awind_acoef (c : Lab n) (hn : 0 < n) (i : Fin n) :
    (∑ q : Fin (n + 1), acoef c hn (Sum.inl (i, q))) = 1 := by
  have hterm : ∀ q : Fin (n + 1),
      acoef c hn (Sum.inl (i, q))
        = (if q.val = 0 then (1 : ℤ) else 0)
          - (isAv c i q.val - (if q.val = 0 then 0 else isAv c i (q.val - 1))) := by
    intro q; rw [acoef_inl]
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Fin.sum_univ_succ]
  have h0 : ((if ((0 : Fin (n + 1))).val = 0 then (1 : ℤ) else 0)
      - (isAv c i ((0 : Fin (n + 1))).val
          - (if ((0 : Fin (n + 1))).val = 0 then 0 else isAv c i (((0 : Fin (n + 1))).val - 1))))
      = 1 - isAv c i 0 := by simp
  have hs : ∀ j : Fin n,
      ((if (j.succ : Fin (n + 1)).val = 0 then (1 : ℤ) else 0)
        - (isAv c i (j.succ : Fin (n + 1)).val
            - (if (j.succ : Fin (n + 1)).val = 0 then 0
                else isAv c i ((j.succ : Fin (n + 1)).val - 1))))
        = (isAv c i j.val - isAv c i (j.val + 1)) := by
    intro j
    have hj : (j.succ : Fin (n + 1)).val = j.val + 1 := Fin.val_succ j
    rw [hj]
    simp only [Nat.add_one_ne_zero, if_false]
    norm_num
  rw [h0, Finset.sum_congr rfl (fun j _ => hs j), sum_fin_telescope (fun v => isAv c i v) n,
    isAv_of_ge c i (le_refl n)]
  ring

lemma awind_acoef' (c : Lab n) (hn : 0 < n) : awind hn (acoef c hn) = 1 :=
  awind_acoef c hn ⟨n - 1, by omega⟩

end AnnulusWinding





/-! ### The oriented flow of the annulus chain

Splitting the (integer) circulation `acoef` into its positive and negative parts gives a
`ℕ`-valued flow on the *oriented* edge set `AOEdge n = AEdge n × Bool` (the `Bool` records whether
the edge is traversed along `aSrc → aTgt` or against).  This is the input of the extractor
`exists_directed_path_of_flow`, which turns any flow with a single source/sink pair into a directed
path along edges of non-zero flow. -/

section AnnulusFlow

variable {n : ℕ}

/-- The oriented edges: an annulus edge together with a direction flag
(`false` = along `aSrc → aTgt`, `true` = against it). -/
abbrev AOEdge (n : ℕ) : Type := AEdge n × Bool

/-- The source vertex of an oriented edge. -/
def aoSrc (hn : 0 < n) (e : AOEdge n) : AVert n := if e.2 then aTgt hn e.1 else aSrc hn e.1

/-- The target vertex of an oriented edge. -/
def aoTgt (hn : 0 < n) (e : AOEdge n) : AVert n := if e.2 then aSrc hn e.1 else aTgt hn e.1

/-- The weight of an oriented edge: the positive part of the chain coefficient (forward) resp. the
negative part (backward). -/
noncomputable def aoW (c : Lab n) (hn : 0 < n) (e : AOEdge n) : ℕ :=
  if e.2 then (-(acoef c hn e.1)).toNat else (acoef c hn e.1).toNat

lemma oW_sub (c : Lab n) (hn : 0 < n) (f : AEdge n) :
    ((aoW c hn (f, false) : ℤ) - (aoW c hn (f, true) : ℤ)) = acoef c hn f := by
  simp only [aoW, Bool.false_eq_true, if_true, if_false]
  by_cases h : 0 ≤ acoef c hn f
  · rw [Int.toNat_of_nonneg h, Int.toNat_of_nonpos (by omega : -acoef c hn f ≤ 0)]
    ring
  · rw [Int.toNat_of_nonpos (by omega : acoef c hn f ≤ 0),
      Int.toNat_of_nonneg (by omega : 0 ≤ -acoef c hn f)]
    ring

/-- **The flag telescope**: the signed difference of the `ℤ`-casts of `aoW` over the two
orientations is the chain coefficient. -/
lemma oW_sum_sub (c : Lab n) (hn : 0 < n) (S : AEdge n → Prop) [DecidablePred S] :
    (∑ f : AEdge n, if S f then (aoW c hn (f, false) : ℤ) else 0)
        - (∑ f : AEdge n, if S f then (aoW c hn (f, true) : ℤ) else 0)
      = ∑ f : AEdge n, if S f then acoef c hn f else 0 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : S f
  · rw [if_pos h, if_pos h, if_pos h, oW_sub]
  · rw [if_neg h, if_neg h, if_neg h]
    ring

/-- **The oriented flow is conserved** (from the `ℤ`-circulation `acirculation`). -/
lemma oFlow (c : Lab n) (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) :
    (∑ e : AOEdge n, if aoSrc hn e = (i, q) then (aoW c hn e : ℤ) else 0)
      = (∑ e : AOEdge n, if aoTgt hn e = (i, q) then (aoW c hn e : ℤ) else 0) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, aoSrc, aoTgt, Bool.false_eq_true, if_true, if_false]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 := oW_sum_sub c hn (S := fun f => aSrc hn f = (i, q))
  have h2 := oW_sum_sub c hn (S := fun f => aTgt hn f = (i, q))
  have h3 := acirculation c hn i q
  generalize hA : (∑ x : AEdge n, if aSrc hn x = (i, q) then (aoW c hn (x, false) : ℤ) else 0) = A
    at h1 ⊢
  generalize hB : (∑ x : AEdge n, if aSrc hn x = (i, q) then (aoW c hn (x, true) : ℤ) else 0) = B
    at h1 ⊢
  generalize hC : (∑ x : AEdge n, if aTgt hn x = (i, q) then (aoW c hn (x, false) : ℤ) else 0) = C
    at h2 ⊢
  generalize hD : (∑ x : AEdge n, if aTgt hn x = (i, q) then (aoW c hn (x, true) : ℤ) else 0) = D
    at h2 ⊢
  generalize hP : (∑ x : AEdge n, if aSrc hn x = (i, q) then acoef c hn x else 0) = P at h1 h3 ⊢
  generalize hQ : (∑ x : AEdge n, if aTgt hn x = (i, q) then acoef c hn x else 0) = Q at h2 h3 ⊢
  linarith

end AnnulusFlow






/-! ### Reindexing the oriented annulus graph to `Fin` (for the extractor)

The extractor `exists_directed_path_of_flow` is stated for a graph with vertex set `Fin nv` and edge
set `Fin m`; here the oriented annulus graph `(AOEdge n, aoSrc, aoTgt)` is reindexed along the
canonical equivalences `Fintype.equivFin`, and `aoFlow` is transported to the `Fin`-indexed
conservation `ef_flow` that the extractor consumes. -/

section AnnulusReindex

variable {n : ℕ}

/-- Reindexing a sum along an equivalence, in the `.symm` form (so that the coherence condition is
definitional). -/
lemma sum_symm_comp {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (F : α → ℤ) :
    (∑ b : β, F (e.symm b)) = ∑ a : α, F a :=
  Fintype.sum_equiv e.symm (fun b : β => F (e.symm b)) F (fun _ => rfl)

/-- The canonical reindexing of the oriented edges. -/
noncomputable def eIdx (hn : 0 < n) : AOEdge n ≃ Fin (Fintype.card (AOEdge n)) :=
  Fintype.equivFin _

/-- The canonical reindexing of the vertices. -/
noncomputable def vIdx (hn : 0 < n) : AVert n ≃ Fin (Fintype.card (AVert n)) :=
  Fintype.equivFin _

/-- The `Fin`-indexed source/target map of the oriented annulus graph. -/
noncomputable def ef (hn : 0 < n) :
    Fin (Fintype.card (AOEdge n)) →
      Fin (Fintype.card (AVert n)) × Fin (Fintype.card (AVert n)) :=
  fun i => (vIdx hn (aoSrc hn ((eIdx hn).symm i)), vIdx hn (aoTgt hn ((eIdx hn).symm i)))

/-- The `Fin`-indexed weights of the oriented annulus graph. -/
noncomputable def ew (c : Lab n) (hn : 0 < n) : Fin (Fintype.card (AOEdge n)) → ℕ :=
  fun i => aoW c hn ((eIdx hn).symm i)

lemma ef_apply (hn : 0 < n) (i : Fin (Fintype.card (AOEdge n))) :
    ef hn i = (vIdx hn (aoSrc hn ((eIdx hn).symm i)), vIdx hn (aoTgt hn ((eIdx hn).symm i))) :=
  rfl

lemma ew_apply (c : Lab n) (hn : 0 < n) (i : Fin (Fintype.card (AOEdge n))) :
    ew c hn i = aoW c hn ((eIdx hn).symm i) := rfl

/-- **The `Fin`-indexed conservation of the oriented flow.** -/
lemma ef_flow (c : Lab n) (hn : 0 < n) (v : Fin (Fintype.card (AVert n))) :
    (∑ i : Fin (Fintype.card (AOEdge n)), if (ef hn i).1 = v then (ew c hn i : ℤ) else 0)
      = (∑ i : Fin (Fintype.card (AOEdge n)), if (ef hn i).2 = v then (ew c hn i : ℤ) else 0) := by
  obtain ⟨w, rfl⟩ := (vIdx hn).surjective v
  have hL : (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).1 = vIdx hn w then (ew c hn i : ℤ) else 0)
      = ∑ e : AOEdge n, if aoSrc hn e = w then (aoW c hn e : ℤ) else 0 := by
    have hpt : ∀ i : Fin (Fintype.card (AOEdge n)),
        (if (ef hn i).1 = vIdx hn w then (ew c hn i : ℤ) else 0)
          = (fun e : AOEdge n => if aoSrc hn e = w then (aoW c hn e : ℤ) else 0)
              ((eIdx hn).symm i) := by
      intro i
      change (if vIdx hn (aoSrc hn ((eIdx hn).symm i)) = vIdx hn w
              then (aoW c hn ((eIdx hn).symm i) : ℤ) else 0)
        = (if aoSrc hn ((eIdx hn).symm i) = w
            then (aoW c hn ((eIdx hn).symm i) : ℤ) else 0)
      by_cases h : aoSrc hn ((eIdx hn).symm i) = w
      · rw [if_pos h, if_pos (show vIdx hn (aoSrc hn ((eIdx hn).symm i)) = vIdx hn w from by rw [h])]
      · rw [if_neg h, if_neg (fun hh => h ((vIdx hn).injective hh))]
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    exact sum_symm_comp (eIdx hn)
      (fun e : AOEdge n => if aoSrc hn e = w then (aoW c hn e : ℤ) else 0)
  have hR : (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).2 = vIdx hn w then (ew c hn i : ℤ) else 0)
      = ∑ e : AOEdge n, if aoTgt hn e = w then (aoW c hn e : ℤ) else 0 := by
    have hpt : ∀ i : Fin (Fintype.card (AOEdge n)),
        (if (ef hn i).2 = vIdx hn w then (ew c hn i : ℤ) else 0)
          = (fun e : AOEdge n => if aoTgt hn e = w then (aoW c hn e : ℤ) else 0)
              ((eIdx hn).symm i) := by
      intro i
      change (if vIdx hn (aoTgt hn ((eIdx hn).symm i)) = vIdx hn w
              then (aoW c hn ((eIdx hn).symm i) : ℤ) else 0)
        = (if aoTgt hn ((eIdx hn).symm i) = w
            then (aoW c hn ((eIdx hn).symm i) : ℤ) else 0)
      by_cases h : aoTgt hn ((eIdx hn).symm i) = w
      · rw [if_pos h, if_pos (show vIdx hn (aoTgt hn ((eIdx hn).symm i)) = vIdx hn w from by rw [h])]
      · rw [if_neg h, if_neg (fun hh => h ((vIdx hn).injective hh))]
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    exact sum_symm_comp (eIdx hn)
      (fun e : AOEdge n => if aoTgt hn e = w then (aoW c hn e : ℤ) else 0)
  rw [hL, hR]
  exact oFlow c hn w.1 w.2

end AnnulusReindex





/-! ### Walks of the oriented graph, their winding, and their lift

A *walk* is a list of oriented edges whose consecutive endpoints match
(`List.IsChain (fun a b => aoTgt hn a = aoSrc hn b)`); it is *closed* when the last target is the
first source.  Its **winding** is the signed number of times it crosses the seam column
`t = n - 1`, i.e. the sum over its steps of `aStep`; this is exactly the displacement in sheets of
its lift to the strip (`T`-displacement), and it agrees with `awind` of the chain the walk
represents. -/

section AnnulusWalk

variable {n : ℕ}

/-- The seam contribution of a step: `+1` for a forward traversal of a `t`-edge in the seam column
`t = n - 1` (the column of edges that wrap around the annulus), `-1` for a backward one, `0`
otherwise. -/
noncomputable def aStep (hn : 0 < n) (e : AOEdge n) : ℤ :=
  match e.1 with
  | Sum.inl (i, _) => if i = ⟨n - 1, by omega⟩ then (if e.2 then -1 else 1) else 0
  | Sum.inr _ => 0

@[simp] lemma aStep_inl (hn : 0 < n) (i : Fin n) (q : Fin (n + 1)) (b : Bool) :
    aStep hn (Sum.inl (i, q), b) = if i = ⟨n - 1, by omega⟩ then (if b then -1 else 1) else 0 :=
  rfl

@[simp] lemma aStep_inr (hn : 0 < n) (i j : Fin n) (b : Bool) :
    aStep hn (Sum.inr (i, j), b) = 0 := rfl

/-- **The winding of a walk**: the sum of the seam contributions of its steps. -/
noncomputable def awindList (hn : 0 < n) (l : List (AOEdge n)) : ℤ :=
  (l.map (aStep hn)).sum

@[simp] lemma awindList_nil (hn : 0 < n) : awindList hn [] = 0 := rfl

@[simp] lemma awindList_cons (hn : 0 < n) (e : AOEdge n) (l : List (AOEdge n)) :
    awindList hn (e :: l) = aStep hn e + awindList hn l := by
  simp [awindList]

lemma awindList_append (hn : 0 < n) (l l' : List (AOEdge n)) :
    awindList hn (l ++ l') = awindList hn l + awindList hn l' := by
  simp [awindList, List.map_append, List.sum_append]

/-- A single step's winding is the seam contribution. -/
@[simp] lemma awindList_singleton (hn : 0 < n) (e : AOEdge n) :
    awindList hn [e] = aStep hn e := by
  simp [awindList]

end AnnulusWalk






/-! ### Peeling one unit of the flow (the extractor's source/sink hypothesis)

Removing one unit of the flow on a single oriented edge `i₀` turns the conservation of `ef_flow` into
the *source/sink* form that the extractor `exists_directed_path_of_flow` consumes: the outflow at
the edge's tail drops by one and the inflow at its head drops by one, so the source is the head and
the sink the tail. -/

section AnnulusPeel

variable {n : ℕ}

/-- **The conservation after peeling one unit of the edge `i₀`.** -/
lemma ef_flow_sub (c : Lab n) (hn : 0 < n) (i0 : Fin (Fintype.card (AOEdge n)))
    (h0 : ew c hn i0 ≠ 0) (v : Fin (Fintype.card (AVert n))) :
    (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).1 = v then ((Function.update (ew c hn) i0 (ew c hn i0 - 1)) i : ℤ) else 0)
      - (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).2 = v then ((Function.update (ew c hn) i0 (ew c hn i0 - 1)) i : ℤ) else 0)
      = (if v = (ef hn i0).2 then (1 : ℤ) else 0) - (if v = (ef hn i0).1 then (1 : ℤ) else 0) := by
  have hw : 0 < ew c hn i0 := Nat.pos_of_ne_zero h0
  have h1 := ef_flow c hn v
  have hk : ∀ (p : Fin (Fintype.card (AOEdge n)) → Prop) [DecidablePred p],
      (∑ i ∈ Finset.univ.filter p, ((Function.update (ew c hn) i0 (ew c hn i0 - 1)) i : ℤ))
        = (∑ i ∈ Finset.univ.filter p, (ew c hn i : ℤ)) - (if p i0 then 1 else 0) := by
    intro p _
    rw [sum_update_sub (ew c hn) i0 hw (Finset.univ.filter p)]
    congr 1
    by_cases hp : p i0
    · rw [if_pos hp, if_pos (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hp⟩)]
    · rw [if_neg hp, if_neg (by intro hc; rw [Finset.mem_filter] at hc; exact hp hc.2)]
  rw [sum_ite_filter (fun i => ((Function.update (ew c hn) i0 (ew c hn i0 - 1)) i : ℤ))
        (fun i => (ef hn i).1 = v),
      sum_ite_filter (fun i => ((Function.update (ew c hn) i0 (ew c hn i0 - 1)) i : ℤ))
        (fun i => (ef hn i).2 = v)]
  rw [sum_ite_filter (f := fun i => (ew c hn i : ℤ)) (fun i => (ef hn i).1 = v),
      sum_ite_filter (f := fun i => (ew c hn i : ℤ)) (fun i => (ef hn i).2 = v)] at h1
  rw [hk (fun i => (ef hn i).1 = v), hk (fun i => (ef hn i).2 = v)]
  have hs1 : (if (ef hn i0).1 = v then (1 : ℤ) else 0) = (if v = (ef hn i0).1 then (1 : ℤ) else 0) := by
    by_cases h : v = (ef hn i0).1
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hh => h hh.symm), if_neg h]
  have hs2 : (if (ef hn i0).2 = v then (1 : ℤ) else 0) = (if v = (ef hn i0).2 then (1 : ℤ) else 0) := by
    by_cases h : v = (ef hn i0).2
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hh => h hh.symm), if_neg h]
  rw [hs1, hs2]
  linarith [h1]

end AnnulusPeel








/-! ### Extracting a closed walk of the oriented flow

The extractor gives a directed path from `(ef hn i₀).2` to `(ef hn i₀).1` along edges of non-zero
(peeled) weight; mapping back along `(eIdx hn).symm` and prepending the edge `i₀` gives a **closed
walk** all of whose edges carry non-zero `aoW`. -/

section AnnulusWalkExtraction

variable {n : ℕ}

/-- Last element of a mapped list. -/
lemma getLast_map' {α β : Type*} (f : α → β) :
    ∀ {l : List α} (h : l ≠ []), (l.map f).getLast (by simpa using h) = f (l.getLast h) := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
      intro h
      cases t with
      | nil => simp
      | cons b t' =>
          simp only [List.map_cons]
          rw [List.getLast_cons (by simp), List.getLast_cons (l := b :: t') (by simp)]
          exact ih (by simp)

/-- Mapping a chain along a relation-preserving map. -/
lemma isChain_map {α β : Type*} {R : α → α → Prop} {S : β → β → Prop} (f : α → β)
    (h : ∀ a b, R a b → S (f a) (f b)) : ∀ {l : List α}, l.IsChain R → (l.map f).IsChain S := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro hch
      cases t with
      | nil => simp
      | cons b t' =>
          simp only [List.map_cons]
          rw [List.isChain_cons_cons] at hch ⊢
          exact ⟨h a b hch.1, ih hch.2⟩

/-- The peeled weights only vanish on edges whose original weight vanishes. -/
lemma update_ne_zero {c : Lab n} {hn : 0 < n} {i0 : Fin (Fintype.card (AOEdge n))}
    {i : Fin (Fintype.card (AOEdge n))}
    (h : Function.update (ew c hn) i0 (ew c hn i0 - 1) i ≠ 0) : ew c hn i ≠ 0 := by
  by_cases hi : i = i0
  · subst hi
    rw [Function.update_self] at h
    exact fun hc => h (by rw [hc])
  · rwa [Function.update_of_ne hi] at h

/-- **Extraction of a closed walk.**  From a non-self-loop oriented edge `i₀` carrying non-zero
flow, the extractor produces a nonempty **closed walk** of the oriented graph, all of whose edges
carry non-zero weight. -/
lemma exists_closed_walk (c : Lab n) (hn : 0 < n)
    (i0 : Fin (Fintype.card (AOEdge n))) (h0 : ew c hn i0 ≠ 0)
    (hns : (ef hn i0).1 ≠ (ef hn i0).2) :
    ∃ (L : List (AOEdge n)) (hL : L ≠ []),
      (∀ e ∈ L, aoW c hn e ≠ 0) ∧
      L.IsChain (fun a b => aoTgt hn a = aoSrc hn b) ∧
      (aoTgt hn (L.getLast hL) = aoSrc hn (L.head hL)) := by
  obtain ⟨l, hl, hw, hsrc, htgt, hchain⟩ :=
    exists_directed_path_of_flow (ef hn) (Function.update (ew c hn) i0 (ew c hn i0 - 1))
      ((ef hn i0).2) ((ef hn i0).1) (Ne.symm hns) (fun v => ef_flow_sub c hn i0 h0 v)
  have hmapne : l.map (eIdx hn).symm ≠ [] := by simpa using hl
  -- the first link, through `(eIdx hn).symm`
  have hlink : aoTgt hn ((eIdx hn).symm i0) = aoSrc hn ((eIdx hn).symm (l.head hl)) := by
    refine ((vIdx hn).injective ?_).symm
    show vIdx hn (aoSrc hn ((eIdx hn).symm (l.head hl))) = vIdx hn (aoTgt hn ((eIdx hn).symm i0))
    rw [show vIdx hn (aoSrc hn ((eIdx hn).symm (l.head hl))) = (ef hn (l.head hl)).1 from rfl,
      show vIdx hn (aoTgt hn ((eIdx hn).symm i0)) = (ef hn i0).2 from rfl, hsrc]
  -- the closing link
  have hlast : aoTgt hn ((l.map (eIdx hn).symm).getLast hmapne) = aoSrc hn ((eIdx hn).symm i0) := by
    rw [getLast_map' (eIdx hn).symm hl]
    refine (vIdx hn).injective ?_
    show vIdx hn (aoTgt hn ((eIdx hn).symm (l.getLast hl)))
      = vIdx hn (aoSrc hn ((eIdx hn).symm i0))
    rw [show vIdx hn (aoTgt hn ((eIdx hn).symm (l.getLast hl))) = (ef hn (l.getLast hl)).2 from rfl,
      show vIdx hn (aoSrc hn ((eIdx hn).symm i0)) = (ef hn i0).1 from rfl, htgt]
  refine ⟨(eIdx hn).symm i0 :: l.map (eIdx hn).symm, by simp, ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact h0
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he'
      exact update_ne_zero (c := c) (hn := hn) (hw i hi)
  · cases l with
    | nil => exact absurd rfl hl
    | cons b t =>
        simp only [List.map_cons]
        rw [List.isChain_cons_cons]
        refine ⟨hlink, ?_⟩
        have hfun : ∀ a b, (ef hn a).2 = (ef hn b).1 →
            aoTgt hn ((eIdx hn).symm a) = aoSrc hn ((eIdx hn).symm b) := by
          intro a b hab
          refine (vIdx hn).injective ?_
          show vIdx hn (aoTgt hn ((eIdx hn).symm a)) = vIdx hn (aoSrc hn ((eIdx hn).symm b))
          rw [show vIdx hn (aoTgt hn ((eIdx hn).symm a)) = (ef hn a).2 from rfl,
            show vIdx hn (aoSrc hn ((eIdx hn).symm b)) = (ef hn b).1 from rfl, hab]
        exact isChain_map (R := fun a b => (ef hn a).2 = (ef hn b).1)
          (S := fun a b => aoTgt hn a = aoSrc hn b) (eIdx hn).symm hfun
          (by simpa only [List.map_cons] using hchain)
  · rw [List.getLast_cons (l := l.map (eIdx hn).symm) hmapne]
    simp only [List.head_cons]
    exact hlast

end AnnulusWalkExtraction






/-! ### The peel and the extraction for an arbitrary flow

For the mass induction of the winding lemma the extraction must be run not only on `ew c hn` but on
the flows obtained from it by removing closed walks.  Both the peel (`ef_flow_sub_gen`) and the
extraction (`exists_closed_walk_gen`) are therefore restated with the flow as a parameter, with the
`Fin`-indexed conservation as a hypothesis. -/

section AnnulusWalkGen

variable {n : ℕ}

/-- **The peel for an arbitrary flow.** -/
lemma ef_flow_sub_gen (hn : 0 < n) {W : Fin (Fintype.card (AOEdge n)) → ℕ}
    (hW : ∀ v : Fin (Fintype.card (AVert n)),
      (∑ i : Fin (Fintype.card (AOEdge n)), if (ef hn i).1 = v then (W i : ℤ) else 0)
        = (∑ i : Fin (Fintype.card (AOEdge n)), if (ef hn i).2 = v then (W i : ℤ) else 0))
    (i0 : Fin (Fintype.card (AOEdge n))) (h0 : W i0 ≠ 0)
    (v : Fin (Fintype.card (AVert n))) :
    (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).1 = v then ((Function.update W i0 (W i0 - 1)) i : ℤ) else 0)
      - (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).2 = v then ((Function.update W i0 (W i0 - 1)) i : ℤ) else 0)
      = (if v = (ef hn i0).2 then (1 : ℤ) else 0) - (if v = (ef hn i0).1 then (1 : ℤ) else 0) := by
  have hw : 0 < W i0 := Nat.pos_of_ne_zero h0
  have h1 := hW v
  have hk : ∀ (p : Fin (Fintype.card (AOEdge n)) → Prop) [DecidablePred p],
      (∑ i ∈ Finset.univ.filter p, ((Function.update W i0 (W i0 - 1)) i : ℤ))
        = (∑ i ∈ Finset.univ.filter p, (W i : ℤ)) - (if p i0 then 1 else 0) := by
    intro p _
    rw [sum_update_sub W i0 hw (Finset.univ.filter p)]
    congr 1
    by_cases hp : p i0
    · rw [if_pos hp, if_pos (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hp⟩)]
    · rw [if_neg hp, if_neg (by intro hc; rw [Finset.mem_filter] at hc; exact hp hc.2)]
  rw [sum_ite_filter (fun i => ((Function.update W i0 (W i0 - 1)) i : ℤ))
        (fun i => (ef hn i).1 = v),
      sum_ite_filter (fun i => ((Function.update W i0 (W i0 - 1)) i : ℤ))
        (fun i => (ef hn i).2 = v)]
  rw [sum_ite_filter (f := fun i => (W i : ℤ)) (fun i => (ef hn i).1 = v),
      sum_ite_filter (f := fun i => (W i : ℤ)) (fun i => (ef hn i).2 = v)] at h1
  rw [hk (fun i => (ef hn i).1 = v), hk (fun i => (ef hn i).2 = v)]
  have hs1 : (if (ef hn i0).1 = v then (1 : ℤ) else 0)
      = (if v = (ef hn i0).1 then (1 : ℤ) else 0) := by
    by_cases h : v = (ef hn i0).1
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hh => h hh.symm), if_neg h]
  have hs2 : (if (ef hn i0).2 = v then (1 : ℤ) else 0)
      = (if v = (ef hn i0).2 then (1 : ℤ) else 0) := by
    by_cases h : v = (ef hn i0).2
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hh => h hh.symm), if_neg h]
  rw [hs1, hs2]
  linarith [h1]

/-- The peeled weights only vanish where the original weight vanishes. -/
lemma update_ne_zero' {W : Fin (Fintype.card (AOEdge n)) → ℕ}
    {i0 i : Fin (Fintype.card (AOEdge n))}
    (h : Function.update W i0 (W i0 - 1) i ≠ 0) : W i ≠ 0 := by
  by_cases hi : i = i0
  · subst hi
    rw [Function.update_self] at h
    exact fun hc => h (by rw [hc])
  · rwa [Function.update_of_ne hi] at h

/-- **Extraction of a closed walk, for an arbitrary flow.** -/
lemma exists_closed_walk_gen (hn : 0 < n) {W : Fin (Fintype.card (AOEdge n)) → ℕ}
    (hW : ∀ v : Fin (Fintype.card (AVert n)),
      (∑ i : Fin (Fintype.card (AOEdge n)), if (ef hn i).1 = v then (W i : ℤ) else 0)
        = (∑ i : Fin (Fintype.card (AOEdge n)), if (ef hn i).2 = v then (W i : ℤ) else 0))
    (i0 : Fin (Fintype.card (AOEdge n))) (h0 : W i0 ≠ 0)
    (hns : (ef hn i0).1 ≠ (ef hn i0).2) :
    ∃ (L : List (AOEdge n)) (hL : L ≠ []),
      (∀ e ∈ L, W (eIdx hn e) ≠ 0) ∧
      L.IsChain (fun a b => aoTgt hn a = aoSrc hn b) ∧
      (aoTgt hn (L.getLast hL) = aoSrc hn (L.head hL)) ∧
      L.head hL = (eIdx hn).symm i0 := by
  obtain ⟨l, hl, hw, hsrc, htgt, hchain⟩ :=
    exists_directed_path_of_flow (ef hn) (Function.update W i0 (W i0 - 1))
      ((ef hn i0).2) ((ef hn i0).1) (Ne.symm hns) (fun v => ef_flow_sub_gen hn hW i0 h0 v)
  have hmapne : l.map (eIdx hn).symm ≠ [] := by simpa using hl
  have hlink : aoTgt hn ((eIdx hn).symm i0) = aoSrc hn ((eIdx hn).symm (l.head hl)) := by
    refine ((vIdx hn).injective ?_).symm
    show vIdx hn (aoSrc hn ((eIdx hn).symm (l.head hl))) = vIdx hn (aoTgt hn ((eIdx hn).symm i0))
    rw [show vIdx hn (aoSrc hn ((eIdx hn).symm (l.head hl))) = (ef hn (l.head hl)).1 from rfl,
      show vIdx hn (aoTgt hn ((eIdx hn).symm i0)) = (ef hn i0).2 from rfl, hsrc]
  have hlast : aoTgt hn ((l.map (eIdx hn).symm).getLast hmapne) = aoSrc hn ((eIdx hn).symm i0) := by
    rw [getLast_map' (eIdx hn).symm hl]
    refine (vIdx hn).injective ?_
    show vIdx hn (aoTgt hn ((eIdx hn).symm (l.getLast hl)))
      = vIdx hn (aoSrc hn ((eIdx hn).symm i0))
    rw [show vIdx hn (aoTgt hn ((eIdx hn).symm (l.getLast hl))) = (ef hn (l.getLast hl)).2 from rfl,
      show vIdx hn (aoSrc hn ((eIdx hn).symm i0)) = (ef hn i0).1 from rfl, htgt]
  refine ⟨(eIdx hn).symm i0 :: l.map (eIdx hn).symm, by simp, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · rw [Equiv.apply_symm_apply]; exact h0
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he'
      rw [Equiv.apply_symm_apply]
      exact update_ne_zero' (W := W) (hw i hi)
  · cases l with
    | nil => exact absurd rfl hl
    | cons b t =>
        simp only [List.map_cons]
        rw [List.isChain_cons_cons]
        refine ⟨hlink, ?_⟩
        have hfun : ∀ a b, (ef hn a).2 = (ef hn b).1 →
            aoTgt hn ((eIdx hn).symm a) = aoSrc hn ((eIdx hn).symm b) := by
          intro a b hab
          refine (vIdx hn).injective ?_
          show vIdx hn (aoTgt hn ((eIdx hn).symm a)) = vIdx hn (aoSrc hn ((eIdx hn).symm b))
          rw [show vIdx hn (aoTgt hn ((eIdx hn).symm a)) = (ef hn a).2 from rfl,
            show vIdx hn (aoSrc hn ((eIdx hn).symm b)) = (ef hn b).1 from rfl, hab]
        exact isChain_map (R := fun a b => (ef hn a).2 = (ef hn b).1)
          (S := fun a b => aoTgt hn a = aoSrc hn b) (eIdx hn).symm hfun
          (by simpa only [List.map_cons] using hchain)
  · rw [List.getLast_cons (l := l.map (eIdx hn).symm) hmapne]
    simp only [List.head_cons]
    exact hlast
  · simp [List.head_cons]

end AnnulusWalkGen







/-! ### The incidence chain of a walk, and its winding

`incChain hn L` is the `1`-chain that a walk `L` stands for (`+1` on each edge it traverses forward,
`-1` on each backward traversal, counted with multiplicity), and **`awind_incChain`** says that its
winding is the winding of the walk, `awindList`.  This is the identity that makes the mass induction
work: removing a walk from a flow changes `awind` of the resulting chain by exactly `awindList` of
the walk removed. -/

section AnnulusIncidence

variable {n : ℕ}

/-- The incidence chain of a single step: `±1` on the traversed edge, `0` elsewhere. -/
noncomputable def stepChain (hn : 0 < n) (e : AOEdge n) : AEdge n → ℤ :=
  fun f => if e.1 = f then (if e.2 then -1 else 1) else 0

/-- The incidence chain of a walk. -/
noncomputable def incChain (hn : 0 < n) (L : List (AOEdge n)) : AEdge n → ℤ :=
  fun f => (L.map (fun e => if e.1 = f then (if e.2 then -1 else 1) else 0)).sum

@[simp] lemma incChain_nil (hn : 0 < n) : incChain hn [] = 0 := by
  ext f
  simp [incChain]

lemma incChain_cons (hn : 0 < n) (e : AOEdge n) (L : List (AOEdge n)) :
    incChain hn (e :: L) = stepChain hn e + incChain hn L := by
  ext f
  simp only [incChain, List.map_cons, List.sum_cons, stepChain, Pi.add_apply]

/-- **The winding of one step's incidence chain is that step's seam contribution.** -/
lemma awind_stepChain (hn : 0 < n) (e : AOEdge n) :
    awind hn (stepChain hn e) = aStep hn e := by
  rw [awind]
  rcases e with ⟨f, b⟩
  rcases f with ⟨i, q₀⟩ | ⟨i, j⟩
  · rw [aStep_inl]
    by_cases h : i = ⟨n - 1, by omega⟩
    · rw [if_pos h, Finset.sum_eq_single q₀]
      · change (if Sum.inl (i, q₀) = Sum.inl (⟨n - 1, by omega⟩, q₀) then
            (if b = true then (-1 : ℤ) else 1) else 0) = (if b = true then (-1 : ℤ) else 1)
        rw [if_pos (by simp [h])]
      · intro q _ hq
        rw [stepChain]
        rw [if_neg]
        intro hh
        change Sum.inl (i, q₀) = Sum.inl (⟨n - 1, by omega⟩, q) at hh
        simp only [Sum.inl.injEq, Prod.mk.injEq] at hh
        exact hq hh.2.symm
      · intro hq; exact absurd (Finset.mem_univ q₀) hq
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro q _
      rw [stepChain]
      rw [if_neg]
      intro hh
      change Sum.inl (i, q₀) = Sum.inl (⟨n - 1, by omega⟩, q) at hh
      simp only [Sum.inl.injEq, Prod.mk.injEq] at hh
      exact h hh.1
  · rw [aStep_inr]
    apply Finset.sum_eq_zero
    intro q _
    rw [stepChain]
    rw [if_neg]
    intro hh
    exact absurd hh (by simp)

/-- **The winding of the incidence chain of a walk is the winding of the walk.** -/
lemma awind_incChain (hn : 0 < n) (L : List (AOEdge n)) :
    awind hn (incChain hn L) = awindList hn L := by
  induction L with
  | nil => simp only [incChain_nil, awindList_nil, awind, Finset.sum_const_zero, Pi.zero_apply]
  | cons e L ih =>
      rw [incChain_cons, awind_add, awind_stepChain, ih, awindList_cons]

/-- **Removing a walk from a chain drops the winding by the walk's winding.**  This is the form in
which the removal step of the strong induction uses `awind_incChain`: taking the chain of a flow and
subtracting the incidence chain of a walk `L` lowers its winding by exactly `awindList hn L`, so a
walk whose winding is non-zero makes the winding drop, and a walk with `awindList hn L ≠ 0` is itself
a witness. -/
lemma awind_sub_incChain (hn : 0 < n) (z : AEdge n → ℤ) (L : List (AOEdge n)) :
    awind hn (z - incChain hn L) = awind hn z - awindList hn L := by
  rw [awind_sub, awind_incChain]

end AnnulusIncidence







/-! ### The chain of a flow, and the chain of `ew c hn`

`chainOfA hn A` is the `ℤ`-chain a flow `A` on the oriented annulus edges stands for (forward
weights minus backward weights), and `chainOfFin hn W` the same for a `Fin`-indexed flow.  The
point of the definitions: **`chainOfA hn (aoW c hn) = acoef c hn`** (by `oW_sub`), so the flow that
the extraction runs on really does represent the annulus interface chain, of winding `1`
(`awind_acoef'`). -/

section AnnulusChainOfFlow

variable {n : ℕ}

/-- The `ℤ`-chain represented by a flow on the oriented annulus edges. -/
noncomputable def chainOfA (hn : 0 < n) (A : AOEdge n → ℕ) : AEdge n → ℤ :=
  fun f => (A (f, false) : ℤ) - (A (f, true) : ℤ)

/-- The `ℤ`-chain represented by a `Fin`-indexed oriented flow. -/
noncomputable def chainOfFin (hn : 0 < n) (W : Fin (Fintype.card (AOEdge n)) → ℕ) :
    AEdge n → ℤ :=
  fun f => (W (eIdx hn (f, false)) : ℤ) - (W (eIdx hn (f, true)) : ℤ)

/-- The `Fin`-indexed flow of an annulus-edge flow. -/
noncomputable def toFin (hn : 0 < n) (A : AOEdge n → ℕ) : Fin (Fintype.card (AOEdge n)) → ℕ :=
  fun i => A ((eIdx hn).symm i)

lemma chainOfA_apply (hn : 0 < n) (A : AOEdge n → ℕ) (f : AEdge n) :
    chainOfA hn A f = (A (f, false) : ℤ) - (A (f, true) : ℤ) := rfl

lemma chainOfFin_apply (hn : 0 < n) (W : Fin (Fintype.card (AOEdge n)) → ℕ) (f : AEdge n) :
    chainOfFin hn W f = (W (eIdx hn (f, false)) : ℤ) - (W (eIdx hn (f, true)) : ℤ) := rfl

/-- **The chain of the flow `aoW c hn` is the annulus interface chain.** -/
lemma chainOfA_aoW (c : Lab n) (hn : 0 < n) : chainOfA hn (aoW c hn) = acoef c hn := by
  ext f
  exact oW_sub c hn f

lemma chainOfFin_toFin (hn : 0 < n) (A : AOEdge n → ℕ) :
    chainOfFin hn (toFin hn A) = chainOfA hn A := by
  ext f
  simp only [chainOfFin, chainOfA, toFin, Equiv.symm_apply_apply]

/-- **The chain of the `Fin`-indexed flow `ew c hn` is the annulus interface chain.** -/
lemma chainOfFin_ew (c : Lab n) (hn : 0 < n) : chainOfFin hn (ew c hn) = acoef c hn := by
  ext f
  rw [chainOfFin_apply]
  have h1 : ew c hn (eIdx hn (f, false)) = aoW c hn (f, false) := by
    rw [ew_apply, Equiv.symm_apply_apply]
  have h2 : ew c hn (eIdx hn (f, true)) = aoW c hn (f, true) := by
    rw [ew_apply, Equiv.symm_apply_apply]
  rw [h1, h2]
  exact oW_sub c hn f

/-- **The winding of the chain of `ew c hn` is `1`.** -/
lemma awind_chainOfFin_ew (c : Lab n) (hn : 0 < n) :
    awind hn (chainOfFin hn (ew c hn)) = 1 := by
  rw [chainOfFin_ew, awind_acoef']

/-- The winding of the chain of `aoW c hn` is `1`. -/
lemma awind_chainOfA_aoW (c : Lab n) (hn : 0 < n) :
    awind hn (chainOfA hn (aoW c hn)) = 1 := by
  rw [chainOfA_aoW, awind_acoef']

end AnnulusChainOfFlow



/-! ### Transporting the conservation to the `Fin`-indexed flow

`exists_closed_walk_gen` and `ef_flow_sub_gen` consume the **`Fin`-indexed** conservation, but the
flows arising in the induction are naturally indexed by the annulus edges.  `toFin_flow` transports
the `aoSrc`/`aoTgt`-indexed conservation of `A` to the `ef`-indexed conservation of `toFin hn A` —
the same `sum_symm_comp` + `change` + `if_pos`/`if_neg` argument as `ef_flow`, with `A` in place of
`ew c hn`. -/

section AnnulusToFinFlow

variable {n : ℕ}

/-- **The conservation of `toFin hn A`** (from the conservation of `A`). -/
lemma toFin_flow (hn : 0 < n) (A : AOEdge n → ℕ)
    (hA : ∀ v : AVert n,
      (∑ e : AOEdge n, if aoSrc hn e = v then (A e : ℤ) else 0)
        = (∑ e : AOEdge n, if aoTgt hn e = v then (A e : ℤ) else 0))
    (v : Fin (Fintype.card (AVert n))) :
    (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).1 = v then (toFin hn A i : ℤ) else 0)
      = (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).2 = v then (toFin hn A i : ℤ) else 0) := by
  obtain ⟨w, rfl⟩ := (vIdx hn).surjective v
  have hL : (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).1 = vIdx hn w then (toFin hn A i : ℤ) else 0)
      = ∑ e : AOEdge n, if aoSrc hn e = w then (A e : ℤ) else 0 := by
    have hpt : ∀ i : Fin (Fintype.card (AOEdge n)),
        (if (ef hn i).1 = vIdx hn w then (toFin hn A i : ℤ) else 0)
          = (fun e : AOEdge n => if aoSrc hn e = w then (A e : ℤ) else 0)
              ((eIdx hn).symm i) := by
      intro i
      change (if vIdx hn (aoSrc hn ((eIdx hn).symm i)) = vIdx hn w
              then (A ((eIdx hn).symm i) : ℤ) else 0)
        = (if aoSrc hn ((eIdx hn).symm i) = w
            then (A ((eIdx hn).symm i) : ℤ) else 0)
      by_cases h : aoSrc hn ((eIdx hn).symm i) = w
      · rw [if_pos h, if_pos (show vIdx hn (aoSrc hn ((eIdx hn).symm i)) = vIdx hn w from by rw [h])]
      · rw [if_neg h, if_neg (fun hh => h ((vIdx hn).injective hh))]
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    exact sum_symm_comp (eIdx hn)
      (fun e : AOEdge n => if aoSrc hn e = w then (A e : ℤ) else 0)
  have hR : (∑ i : Fin (Fintype.card (AOEdge n)),
        if (ef hn i).2 = vIdx hn w then (toFin hn A i : ℤ) else 0)
      = ∑ e : AOEdge n, if aoTgt hn e = w then (A e : ℤ) else 0 := by
    have hpt : ∀ i : Fin (Fintype.card (AOEdge n)),
        (if (ef hn i).2 = vIdx hn w then (toFin hn A i : ℤ) else 0)
          = (fun e : AOEdge n => if aoTgt hn e = w then (A e : ℤ) else 0)
              ((eIdx hn).symm i) := by
      intro i
      change (if vIdx hn (aoTgt hn ((eIdx hn).symm i)) = vIdx hn w
              then (A ((eIdx hn).symm i) : ℤ) else 0)
        = (if aoTgt hn ((eIdx hn).symm i) = w
            then (A ((eIdx hn).symm i) : ℤ) else 0)
      by_cases h : aoTgt hn ((eIdx hn).symm i) = w
      · rw [if_pos h, if_pos (show vIdx hn (aoTgt hn ((eIdx hn).symm i)) = vIdx hn w from by rw [h])]
      · rw [if_neg h, if_neg (fun hh => h ((vIdx hn).injective hh))]
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    exact sum_symm_comp (eIdx hn)
      (fun e : AOEdge n => if aoTgt hn e = w then (A e : ℤ) else 0)
  rw [hL, hR]
  exact hA w

/-- The `(i,q)`-indexed form of `toFin_flow`. -/
lemma toFin_flow' (hn : 0 < n) (A : AOEdge n → ℕ)
    (hA : ∀ (i : Fin n) (q : Fin (n + 1)),
      (∑ e : AOEdge n, if aoSrc hn e = (i, q) then (A e : ℤ) else 0)
        = (∑ e : AOEdge n, if aoTgt hn e = (i, q) then (A e : ℤ) else 0)) :
    ∀ v : Fin (Fintype.card (AVert n)),
      (∑ i : Fin (Fintype.card (AOEdge n)),
          if (ef hn i).1 = v then (toFin hn A i : ℤ) else 0)
        = (∑ i : Fin (Fintype.card (AOEdge n)),
          if (ef hn i).2 = v then (toFin hn A i : ℤ) else 0) :=
  fun v => toFin_flow hn A (fun w => hA w.1 w.2) v

/-- `ef_flow` re-derived through `toFin_flow` (consistency check: `toFin hn (aoW c hn) = ew c hn`). -/
lemma ef_flow' (c : Lab n) (hn : 0 < n) (v : Fin (Fintype.card (AVert n))) :
    (∑ i : Fin (Fintype.card (AOEdge n)), if (ef hn i).1 = v then (ew c hn i : ℤ) else 0)
      = (∑ i : Fin (Fintype.card (AOEdge n)), if (ef hn i).2 = v then (ew c hn i : ℤ) else 0) :=
  toFin_flow hn (aoW c hn) (fun w => oFlow c hn w.1 w.2) v

end AnnulusToFinFlow




/-! ### The chain and the winding of a peeled flow

Peeling one unit of a flow `A` at an edge `e₀` subtracts exactly the incidence chain `stepChain e₀`
from the chain it represents, and hence subtracts `aStep hn e₀` from the winding.  These are the two
identities the peel case of the strong induction runs on. -/

section AnnulusPeelChain

variable {n : ℕ}

/-- **The chain of a peeled flow.** -/
lemma chainOfA_update (hn : 0 < n) (A : AOEdge n → ℕ) (e0 : AOEdge n) (h : 0 < A e0) :
    chainOfA hn (Function.update A e0 (A e0 - 1)) = chainOfA hn A - stepChain hn e0 := by
  ext f
  rw [Pi.sub_apply, chainOfA_apply, chainOfA_apply, stepChain]
  by_cases hf : f = e0.1
  · subst hf
    rcases e0 with ⟨f0, b⟩
    rcases b with _ | _
    · -- `false`: the peeled edge is `(f₀, false)`
      rw [if_pos rfl, Function.update_self]
      have h1 : (Function.update (A : AOEdge n → ℕ) (f0, false) (A (f0, false) - 1))
          (f0, true) = A (f0, true) := by
        rw [Function.update_of_ne]; simp
      rw [h1]
      have h2 : (((A (f0, false) - 1 : ℕ)) : ℤ) = (A (f0, false) : ℤ) - 1 := by omega
      rw [h2]
      simp
      ring
    · -- `true`: the peeled edge is `(f₀, true)`
      rw [if_pos rfl, Function.update_self]
      have h1 : (Function.update (A : AOEdge n → ℕ) (f0, true) (A (f0, true) - 1))
          (f0, false) = A (f0, false) := by
        rw [Function.update_of_ne]; simp
      rw [h1]
      have h2 : (((A (f0, true) - 1 : ℕ)) : ℤ) = (A (f0, true) : ℤ) - 1 := by omega
      rw [h2]
      simp
      ring
  · rw [if_neg (fun hc => hf hc.symm)]
    have h1 : (Function.update (A : AOEdge n → ℕ) e0 (A e0 - 1)) (f, false)
        = A (f, false) := by
      rw [Function.update_of_ne]; intro hc; exact hf (by rw [← hc])
    have h2 : (Function.update (A : AOEdge n → ℕ) e0 (A e0 - 1)) (f, true) = A (f, true) := by
      rw [Function.update_of_ne]; intro hc; exact hf (by rw [← hc])
    rw [h1, h2]
    ring

/-- **The winding of a peeled flow.** -/
lemma awind_chainOfA_update (hn : 0 < n) (A : AOEdge n → ℕ) (e0 : AOEdge n) (h : 0 < A e0) :
    awind hn (chainOfA hn (Function.update A e0 (A e0 - 1)))
      = awind hn (chainOfA hn A) - aStep hn e0 := by
  rw [chainOfA_update hn A e0 h, awind_sub, awind_stepChain]

end AnnulusPeelChain




/-! ### The base of the strong induction

The easy ends of the induction: a self-loop whose seam contribution does not vanish is *itself* a
closed walk with non-zero winding (so it settles the case `n = 1` outright), and a flow of mass zero
represents the zero chain, whose winding vanishes (so it cannot satisfy the hypothesis). -/

section AnnulusInductionBase

variable {n : ℕ}

/-- **A self-loop with non-zero seam contribution is a closed walk with non-zero winding.** -/
lemma exists_closed_walk_of_selfloop (hn : 0 < n) (A : AOEdge n → ℕ) (e0 : AOEdge n)
    (hloop : aoSrc hn e0 = aoTgt hn e0) (hpos : 0 < A e0) (hst : aStep hn e0 ≠ 0) :
    ∃ (L : List (AOEdge n)) (hL : L ≠ []),
      (∀ e ∈ L, 0 < A e) ∧
      L.IsChain (fun a b => aoTgt hn a = aoSrc hn b) ∧
      (aoTgt hn (L.getLast hL) = aoSrc hn (L.head hL)) ∧
      awindList hn L ≠ 0 := by
  refine ⟨[e0], by simp, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [List.mem_singleton] at he
    subst he
    exact hpos
  · simp
  · simp [hloop]
  · simpa [awindList] using hst

/-- A flow whose weights all vanish represents the zero chain. -/
lemma chainOfA_eq_zero_of_mass_zero (hn : 0 < n) {A : AOEdge n → ℕ} (h : ∀ e, A e = 0) :
    chainOfA hn A = 0 := by
  ext f
  simp only [chainOfA, h, Pi.zero_apply]
  norm_num

/-- The winding of the zero chain vanishes. -/
lemma awind_zero (hn : 0 < n) : awind hn (0 : AEdge n → ℤ) = 0 := by
  simp only [awind, Pi.zero_apply, Finset.sum_const_zero]

end AnnulusInductionBase


/-! ### The `ℕ`-flow derived from a `ℤ`-chain

The strong induction is stated on `ℤ`-chains `z` (the removal `z - incChain hn L` needs no side
condition), but the extraction needs an `ℕ`-valued flow.  `zFlow hn z` is that flow: the positive part
of `z` on the forward orientation, the negative part on the backward one.  It is the `aoW`-of-`z`
construction, and **`chainOfA_zFlow`** says that it represents exactly the chain `z` back again —
so passing to the flow and back is lossless. -/

section AnnulusZFlow

variable {n : ℕ}

/-- The `ℕ`-flow derived from a `ℤ`-chain. -/
noncomputable def zFlow (hn : 0 < n) (z : AEdge n → ℤ) : AOEdge n → ℕ :=
  fun e => if e.2 then (-(z e.1)).toNat else (z e.1).toNat

/-- **The derived flow represents the same chain.** -/
lemma chainOfA_zFlow (hn : 0 < n) (z : AEdge n → ℤ) : chainOfA hn (zFlow hn z) = z := by
  ext f
  rw [chainOfA_apply]
  simp only [zFlow, Bool.false_eq_true, if_true, if_false]
  by_cases h : 0 ≤ z f
  · rw [Int.toNat_of_nonneg h, Int.toNat_of_nonpos (by omega : -z f ≤ 0)]
    ring
  · rw [Int.toNat_of_nonpos (by omega : z f ≤ 0),
      Int.toNat_of_nonneg (by omega : 0 ≤ -z f)]
    ring


/-- **The derived flow is conserved**, whenever the chain is a circulation. -/
lemma zFlow_conservation (hn : 0 < n) (z : AEdge n → ℤ)
    (hz : ∀ v : AVert n, (∑ e : AEdge n, if aSrc hn e = v then z e else 0)
        = (∑ e : AEdge n, if aTgt hn e = v then z e else 0)) :
    ∀ v : AVert n,
      (∑ e : AOEdge n, if aoSrc hn e = v then (zFlow hn z e : ℤ) else 0)
        = (∑ e : AOEdge n, if aoTgt hn e = v then (zFlow hn z e : ℤ) else 0) := by
  intro v
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, aoSrc, aoTgt, Bool.false_eq_true, if_true, if_false]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have key : ∀ (p : AEdge n → Prop) [DecidablePred p],
      (∑ f : AEdge n, if p f then ((zFlow hn z (f, false)) : ℤ) else 0)
        - (∑ f : AEdge n, if p f then ((zFlow hn z (f, true)) : ℤ) else 0)
      = ∑ f : AEdge n, if p f then z f else 0 := by
    intro p _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro f _
    by_cases h : p f
    · rw [if_pos h, if_pos h, if_pos h]
      simp only [zFlow, Bool.false_eq_true, if_true, if_false]
      by_cases hz' : 0 ≤ z f
      · rw [Int.toNat_of_nonneg hz', Int.toNat_of_nonpos (by omega : -z f ≤ 0)]
        ring
      · rw [Int.toNat_of_nonpos (by omega : z f ≤ 0),
          Int.toNat_of_nonneg (by omega : 0 ≤ -z f)]
        ring
    · rw [if_neg h, if_neg h, if_neg h]
      ring
  have h1 := key (fun f => aSrc hn f = v)
  have h2 := key (fun f => aTgt hn f = v)
  have h3 := hz v
  generalize hA : (∑ f : AEdge n, if aSrc hn f = v then ((zFlow hn z (f, false)) : ℤ) else 0) = A
    at h1 ⊢
  generalize hB : (∑ f : AEdge n, if aSrc hn f = v then ((zFlow hn z (f, true)) : ℤ) else 0) = B
    at h1 ⊢
  generalize hC : (∑ f : AEdge n, if aTgt hn f = v then ((zFlow hn z (f, false)) : ℤ) else 0) = C
    at h2 ⊢
  generalize hD : (∑ f : AEdge n, if aTgt hn f = v then ((zFlow hn z (f, true)) : ℤ) else 0) = D
    at h2 ⊢
  generalize hP : (∑ f : AEdge n, if aSrc hn f = v then z f else 0) = P at h1 h3 ⊢
  generalize hQ : (∑ f : AEdge n, if aTgt hn f = v then z f else 0) = Q at h2 h3 ⊢
  linarith


/-- A non-zero chain has a non-zero derived-flow weight. -/
lemma exists_zFlow_ne_zero (hn : 0 < n) {z : AEdge n → ℤ} (hz : z ≠ 0) :
    ∃ e : AOEdge n, zFlow hn z e ≠ 0 := by
  by_contra h
  apply hz
  ext f
  have h1 : zFlow hn z (f, false) = 0 := by
    by_contra hc; exact h ⟨(f, false), hc⟩
  have h2 : zFlow hn z (f, true) = 0 := by
    by_contra hc; exact h ⟨(f, true), hc⟩
  have hf : chainOfA hn (zFlow hn z) f = z f := by rw [chainOfA_zFlow]
  rw [chainOfA_apply, h1, h2] at hf
  simpa using hf.symm

/-- A chain of non-zero winding is a non-zero chain. -/
lemma ne_zero_of_awind_ne_zero (hn : 0 < n) {z : AEdge n → ℤ} (h : awind hn z ≠ 0) : z ≠ 0 := by
  intro hz
  rw [hz, awind_zero hn] at h
  exact h rfl

/-- **The induction's step case has something to peel**: a chain of non-zero winding has an oriented
edge of non-zero derived-flow weight. -/
lemma exists_zFlow_ne_zero_of_awind (hn : 0 < n) {z : AEdge n → ℤ} (h : awind hn z ≠ 0) :
    ∃ e : AOEdge n, zFlow hn z e ≠ 0 :=
  exists_zFlow_ne_zero hn (ne_zero_of_awind_ne_zero hn h)

end AnnulusZFlow


/-! ### Deriving `mv_obligation` from the shared commons

The crux is now proved in the *commons*, in the closed-strip (excisive-cover) form, by the two-set
Mayer–Vietoris decomposition: `Commons.Topology.Strip.crux_via_decomposition` in
`Submission/Commons/Topology/Strip/exists_translate_path_of_ess_of_cover.lean`.  The two lemmas below
transport it to the *open* strip of this file: a finite shrink `{a + ε ≤ y ≤ b - ε}` of the open
strip contains the two translate paths, and on that closed strip all the covering hypotheses of the
commons theorem hold, so the crux applies there and (by monotonicity of `JoinedIn`) in the open
strip as well. -/

/-- A continuous real function on the unit interval that lies strictly above `a` has a lower bound
strictly above `a`. -/
lemma exists_lt_le_bound_of_continuous {a : ℝ} {f : Set.Icc (0:ℝ) 1 → ℝ} (hf : Continuous f)
    (haf : ∀ t, a < f t) : ∃ a' : ℝ, a < a' ∧ ∀ t, a' ≤ f t := by
  obtain ⟨a', ha', hle⟩ := isCompact_univ.exists_forall_le' (f := f) hf.continuousOn
    (fun t _ => haf t)
  exact ⟨a', ha', fun t => hle t (Set.mem_univ t)⟩

/-- **Shrinking the strip.**  Two paths lying in the open strip `a < y < b` are contained in a
smaller closed strip `{a + ε ≤ y ≤ b - ε}` with `ε > 0` and `2ε < b - a`. -/
lemma exists_shrunk_strip {a b : ℝ} (hab : a < b) {F G : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hF : ∀ t, a < (F t).2 ∧ (F t).2 < b) (hG : ∀ t, a < (G t).2 ∧ (G t).2 < b) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε < b - a ∧ (∀ t, a + ε ≤ (F t).2 ∧ (F t).2 ≤ b - ε) ∧
      (∀ t, a + ε ≤ (G t).2 ∧ (G t).2 ≤ b - ε) := by
  have hFs : Continuous fun t : Set.Icc (0:ℝ) 1 => (F t).2 := continuous_snd.comp F.continuous
  have hGs : Continuous fun t : Set.Icc (0:ℝ) 1 => (G t).2 := continuous_snd.comp G.continuous
  have hFb : Continuous fun t : Set.Icc (0:ℝ) 1 => b - (F t).2 := continuous_const.sub hFs
  have hGb : Continuous fun t : Set.Icc (0:ℝ) 1 => b - (G t).2 := continuous_const.sub hGs
  obtain ⟨aF, haF, hleF⟩ := exists_lt_le_bound_of_continuous hFs (fun t => (hF t).1)
  obtain ⟨aG, haG, hleG⟩ := exists_lt_le_bound_of_continuous hGs (fun t => (hG t).1)
  obtain ⟨uF, huF, hleuF⟩ :=
    exists_lt_le_bound_of_continuous (a := 0) hFb (fun t => by have := (hF t).2; linarith)
  obtain ⟨uG, huG, hleuG⟩ :=
    exists_lt_le_bound_of_continuous (a := 0) hGb (fun t => by have := (hG t).2; linarith)
  have h1 : 0 < aF - a := by linarith
  have h2 : 0 < aG - a := by linarith
  have h3 : 0 < (b - a) / 2 := by linarith
  set m : ℝ := min (min (aF - a) (aG - a)) (min (min uF uG) ((b - a) / 2)) with hm
  have hmpos : 0 < m := by
    rw [hm]; exact lt_min (lt_min h1 h2) (lt_min (lt_min huF huG) h3)
  have hmF : m ≤ aF - a := by
    rw [hm]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hmG : m ≤ aG - a := by
    rw [hm]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hmuF : m ≤ uF := by
    rw [hm]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hmuG : m ≤ uG := by
    rw [hm]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hmba : m ≤ (b - a) / 2 := by
    rw [hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨m / 2, by linarith, by linarith, ?_, ?_⟩
  · intro t
    exact ⟨by have := hleF t; linarith, by have := hleuF t; linarith⟩
  · intro t
    exact ⟨by have := hleG t; linarith, by have := hleuG t; linarith⟩

/-- **The Mayer–Vietoris obligation.**

For `T`-invariant open `VA`, `VB` covering the open strip `Ω = stripS a b`, each containing a
`T`-crossing, some point of `VA ∩ VB` is joined *inside* `VA ∩ VB` to a positive translate of
itself: `∃ q ∈ VA ∩ VB, ∃ m : ℤ, 1 ≤ m ∧ JoinedIn (VA ∩ VB) q (Tz p m q)`.

Equivalently: some component of `VA ∩ VB` has non-zero winding in the annulus (finite `T`-orbit).
This is exactly what Mayer–Vietoris for the open cover `{VA, VB}` of `Ω` supplies — exactness of
`H₁(VA ∩ VB) → H₁(VA) ⊕ H₁(VB) → H₁(Ω) → …` applied to the two essential classes coming from
`hwindA`, `hwindB`.  The reduction of the crux to it is `crux_of_finite_orbit_component`, proved
above; the `m = 1` instance is *equivalent* to the crux, since Janiszewski in the simply connected
strip (`joinedIn_inter_of_joinedIn_strip`) turns a crossing in `VA` and one in `VB` into one in
`VA ∩ VB`.

**Proved (session 109) by importing the commons.**  The commons module
`Submission.Commons.Topology.Strip.exists_translate_path_of_ess_of_cover` proves the crux in the
*closed*-strip excisive-cover form (`crux_via_decomposition`, via the two-set decomposition of a
locally constant `ℤ`-valued sheet index on the complement of two disjoint closed sets — the
Mayer–Vietoris statement in the form the argument needs).  The open strip is handled by shrinking:
the two translate paths of `hwindA`, `hwindB` are compact in the open strip, so they are contained
in a closed strip `{a + ε ≤ y ≤ b - ε}` (`exists_shrunk_strip`), on which the cover restricts to a
cover and the commons theorem applies.  Its conclusion is joinedness inside `W₁ ∩ W₂ ⊆ VA ∩ VB`,
which strengthens by monotonicity of `JoinedIn` to joinedness inside `VA ∩ VB`. -/

theorem mv_obligation {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ stripS a b) (hsubB : VB ⊆ stripS a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z)) :
    ∃ q ∈ VA ∩ VB, ∃ m : ℤ, 1 ≤ m ∧ JoinedIn (VA ∩ VB) q (Tz p m q) := by
  classical
  obtain ⟨zA, hzA, hJA⟩ := hwindA
  obtain ⟨zB, hzB, hJB⟩ := hwindB
  obtain ⟨γA, hγA⟩ := hJA
  obtain ⟨γB, hγB⟩ := hJB
  have hFA : ∀ t, a < (γA t).2 ∧ (γA t).2 < b := fun t => hsubA (hγA t)
  have hGB : ∀ t, a < (γB t).2 ∧ (γB t).2 < b := fun t => hsubB (hγB t)
  obtain ⟨ε, hεpos, hεsmall, hFb, hGb⟩ :=
    exists_shrunk_strip hab (F := γA.toContinuousMap) (G := γB.toContinuousMap) hFA hGB
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | a + ε ≤ q.2 ∧ q.2 ≤ b - ε} with hS
  have hmemS : ∀ q : ℝ × ℝ, q ∈ S ↔ a + ε ≤ q.2 ∧ q.2 ≤ b - ε := fun q => Iff.rfl
  have hSopen : a + ε < b - ε := by linarith
  have hSsub : S ⊆ stripS a b := by
    intro q hq
    rw [stripS]
    exact ⟨by linarith [(hmemS q).mp hq |>.1], by linarith [(hmemS q).mp hq |>.2]⟩
  set W₁ : Set (ℝ × ℝ) := VA ∩ S with hW₁
  set W₂ : Set (ℝ × ℝ) := VB ∩ S with hW₂
  have hmemW₁ : ∀ q : ℝ × ℝ, q ∈ W₁ ↔ q ∈ VA ∧ q ∈ S := by
    intro q; rw [hW₁]; exact Set.mem_inter_iff q VA S
  have hmemW₂ : ∀ q : ℝ × ℝ, q ∈ W₂ ↔ q ∈ VB ∧ q ∈ S := by
    intro q; rw [hW₂]; exact Set.mem_inter_iff q VB S
  have hperW₁ : ∀ q : ℝ × ℝ, q ∈ W₁ ↔ (q.1 + p, q.2) ∈ W₁ := by
    intro q
    rw [hmemW₁ q, hmemW₁ (q.1 + p, q.2)]
    have hS' : a + ε ≤ (q.1 + p, q.2).2 ∧ (q.1 + p, q.2).2 ≤ b - ε
        ↔ a + ε ≤ q.2 ∧ q.2 ≤ b - ε := Iff.rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hperA q).mp h1, hS'.mp h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hperA q).mpr h1, hS'.mpr h2⟩
  have hperW₂ : ∀ q : ℝ × ℝ, q ∈ W₂ ↔ (q.1 + p, q.2) ∈ W₂ := by
    intro q
    rw [hmemW₂ q, hmemW₂ (q.1 + p, q.2)]
    have hS' : a + ε ≤ (q.1 + p, q.2).2 ∧ (q.1 + p, q.2).2 ≤ b - ε
        ↔ a + ε ≤ q.2 ∧ q.2 ≤ b - ε := Iff.rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hperB q).mp h1, hS'.mp h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hperB q).mpr h1, hS'.mpr h2⟩
  have hcovW : W₁ ∪ W₂ = S := by
    rw [hW₁, hW₂, ← Set.union_inter_distrib_right, hcover]
    exact (Set.inter_eq_right).mpr hSsub
  have hsrc : (γA.toContinuousMap (0 : Set.Icc (0:ℝ) 1)).2 = zA.2 := by
    rw [show γA.toContinuousMap (0 : Set.Icc (0:ℝ) 1) = γA 0 from rfl, Path.source]
  have hsrcB : (γB.toContinuousMap (0 : Set.Icc (0:ℝ) 1)).2 = zB.2 := by
    rw [show γB.toContinuousMap (0 : Set.Icc (0:ℝ) 1) = γB 0 from rfl, Path.source]
  have hne₁ : ∃ z : ℝ × ℝ, z ∈ W₁ ∧ JoinedIn W₁ z (z.1 + p, z.2) := by
    have h0 : a + ε ≤ zA.2 ∧ zA.2 ≤ b - ε := by
      have h := hFb 0
      rwa [hsrc] at h
    refine ⟨zA, ?_, ?_⟩
    · rw [hmemW₁]; exact ⟨hzA, (hmemS zA).mpr h0⟩
    · refine ⟨γA, fun t => ?_⟩
      rw [hmemW₁]
      exact ⟨hγA t, (hmemS (γA t)).mpr (hFb t)⟩
  have hne₂ : ∃ z : ℝ × ℝ, z ∈ W₂ ∧ JoinedIn W₂ z (z.1 + p, z.2) := by
    have h0 : a + ε ≤ zB.2 ∧ zB.2 ≤ b - ε := by
      have h := hGb 0
      rwa [hsrcB] at h
    refine ⟨zB, ?_, ?_⟩
    · rw [hmemW₂]; exact ⟨hzB, (hmemS zB).mpr h0⟩
    · refine ⟨γB, fun t => ?_⟩
      rw [hmemW₂]
      exact ⟨hγB t, (hmemS (γB t)).mpr (hGb t)⟩
  have hsub₁ : W₁ ⊆ S := fun q hq => (hmemW₁ q).mp hq |>.2
  have hsub₂ : W₂ ⊆ S := fun q hq => (hmemW₂ q).mp hq |>.2
  have hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ S := ⟨VA, hVA, hW₁⟩
  have hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ S := ⟨VB, hVB, hW₂⟩
  obtain ⟨z, hz₁, hz₂, hJ⟩ := Commons.Topology.Strip.crux_via_decomposition hp hSopen
    hsub₁ hsub₂ hopen₁ hopen₂ hperW₁ hperW₂ hcovW hne₁ hne₂
  have hzVA : z ∈ VA := (hmemW₁ z).mp hz₁ |>.1
  have hzVB : z ∈ VB := (hmemW₂ z).mp hz₂ |>.1
  refine ⟨z, ⟨hzVA, hzVB⟩, 1, le_refl 1, ?_⟩
  have hTz : Tz p (1 : ℤ) z = (z.1 + p, z.2) := by simp [Tz]
  rw [hTz]
  refine hJ.mono ?_
  intro q hq
  rw [Set.mem_inter_iff] at hq ⊢
  exact ⟨(hmemW₁ q).mp hq.1 |>.1, (hmemW₂ q).mp hq.2 |>.1⟩

/-- **The crux (Denne's cancellation).**

Let `VA`, `VB` be open `T`-invariant subsets of the open strip `a < q.2 < b` with
`VA ∪ VB = stripS a b`.  If each of `VA`, `VB` contains a path from a point to its `T`-translate
(an *essential* path), then `Ess p VA ∩ Ess p VB` is nonempty.

Equivalently: `VA ∩ VB` contains a point joined to its `T`-translate inside `VA ∩ VB`;
equivalently, in the annulus `(ℝ/pℤ) × (a,b)`, the intersection of the two open sets contains an
essential loop.  This is Denne's `prop:homology` (Mayer–Vietoris cancellation) in covering-space
form; see the summary above and the sessions recorded in this file for the reduction, the crossing
dichotomy, the proved `τ > σ` regime, and the remaining (Obligation O) in the `τ < σ` regime. -/
theorem crux_Z_meet {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z)) :
    ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB := by
  have hsubA : VA ⊆ stripS a b := by rw [← hcover]; exact subset_union_left
  have hsubB : VB ⊆ stripS a b := by rw [← hcover]; exact subset_union_right
  exact crux_of_finite_orbit_component hp hVA hVB hperA hperB
    (mv_obligation hp hab hVA hVB hsubA hsubB hperA hperB hcover hwindA hwindB)

/-- **A first proved case of `dennes_prop_homology`.**  If the closed sets `A, B` together miss one
horizontal level `{q.2 = c}` of the strip, then that level is itself a `T`-crossing inside the
complement of `A ∪ B`, and the conclusion of `dennes_prop_homology` follows without any homological
input.  (This is the "the picture does not reach across the strip" case; the interesting cases are
those where `A ∪ B` meets every level.) -/
theorem dennes_prop_homology_of_misses_level {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {A B : Set (ℝ × ℝ)} {c : ℝ} (hc : c ∈ Set.Ioo a b)
    (hlev : ∀ s : ℝ, (s, c) ∈ (A ∪ B)ᶜ) :
    ∃ z : ℝ × ℝ, z ∈ stripS a b ∧ z ∈ (A ∪ B)ᶜ ∧
      JoinedIn (stripS a b ∩ (A ∪ B)ᶜ) z (Tmap p z) := by
  have hstrip : ∀ u : Set.Icc (0:ℝ) 1, ((u : ℝ) * p, c) ∈ stripS a b := by
    intro u
    exact ⟨hc.1, hc.2⟩
  refine ⟨(0, c), ⟨hc.1, hc.2⟩, hlev 0, ?_⟩
  refine ⟨{ toFun := fun u : Set.Icc (0:ℝ) 1 => ((u : ℝ) * p, c),
             continuous_toFun := by fun_prop, source' := by simp,
             target' := by simp [Tmap] },
      fun u => ⟨hstrip u, hlev _⟩⟩

/-- **The Mayer–Vietoris input, named as its own target: two essential components must meet.**

Let `VA, VB` be open, `T`-invariant and cover the strip, and suppose each is *essential* (contains a
`T`-crossing, i.e. an essential loop in the quotient annulus).  Then there are essential points
`z_A ∈ Ess p VA`, `z_B ∈ Ess p VB` whose `T`-invariant components meet.

This is *equivalent* to the crux: `⟸` is `ess_meets_of_components_meet` (basepoint pushing), and
`⟹` is immediate from `crux_Z_meet` with `z_A = z_B` (proof below).  So the statement below is
derived, and the *remaining gap* of the file is its proof by the homological input, which splits in
two halves to be attacked separately:

* **(H1 / Mayer–Vietoris half)** *degree bookkeeping on the strip.*  In the quotient annulus the two
  essential loops `α ⊆ VA/T` and `β ⊆ VB/T` represent the same class in `H₁ ≅ ℤ`, so `α - β` is
  null-homologous, and the Mayer–Vietoris exactness
  `H₁(S∖(A∪B)) → H₁(S∖A) ⊕ H₁(S∖B) → H₁(S)` pulls a degree-one cycle back to `VA ∩ VB`;
  in the monodromy language of `retDeg` this is the statement that degrees `1` in
  `retDeg p VA ·` and `retDeg p VB ·` at a *common* point force `1 ∈ retDeg p (VA ∩ VB) ·`.
* **(topological half)** *why non-meeting components force a degree contradiction.*  A `T`-crossing
  in `VA` stays inside the `T`-invariant component `C_A`; if `C_A ∩ C_B = ∅` then that curve keeps
  degree `1` while leaving `VA ∩ VB`, contradicting the bookkeeping above.  This half is pure point
  set and should be provable from `connectedComponentIn_eq_of_mem_Ess` and `retDeg_mono`.

Nothing else in the file depends on either half; both are independent of each other. -/
theorem exists_meeting_components {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hwindA : ∃ z : ℝ × ℝ, z ∈ Ess p VA) (hwindB : ∃ z : ℝ × ℝ, z ∈ Ess p VB) :
    ∃ zA zB : ℝ × ℝ, zA ∈ Ess p VA ∧ zB ∈ Ess p VB ∧
      (connectedComponentIn VA zA ∩ connectedComponentIn VB zB).Nonempty := by
  have hA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z) := by
    obtain ⟨z, hz⟩ := hwindA
    exact ⟨z, mem_Ess.mp hz⟩
  have hB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z) := by
    obtain ⟨z, hz⟩ := hwindB
    exact ⟨z, mem_Ess.mp hz⟩
  obtain ⟨z, hzA, hzB⟩ := crux_Z_meet hp hab hVA hVB hperA hperB hcover hA hB
  refine ⟨z, z, hzA, hzB, z, ?_, ?_⟩
  · exact mem_connectedComponentIn (ess_subset p VA hzA)
  · exact mem_connectedComponentIn (ess_subset p VB hzB)

/-- **Denne's `prop:homology` — the interface lemma of the crux, in complementary form.**

Let `A, B ⊆ stripS a b` be closed, `T`-invariant and disjoint.  If the complements of `A` and of `B`
within the strip each carry a `T`-crossing (equivalently: each complement contains an essential loop
in the quotient annulus), then the complement of `A ∪ B` carries one too.

This isolates the homological input of the whole development as a single interface.  It is the
closed-sets form of `crux_Z_meet` (put `VA = strip ∩ Aᶜ`, `VB = strip ∩ Bᶜ`), and it is the statement
Denne proves by Mayer–Vietoris surjectivity
`H₁(S∖(A∪B)) → H₁(S∖A) ⊕ H₁(S∖B) → H₁(S)`; its proof is the remaining gap of this file. -/
theorem dennes_prop_homology {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {A B : Set (ℝ × ℝ)} (hA : IsClosed A) (hB : IsClosed B)
    (hAper : ∀ q : ℝ × ℝ, q ∈ A ↔ Tmap p q ∈ A)
    (hBper : ∀ q : ℝ × ℝ, q ∈ B ↔ Tmap p q ∈ B)
    (hdisj : Disjoint A B)
    (hwindA : ∃ z : ℝ × ℝ, z ∈ stripS a b ∧ z ∈ Aᶜ ∧
      JoinedIn (stripS a b ∩ Aᶜ) z (Tmap p z))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ stripS a b ∧ z ∈ Bᶜ ∧
      JoinedIn (stripS a b ∩ Bᶜ) z (Tmap p z)) :
    ∃ z : ℝ × ℝ, z ∈ stripS a b ∧ z ∈ (A ∪ B)ᶜ ∧
      JoinedIn (stripS a b ∩ (A ∪ B)ᶜ) z (Tmap p z) := by
  set VA : Set (ℝ × ℝ) := stripS a b ∩ Aᶜ with hVAdef
  set VB : Set (ℝ × ℝ) := stripS a b ∩ Bᶜ with hVBdef
  have hVA : IsOpen VA := (isOpen_stripS a b).inter hA.isOpen_compl
  have hVB : IsOpen VB := (isOpen_stripS a b).inter hB.isOpen_compl
  have hstrip_iff : ∀ q : ℝ × ℝ, q ∈ stripS a b ↔ Tmap p q ∈ stripS a b := by
    intro q
    simp only [stripS_iff, Tmap]
  have hperA' : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA := by
    intro q
    rw [hVAdef]
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    rw [hstrip_iff q, (hAper q).not]
  have hperB' : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB := by
    intro q
    rw [hVBdef]
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    rw [hstrip_iff q, (hBper q).not]
  have hcover' : VA ∪ VB = stripS a b := by
    rw [hVAdef, hVBdef]
    ext q
    constructor
    · rintro (⟨hs, -⟩ | ⟨hs, -⟩) <;> exact hs
    · intro hs
      by_cases hqA : q ∈ A
      · exact Or.inr ⟨hs, fun hqB => Set.disjoint_left.mp hdisj hqA hqB⟩
      · exact Or.inl ⟨hs, hqA⟩
  obtain ⟨zA, hzAstrip, hzA, hjoinA⟩ := hwindA
  obtain ⟨zB, hzBstrip, hzB, hjoinB⟩ := hwindB
  have hwindA' : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z) :=
    ⟨zA, ⟨hzAstrip, hzA⟩, hjoinA⟩
  have hwindB' : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z) :=
    ⟨zB, ⟨hzBstrip, hzB⟩, hjoinB⟩
  obtain ⟨z, hzA', hzB'⟩ := crux_Z_meet hp hab hVA hVB hperA' hperB' hcover' hwindA' hwindB'
  have hzVA : z ∈ VA := ess_subset p VA hzA'
  have hzVB : z ∈ VB := ess_subset p VB hzB'
  have hjoin : JoinedIn (VA ∩ VB) z (Tmap p z) :=
    joinedIn_inter_of_joinedIn_strip hab hVA hVB hcover' ⟨hzVA, hzVB⟩
      ⟨(hperA' z).mp hzVA, (hperB' z).mp hzVB⟩ hzA'.2 hzB'.2
  have hinter : VA ∩ VB = stripS a b ∩ (A ∪ B)ᶜ := by
    rw [hVAdef, hVBdef]
    ext q
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union]
    tauto
  have hz : z ∈ stripS a b ∩ (A ∪ B)ᶜ := by
    rw [← hinter]
    exact ⟨hzVA, hzVB⟩
  have hjoin' : JoinedIn (stripS a b ∩ (A ∪ B)ᶜ) z (Tmap p z) := by
    rw [← hinter]
    exact hjoin
  exact ⟨z, hz.1, hz.2, hjoin'⟩

/-! ### Session 63: sliding, and the rigidity of the no-crux case revisited

This session isolated two new *proved* structural facts about the failure case of the crux.  They
sharpen the frontier as follows.

* **(Sliding.)**  A translate crossing can be **re-based along any path of `W = VA ∩ VB`**: if `W`
  is `T`-invariant, `x ~ y` inside `W`, and `y ~ T y` inside a `T`-invariant `U`, then
  `x ~ T x` inside `W ∪ U`.  (`joinedIn_slide`.)  Consequence (`crux_of_ess_W_path`): if a point of
  `Ess p VA` is joined **inside `W`** to a point of `Ess p VB` — more generally if a point `x` of
  `Ess p VA` is joined inside `W` to any point `y` with `y ~ T y` in `VB` — then the crux holds.

* **(Rigidity, sharp form.)**  Under the failure of the crux, no point of `Ess p VA` is joined to a
  point of `Ess p VB` inside `W` (`no_crux_no_joinedIn_W_of_ess`); in particular the *essential* part
  of `VA ∩ VB` is split between `Ess p VA` and `Ess p VB` (`no_crux_ess_inter_other` shows both
  `Ess p VA ∩ VB` and `Ess p VB ∩ VA` are nonempty).  So the negation of the crux has the
  following exact shape:

    `Ess p VA ∩ W` and `Ess p VB ∩ W` are disjoint, nonempty, `T`-invariant unions of components of
    `W`, no two of which are joined inside `W`.

  The remaining content of the crux is therefore *purely about the two unions of components of `W`
  and the sets `K_A`, `K_B`*: the cover `VA ∪ VB = stripS a b` has not been used yet beyond
  `component_meets_of_no_crux`.

* **(Two-phase caution.)**  The example `W = ⋃_k ((k-0.2, k+0.8) × (0,½)) ∪ ⋃_k ((k+0.3, k+1.3) ×
  (½,1))` (`p = 1`) is `T`-invariant, open in the strip and satisfies the no-crossing hypothesis,
  but `K = stripS ∖ W` is **connected** there, so it admits *no* decomposition
  `K = K_A ⊔ K_B` into two disjoint closed `T`-invariant parts: the no-crux configuration forces
  `K` to be disconnected, and that is an extra restriction a counterexample must respect. -/

/-- **Sliding a translate crossing along a path of `W`.**

Let `W` be `T`-invariant.  If `x` is joined to `y` inside `W` and `y` is joined to `T y` inside a set
`U`, then `x` is joined to `T x` inside `W ∪ U`: concatenate a path `δ : x ⇝ y` in `W`, a path
`γ : y ⇝ T y` in `U`, and the reversed translate `T δ : T x ⇝ T y` of `δ`, which lies in `W` by
`T`-invariance. -/
theorem joinedIn_slide {p : ℝ} {W U : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tmap p q ∈ W)
    {x y : ℝ × ℝ} (hxy : JoinedIn W x y) (hy : JoinedIn U y (Tmap p y)) :
    JoinedIn (W ∪ U) x (Tmap p x) := by
  have h1 : JoinedIn (W ∪ U) x y := hxy.mono Set.subset_union_left
  have h2 : JoinedIn (W ∪ U) y (Tmap p y) := hy.mono Set.subset_union_right
  have h3 : JoinedIn W (Tmap p x) (Tmap p y) := joinedIn_translate hW hxy
  have h4 : JoinedIn (W ∪ U) (Tmap p x) (Tmap p y) := h3.mono Set.subset_union_left
  exact (h1.trans h2).trans h4.symm

/-- **A `W`-path between essential points gives the crux.**

If `W = VA ∩ VB` is `T`-invariant and a point `x ∈ Ess p VA` is joined **inside `W`** to a point `y`
with `y ∈ VB` and `y ~ T y` inside `VB`, then the crux holds: by `joinedIn_slide` (`U := VB`), `x` is
joined to `T x` inside `W ∪ VB = VB`, so `x ∈ Ess p VB`, and `x ∈ Ess p VA` by hypothesis. -/
theorem crux_of_ess_W_path {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ VA ∩ VB ↔ Tmap p q ∈ VA ∩ VB)
    {x y : ℝ × ℝ} (hx : x ∈ Ess p VA) (hy : JoinedIn VB y (Tmap p y))
    (hxy : JoinedIn (VA ∩ VB) x y) :
    ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB := by
  have hsub : (VA ∩ VB : Set (ℝ × ℝ)) ∪ VB = VB := Set.union_eq_right.mpr Set.inter_subset_right
  have hjoinVB : JoinedIn VB x (Tmap p x) := by
    have h := joinedIn_slide (p := p) (W := VA ∩ VB) (U := VB) hW hxy hy
    rwa [hsub] at h
  exact ⟨x, hx, ⟨hxy.source_mem.2, hjoinVB⟩⟩

/-- **Under the failure of the crux, no `W`-path joins `Ess p VA` to `Ess p VB`.**

This is the contrapositive of `crux_of_ess_W_path`: a `W`-path from an essential point of `VA` to an
essential point of `VB` would produce the crux (using the `VB`-crossing through the latter point). -/
theorem no_crux_no_joinedIn_W_of_ess {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hW : ∀ q : ℝ × ℝ, q ∈ VA ∩ VB ↔ Tmap p q ∈ VA ∩ VB)
    (hnocrux : ¬ ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB)
    {x y : ℝ × ℝ} (hx : x ∈ Ess p VA) (hy : y ∈ Ess p VB)
    (hxy : JoinedIn (VA ∩ VB) x y) : False :=
  hnocrux (crux_of_ess_W_path hW hx (mem_Ess.mp hy).2 hxy)

/-- **Under the failure of the crux, the essential part of `VA` meets `VB` (and vice versa).**

The component of an essential point of `VA` is contained in `Ess p VA` and (by
`component_meets_of_no_crux`) meets `VB`; hence `Ess p VA ∩ VB` is nonempty.  Symmetrically
`Ess p VB ∩ VA` is nonempty.  So under the failure of the crux the two essential parts are
*separated inside `W`* (`no_crux_no_joinedIn_W_of_ess`) while both meeting the other set. -/
theorem no_crux_ess_inter_other {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z))
    (hnocrux : ¬ ∃ z : ℝ × ℝ, z ∈ Ess p VA ∧ z ∈ Ess p VB) :
    (Ess p VA ∩ VB).Nonempty ∧ (Ess p VB ∩ VA).Nonempty := by
  constructor
  · obtain ⟨z, hzVA, hzjoin⟩ := hwindA
    have hzEss : z ∈ Ess p VA := ⟨hzVA, hzjoin⟩
    have hmeet := component_meets_of_no_crux hp hab hVA hVB hperA hperB hcover hwindB hnocrux hzVA
    obtain ⟨w, hwC, hwB⟩ := hmeet
    exact ⟨w, connectedComponentIn_subset_Ess hperA hVA hzEss hwC, hwB⟩
  · obtain ⟨z, hzVB, hzjoin⟩ := hwindB
    have hzEss : z ∈ Ess p VB := ⟨hzVB, hzjoin⟩
    have hnocrux' : ¬ ∃ z : ℝ × ℝ, z ∈ Ess p VB ∧ z ∈ Ess p VA :=
      fun h => hnocrux (h.imp fun z hz => ⟨hz.2, hz.1⟩)
    have hmeet := component_meets_of_no_crux hp hab hVB hVA hperB hperA
      (by rw [Set.union_comm]; exact hcover) hwindA hnocrux' hzVB
    obtain ⟨w, hwC, hwA⟩ := hmeet
    exact ⟨w, connectedComponentIn_subset_Ess hperB hVB hzEss hwC, hwA⟩

/-- **A *connected level slice* of the intersection gives the crux.**

Let `W = VA ∩ VB`.  Every horizontal level `{q.2 = y}` is `T`-invariant, and so is `W`, so the slice
`W ∩ {q.2 = y}` is `T`-invariant.  If that slice is *connected* (and nonempty) then any of its
points is joined to its `T`-translate by a path *inside the slice* — the horizontal segment works,
because the first-coordinate projection of a connected subset of the line is an interval — hence
inside `W`.  Monotonicity (`W ⊆ VA`, `W ⊆ VB`) then gives the conclusion.

So **a crux failure forces every nonempty slice `W ∩ {q.2 = y}` to be disconnected**, i.e. the wall
`K = (VA∖VB) ∪ (VB∖VA)` must separate every level it meets.  (This is the sharp form of the
"columns" picture of the failure: the slice is a `p`-periodic union of open intervals, and each of
those intervals has length `< p`, since a slice-piece of length `≥ p` would itself contain a
translate crossing.) -/
theorem crux_of_level_preconnected {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    {y : ℝ} (hne : ((VA ∩ VB) ∩ {q : ℝ × ℝ | q.2 = y}).Nonempty)
    (hconn : IsPreconnected ((VA ∩ VB) ∩ {q : ℝ × ℝ | q.2 = y})) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (Tmap p z) ∧ JoinedIn VB z (Tmap p z) := by
  set S : Set (ℝ × ℝ) := (VA ∩ VB) ∩ {q : ℝ × ℝ | q.2 = y} with hS
  obtain ⟨z, hzS⟩ := hne
  have hzW : z ∈ VA ∩ VB := hzS.1
  have hTzW : Tmap p z ∈ VA ∩ VB :=
    ⟨(hperA z).mp hzW.1, (hperB z).mp hzW.2⟩
  have hTz2 : (Tmap p z).2 = y := by rw [Tmap_apply]; exact hzS.2
  have hTzS : Tmap p z ∈ S := ⟨hTzW, hTz2⟩
  -- the first-coordinate projection of the slice is a connected subset of `ℝ`, hence an interval
  have hproj : IsPreconnected (Prod.fst '' S) := hconn.image _ continuous_fst.continuousOn
  have hord : (Prod.fst '' S).OrdConnected := hproj.ordConnected
  have hz1 : z.1 ∈ Prod.fst '' S := ⟨z, hzS, rfl⟩
  have hTz1 : (Tmap p z).1 ∈ Prod.fst '' S := ⟨Tmap p z, hTzS, rfl⟩
  have hzp : z.1 ≤ (Tmap p z).1 := by rw [Tmap_apply]; linarith [hp]
  -- every first coordinate between those of `z` and `T z` occurs, so the horizontal segment lies in `W`
  have hseg : ∀ u ∈ Set.Icc z.1 (Tmap p z).1, ((u, y) : ℝ × ℝ) ∈ VA ∩ VB := by
    intro u hu
    obtain ⟨q, hqS, hq⟩ := hord.out hz1 hTz1 hu
    have h1 : q = (u, y) := Prod.ext hq hqS.2
    have h2 : (u, y) ∈ S := h1 ▸ hqS
    exact h2.1
  -- the horizontal segment from `z` to `T z` lies in `W`
  have hpath : JoinedIn (VA ∩ VB) z (Tmap p z) := by
    refine ⟨{ toContinuousMap :=
        { toFun := fun t : Set.Icc (0 : ℝ) 1 => (z.1 + (t : ℝ) * p, y)
          continuous_toFun := by fun_prop }, source' := ?_, target' := ?_ }, ?_⟩
    · refine Prod.ext ?_ ?_
      · simp
      · simpa using hzS.2.symm
    · refine Prod.ext ?_ ?_
      · simp [Tmap_apply]
      · simp only [Tmap_apply]
        exact hzS.2.symm
    · intro t
      have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := t.2
      have hmem : z.1 + (t : ℝ) * p ∈ Set.Icc z.1 (Tmap p z).1 := by
        refine ⟨by nlinarith [ht.1, hp], ?_⟩
        rw [Tmap_apply]
        nlinarith [ht.1, ht.2, hp]
      exact hseg _ hmem
  exact ⟨z, hzW, hpath.mono Set.inter_subset_left, hpath.mono Set.inter_subset_right⟩

/-- **A full horizontal band inside the intersection gives the crux.**

If the whole open band `{q | c < q.2 ∧ q.2 < d}` lies in `W = VA ∩ VB`, then the crux holds: the
band is `T`-invariant and connected, hence path connected (it is open in `ℝ²`), so any of its points
is joined to its translate inside the band, i.e. inside `W`; monotonicity finishes.  This is the
second half of the "the wall must meet every level" analysis (session 69): in the collared setting
`VA ⊇ {q.2 < a+δ}` (from `VB∖VA ⊆ {q.2 ≥ a+δ}`) and `VB = Ω∖(VA∖VB)`, so a `VA∖VB` that misses the
open bottom band puts the whole bottom band inside `VA ∩ VB`. -/
theorem crux_of_band_subset {p a b c d : ℝ} (hp : 0 < p) (hab : a < b) (hcd : c < d)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hband : ∀ q : ℝ × ℝ, c < q.2 → q.2 < d → q ∈ VA ∩ VB) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (Tmap p z) ∧ JoinedIn VB z (Tmap p z) := by
  have hcm : c < (c + d) / 2 := by linarith
  have hmd : (c + d) / 2 < d := by linarith
  set z : ℝ × ℝ := (0, (c + d) / 2) with hz
  have hzW : z ∈ VA ∩ VB := hband z hcm hmd
  have hTzW : Tmap p z ∈ VA ∩ VB := by
    refine hband _ ?_ ?_ <;> rw [Tmap_apply] <;> [exact hcm; exact hmd]
  have hpath : JoinedIn (VA ∩ VB) z (Tmap p z) := by
    refine ⟨{ toContinuousMap :=
        { toFun := fun t : Set.Icc (0 : ℝ) 1 => ((t : ℝ) * p, (c + d) / 2)
          continuous_toFun := by fun_prop }, source' := ?_, target' := ?_ }, ?_⟩
    · refine Prod.ext ?_ ?_ <;> simp [hz]
    · refine Prod.ext ?_ ?_ <;> simp [Tmap_apply, hz]
    · intro t
      exact hband _ hcm hmd
  exact ⟨z, hzW, hpath.mono Set.inter_subset_left, hpath.mono Set.inter_subset_right⟩

/-! ### The interface, and what is proved of it so far (session 24)

* `dennes_prop_homology` — **the interface**: the closed-sets form of the crux (derived above from
  `crux_Z_meet`, so it has the crux's exact strength).  Its proof is the remaining gap; it is what
  Denne obtains from the Mayer–Vietoris surjectivity
  `H₁(S∖(A∪B)) → H₁(S∖A) ⊕ H₁(S∖B) → H₁(S)`.
* `dennes_prop_homology_of_misses_level` — **a first proved case**: if `A ∪ B` misses one horizontal
  level of the strip, that level is a `T`-crossing in the complement and the conclusion is
  immediate.  So the interface is non-vacuous and correctly stated.
* `joinedIn_Tz`, `joinedIn_Tz_add`, `joinedIn_Tz_neg` — **the monodromy layer**, the first genuinely
  homological piece: for a `T`-invariant `W` and `z ∈ W`, translating a joinable path gives
  `Tz p k z ~ Tz p k w` (`joinedIn_Tz`), and the *degrees* `{k : z ~ Tz p k z in W}` are closed
  under addition and negation, hence form an additive subgroup of `ℤ`.  Equivalently: the fibre of
  the covering `W → W/T` over `z` is a coset of the subgroup of returning degrees.  Any treatment of
  the crux by covering-space/monodromy methods consumes exactly this.

The next pieces to add at this seam: (i) the same monodromy structure for `W = VA ∩ VB` with the
two `T`-crossings supplying two cosets, and (ii) the actual Mayer–Vietoris input — or an elementary
substitute — producing a *non-returning* loop, i.e. an element of the subgroup different from `0`. -/

/-- **Cancellation for a two-set open cover of a periodic strip (Denne).**

Let `VA, VB` be open subsets of the open horizontal strip `a < y < b`, each invariant under the
translation `T(x,y) = (x+p,y)` (`p > 0`), with `VA ∪ VB = strip`.  If each of `VA` and `VB`
contains a path joining a point to its translate, then `VA ∩ VB` contains such a path.

Equivalently, in the annulus `(ℝ/pℤ) × (a,b)`: two open sets covering it, each containing an
essential loop, have an intersection containing an essential loop. -/
theorem annulus_essential_intersection {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hsubB : VB ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hcover : VA ∪ VB = {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (z.1 + p, z.2))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (z.1 + p, z.2)) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (z.1 + p, z.2) ∧
      JoinedIn VB z (z.1 + p, z.2) := by
  have hcover' : VA ∪ VB = stripS a b := hcover
  obtain ⟨z, hzA, hzB⟩ := crux_Z_meet hp hab hVA hVB hperA hperB hcover' hwindA hwindB
  exact ⟨z, ⟨(ess_subset p VA hzA), (ess_subset p VB hzB)⟩, hzA.2, hzB.2⟩

/-! ### Session 64: the component engine, and the *unconditional* meeting of `Ess p VA` with `VB`

Every "no interlocking" argument in this file (and the commons'
`Commons.Topology.Strip.essT_not_subset_obstacles_of_interlocking`, where the engine is a `private`
lemma) rests on one point-set fact: *two open sets covering a preconnected set cannot have a component
of one of them disjoint from the other*.  It is recorded here in general form, together with its
consequence for the crux: `Ess p VA` meets `VB` **without** any hypothesis on the crux (earlier
sessions only had this under the failure hypothesis, as `no_crux_ess_inter_other`).

The residual after this lemma is precisely the *meeting of the two essential parts*: the engine gives
`Ess p VA ∩ VB ≠ ∅` and `Ess p VB ∩ VA ≠ ∅`, while the crux asks for `Ess p VA ∩ Ess p VB ≠ ∅`; by
`crux_of_ess_W_path` the latter is *equivalent* to the crux.  So the gap is exactly "the two
`T`-invariant components, each of which is known to meet the other set, meet each other". -/

/-- **The component engine.**  If `A`, `B` are open sets covering a preconnected set `E` in a
topological space, `B` is nonempty and `z ∈ A`, then the connected component of `z` in `A` meets
`B`.

(Proof: if `C := connectedComponentIn A z` missed `B`, then `E ∩ closure C = C`, so the preconnected
`E` is covered by the two disjoint open sets `C` and `(closure C)ᶜ`, whence `E ⊆ C`; but `B ≠ ∅`
and `B ⊆ E`, contradiction.) -/
theorem component_meets_of_isOpen_cover {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {E A B : Set X}
    (hEpre : IsPreconnected E) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = E) (hBne : B.Nonempty) {z : X} (hz : z ∈ A) :
    ((connectedComponentIn A z) ∩ B).Nonempty := by
  classical
  set C : Set X := connectedComponentIn A z with hCdef
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hCA : C ⊆ A := connectedComponentIn_subset A z
  have hCE : C ⊆ E := fun w hw => by rw [← hcover]; exact Or.inl (hCA hw)
  have hCpc : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCopen : IsOpen C := hA.connectedComponentIn
  have hclosedA : A ∩ closure C ⊆ C := by
    rintro w ⟨hwA, hwcl⟩
    have hpre : IsPreconnected (insert w C) :=
      hCpc.subset_closure (subset_insert w C) (fun x hx => by
        rcases hx with rfl | hxC
        · exact hwcl
        · exact subset_closure hxC)
    have hsub : insert w C ⊆ A := by
      intro x hx; rcases hx with rfl | hxC
      · exact hwA
      · exact hCA hxC
    have hzin : z ∈ insert w C := Or.inr hzC
    have hkey := IsPreconnected.subset_connectedComponentIn hpre hzin hsub
    rw [← hCdef] at hkey
    exact hkey (Or.inl rfl)
  by_contra hcon
  have hCB : C ∩ B = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
  have hEcl : E ∩ closure C = C := by
    refine Set.Subset.antisymm ?_ (fun w hw => ⟨hCE hw, subset_closure hw⟩)
    rintro w ⟨hwE, hwcl⟩
    have hwAB : w ∈ A ∪ B := by rw [hcover]; exact hwE
    rcases hwAB with hwA | hwB
    · exact hclosedA ⟨hwA, hwcl⟩
    · exfalso
      obtain ⟨c, hcB, hcC⟩ := mem_closure_iff.mp hwcl B hB hwB
      exact (Set.eq_empty_iff_forall_notMem.mp hCB) c ⟨hcC, hcB⟩
  have hEsubC : E ⊆ C := by
    have huv : Disjoint C (((closure C))ᶜ : Set X) :=
      Set.disjoint_left.mpr (fun x hxC hxcl => hxcl (subset_closure hxC))
    have hsuv : E ⊆ C ∪ ((closure C))ᶜ := by
      intro x hx
      by_cases hxC : x ∈ C
      · exact Or.inl hxC
      · exact Or.inr (by
          rw [Set.mem_compl_iff]
          intro hxcl
          exact hxC (by rw [← hEcl]; exact ⟨hx, hxcl⟩))
    rcases IsPreconnected.subset_or_subset hCopen isClosed_closure.isOpen_compl huv hsuv hEpre
      with h | h
    · exact h
    · exfalso; exact (h (hCE hzC)) (subset_closure hzC)
  obtain ⟨bb, hbB⟩ := hBne
  have hbE : bb ∈ E := by rw [← hcover]; exact Or.inr hbB
  exact hcon ⟨bb, hEsubC hbE, hbB⟩

/-- **Every component of one part of an open cover of the strip meets the other part.** -/
theorem component_meets_of_cover {a b : ℝ} {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA)
    (hVB : IsOpen VB) (hcover : VA ∪ VB = stripS a b) (hVBne : VB.Nonempty)
    {z : ℝ × ℝ} (hz : z ∈ VA) : ((connectedComponentIn VA z) ∩ VB).Nonempty :=
  component_meets_of_isOpen_cover (convex_stripS a b).isPreconnected hVA hVB hcover hVBne hz

/-- **The essential part of `VA` meets `VB` (no hypothesis on the crux).**

The component of an essential point of `VA` is contained in `Ess p VA` and, by the component engine,
meets `VB`.  Symmetrically `Ess p VB ∩ VA ≠ ∅`.  This is the unconditional form of
`no_crux_ess_inter_other`; the crux is precisely the passage from "each essential part meets the
*other* set" to "the two essential parts meet each other". -/
theorem ess_inter_VB_of_cover {p a b : ℝ} (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hcover : VA ∪ VB = stripS a b) (hVBne : VB.Nonempty)
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z)) :
    (Ess p VA ∩ VB).Nonempty := by
  obtain ⟨z, hzVA, hzjoin⟩ := hwindA
  have hzEss : z ∈ Ess p VA := ⟨hzVA, hzjoin⟩
  obtain ⟨w, hwC, hwB⟩ := component_meets_of_cover hVA hVB hcover hVBne hzVA
  exact ⟨w, connectedComponentIn_subset_Ess hperA hVA hzEss hwC, hwB⟩

/-- **Under the failure of the crux, the essential component of `VA` also contains points of the
*other* wall `VA \\ VB`.**

Let `z ∈ Ess p VA` and `E := connectedComponentIn VA z` (a `T`-invariant component of `VA`).  If `E`
were contained in `VB`, then `E ⊆ VA ∩ VB = W`; as `E` is preconnected it would lie in the single
component `C := connectedComponentIn W z` of `W`, and `E` is `T`-invariant, so `T z ∈ E ⊆ C` while
also `T z ∈ T '' C`, forcing `T '' C = C`.  A `T`-invariant component of `W` contains a translate
crossing *inside* that component (`component_invariant_iff_exists_crossing`), contradicting `hno`.
So `E` must leave `W`, and its points outside `W` are exactly its points of `VA \\ VB`.

This is the structural shape of the failure: the essential component of `VA` meets `VB`
(`ess_inter_VB_of_cover`) **and** crosses into `VA \\ VB`. -/
theorem exists_mem_sdiff_of_no_crux {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hno : ∀ q : ℝ × ℝ, q ∈ VA ∩ VB → ¬ JoinedIn (VA ∩ VB) q (Tmap p q))
    {z : ℝ × ℝ} (hz : z ∈ Ess p VA) :
    ∃ q ∈ VA, q ∉ VB ∧ q ∈ connectedComponentIn VA z := by
  by_contra hcon
  push_neg at hcon
  have hEVA : connectedComponentIn VA z ⊆ VA := connectedComponentIn_subset VA z
  have hEW : connectedComponentIn VA z ⊆ VA ∩ VB := by
    intro q hq
    refine ⟨hEVA hq, ?_⟩
    by_contra hqB
    exact hcon q (hEVA hq) hqB hq
  have hzE : z ∈ connectedComponentIn VA z := mem_connectedComponentIn hz.1
  have hWper : ∀ q : ℝ × ℝ, q ∈ VA ∩ VB ↔ Tmap p q ∈ VA ∩ VB := by
    intro q
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hperA q).mp h1, (hperB q).mp h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hperA q).mpr h1, (hperB q).mpr h2⟩
  have hsub : connectedComponentIn VA z ⊆ connectedComponentIn (VA ∩ VB) z :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn hzE hEW
  have hEinv : Tmap p '' connectedComponentIn VA z = connectedComponentIn VA z := by
    rw [Tmap_image_connectedComponentIn hperA hz.1, connectedComponentIn_eq_of_mem_Ess hperA hz]
  have hzW : z ∈ VA ∩ VB := hEW hzE
  have hTzE : Tmap p z ∈ connectedComponentIn VA z := by
    rw [← hEinv]; exact ⟨z, hzE, rfl⟩
  have hTzC : Tmap p z ∈ connectedComponentIn (VA ∩ VB) z := hsub hTzE
  have hsame : connectedComponentIn (VA ∩ VB) (Tmap p z) = connectedComponentIn (VA ∩ VB) z :=
    (connectedComponentIn_eq hTzC).symm
  have hTC : Tmap p '' connectedComponentIn (VA ∩ VB) z
      = connectedComponentIn (VA ∩ VB) (Tmap p z) :=
    Tmap_image_connectedComponentIn hWper hzW
  have hinv : Tmap p '' connectedComponentIn (VA ∩ VB) z = connectedComponentIn (VA ∩ VB) z := by
    rw [hTC, hsame]
  have hCsub : connectedComponentIn (VA ∩ VB) z ⊆ VA ∩ VB :=
    connectedComponentIn_subset (VA ∩ VB) z
  obtain ⟨q, hqC, hqjoin⟩ :=
    (component_invariant_iff_exists_crossing hWper (hVA.inter hVB) hzW).mp hinv
  exact hno q (hCsub hqC) (hqjoin.mono hCsub)

/-- The symmetric form of `ess_inter_VB_of_cover`. -/
theorem ess_inter_VA_of_cover {p a b : ℝ} (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b) (hVAne : VA.Nonempty)
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z)) :
    (Ess p VB ∩ VA).Nonempty := by
  obtain ⟨z, hzVB, hzjoin⟩ := hwindB
  have hzEss : z ∈ Ess p VB := ⟨hzVB, hzjoin⟩
  have hcover' : VB ∪ VA = stripS a b := by rw [Set.union_comm]; exact hcover
  obtain ⟨w, hwC, hwA⟩ := component_meets_of_cover hVB hVA hcover' hVAne hzVB
  exact ⟨w, connectedComponentIn_subset_Ess hperB hVB hzEss hwC, hwA⟩

/-! ### Session 66: what `IsOpen` buys — the two wall pieces are saturated and mutually separated

In the crux setting (`VA`, `VB` open `T`-invariant with `VA ∪ VB = Ω = stripS a b`) put
`K_A := VA \ VB` and `K_B := VB \ VA`, so that `W = VA ∩ VB = Ω \ (K_A ∪ K_B)` and both pieces are
closed in `Ω`.  The hypotheses `hVA`, `hVB` say more than closedness in `Ω`: since `Ω \ VB = K_A`
and `Ω \ VA = K_B`, *openness in `ℝ²`* forces the walls to contain their own accumulation points
inside the strip (*saturation*), and hence to be mutually separated.  This is the precise sense in
which the crux is stronger than the refuted "closed in the open strip" statements (session 65) and
than the potential statement (session 66): in the two-banded spiral tower no split of the wall set
into two such saturated pieces exists. -/
theorem saturated_of_open_cover {a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hcover : VA ∪ VB = stripS a b) :
    closure (VA \ VB) ∩ stripS a b ⊆ VA \ VB ∧
    closure (VB \ VA) ∩ stripS a b ⊆ VB \ VA ∧
    Disjoint (VA \ VB) (closure (VB \ VA)) ∧
    Disjoint (VB \ VA) (closure (VA \ VB)) := by
  have hsubA : VA ⊆ stripS a b := hcover ▸ subset_union_left
  have hsubB : VB ⊆ stripS a b := hcover ▸ subset_union_right
  -- `Ω \ VB = VA \ VB` and `Ω \ VA = VB \ VA`
  have hKA : stripS a b \ VB = VA \ VB := by
    ext q
    constructor
    · rintro ⟨hq, hqB⟩
      have : q ∈ VA ∪ VB := by rw [hcover]; exact hq
      exact ⟨this.resolve_right hqB, hqB⟩
    · rintro ⟨hqA, hqB⟩
      exact ⟨hsubA hqA, hqB⟩
  have hKB : stripS a b \ VA = VB \ VA := by
    ext q
    constructor
    · rintro ⟨hq, hqA⟩
      have : q ∈ VA ∪ VB := by rw [hcover]; exact hq
      exact ⟨this.resolve_left hqA, hqA⟩
    · rintro ⟨hqB, hqA⟩
      exact ⟨hsubB hqB, hqA⟩
  have hclA : closure (VA \ VB) ⊆ VBᶜ := closure_minimal (fun q hq => hq.2) hVB.isClosed_compl
  have hclB : closure (VB \ VA) ⊆ VAᶜ := closure_minimal (fun q hq => hq.2) hVA.isClosed_compl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    have hqVB : q ∉ VB := hclA hq.1
    rw [← hKA]
    exact ⟨hq.2, hqVB⟩
  · intro q hq
    have hqVA : q ∉ VA := hclB hq.1
    rw [← hKB]
    exact ⟨hq.2, hqVA⟩
  · rw [Set.disjoint_left]
    intro q hqA hqcl
    exact hclB hqcl hqA.1
  · rw [Set.disjoint_left]
    intro q hqB hqcl
    exact hclA hqcl hqB.1

/-! ### Session 66: the frontier, precisely

With the residual back on `mv_obligation` (= the crux = "`VA ∩ VB` has a translate crossing"), here is
the exact state of the identification layer, so that the next session does not have to re-derive it.

**What is available.**  Two of the three ingredients of the classical (Denne) argument are now on the
shelf:

1. *the sheet index* — `exists_sheet_index_aei` (this file): under `hno` for `W`, a `ℤ`-valued function
   `ind` on `W` with `ind (Tmap p q) = ind q + 1` and `ind` constant along joins inside `W`.  (Its
   engine, the freeness of the `ℤ`-action on components, is
   `Commons.Topology.Strip.orbit_injective` / `eq_zero_of_joinedIn_zpow` in the commons.)
2. *the monodromy/decomposition theorem* —
   `Commons.Topology.Jordan.ClosedDisjoint.QD.exists_decomposition`: for `A`, `B` closed disjoint
   subsets of a connected, locally path connected, *simply connected* metric space `X`, and a
   locally constant `h : ↥((A ∪ B)ᶜ) → ℤ`, there are locally constant `f : ↥(Aᶜ) → ℤ` and
   `g : ↥(Bᶜ) → ℤ` with `h = g - f` on `(A ∪ B)ᶜ`.

**How to feed 1 into 2 in the crux setting.**  Take `X := ↥(stripS a b)` (contractible, hence simply
connected: `hmono` holds — the same instances as in `joinedIn_inter_of_joinedIn_strip` above),
`A := {q : X | (q : ℝ × ℝ) ∉ VB}` and `B := {q : X | (q : ℝ × ℝ) ∉ VA}`.  Then `A`, `B` are closed
(preimages of complements of the open `VB`, `VA`), `A ∩ B = ∅`, `(A ∪ B)ᶜ = X ∩ (VA ∩ VB)`, and the
sheet index of `W = VA ∩ VB` is a locally constant `ℤ`-valued function on that free region.  So
``exists_decomposition` applies and yields `ind = g - f` with `f` locally constant on `VB`, `g`
locally constant on `VA` (names as in the theorem: `f` lives on `Aᶜ = VB`, `g` on `Bᶜ = VA`).

**What that gives (KEY FINDING 3 of `NOTES_annulus_duality_open.md`).**  A locally constant function
is constant on each component.  For `z ∈ Ess p VA` the points `z` and `Tmap p z` lie in one component
of `VA`, so `g (Tmap p z) = g z`; together with `ind = g - f` and `ind (Tmap p z) = ind z + 1` this
forces

  `f (Tmap p z) = f z - 1`   for `z ∈ Ess p VA ∩ VB`,
  `f (Tmap p z) = f z`       for `z ∈ Ess p VB ∩ VA`

(the second because for `z ∈ Ess p VB` the points `z`, `Tmap p z` lie in one component of `VB`).
Since `Ess p VA ∩ VB ≠ ∅` and `Ess p VB ∩ VA ≠ ∅` (`ess_inter_VB_of_cover` / `ess_inter_VA_of_cover`
above), `f` is unbounded below on `VB` and `g` unbounded above on `VA`, and in the *collared* case
(`K_A` avoiding the top collar, `K_B` the bottom one) the argument of that note gives: the
`T`-invariant component of `VB` through the bottom band avoids `Ess p VA`, and symmetrically.  Hence
the whole content of the collared case is

  `D_A ∩ D ≠ ∅`,   `D_A` the `T`-invariant component of `VA` through the top band,
                   `D` the `T`-invariant component of `VB` through the bottom band,

which is exactly the crux restricted to that configuration and is *not* known here.  Nothing else
about the residual is known: in particular the potential route (session 66) and the strip-accumulation
route (session 65) are both refuted, so the honest remaining obligation is the above, or a direct
proof of `mv_obligation` (Mayer–Vietoris for `H₁` of the two-set open cover plus the degree
identification). -/

/-! ### Session 67: the collared case, isolated

**Correction of the session-66 frontier note.**  The collared reduction recorded there ("the whole
content of the collared case is `D_A ∩ D ≠ ∅`") is *not* an equivalence, and the claim as written is
too strong.  What is true (and proved below) are the two cheap implications:

* if a point of a `T`-invariant component of `VA` coincides with one of `VB` (e.g. a point of the
  two *collar* components), then the crux conclusion holds (`joinedIn_both_of_mem_collar_components`);
  note that the collar exclusion only gives `VA ∪ VB = Ω` with `(VA \ VB) ⊆ {q.2 ≤ b - δ}`, so a
  point of the upper collar may well lie in `VB \ VA`: it is only the *union* that covers the
  collar;
* if the crux conclusion *fails* (`Ess p VA ∩ Ess p VB = ∅`), then the two collar components are
  disjoint (`no_crux_collar_disjoint`).

The converse of the second is false: the **level cut** `VA := stripS a b \ {q.2 = c}`,
`VB := stripS a b \ {q.2 = a + ε/2}` (with `a + ε < c < b - δ`) satisfies all the collared
hypotheses — `VA`, `VB` are open `T`-invariant, `VA ∪ VB = stripS a b` since
`(VA \ VB) = {q.2 = a+ε/2}` and `(VB \ VA) = {q.2 = c}` are disjoint and lie in the two collar
exclusions, and both are essential — yet the collar component of `VA` is `{q.2 > c}` and that of
`VB` is `{q.2 < a+ε/2}`, which are disjoint; the crux still holds, with the crossing carried by the
*middle* component `{a+ε/2 < q.2 < c} ⊆ VA ∩ VB`.  So the collar components are a *sufficient*
witness only; `D_A ∩ D ≠ ∅` cannot replace the collared case.

**The isolated goal** is therefore the collared case of the crux itself, `collared_crux` below
(the general case being reduced to it by the shrinkage steps C1–C6 of
`NOTES_annulus_duality_open.md`; those shrinkages are *not* formalised here).  The two cheap
implications above are proved, so that any proof of `collared_crux` can be assembled with them. -/

/-- **A horizontal band contained in `V` makes its points essential for `V`.**  If every point of
the open band `c < q.2 < d` lies in `V`, then a point of the band is joined to its `T`-translate
inside `V` by the horizontal segment, which stays in the band. -/
lemma mem_Ess_of_band_subset {p c d : ℝ} {V : Set (ℝ × ℝ)}
    (hband : ∀ q : ℝ × ℝ, c < q.2 → q.2 < d → q ∈ V)
    {q : ℝ × ℝ} (h1 : c < q.2) (h2 : q.2 < d) : q ∈ Ess p V := by
  refine ⟨hband q h1 h2, ?_⟩
  refine ⟨{ toContinuousMap :=
              { toFun := fun t : Set.Icc (0 : ℝ) 1 => (q.1 + (t : ℝ) * p, q.2)
                continuous_toFun := by fun_prop },
            source' := ?_, target' := ?_ }, ?_⟩
  · simp
  · simp [Tmap]
  · intro t; exact hband _ h1 h2

/-- **A point of both collar components is joined to its translate in both sets.**  This is the
*sufficient* direction of the collared reduction: `D_A ∩ D ≠ ∅ ⟹` the crux conclusion. -/
theorem joinedIn_both_of_mem_collar_components {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    {qA qB z : ℝ × ℝ} (hqA : qA ∈ Ess p VA) (hqB : qB ∈ Ess p VB)
    (hzA : z ∈ connectedComponentIn VA qA) (hzB : z ∈ connectedComponentIn VB qB) :
    z ∈ VA ∩ VB ∧ JoinedIn VA z (Tmap p z) ∧ JoinedIn VB z (Tmap p z) :=
  ⟨⟨connectedComponentIn_subset VA qA hzA, connectedComponentIn_subset VB qB hzB⟩,
   (connectedComponentIn_subset_Ess hperA hVA hqA hzA).2,
   (connectedComponentIn_subset_Ess hperB hVB hqB hzB).2⟩

/-- **Under the failure of the crux the two collar components are disjoint.**  (The converse fails —
see the level-cut counterexample in the session-67 note — so this is a constraint on failure
configurations, not a reduction.) -/
theorem no_crux_collar_disjoint {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    {qA qB : ℝ × ℝ} (hqA : qA ∈ Ess p VA) (hqB : qB ∈ Ess p VB)
    (hno : Ess p VA ∩ Ess p VB = ∅) :
    connectedComponentIn VA qA ∩ connectedComponentIn VB qB = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzA, hzB⟩
  exact Set.eq_empty_iff_forall_notMem.mp hno z
    ⟨connectedComponentIn_subset_Ess hperA hVA hqA hzA,
     connectedComponentIn_subset_Ess hperB hVB hqB hzB⟩

/-- **A level that meets no wall is free — the collared win case C1/C2'.**  If for some height
`c ∈ (a,b)` no point of the horizontal line `q.2 = c` lies in `VA \ VB` or in `VB \ VA`, then the
whole line lies in `VA ∩ VB` (it is covered by `VA ∪ VB`); in particular `(0,c)` is joined to its
translate `(p,c)` inside `VA` and inside `VB` (the horizontal segment stays on the line), which is
the crux conclusion.  So under the failure of the crux every level of `(a,b)` meets the union of the
two wall pieces. -/
theorem crux_conclusion_of_free_level {p a b c : ℝ} (hac : a < c) (hcb : c < b)
    {VA VB : Set (ℝ × ℝ)} (hcover : VA ∪ VB = stripS a b)
    (hfree : ∀ x : ℝ, ((x, c) : ℝ × ℝ) ∉ (VA \ VB) ∪ (VB \ VA)) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (Tmap p z) ∧ JoinedIn VB z (Tmap p z) := by
  have hboth : ∀ x : ℝ, ((x, c) : ℝ × ℝ) ∈ VA ∧ ((x, c) : ℝ × ℝ) ∈ VB := by
    intro x
    have hΩ : ((x, c) : ℝ × ℝ) ∈ stripS a b := ⟨hac, hcb⟩
    have hunion : ((x, c) : ℝ × ℝ) ∈ VA ∪ VB := hcover ▸ hΩ
    rcases hunion with h | h
    · refine ⟨h, ?_⟩
      by_contra hB
      exact hfree x (Or.inl ⟨h, hB⟩)
    · refine ⟨?_, h⟩
      by_contra hA
      exact hfree x (Or.inr ⟨h, hA⟩)
  refine ⟨(0, c), ⟨(hboth 0).1, (hboth 0).2⟩, ?_, ?_⟩
  · refine ⟨{ toContinuousMap :=
                { toFun := fun t : Set.Icc (0 : ℝ) 1 => ((t : ℝ) * p, c)
                  continuous_toFun := by fun_prop },
              source' := ?_, target' := ?_ }, ?_⟩
    · simp
    · simp [Tmap]
    · intro t; exact (hboth ((t : ℝ) * p)).1
  · refine ⟨{ toContinuousMap :=
                { toFun := fun t : Set.Icc (0 : ℝ) 1 => ((t : ℝ) * p, c)
                  continuous_toFun := by fun_prop },
              source' := ?_, target' := ?_ }, ?_⟩
    · simp
    · simp [Tmap]
    · intro t; exact (hboth ((t : ℝ) * p)).2

/-- **A level strictly inside the lower collar lies in `VA`.**  If `c < a + ε`, then no point of
the level `{q.2 = c}` can lie in `VB \ VA` (whose heights are `≥ a + ε`), and the level is covered by
`VA ∪ VB`; hence the whole level lies in `VA`.  This is the first band ingredient of the overlapping
case. -/
theorem level_subset_left_of_collar {a b ε c : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hcover : VA ∪ VB = stripS a b) (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hac : a < c) (hcb : c < b) (hcε : c < a + ε) :
    ∀ x : ℝ, ((x, c) : ℝ × ℝ) ∈ VA := by
  intro x
  have hΩ : ((x, c) : ℝ × ℝ) ∈ stripS a b := ⟨hac, hcb⟩
  rcases (hcover ▸ hΩ : ((x, c) : ℝ × ℝ) ∈ VA ∪ VB) with h | h
  · exact h
  · by_contra hA
    exact absurd (hKB ⟨h, hA⟩ : a + ε ≤ ((x, c) : ℝ × ℝ).2) (not_le.mpr hcε)

/-- **A level strictly inside the upper collar lies in `VB`** (the symmetric statement). -/
theorem level_subset_right_of_collar {a b δ c : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hcover : VA ∪ VB = stripS a b) (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hac : a < c) (hcb : c < b) (hcδ : b - δ < c) :
    ∀ x : ℝ, ((x, c) : ℝ × ℝ) ∈ VB := by
  intro x
  have hΩ : ((x, c) : ℝ × ℝ) ∈ stripS a b := ⟨hac, hcb⟩
  rcases (hcover ▸ hΩ : ((x, c) : ℝ × ℝ) ∈ VA ∪ VB) with h | h
  · by_contra hB
    exact absurd (hKA ⟨h, hB⟩ : ((x, c) : ℝ × ℝ).2 ≤ b - δ) (not_le.mpr hcδ)
  · exact h

/-- **The band inside the lower collar is essential for `VA`.**  Every point of the level `{q.2 = c}`
(for `c < a + ε`) is joined to its translate inside `VA` by the horizontal segment, which stays on
the level and hence in `VA` by the previous lemma.  So, under the failure of the crux, the whole
band `(a, a + ε)` lies in `Ess p VA`. -/
theorem band_subset_Ess_of_collar {p a b ε c : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hcover : VA ∪ VB = stripS a b) (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hac : a < c) (hcb : c < b) (hcε : c < a + ε) {x : ℝ} :
    ((x, c) : ℝ × ℝ) ∈ Ess p VA := by
  have hlevel := level_subset_left_of_collar hcover hKB hac hcb hcε
  refine ⟨hlevel x, ?_⟩
  refine ⟨{ toContinuousMap :=
              { toFun := fun t : Set.Icc (0 : ℝ) 1 => (x + (t : ℝ) * p, c)
                continuous_toFun := by fun_prop },
            source' := ?_, target' := ?_ }, ?_⟩
  · simp
  · simp [Tmap]
  · intro t; exact hlevel (x + (t : ℝ) * p)

/-- **The band inside the upper collar is essential for `VB`** (the symmetric statement). -/
theorem band_subset_Ess_of_collar_right {p a b δ c : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hcover : VA ∪ VB = stripS a b) (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hac : a < c) (hcb : c < b) (hcδ : b - δ < c) {x : ℝ} :
    ((x, c) : ℝ × ℝ) ∈ Ess p VB := by
  have hlevel := level_subset_right_of_collar hcover hKA hac hcb hcδ
  refine ⟨hlevel x, ?_⟩
  refine ⟨{ toContinuousMap :=
              { toFun := fun t : Set.Icc (0 : ℝ) 1 => (x + (t : ℝ) * p, c)
                continuous_toFun := by fun_prop },
            source' := ?_, target' := ?_ }, ?_⟩
  · simp
  · simp [Tmap]
  · intro t; exact hlevel (x + (t : ℝ) * p)

/-- **A component of `V` that reaches a band contained in `V` is `T`-invariant, hence essential.**

If the whole open band `c < q.2 < d` lies in `V` and the `V`-component `C` of `z` meets the band,
then the band (being preconnected, inside `V`) lies in `C`; as `T` preserves heights, `T q` is again
in the band, hence in `C`, so `T '' C` is the component of `T q`, which is `C` itself.  Therefore
`T z ∈ C` and `z` is joined to `T z` inside `C ⊆ V`.

In the collared case this is the key interface step: a point of the touching level `{q.2 = b - δ}`
which lies in `VA` and whose `VA`-component meets the *lower* band is already in `Ess p VA` (and
symmetrically for `VB` and the upper band). -/
theorem mem_Ess_of_component_meets_band {p c d : ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (hper : ∀ q : ℝ × ℝ, q ∈ V ↔ Tmap p q ∈ V)
    (hband : ∀ q : ℝ × ℝ, c < q.2 → q.2 < d → q ∈ V)
    {z q : ℝ × ℝ} (hz : z ∈ V) (hq : q ∈ connectedComponentIn V z)
    (h1 : c < q.2) (h2 : q.2 < d) :
    z ∈ Ess p V := by
  have hbandsub : ∀ q' : ℝ × ℝ, c < q'.2 → q'.2 < d → q' ∈ connectedComponentIn V z := by
    intro q' h1' h2'
    have hpre : IsPreconnected {r : ℝ × ℝ | c < r.2 ∧ r.2 < d} := (convex_stripS c d).isPreconnected
    have hsub : {r : ℝ × ℝ | c < r.2 ∧ r.2 < d} ⊆ V := fun r hr => hband r hr.1 hr.2
    have hmem : {r : ℝ × ℝ | c < r.2 ∧ r.2 < d} ⊆ connectedComponentIn V q :=
      IsPreconnected.subset_connectedComponentIn hpre ⟨h1, h2⟩ hsub
    exact (connectedComponentIn_eq hq) ▸ hmem ⟨h1', h2'⟩
  -- `T q` is again in the band, hence in `C`
  have hTqC : Tmap p q ∈ connectedComponentIn V z := by
    refine hbandsub _ ?_ h2
    rw [Tmap]; exact h1
  have hqV : q ∈ V := hband q h1 h2
  have himg : Tmap p '' connectedComponentIn V q = connectedComponentIn V z := by
    rw [Tmap_image_connectedComponentIn hper hqV, connectedComponentIn_eq hTqC]
  have hzCq : z ∈ connectedComponentIn V q :=
    (connectedComponentIn_eq hq).symm ▸ mem_connectedComponentIn hz
  have hTz : Tmap p z ∈ connectedComponentIn V z := by
    rw [← himg]
    exact ⟨z, hzCq, rfl⟩
  have hCop : IsOpen (connectedComponentIn V z) := hV.connectedComponentIn
  have hpc : IsPathConnected (connectedComponentIn V z) :=
    (hCop.isConnected_iff_isPathConnected).mp
      ⟨⟨z, mem_connectedComponentIn hz⟩, isPreconnected_connectedComponentIn⟩
  exact ⟨hz, (hpc.joinedIn z (mem_connectedComponentIn hz) _ hTz).mono
    (connectedComponentIn_subset V z)⟩

/-! ### Session 69: the interface dichotomy of the touching case (`a + ε = b - δ =: c₀`)

Everything of the touching case now lives on the single level `L := {q.2 = c₀}`.  What is proved:

* below `c₀` the levels lie in `VA` and hence in `Ess p VA` (`level_subset_left_of_collar`,
  `band_subset_Ess_of_collar`); above `c₀` symmetrically in `Ess p VB`
  (`level_subset_right_of_collar`, `band_subset_Ess_of_collar_right`);
* `mem_Ess_of_component_meets_band`: **any point of `VA` whose `VA`-component reaches the lower band
  is already in `Ess p VA`** (the band lies in the component, `T q` is again in the band, so
  `T '' C = C`), and symmetrically for `VB` and the upper band;
* `saturated_of_open_cover`: the wall pieces are *saturated*, `closure K ∩ Ω = K`, i.e. each contains
  its own accumulation points inside the strip.

**The dichotomy.**  Partition the interface level: `P := L ∩ K_A`, `Q := L ∩ K_B`,
`R := L ∖ (P ∪ Q) = L ∩ VA ∩ VB`.  Saturation says exactly that `P` is the set of points of `L` that
are limits of `K_A` from below (and `Q` from above), so `P` and `Q` are **disjoint** closed
`T`-invariant subsets of the line `L`, with `R` open and `T`-invariant.

* If `R` contains a full period (`R` is a union of open intervals of length `≤ p`, being `T`-invariant
  and contained in the line), then `R` carries a `T`-crossing and the collared conclusion follows from
  a connected `T`-invariant subset of `VA ∩ VB` (as in `crux_conclusion_of_free_level`'s argument).
* Otherwise, for `z ∈ R`, one of the two components of `z` (in `VA`, in `VB`) must fail to reach its
  band, by the two bullet points above together with the failure hypothesis `Ess p VA ∩ Ess p VB = ∅`;
  that failure of *reaching* is a statement about which wall pieces separate `z` from the bands, and
  is the remaining obligation of the touching case.

This is the state of the touching case, recorded so the next stretch starts at the level `L` with
`P`, `Q`, `R` rather than at the whole strip. -/

/-- **Failure to reach, in its cleanest form.**  Collared setting.  Let `zA` be a point of `VA` in
the lower band (`zA.2 < a + ε`) and `zB` a point of `VB` in the upper band (`b - δ < zB.2`).  If the
crux conclusion fails (`Ess p VA ∩ Ess p VB = ∅`) then the `VA`-component of `zA` and the
`VB`-component of `zB` are **disjoint**: a common point would be a point of `VA ∩ VB` whose two
components each reach their band, hence (by `mem_Ess_of_component_meets_band` and
`connectedComponentIn_subset_Ess`) would lie in `Ess p VA ∩ Ess p VB`.

This is the "failure to reach" branch of the session-69 interface dichotomy, isolated as a statement
about the two collar components. -/
theorem component_inter_eq_empty_of_no_crux {p a b δ ε : ℝ} (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hεb : a + ε ≤ b) (hbδa : a ≤ b - δ)
    (hno : Ess p VA ∩ Ess p VB = ∅)
    {zA zB : ℝ × ℝ} (hzA : zA ∈ VA) (hzB : zB ∈ VB)
    (hzA2 : zA.2 < a + ε) (hzB2 : b - δ < zB.2) :
    connectedComponentIn VA zA ∩ connectedComponentIn VB zB = ∅ := by
  have hbandA : ∀ q : ℝ × ℝ, a < q.2 → q.2 < a + ε → q ∈ VA := by
    intro q h1 h2
    have hqΩ : q ∈ stripS a b := ⟨h1, lt_of_lt_of_le h2 hεb⟩
    rcases (hcover ▸ hqΩ : q ∈ VA ∪ VB) with h | h
    · exact h
    · by_contra hqA
      exact absurd (hKB ⟨h, hqA⟩ : a + ε ≤ q.2) (not_le.mpr h2)
  have hbandB : ∀ q : ℝ × ℝ, b - δ < q.2 → q.2 < b → q ∈ VB := by
    intro q h1 h2
    have hqΩ : q ∈ stripS a b := ⟨lt_of_le_of_lt hbδa h1, h2⟩
    rcases (hcover ▸ hqΩ : q ∈ VA ∪ VB) with h | h
    · by_contra hqB
      exact absurd (hKA ⟨h, hqB⟩ : q.2 ≤ b - δ) (not_le.mpr h1)
    · exact h
  have hzA' : zA ∈ Ess p VA :=
    mem_Ess_of_component_meets_band hVA hperA hbandA hzA (mem_connectedComponentIn hzA)
      (hcover ▸ (show zA ∈ VA ∪ VB from Or.inl hzA) : zA ∈ stripS a b).1 hzA2
  have hzB' : zB ∈ Ess p VB :=
    mem_Ess_of_component_meets_band hVB hperB hbandB hzB (mem_connectedComponentIn hzB)
      hzB2 (by
        have hzBΩ : zB ∈ stripS a b := hcover ▸ (show zB ∈ VA ∪ VB from Or.inr hzB)
        exact hzBΩ.2)
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro z ⟨hzAcomp, hzBcomp⟩
  exact Set.eq_empty_iff_forall_notMem.mp hno z
    ⟨connectedComponentIn_subset_Ess hperA hVA hzA' hzAcomp,
     connectedComponentIn_subset_Ess hperB hVB hzB' hzBcomp⟩

/-- **The interface disjunction (touching case).**

Collared setting with the interface level pinned (`b - δ ≤ z.2 ≤ a + ε`).  If the crux conclusion
fails, then for every `z` on the interface lying in both `VA` and `VB`, **at least one** of the two
components of `z` fails to reach its band:

  `connectedComponentIn VA z ∩ (lower band) = ∅`   or   `connectedComponentIn VB z ∩ (upper band) = ∅`.

Equivalently: no point of the interface has both components reaching their bands.  This is the
localized form of the remaining case of the touching case: with `P = L ∩ K_A`, `Q = L ∩ K_B` (disjoint
by saturation) and `R = L ∩ VA ∩ VB`, every `z ∈ R` falls into at least one of the two branches, and
the task left is to say *which* wall piece performs the cutting in each branch. -/
theorem interface_dichotomy {p a b δ ε : ℝ} (hab : a < b) (hεb : a + ε ≤ b) (hbδa : a ≤ b - δ)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hno : Ess p VA ∩ Ess p VB = ∅)
    {z : ℝ × ℝ} (hzA : z ∈ VA) (hzB : z ∈ VB)
    (hzlow : b - δ ≤ z.2) (hzhigh : z.2 ≤ a + ε) :
    (connectedComponentIn VA z ∩ {q : ℝ × ℝ | a < q.2 ∧ q.2 < a + ε} = ∅) ∨
    (connectedComponentIn VB z ∩ {q : ℝ × ℝ | b - δ < q.2 ∧ q.2 < b} = ∅) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨zA, hzAcomp, hzA1, hzA2⟩, ⟨zB, hzBcomp, hzB1, hzB2⟩⟩ := hcon
  have hzAVA : zA ∈ VA := connectedComponentIn_subset VA z hzAcomp
  have hzBVB : zB ∈ VB := connectedComponentIn_subset VB z hzBcomp
  have hempty := component_inter_eq_empty_of_no_crux hab hVA hVB hperA hperB hcover hKA hKB
    hεb hbδa hno hzAVA hzBVB hzA2 hzB1
  have hzmem : z ∈ connectedComponentIn VA zA ∩ connectedComponentIn VB zB :=
    ⟨(connectedComponentIn_eq hzAcomp).symm ▸ mem_connectedComponentIn hzA,
     (connectedComponentIn_eq hzBcomp).symm ▸ mem_connectedComponentIn hzB⟩
  exact Set.eq_empty_iff_forall_notMem.mp hempty z hzmem

/-- The trace of the first wall piece `VA \ VB` on the interface level `{q.2 = b - δ}`. -/
def Ptrace (b δ : ℝ) (VA VB : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | q.2 = b - δ ∧ q ∈ VA ∧ q ∉ VB}

/-- The trace of the second wall piece `VB \ VA` on the interface level `{q.2 = b - δ}`. -/
def Qtrace (b δ : ℝ) (VA VB : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | q.2 = b - δ ∧ q ∈ VB ∧ q ∉ VA}

/-- **The two wall traces on the interface line are disjoint and `T`-periodic.**

With `P := Ptrace b δ VA VB` and `Q := Qtrace b δ VA VB`: `P` and `Q` are disjoint (they see the
complementary sides of `VA \ VB`) and each is invariant under the translation `Tmap p`, because both
the level `{q.2 = b - δ}` and the membership in `VA`, `VB` are `T`-invariant.  Together with the
interface level `{q.2 = b - δ}` this gives the decomposition of the level into `P ⊔ Q ⊔ R` with
`R = {q.2 = b - δ} ∩ VA ∩ VB`, which is open and `T`-invariant; and by saturation
(`saturated_of_open_cover`) the wall pieces contain their own accumulation, so `P` and `Q` are the
closed parts of the level.  This reduces the touching case to a one-dimensional statement about two
disjoint periodic subsets of a line. -/
theorem interface_traces {p a b δ : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB) :
    Disjoint (Ptrace b δ VA VB) (Qtrace b δ VA VB) ∧
    (∀ q : ℝ × ℝ, q ∈ Ptrace b δ VA VB ↔ Tmap p q ∈ Ptrace b δ VA VB) ∧
    (∀ q : ℝ × ℝ, q ∈ Qtrace b δ VA VB ↔ Tmap p q ∈ Qtrace b δ VA VB) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Ptrace, Qtrace, Set.disjoint_left]
    rintro q ⟨-, -, hqP⟩ ⟨-, hqQ, -⟩
    exact hqP hqQ
  · intro q
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, (hperA q).mp h2, fun hc => h3 ((hperB q).mpr hc)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, (hperA q).mpr h2, fun hc => h3 ((hperB q).mp hc)⟩
  · intro q
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, (hperB q).mp h2, fun hc => h3 ((hperA q).mpr hc)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, (hperB q).mpr h2, fun hc => h3 ((hperA q).mp hc)⟩

/-- **The first interface trace is closed in the strip** (saturation).  The trace `P` of the wall
piece `VA \ VB` on the level `{q.2 = b - δ}` contains its own accumulation points inside `Ω`:
`closure P ∩ Ω ⊆ P`.  This is the named form of the fact the interface argument consumes — `P` is one
of the two *closed* periodic pieces of the interface line — and it follows from the saturation of the
wall pieces (`saturated_of_open_cover`) together with `P ⊆ {q.2 = b - δ}`. -/
theorem closure_Ptrace_inter_subset {a b δ : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hcover : VA ∪ VB = stripS a b) :
    closure (Ptrace b δ VA VB) ∩ stripS a b ⊆ Ptrace b δ VA VB := by
  intro q hq
  have hsub : closure (Ptrace b δ VA VB) ⊆ closure (VA \ VB) :=
    closure_mono (fun r hr => ⟨hr.2.1, hr.2.2⟩)
  have hKA := saturated_of_open_cover (a := a) (b := b) hVA hVB hcover
  have hqK : q ∈ VA \ VB := hKA.1 ⟨hsub hq.1, hq.2⟩
  have hcl : closure (Ptrace b δ VA VB) ⊆ {q : ℝ × ℝ | q.2 = b - δ} :=
    closure_minimal (fun r hr => hr.1) (isClosed_eq continuous_snd continuous_const)
  exact ⟨hcl hq.1, hqK.1, hqK.2⟩

/-- **The second interface trace is closed in the strip** (saturation), symmetrically:
`closure Q ∩ Ω ⊆ Q`. -/
theorem closure_Qtrace_inter_subset {a b δ : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hcover : VA ∪ VB = stripS a b) :
    closure (Qtrace b δ VA VB) ∩ stripS a b ⊆ Qtrace b δ VA VB := by
  intro q hq
  have hsub : closure (Qtrace b δ VA VB) ⊆ closure (VB \ VA) :=
    closure_mono (fun r hr => ⟨hr.2.1, hr.2.2⟩)
  have hKA := saturated_of_open_cover (a := a) (b := b) hVA hVB hcover
  have hqK : q ∈ VB \ VA := hKA.2.1 ⟨hsub hq.1, hq.2⟩
  have hcl : closure (Qtrace b δ VA VB) ⊆ {q : ℝ × ℝ | q.2 = b - δ} :=
    closure_minimal (fun r hr => hr.1) (isClosed_eq continuous_snd continuous_const)
  exact ⟨hcl hq.1, hqK.1, hqK.2⟩

/-- **A component of an open set is closed in it**: `A ∩ closure C ⊆ C` for `C` the component of a
point of the open set `A`.  (The component is open, so the only points of its closure inside `A` are
its own.) -/
theorem isOpen_inter_closure_subset_connectedComponentIn {A : Set (ℝ × ℝ)} (hA : IsOpen A)
    {z : ℝ × ℝ} (hz : z ∈ A) :
    A ∩ closure (connectedComponentIn A z) ⊆ connectedComponentIn A z := by
  rintro w ⟨hwA, hwcl⟩
  have hCpc : IsPreconnected (connectedComponentIn A z) := isPreconnected_connectedComponentIn
  have hpre : IsPreconnected (insert w (connectedComponentIn A z)) :=
    hCpc.subset_closure (subset_insert w _) (fun x hx => by
      rcases hx with rfl | hxC
      · exact hwcl
      · exact subset_closure hxC)
  have hsub : insert w (connectedComponentIn A z) ⊆ A := by
    intro x hx
    rcases hx with rfl | hxC
    · exact hwA
    · exact connectedComponentIn_subset A z hxC
  have hkey := IsPreconnected.subset_connectedComponentIn hpre
    (Or.inr (mem_connectedComponentIn hz)) hsub
  exact hkey (Or.inl rfl)

/-- **The frontier of a component of `VA` lies in the other wall piece.**  If `VA`, `VB` are open with
`VA ∪ VB = Ω = stripS a b` and `z ∈ VA`, then

  `frontier (connectedComponentIn VA z) ∩ Ω ⊆ VB \ VA`.

Indeed the component is open, so its frontier misses it and, by
`isOpen_inter_closure_subset_connectedComponentIn`, also misses all of `VA`; the frontier is inside
`closure VA`, and `Ω \ VA = VB \ VA` because `Ω = VA ∪ VB`.  So whatever separates a point of `VA`
from the rest of `VA` is made of points of the *complementary* wall piece — the mechanism behind the
two branches of the interface dichotomy. -/
theorem frontier_connectedComponentIn_inter_subset {a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hcover : VA ∪ VB = stripS a b) {z : ℝ × ℝ} (hz : z ∈ VA) :
    frontier (connectedComponentIn VA z) ∩ stripS a b ⊆ VB \ VA := by
  intro q hq
  have hCopen : IsOpen (connectedComponentIn VA z) := hVA.connectedComponentIn
  have hqcl : q ∈ closure (connectedComponentIn VA z) := frontier_subset_closure hq.1
  have hqVA : q ∉ VA := by
    intro hqVA
    have hnotC : q ∉ connectedComponentIn VA z := by
      have hfe : frontier (connectedComponentIn VA z)
          = closure (connectedComponentIn VA z) \ connectedComponentIn VA z := hCopen.frontier_eq
      have := hq.1
      rw [hfe] at this
      exact this.2
    exact hnotC (isOpen_inter_closure_subset_connectedComponentIn hVA hz ⟨hqVA, hqcl⟩)
  have hunion : q ∈ VA ∪ VB := hcover ▸ hq.2
  rcases hunion with h | h
  · exact absurd h hqVA
  · exact ⟨h, hqVA⟩

/-- **The collared case with *disjoint* collars (`b - δ < a + ε`).**  Then the strip is the union of
the two open bands `(a, a+ε)` and `(b-δ, b)`, and a level in the gap `b - δ < c < a + ε` misses both
wall pieces (`VA \ VB` has heights `≤ b - δ`, `VB \ VA` has heights `≥ a + ε`); the free-level lemma
applies verbatim.  This is the collared case C1 of the annulus notes. -/
theorem collared_crux_of_disjoint_collars {p a b δ ε : ℝ} (hp : 0 < p) (hab : a < b)
    (hδ : 0 < δ) (hε : 0 < ε) (hgap : b - δ < a + ε)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ stripS a b) (hsubB : VB ⊆ stripS a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z)) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (Tmap p z) ∧ JoinedIn VB z (Tmap p z) := by
  have hmin : max a (b - δ) < min (a + ε) b :=
    max_lt_iff.mpr ⟨lt_min (by linarith) hab, lt_min hgap (by linarith)⟩
  obtain ⟨c, hc1, hc2⟩ := exists_between hmin
  have hca : a < c := lt_of_le_of_lt (le_max_left _ _) hc1
  have hcδ : b - δ < c := lt_of_le_of_lt (le_max_right _ _) hc1
  have hcb : c < b := lt_of_lt_of_le hc2 (min_le_right _ _)
  have hcε : c < a + ε := lt_of_lt_of_le hc2 (min_le_left _ _)
  refine crux_conclusion_of_free_level hca hcb hcover ?_
  intro x
  rintro (h | h)
  · exact absurd (hKA h : ((x, c) : ℝ × ℝ).2 ≤ b - δ) (not_le.mpr hcδ)
  · exact absurd (hKB h : a + ε ≤ ((x, c) : ℝ × ℝ).2) (not_le.mpr hcε)

/-! ### Session 73/74: the barrier step of the touching case, stated

The touching case is down to the local question at `z ∈ R = {q.2 = b - δ} ∩ VA ∩ VB`:
`interface_dichotomy` gives `z ∉ D_A` or `z ∉ D_B`, where `D_A` is the component of `VA` through the
lower band and `D_B` that of `VB` through the upper band.  The barrier step is the following
statement, whose inputs are all proved:

**Barrier lemma.**  In the touching case, let `z ∈ R` with `z ∉ D_A`.  Then `z` is separated from the
lower band *within `VA`* by a barrier which meets the interface level, i.e. there are a point
`q ∈ D_A` (a point of the lower band) and a point `p ∈ frontier (connectedComponentIn VA z)` with
`p` on the segment joining `z` to `q`; and every such `p` lies in `K_B` (see below), so the barrier is
a piece of the *other* wall, and by saturation it must reach `P`.

Two ingredients are already in hand for it:

* **`frontier (connectedComponentIn VA z) ∩ Ω ⊆ VB \ VA`.**  A component of `VA` is open and its
  frontier inside `Ω` lies in `closure VA \ VA`, while `Ω \ VA = VB \ VA` because `Ω = VA ∪ VB`;
  hence the frontier of the component is made of points of the *complementary* wall piece.  This is
  why the cutting in the two branches of `interface_dichotomy` is performed by `K_B` in the first
  branch and by `K_A` in the second — and why the traces `P = Ptrace` (resp. `Q = Qtrace`) are the
  right objects: a barrier separating an interface point from a band is a `T`-invariant closed piece
  of the complementary wall, which by saturation contains its interface accumulation.
* **the vertical first-exit.**  `VA` is open and contains `z`, so the vertical segment from `z` down
  to any point of the lower band starts inside `D_A(z)` and ends outside it; the first point where it
  leaves is a frontier point of the component.  Composing this with the previous item produces the
  barrier point `p ∈ K_B` on the vertical through `z`.

What is *not* yet formalised here: the passage from "the barrier reaches the interface level" to the
one-dimensional statement "`P` (resp. `Q`) separates the trace point from the band", which is the
form the cutting argument consumes.  The state of the touching case is therefore: two disjoint,
`T`-periodic, closed traces `P`, `Q` on the interface level (`interface_traces`,
`closure_Ptrace_inter_subset`, `closure_Qtrace_inter_subset`), the disjunction
(`interface_dichotomy`), and the barrier structure above. -/

/-- The parametrised vertical segment from `e` (at `t = 0`) up to the level of `z` (at `t = 1`),
keeping the `x`-coordinate of `z`.  This is the map `H` of the first-exit argument
(`exists_frontier_exit_on_vertical`). -/
def vseg (z e : ℝ × ℝ) (t : ℝ) : ℝ × ℝ := (z.1, z.2 + t * (e.2 - z.2))

@[simp] lemma vseg_fst (z e : ℝ × ℝ) (t : ℝ) : (vseg z e t).1 = z.1 := rfl
@[simp] lemma vseg_snd (z e : ℝ × ℝ) (t : ℝ) : (vseg z e t).2 = z.2 + t * (e.2 - z.2) := rfl
@[simp] lemma vseg_zero (z e : ℝ × ℝ) : vseg z e 0 = (z.1, z.2) := by
  simp [vseg]
lemma vseg_one (z e : ℝ × ℝ) : (vseg z e 1).2 = e.2 := by rw [vseg_snd, one_mul]; ring

lemma vseg_continuous (z e : ℝ × ℝ) : Continuous (vseg z e) := by
  rw [show vseg z e = fun t => (z.1, z.2 + t * (e.2 - z.2)) from rfl]
  fun_prop

/-- **The exit segment stays between the two heights.**  For `t ∈ [0,1]` the height of `vseg z e t` is
the convex combination of the heights of `z` and `e`, hence lies between them. -/
lemma vseg_mem_Icc {z e : ℝ × ℝ} (h : e.2 < z.2) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    e.2 ≤ (vseg z e t).2 ∧ (vseg z e t).2 ≤ z.2 := by
  constructor <;> · rw [vseg_snd]; nlinarith

/-- **The exit segment lies in the strip** (for `e` above the lower boundary and `z` on the level
`b - δ`). -/
lemma vseg_mem_stripS {a b δ : ℝ} (hδ : 0 < δ) {z e : ℝ × ℝ} (hz : z.2 = b - δ)
    (hea : a < e.2) (hez₂ : e.2 < z.2) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    vseg z e t ∈ stripS a b := by
  obtain ⟨hlo, hhi⟩ := vseg_mem_Icc hez₂ h0 h1
  refine ⟨lt_of_lt_of_le hea hlo, ?_⟩
  rw [hz] at hhi
  linarith

/-- **The first-exit time** of the segment `vseg z e` from the component of `z` in `VA`: the
supremum of the times `t ∈ [0,1]` up to which the segment stays inside `connectedComponentIn VA z`.
This is the `τ` of the first-exit argument (`exists_frontier_exit_on_vertical`). -/
noncomputable def exitTime (VA : Set (ℝ × ℝ)) (z e : ℝ × ℝ) : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ t' ∈ Set.Icc (0 : ℝ) t, vseg z e t' ∈ connectedComponentIn VA z}

@[simp] lemma exitTime_eq_sSup (VA : Set (ℝ × ℝ)) (z e : ℝ × ℝ) :
    exitTime VA z e = sSup {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ t' ∈ Set.Icc (0 : ℝ) t, vseg z e t' ∈ connectedComponentIn VA z} := rfl

/-- **The exit point lies in the closure of the component.**  The exit time `τ = exitTime VA z e` is a
supremum of times up to which the segment `vseg z e` stays in `connectedComponentIn VA z`; taking
times `s ∈ S` arbitrarily close to `τ` from below (possible by the sup property) and using continuity
of the segment exhibits the exit point `vseg z e τ` as a limit of points of the component. -/
theorem vseg_exitTime_mem_closure {VA : Set (ℝ × ℝ)} {z e : ℝ × ℝ} (hz : z ∈ VA)
    (hnot : e ∉ connectedComponentIn VA z) :
    vseg z e (exitTime VA z e) ∈ closure (connectedComponentIn VA z) := by
  classical
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ t' ∈ Set.Icc (0 : ℝ) t, vseg z e t' ∈ connectedComponentIn VA z} with hS
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, by norm_num⟩, ?_⟩
    intro t' ht'
    have ht'0 : t' = 0 := by simpa [Set.mem_Icc] using ht'
    rw [ht'0, vseg_zero]
    simpa using mem_connectedComponentIn hz
  have hbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have hτ : exitTime VA z e = sSup S := by rw [exitTime_eq_sSup, hS]
  rw [hτ]
  refine mem_closure_iff.mpr ?_
  intro U hU hx
  have hpre : vseg z e ⁻¹' U ∈ 𝓝 (sSup S) :=
    (vseg_continuous z e).continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨s, hsS, hsgt⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩
    (show sSup S - ε < sSup S by linarith)
  refine ⟨vseg z e s, ?_, hsS.2 s ⟨hsS.1.1, le_rfl⟩⟩
  exact hεsub (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith [le_csSup hbdd hsS]⟩)

/-- **Every time strictly below the exit time maps into the component** (the `hlt` helper of the
first-exit argument, with its hypotheses in the form the call sites can supply: `0 ≤ t` and
`t < exitTime VA z e`).

By definition `exitTime VA z e = sSup S` where `S` is the set of times up to which the segment stays
in `connectedComponentIn VA z`; the sup property produces `t'' ∈ S` with `t'' > t`, and `t'' ∈ S`
gives membership of the whole `[0, t'']`, in particular of `t`. -/
theorem vseg_lt_exitTime_mem_component {VA : Set (ℝ × ℝ)} {z e : ℝ × ℝ} (hz : z ∈ VA)
    {t : ℝ} (h0 : 0 ≤ t) (ht : t < exitTime VA z e) :
    vseg z e t ∈ connectedComponentIn VA z := by
  classical
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ t' ∈ Set.Icc (0 : ℝ) t, vseg z e t' ∈ connectedComponentIn VA z} with hS
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, by norm_num⟩, ?_⟩
    intro t' ht'
    have ht'0 : t' = 0 := by simpa [Set.mem_Icc] using ht'
    rw [ht'0, vseg_zero]
    simpa using mem_connectedComponentIn hz
  have hτ : exitTime VA z e = sSup S := by rw [exitTime_eq_sSup, hS]
  rw [hτ] at ht
  obtain ⟨t'', ht''S, ht''gt⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ ht
  exact ht''S.2 t ⟨h0, le_of_lt ht''gt⟩

/-- **Plumbing point 2: a time just past the exit time lands in the component.**  If the exit point
`vseg z e (exitTime VA z e)` lies in the open component `connectedComponentIn VA z`, then so does
`vseg z e s` for some `s > exitTime VA z e`.

The chain: openness of the component gives `ε > 0` with `Metric.ball p ε ⊆ component`; continuity of
`vseg z e` at the exit time turns that ball into a neighbourhood of `exitTime VA z e`, hence (by
`Metric.mem_nhds_iff`) into an `η > 0` with `ball τ η ⊆ vseg z e ⁻¹' ball p ε`; and `s := τ + η/2`
satisfies `dist s τ = η/2 < η`. -/
theorem exists_lt_vseg_mem_component_of_mem {VA : Set (ℝ × ℝ)} (hVA : IsOpen VA)
    {z e : ℝ × ℝ} (hmem : vseg z e (exitTime VA z e) ∈ connectedComponentIn VA z) :
    ∃ s : ℝ, exitTime VA z e < s ∧ vseg z e s ∈ connectedComponentIn VA z := by
  classical
  have hCop : IsOpen (connectedComponentIn VA z) := hVA.connectedComponentIn
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hCop.mem_nhds hmem)
  have hpre : vseg z e ⁻¹' Metric.ball (vseg z e (exitTime VA z e)) ε ∈ 𝓝 (exitTime VA z e) :=
    (vseg_continuous z e).continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball]; simpa using hε))
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨exitTime VA z e + η / 2, by linarith, hεsub (hηsub ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Plumbing point 3: truncating the exit time to `1`.**  If `τ < 1` and `s > τ` lies in a ball of
radius `η` around `τ`, then `t := min 1 s` still satisfies `τ < t`, `t ≤ 1` and `t ∈ ball τ η`.

This is the step that failed before by running `linarith` on the `min` as a whole: the point is that
`s ∈ ball τ η` gives `dist s τ < η`, that `t ≤ s` gives `dist t τ ≤ dist s τ` *once `τ < t` is
known*, and that `τ < t` follows from `τ < 1` and `τ < s` by `lt_min`. -/
lemma min_one_mem_ball {τ s η : ℝ} (hτ1 : τ < 1) (hs : τ < s) (hball : s ∈ Metric.ball τ η) :
    τ < min 1 s ∧ min 1 s ≤ 1 ∧ min 1 s ∈ Metric.ball τ η := by
  have hlt : τ < min 1 s := lt_min hτ1 hs
  have hle1 : min 1 s ≤ 1 := min_le_left _ _
  have hles : min 1 s ≤ s := min_le_right _ _
  refine ⟨hlt, hle1, ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hball ⊢
  obtain ⟨hb1, hb2⟩ := hball
  constructor <;> linarith

/-- **The maximality contradiction of the first-exit argument.**  If the exit point
`vseg z e (exitTime VA z e)` lies in the component of `z`, and the exit time is below `1`, then a time
just past the exit time (truncated with `min 1`, `min_one_mem_ball`) also maps into the component, so
the whole `[0, t]` maps into it; that puts `t` in the defining set `S` and contradicts
`t > sSup S = exitTime VA z e`. -/
theorem false_of_exitTime_mem {VA : Set (ℝ × ℝ)} (hVA : IsOpen VA) {z e : ℝ × ℝ} (hz : z ∈ VA)
    (hτ1 : exitTime VA z e < 1)
    (hmem : vseg z e (exitTime VA z e) ∈ connectedComponentIn VA z) : False := by
  classical
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ t' ∈ Set.Icc (0 : ℝ) t, vseg z e t' ∈ connectedComponentIn VA z} with hS
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, by norm_num⟩, ?_⟩
    intro t' ht'
    have ht'0 : t' = 0 := by simpa [Set.mem_Icc] using ht'
    rw [ht'0, vseg_zero]
    simpa using mem_connectedComponentIn hz
  have hbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have hτ : exitTime VA z e = sSup S := by rw [exitTime_eq_sSup, hS]
  have hsSup1 : sSup S < 1 := by rw [← hτ]; exact hτ1
  have hCop : IsOpen (connectedComponentIn VA z) := hVA.connectedComponentIn
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hCop.mem_nhds hmem)
  have hpre : vseg z e ⁻¹' Metric.ball (vseg z e (sSup S)) ε ∈ 𝓝 (sSup S) := by
    rw [← hτ]
    exact (vseg_continuous z e).continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball]; simpa using hε))
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hsball : sSup S + η / 2 ∈ Metric.ball (sSup S) η := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  obtain ⟨hlt, hle1, hball⟩ :=
    min_one_mem_ball hsSup1 (by linarith : sSup S < sSup S + η / 2) hsball
  have htC : vseg z e (min 1 (sSup S + η / 2)) ∈ connectedComponentIn VA z :=
    hεsub (hηsub hball)
  refine absurd (le_csSup hbdd ?_) (not_le.mpr hlt)
  refine ⟨⟨le_trans (le_csSup hbdd h0S) hlt.le, hle1⟩, ?_⟩
  intro t' ht'
  rcases lt_trichotomy t' (sSup S) with h | h | h
  · exact vseg_lt_exitTime_mem_component hz ht'.1 (hτ ▸ h)
  · rw [h]; exact hmem
  · refine hεsub (hηsub ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have htle : t' ≤ sSup S + η / 2 := le_trans ht'.2 (min_le_right _ _)
    constructor <;> linarith

/-- **The exit time is not `1`.**  If `exitTime VA z e = 1`, then every time below `1` maps into the
component (`vseg_lt_exitTime_mem_component`), so by continuity `e = vseg z e 1` is a limit of points of
the component; as `e ∈ VA`, `isOpen_inter_closure_subset_connectedComponentIn` then puts `e` *in* the
component, contradicting the hypothesis. -/
theorem exitTime_ne_one {VA : Set (ℝ × ℝ)} (hVA : IsOpen VA) {z e : ℝ × ℝ} (hez : e.1 = z.1)
    (hz : z ∈ VA) (he : e ∈ VA) (hnot : e ∉ connectedComponentIn VA z) :
    exitTime VA z e ≠ 1 := by
  intro h1
  have h1' : vseg z e 1 = e := by
    ext
    · rw [vseg_fst]; exact hez.symm
    · rw [vseg_one]
  have hcl : e ∈ closure (connectedComponentIn VA z) := by
    rw [← h1']
    refine mem_closure_iff.mpr ?_
    intro U hU hx
    have hx' : vseg z e (exitTime VA z e) ∈ U := by rw [h1]; exact hx
    have hpre : vseg z e ⁻¹' U ∈ 𝓝 (1 : ℝ) := by
      rw [← h1]
      exact (vseg_continuous z e).continuousAt.preimage_mem_nhds (hU.mem_nhds hx')
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hpre
    obtain ⟨t, ht1, ht2⟩ := exists_between
      (show max 0 ((1 : ℝ) - η) < 1 by exact max_lt (by norm_num) (by linarith))
    have ht0 : 0 < t := lt_of_le_of_lt (le_max_left _ _) ht1
    have htη : (1 : ℝ) - η < t := lt_of_le_of_lt (le_max_right _ _) ht1
    have htball : t ∈ Metric.ball (1 : ℝ) η := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact ⟨vseg z e t, hηsub htball,
      vseg_lt_exitTime_mem_component hz (le_of_lt ht0) (by rw [h1]; exact ht2)⟩
  exact hnot (isOpen_inter_closure_subset_connectedComponentIn hVA hz ⟨he, hcl⟩)

/-- **Vertical first exit from the component of an interface point.**

Let `z ∈ VA` lie on the interface level (`z.2 = b - δ`), let `y₀ ∈ (a, b - δ)` be a height in the
lower band, and suppose `z` is *not* in the component of `VA` through the band point
`(z.1, y₀)` — i.e. the vertical segment from `z` down to `(z.1, y₀)`, which starts inside the
component of `z` and ends outside it, really does leave.  Then it leaves at a *first* point `p` on
that segment (same `x`-coordinate, height between `y₀` and `z.2`), and

  `p ∈ frontier (connectedComponentIn VA z) ∩ (VB \ VA)`,

the frontier conclusion coming from `frontier_connectedComponentIn_inter_subset`.  This is the
barrier point of the touching case: the wall piece `K_B` cuts the component of `z` off from the lower
band, and by saturation the barrier reaches the interface (i.e. shows up in `Ptrace`).

**Status (session 80).**  With `exitTime` defined and `vseg_exitTime_mem_closure` proved, exactly
two steps remain:

1. `vseg z e (exitTime VA z e) ∉ connectedComponentIn VA z`.  If it were in the open component, a ball
   around it would lie in the component; continuity of `vseg z e` puts `vseg z e s` in that ball for
   `s` just above `τ`, while every `t < τ` has `vseg z e t` in the component (by the sup property of
   `τ = sSup S`), so the whole `[0,s]` would lie in the component and `s ∈ S`, contradicting
   maximality of `τ`.  Here `τ ≠ 1` follows from `e ∉ component`: if `τ = 1` then `e = vseg z e 1` is
   a limit of component points, so `e ∈ closure (component) ∩ VA ⊆ component` by
   `isOpen_inter_closure_subset_connectedComponentIn` — contradiction.  (Note: this step needs
   `e ∈ VA` and `e.1 = z.1`.)
2. The verbatim call to `frontier_connectedComponentIn_inter_subset` (with the closure lemma of step
   0 = `vseg_exitTime_mem_closure` and step 1), plus `vseg_mem_Icc` / `vseg_mem_stripS` for the
   coordinate conclusions `p.1 = z.1` and `e.2 ≤ p.2 ≤ z.2`.

Technique available in the workspace for the `sSup` argument: `exit_point_mem_VB` in
`Submission/Work/Topology/Strip/exit_point.lean` (its `H` is `vseg`).  Mathlib drift note: current
`exists_lt_of_lt_csSup` takes only the nonemptiness witness and the inequality (no `BddAbove`
argument); `BddAbove` is still needed for `le_csSup`. -/
theorem exists_frontier_exit_on_vertical {a b δ : ℝ} (hδ : 0 < δ)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hcover : VA ∪ VB = stripS a b)
    {z e : ℝ × ℝ} (he : e ∈ VA) (hez : e.1 = z.1) (hez₂ : e.2 < z.2) (hea : a < e.2)
    (hz : z ∈ VA) (hzc : z.2 = b - δ) (hnot : e ∉ connectedComponentIn VA z) :
    ∃ p : ℝ × ℝ, p.1 = z.1 ∧ e.2 ≤ p.2 ∧ p.2 ≤ z.2 ∧
      p ∈ frontier (connectedComponentIn VA z) ∩ (VB \ VA) := by
  classical
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ t' ∈ Set.Icc (0 : ℝ) t, vseg z e t' ∈ connectedComponentIn VA z} with hS
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, by norm_num⟩, ?_⟩
    intro t' ht'
    have ht'0 : t' = 0 := by simpa [Set.mem_Icc] using ht'
    rw [ht'0, vseg_zero]
    simpa using mem_connectedComponentIn hz
  have hbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have hτ0 : (0 : ℝ) ≤ exitTime VA z e := by
    rw [exitTime_eq_sSup, ← hS]; exact le_csSup hbdd h0S
  have hτ1 : exitTime VA z e ≤ 1 := by
    rw [exitTime_eq_sSup, ← hS]; exact csSup_le ⟨0, h0S⟩ fun t ht => ht.1.2
  have hτlt : exitTime VA z e < 1 :=
    lt_of_le_of_ne hτ1 (exitTime_ne_one hVA hez hz he hnot)
  have hnotmem : vseg z e (exitTime VA z e) ∉ connectedComponentIn VA z :=
    fun hmem => false_of_exitTime_mem hVA hz hτlt hmem
  have hcl := vseg_exitTime_mem_closure hz hnot
  have hstrip : vseg z e (exitTime VA z e) ∈ stripS a b :=
    vseg_mem_stripS hδ hzc hea hez₂ hτ0 hτ1
  have hfr : vseg z e (exitTime VA z e) ∈ frontier (connectedComponentIn VA z) := by
    have hop : IsOpen (connectedComponentIn VA z) := hVA.connectedComponentIn
    have hfe : frontier (connectedComponentIn VA z)
        = closure (connectedComponentIn VA z) \ connectedComponentIn VA z := hop.frontier_eq
    rw [hfe]
    exact ⟨hcl, hnotmem⟩
  exact ⟨vseg z e (exitTime VA z e), vseg_fst z e _, (vseg_mem_Icc hez₂ hτ0 hτ1).1,
    (vseg_mem_Icc hez₂ hτ0 hτ1).2, hfr,
    frontier_connectedComponentIn_inter_subset hVA hcover hz ⟨hfr, hstrip⟩⟩


/-- **The barrier point, in the form the overlapping-collar case consumes it.**

This is the first step of the argument for `collared_crux`: in the branch of `interface_dichotomy`
where the `VA`-component of an interface point `z` fails to reach the lower band, take `e` to be the
point of the lower band on the vertical through `z` (so `e ∈ VA` by the band lemmas, `e.2 > a` and
`e.2 < z.2`), and `e ∉ connectedComponentIn VA z`.  Then the discharged exit lemma
(`exists_frontier_exit_on_vertical`) supplies a barrier point `p` on that vertical segment, lying in
`frontier (connectedComponentIn VA z) ∩ (VB \ VA)` — i.e. a point where the *other* wall piece cuts
the component of `z` off from its band.  By saturation the barrier reaches the interface, so it shows
up in `Ptrace`, which is the one-dimensional statement the cutting argument runs on. -/
theorem barrier_point_of_interface {a b δ : ℝ} (hδ : 0 < δ) {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hcover : VA ∪ VB = stripS a b)
    {z e : ℝ × ℝ} (he : e ∈ VA) (hez : e.1 = z.1) (hez₂ : e.2 < z.2) (hea : a < e.2)
    (hz : z ∈ VA) (hzc : z.2 = b - δ) (hnot : e ∉ connectedComponentIn VA z) :
    ∃ p : ℝ × ℝ, p.1 = z.1 ∧ e.2 ≤ p.2 ∧ p.2 ≤ z.2 ∧
      p ∈ frontier (connectedComponentIn VA z) ∩ (VB \ VA) :=
  exists_frontier_exit_on_vertical hδ hVA hcover he hez hez₂ hea hz hzc hnot

/-- **The exit segment stays between the two heights, upward version.**  For the `VB`-branch of
`interface_dichotomy` the band point `e` lies *above* the interface point `z`, so the direction-free
parametrisation `vseg z e` is used with `z.2 < e.2`; the height then lies between `z.2` and `e.2`. -/
lemma vseg_mem_Icc' {z e : ℝ × ℝ} (h : z.2 < e.2) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    z.2 ≤ (vseg z e t).2 ∧ (vseg z e t).2 ≤ e.2 := by
  constructor <;> · rw [vseg_snd]; nlinarith

/-- **The upward exit segment lies in the strip**: for `e` below the upper boundary (`e.2 < b`) and `z`
on the level `b - δ`, the whole segment `vseg z e` lies in `stripS a b`. -/
lemma vseg_mem_stripS' {a b δ : ℝ} (haδ : a < b - δ) {z e : ℝ × ℝ} (hz : z.2 = b - δ)
    (heb : e.2 < b) (hze : z.2 < e.2) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    vseg z e t ∈ stripS a b := by
  obtain ⟨hlo, hhi⟩ := vseg_mem_Icc' hze h0 h1
  refine ⟨?_, lt_of_le_of_lt hhi heb⟩
  rw [hz] at hlo
  linarith

/-- **The upward first exit** (mirror of `exists_frontier_exit_on_vertical`).  Same assembly, with the
band point `e` *above* the interface point `z` (`z.2 < e.2`, `e.2 < b`) and the level inside the strip
(`a < b - δ`); the two segment bounds are the upward ones, `vseg_mem_Icc'` and `vseg_mem_stripS'`, and
nothing else in the argument depends on the sign of `e.2 - z.2`. -/
theorem exists_frontier_exit_on_vertical' {a b δ : ℝ} (haδ : a < b - δ)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hcover : VA ∪ VB = stripS a b)
    {z e : ℝ × ℝ} (he : e ∈ VA) (hez : e.1 = z.1) (hze : z.2 < e.2) (heb : e.2 < b)
    (hz : z ∈ VA) (hzc : z.2 = b - δ) (hnot : e ∉ connectedComponentIn VA z) :
    ∃ p : ℝ × ℝ, p.1 = z.1 ∧ z.2 ≤ p.2 ∧ p.2 ≤ e.2 ∧
      p ∈ frontier (connectedComponentIn VA z) ∩ (VB \ VA) := by
  classical
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ t' ∈ Set.Icc (0 : ℝ) t, vseg z e t' ∈ connectedComponentIn VA z} with hS
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, by norm_num⟩, ?_⟩
    intro t' ht'
    have ht'0 : t' = 0 := by simpa [Set.mem_Icc] using ht'
    rw [ht'0, vseg_zero]
    simpa using mem_connectedComponentIn hz
  have hbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have hτ0 : (0 : ℝ) ≤ exitTime VA z e := by
    rw [exitTime_eq_sSup, ← hS]; exact le_csSup hbdd h0S
  have hτ1 : exitTime VA z e ≤ 1 := by
    rw [exitTime_eq_sSup, ← hS]; exact csSup_le ⟨0, h0S⟩ fun t ht => ht.1.2
  have hτlt : exitTime VA z e < 1 :=
    lt_of_le_of_ne hτ1 (exitTime_ne_one hVA hez hz he hnot)
  have hnotmem : vseg z e (exitTime VA z e) ∉ connectedComponentIn VA z :=
    fun hmem => false_of_exitTime_mem hVA hz hτlt hmem
  have hcl := vseg_exitTime_mem_closure hz hnot
  have hstrip : vseg z e (exitTime VA z e) ∈ stripS a b :=
    vseg_mem_stripS' haδ hzc heb hze hτ0 hτ1
  have hfr : vseg z e (exitTime VA z e) ∈ frontier (connectedComponentIn VA z) := by
    have hop : IsOpen (connectedComponentIn VA z) := hVA.connectedComponentIn
    have hfe : frontier (connectedComponentIn VA z)
        = closure (connectedComponentIn VA z) \ connectedComponentIn VA z := hop.frontier_eq
    rw [hfe]
    exact ⟨hcl, hnotmem⟩
  exact ⟨vseg z e (exitTime VA z e), vseg_fst z e _, (vseg_mem_Icc' hze hτ0 hτ1).1,
    (vseg_mem_Icc' hze hτ0 hτ1).2, hfr,
    frontier_connectedComponentIn_inter_subset hVA hcover hz ⟨hfr, hstrip⟩⟩

/-- **The barrier point, upward (`VB`-branch of `interface_dichotomy`).**  Mirror of
`barrier_point_of_interface`: here the band point `e` lies above the interface point `z`, and the
barrier point `p` supplied by the upward exit lemma lies on the vertical segment between them, in
`frontier (connectedComponentIn VA z) ∩ (VB \ VA)`. -/
theorem barrier_point_of_interface' {a b δ : ℝ} (haδ : a < b - δ) {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hcover : VA ∪ VB = stripS a b)
    {z e : ℝ × ℝ} (he : e ∈ VA) (hez : e.1 = z.1) (hze : z.2 < e.2) (heb : e.2 < b)
    (hz : z ∈ VA) (hzc : z.2 = b - δ) (hnot : e ∉ connectedComponentIn VA z) :
    ∃ p : ℝ × ℝ, p.1 = z.1 ∧ z.2 ≤ p.2 ∧ p.2 ≤ e.2 ∧
      p ∈ frontier (connectedComponentIn VA z) ∩ (VB \ VA) :=
  exists_frontier_exit_on_vertical' haδ hVA hcover he hez hze heb hz hzc hnot

/-- **Step (ii), first piece: the barrier's accumulation lies in the wall.**

The barrier of `barrier_point_of_interface` / `barrier_point_of_interface'` is a point of
`frontier (connectedComponentIn VA z) ∩ Ω`, and `frontier_connectedComponentIn_inter_subset` puts the
whole frontier inside `Ω` into the complementary wall `VB \ VA`.  Since that wall is *saturated*
(`saturated_of_open_cover`), its closure inside `Ω` is itself; hence not only the barrier point but all
its `Ω`-accumulation lies in the wall.  This is the hinge that upgrades "the barrier is a frontier
point" into "the barrier is a closed-in-`Ω` piece of the wall", which is what
`closure_Ptrace_inter_subset` / `closure_Qtrace_inter_subset` consume to capture its interface trace. -/
theorem closure_frontier_inter_subset_sdiff {a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hcover : VA ∪ VB = stripS a b) {z : ℝ × ℝ} (hz : z ∈ VA) :
    closure (frontier (connectedComponentIn VA z) ∩ stripS a b) ∩ stripS a b ⊆ VB \ VA := by
  have hsub : frontier (connectedComponentIn VA z) ∩ stripS a b ⊆ VB \ VA :=
    frontier_connectedComponentIn_inter_subset hVA hcover hz
  have hcl : closure (frontier (connectedComponentIn VA z) ∩ stripS a b) ⊆ closure (VB \ VA) :=
    closure_mono hsub
  obtain ⟨-, hB, -, -⟩ := saturated_of_open_cover (a := a) (b := b) hVA hVB hcover
  intro q hq
  exact hB ⟨hcl hq.1, hq.2⟩

/-- **The barrier-to-trace passage in the touching case.**  If the collars touch
(`a + ε = b - δ`), then the barrier point of `barrier_point_of_interface` — which lies on the vertical
through the interface point `z`, below `z`, and in the wall `VB \ VA` — has height *exactly* `b - δ`:
it is at most `z.2 = b - δ` (it lies on the segment) and at least `a + ε = b - δ` (it lies in the wall
piece whose heights are `≥ a + ε`).  So the barrier point lies on the interface level and, being in
`VB \ VA`, is a point of `Qtrace b δ VA VB`.

This is the trace passage the one-dimensional cutting argument consumes: in the `VA`-branch of
`interface_dichotomy` the barrier is a point of the interface belonging to the *other* wall `K_B`,
i.e. to the trace `Q`. -/
theorem exists_mem_Qtrace_of_barrier {a b δ ε : ℝ} (hδ : 0 < δ) (htouch : a + ε = b - δ)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hcover : VA ∪ VB = stripS a b)
    (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    {z e : ℝ × ℝ} (he : e ∈ VA) (hez : e.1 = z.1) (hez₂ : e.2 < z.2) (hea : a < e.2)
    (hz : z ∈ VA) (hzc : z.2 = b - δ) (hnot : e ∉ connectedComponentIn VA z) :
    ∃ p : ℝ × ℝ, p.1 = z.1 ∧ p ∈ Qtrace b δ VA VB := by
  obtain ⟨p, hp1, -, hpz, -, hpK⟩ :=
    barrier_point_of_interface hδ hVA hcover he hez hez₂ hea hz hzc hnot
  have hge : a + ε ≤ p.2 := hKB hpK
  rw [htouch] at hge
  exact ⟨p, hp1, by linarith, hpK.1, hpK.2⟩

/-- **The barrier-to-trace passage, `VB`-branch.**  Mirror of `exists_mem_Qtrace_of_barrier`: in the
`VB`-branch of `interface_dichotomy` the barrier is a point of `frontier (connectedComponentIn VB z)`
lying in the *other* wall `VA \ VB`, whose heights are `≤ b - δ`; it also has height `≥ z.2 = b - δ`,
so its height is exactly `b - δ` — and being in `VA \ VB` it is a point of `Ptrace b δ VA VB`.  (No
touching hypothesis is needed here: the two bounds `z.2 = b - δ` and `≤ b - δ` already coincide.) -/
theorem exists_mem_Ptrace_of_barrier' {a b δ : ℝ} (haδ : a < b - δ)
    {VA VB : Set (ℝ × ℝ)} (hVB : IsOpen VB) (hcover : VA ∪ VB = stripS a b)
    (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    {z e : ℝ × ℝ} (he : e ∈ VB) (hez : e.1 = z.1) (hze : z.2 < e.2) (heb : e.2 < b)
    (hz : z ∈ VB) (hzc : z.2 = b - δ) (hnot : e ∉ connectedComponentIn VB z) :
    ∃ p : ℝ × ℝ, p.1 = z.1 ∧ p ∈ Ptrace b δ VA VB := by
  have hcover' : VB ∪ VA = stripS a b := by rw [Set.union_comm]; exact hcover
  obtain ⟨p, hp1, hpz, -, -, hpK⟩ :=
    barrier_point_of_interface' (VA := VB) (VB := VA) haδ hVB hcover' he hez hze heb hz hzc hnot
  have hle : p.2 ≤ b - δ := hKA hpK
  exact ⟨p, hp1, by linarith, hpK.1, hpK.2⟩

/-- **The band point on the vertical through `z`.**  For `z` on the interface level, the point
`e := (z.1, (a + b - δ)/2)` shares `z`'s `x`-coordinate and lies strictly between the lower boundary
`a` and the level `z.2 = b - δ` — so, by the band lemmas, `e ∈ VA` and `e.2 < z.2`, which is what the
first branch of the `interface_cutting` assembly feeds to `exists_mem_Qtrace_of_barrier`. -/
lemma band_point_props {a b δ : ℝ} (haδ : a < b - δ) {z : ℝ × ℝ} (hzc : z.2 = b - δ) :
    a < ((z.1, (a + b - δ) / 2) : ℝ × ℝ).2 ∧
      ((z.1, (a + b - δ) / 2) : ℝ × ℝ).2 < z.2 ∧
      ((z.1, (a + b - δ) / 2) : ℝ × ℝ).1 = z.1 :=
  ⟨by linarith, by linarith, rfl⟩


/-- **Step (iii): the interface cutting statement.**  In the touching case (`a + ε = b - δ`), under the
failure of the crux, every point `z` of the open invariant part `R = {q.2 = b - δ} ∩ VA ∩ VB` of the
interface level is *cut* by one of the two trace pieces: there is a point of `Qtrace` on the vertical
through `z` (the `VA`-branch of `interface_dichotomy`, barrier in the wall `VB \ VA`) or a point of
`Ptrace` on that vertical (the `VB`-branch, barrier in `VA \ VB`).

This is the one-dimensional statement that the touching case reduces to: it involves only the two
disjoint, `T`-periodic, closed traces `P = Ptrace`, `Q = Qtrace` on the interface line (`interface_traces`,
`closure_Ptrace_inter_subset`, `closure_Qtrace_inter_subset`) and the open invariant complement part
`R`, whose points are cut as above.  The first line of the assembly is
`interface_dichotomy (p := p) hab hεb hbδa hVA hVB hperA hperB hcover hKA hKB hno hzA hzB
hzc.le hzc.ge`, where `hab : a < b`, `hεb : a + ε ≤ b` and `hbδa : a ≤ b - δ` are derived from
`hδ` and `htouch`; it hands back the disjunction "the `VA`-component of `z` misses the lower band or
the `VB`-component misses the upper band".  Its other inputs are `interface_dichotomy` the two band inclusions (supplied by the collared hypotheses through
`level_subset_left_of_collar` / `level_subset_right_of_collar` and
`band_subset_Ess_of_collar`), and the trace passages `exists_mem_Qtrace_of_barrier` /
`exists_mem_Ptrace_of_barrier'`. -/
theorem interface_cutting {a b δ ε : ℝ} (hδ : 0 < δ) (haδ : a < b - δ)
    (htouch : a + ε = b - δ)
    {p : ℝ} {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hno : Ess p VA ∩ Ess p VB = ∅)
    (hbandA : ∀ q : ℝ × ℝ, a < q.2 → q.2 < b - δ → q ∈ VA)
    (hbandB : ∀ q : ℝ × ℝ, b - δ < q.2 → q.2 < b → q ∈ VB)
    {z : ℝ × ℝ} (hzA : z ∈ VA) (hzB : z ∈ VB) (hzc : z.2 = b - δ) :
    (∃ q : ℝ × ℝ, q.1 = z.1 ∧ q ∈ Qtrace b δ VA VB) ∨
    (∃ q : ℝ × ℝ, q.1 = z.1 ∧ q ∈ Ptrace b δ VA VB) := by
  have hab : a < b := by linarith
  have hεb : a + ε ≤ b := by linarith
  have hbδa : a ≤ b - δ := le_of_lt haδ
  have hdich := interface_dichotomy (p := p) hab hεb hbδa hVA hVB hperA hperB hcover hKA hKB
    hno hzA hzB (le_of_eq hzc.symm) (by rw [hzc]; linarith)
  rcases hdich with hmissA | hmissB
  · obtain ⟨he1, he2, he3⟩ := band_point_props haδ hzc
    obtain ⟨q, hq1, hqQ⟩ := exists_mem_Qtrace_of_barrier hδ htouch hVA hcover hKB
      (hbandA _ he1 (hzc ▸ he2)) he3 he2 he1 hzA hzc
      (fun hmem => by
        have hmem' : ((z.1, (a + b - δ) / 2) : ℝ × ℝ) ∈
            connectedComponentIn VA z ∩ {q : ℝ × ℝ | a < q.2 ∧ q.2 < a + ε} :=
          ⟨hmem, he1, by linarith⟩
        rw [hmissA] at hmem'
        exact hmem')
    exact Or.inl ⟨q, hq1, hqQ⟩
  · have he : ((z.1, (b - δ + b) / 2) : ℝ × ℝ) ∈ VB :=
      hbandB _ (by linarith) (by linarith)
    obtain ⟨q, hq1, hqQ⟩ := exists_mem_Ptrace_of_barrier' (z := z) haδ hVB hcover hKA
      he rfl (by rw [hzc]; linarith) (by linarith) hzB hzc
      (fun hmem => by
        have hmem' : ((z.1, (b - δ + b) / 2) : ℝ × ℝ) ∈
            connectedComponentIn VB z ∩ {q : ℝ × ℝ | b - δ < q.2 ∧ q.2 < b} :=
          ⟨hmem, by linarith, by linarith⟩
        rw [hmissB] at hmem'
        exact hmem')
    exact Or.inr ⟨q, hq1, hqQ⟩


/-! ### Session 68: the **touching** (height-separated) case of the collared crux is proved

The new theorem of this session is `collared_crux_touching`: the collared crux in the case
`a + ε = b - δ`, i.e. when the two wall pieces `K_A = VA \ VB` and `K_B = VB \ VA` are **separated by
a horizontal level** (`K_A` below the level `b - δ`, `K_B` above it).  This case — the "no gap"
endpoint of the shrinkage calculus — is proved here from the interface cutting statement
(`interface_cutting`) together with one elementary one-dimensional fact
(`level_met_of_meets_between`): the set of heights attained by a closed-in-the-strip, `T`-invariant
set is closed, so if it contains an interval `(α,β)` it contains `[α,β]`.

The strict-overlap case `a + ε < b - δ` is isolated as `collared_crux_overlap`; it is the genuinely
hard case (and, in the shrinkage calculus of `NOTES_annulus_duality_open.md`, the generic one).

The **shape of the proof in the touching case** is worth recording, since the same skeleton is what
the strict-overlap case has to generalise.  Under the failure of the crux (`hno`) the interface level
`L = {q.2 = b - δ}` is partitioned as `P ⊔ Q ⊔ R`, with `P = L ∩ (VA \ VB)`, `Q = L ∩ (VB \ VA)` and
`R = L ∩ VA ∩ VB`.  `interface_cutting` gives `R = ∅` (its conclusion puts a point of `Q` or of `P`
*on the vertical through `z`, hence at `z` itself*, which contradicts `z ∈ VA ∩ VB`).  Then `L = P ⊔ Q`
with both pieces closed in `L` (saturation), and `L` is connected, so `L ⊆ P` or `L ⊆ Q`.  Say
`L ⊆ P`: then `K_B = VB \ VA` misses `L` and lies strictly above it.  But `K_B` is closed in the strip
and meets *every* level of `(b - δ, b)` (otherwise that level would be a free level, giving the crux
by `crux_conclusion_of_free_level`), so by `level_met_of_meets_between` it would meet `L` — a
contradiction.  The case `L ⊆ Q` is symmetric, with `K_A` and the levels below `b - δ`.
-/

/-- **Every point has an integer translate with `x`-coordinate in `[0,p]`** (`p > 0`): take
`k = ⌈-q.1/p⌉`. -/
lemma exists_Tz_mem_Icc {p : ℝ} (hp : 0 < p) (q : ℝ × ℝ) :
    ∃ k : ℤ, (Tz p k q).1 ∈ Set.Icc (0 : ℝ) p := by
  refine ⟨⌈-q.1 / p⌉, ?_, ?_⟩
  · have h1 : -q.1 / p ≤ ((⌈-q.1 / p⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h2 : (0 : ℝ) ≤ q.1 + ((⌈-q.1 / p⌉ : ℤ) : ℝ) * p := by
      have h3 : -q.1 / p * p ≤ ((⌈-q.1 / p⌉ : ℤ) : ℝ) * p :=
        mul_le_mul_of_nonneg_right h1 hp.le
      rw [div_mul_cancel₀ _ (ne_of_gt hp)] at h3
      linarith
    show (0 : ℝ) ≤ (Tz p ⌈-q.1 / p⌉ q).1
    simp only [Tz]
    exact h2
  · have h1 : (((⌈-q.1 / p⌉ : ℤ)) : ℝ) < -q.1 / p + 1 := Int.ceil_lt_add_one _
    have h2 : q.1 + ((⌈-q.1 / p⌉ : ℤ) : ℝ) * p ≤ p := by
      have h3 : ((⌈-q.1 / p⌉ : ℤ) : ℝ) * p < (-q.1 / p + 1) * p :=
        mul_lt_mul_of_pos_right h1 hp
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul] at h3
      linarith
    show (Tz p ⌈-q.1 / p⌉ q).1 ≤ p
    simp only [Tz]
    exact h2

/-- **Levels between two met levels are met.**  Let `K` be a subset of the open strip `stripS a b`
which is *closed in the strip* (`closure K ∩ stripS a b ⊆ K`) and invariant under the periodic
translation `Tmap p` (`p > 0`).  If `K` meets every horizontal level `α < t < β` for some
`a < α < β < b`, then `K` meets every level `α ≤ t ≤ β`.

The point is that the set of attained heights is closed: it is the image of the *compact* set
`K ∩ ([0,p] × [α,β])` under the height projection (`T`-invariance moves every point of `K` into the
`x`-box), and it already contains the dense set `(α,β)`. -/
lemma level_met_of_meets_between {p a b : ℝ} (hp : 0 < p) {K : Set (ℝ × ℝ)}
    (hKsub : K ⊆ stripS a b) (hKcl : closure K ∩ stripS a b ⊆ K)
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ Tmap p q ∈ K)
    {α β : ℝ} (hα : a < α) (hαβ : α < β) (hβ : β < b)
    (hmeet : ∀ t : ℝ, α < t → t < β → ∃ q : ℝ × ℝ, q ∈ K ∧ q.2 = t) :
    ∀ t : ℝ, α ≤ t → t ≤ β → ∃ q : ℝ × ℝ, q ∈ K ∧ q.2 = t := by
  set C : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) p ×ˢ Set.Icc α β with hCdef
  have hCcl : IsClosed C := isClosed_Icc.prod isClosed_Icc
  have hCcp : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hCsub : C ⊆ stripS a b := by
    rintro q ⟨hq1, hq2⟩
    exact ⟨lt_of_lt_of_le hα hq2.1, lt_of_le_of_lt hq2.2 hβ⟩
  have hKC : K ∩ C = closure K ∩ C := by
    ext q
    exact ⟨fun h => ⟨subset_closure h.1, h.2⟩,
      fun h => ⟨hKcl ⟨h.1, hCsub h.2⟩, h.2⟩⟩
  have hKcp : IsCompact (K ∩ C) := by
    rw [hKC]
    exact hCcp.of_isClosed_subset (isClosed_closure.inter hCcl) Set.inter_subset_right
  have hHcl : IsClosed ((fun q : ℝ × ℝ => q.2) '' (K ∩ C)) :=
    (hKcp.image continuous_snd).isClosed
  have hsub : Set.Ioo α β ⊆ (fun q : ℝ × ℝ => q.2) '' (K ∩ C) := by
    rintro t ⟨ht1, ht2⟩
    obtain ⟨q, hqK, hqt⟩ := hmeet t ht1 ht2
    obtain ⟨k, hk⟩ := exists_Tz_mem_Icc hp q
    refine ⟨Tz p k q, ⟨(Tz_mem_iff hper k q).mpr hqK, hk, ?_, ?_⟩, ?_⟩
    · show α ≤ (Tz p k q).2
      rw [show (Tz p k q).2 = q.2 from rfl, hqt]; exact le_of_lt ht1
    · show (Tz p k q).2 ≤ β
      rw [show (Tz p k q).2 = q.2 from rfl, hqt]; exact le_of_lt ht2
    · show (Tz p k q).2 = t
      rw [show (Tz p k q).2 = q.2 from rfl, hqt]
  intro t ht1 ht2
  have ht : t ∈ closure (Set.Ioo α β) := by
    rw [closure_Ioo hαβ.ne]; exact ⟨ht1, ht2⟩
  obtain ⟨q, ⟨hqK, -⟩, hqt⟩ := closure_minimal hsub hHcl ht
  exact ⟨q, hqK, hqt⟩

/-- **The attained heights (over an `x`-box) of a set closed in the strip are closed.**

If `K ⊆ stripS a b` is closed in the strip (`closure K ∩ stripS a b ⊆ K`) and `a < α`, `β < b`, then
`{q.2 : q ∈ K, q.1 ∈ [0,p]}` is a closed subset of `ℝ`: it is the image of the compact set
`K ∩ ([0,p] × [α,β])` under the (continuous) height projection, and `K ∩ ([0,p]×[α,β])` is compact
because it equals `closure K ∩ ([0,p]×[α,β])` and `[0,p]×[α,β] ⊆ stripS a b`.

This is the engine of `level_met_of_meets_between` and of the "missed levels are open" statement
below. -/
lemma isClosed_image_height {a b : ℝ} {K : Set (ℝ × ℝ)}
    (hKsub : K ⊆ stripS a b) (hKcl : closure K ∩ stripS a b ⊆ K)
    {p α β : ℝ} (hα : a < α) (hβ : β < b) :
    IsClosed ((fun q : ℝ × ℝ => q.2) '' (K ∩ (Set.Icc (0 : ℝ) p ×ˢ Set.Icc α β))) := by
  set C : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) p ×ˢ Set.Icc α β with hCdef
  have hCcl : IsClosed C := isClosed_Icc.prod isClosed_Icc
  have hCsub : C ⊆ stripS a b := by
    rintro q ⟨hq1, hq2⟩
    exact ⟨lt_of_lt_of_le hα hq2.1, lt_of_le_of_lt hq2.2 hβ⟩
  have hKC : K ∩ C = closure K ∩ C := by
    ext q
    exact ⟨fun h => ⟨subset_closure h.1, h.2⟩,
      fun h => ⟨hKcl ⟨h.1, hCsub h.2⟩, h.2⟩⟩
  have hcp : IsCompact (K ∩ C) := by
    rw [hKC]
    exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      (isClosed_closure.inter hCcl) Set.inter_subset_right
  exact (hcp.image continuous_snd).isClosed

/-- **A level missed by a closed-in-the-strip `T`-invariant set is missed on a whole band.**

Let `K ⊆ stripS a b` be closed in the strip and `T`-invariant (`p > 0`), and let `K` avoid the
horizontal level `{q.2 = t}` (`a < t < b`).  Then there is `ε > 0` such that `K` avoids *every*
level `|s - t| < ε`.

This is the complement of the closedness statement `isClosed_image_height` combined with
`T`-invariance (which moves every point of `K` into the `x`-box `[0,p]`).  It is the sharp
structural statement behind the failure hypothesis of the crux: under that hypothesis the two sets
`E_A = {t : K_A misses the level t}` and `E_B = {t : K_B misses the level t}` are **open** and
disjoint (a level missed by both is a free level, which gives the crux by
`crux_conclusion_of_free_level`), so `(a,b) = E_A ⊔ E_B ⊔ F` with `F` closed — the sharpening of the
residual recorded in the status block. -/
lemma exists_band_free_of_misses_level {p a b : ℝ} (hp : 0 < p) {K : Set (ℝ × ℝ)}
    (hKsub : K ⊆ stripS a b) (hKcl : closure K ∩ stripS a b ⊆ K)
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ Tmap p q ∈ K)
    {t : ℝ} (hat : a < t) (htb : t < b) (hmiss : ∀ x : ℝ, ((x, t) : ℝ × ℝ) ∉ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε → ∀ x : ℝ, ((x, s) : ℝ × ℝ) ∉ K := by
  set α : ℝ := (a + t) / 2 with hαdef
  set β : ℝ := (t + b) / 2 with hβdef
  have haα : a < α := by rw [hαdef]; linarith
  have hαt : α < t := by rw [hαdef]; linarith
  have htb' : t < β := by rw [hβdef]; linarith
  have hβb : β < b := by rw [hβdef]; linarith
  have hcl := isClosed_image_height (p := p) hKsub hKcl haα hβb
  have hnotmem : t ∉ (fun q : ℝ × ℝ => q.2) ''
      (K ∩ (Set.Icc (0 : ℝ) p ×ˢ Set.Icc α β)) := by
    rintro ⟨q, ⟨hqK, -, -⟩, hqt⟩
    have h1 : ((q.1, q.2) : ℝ × ℝ) ∈ K := (Prod.eta q).symm ▸ hqK
    have h2 : q.2 = t := hqt
    rw [h2] at h1
    exact hmiss q.1 h1
  have hopen : IsOpen ((fun q : ℝ × ℝ => q.2) ''
      (K ∩ (Set.Icc (0 : ℝ) p ×ˢ Set.Icc α β)))ᶜ := hcl.isOpen_compl
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Metric.mem_nhds_iff.mp
    (hopen.mem_nhds hnotmem)
  refine ⟨min ε₀ (min (t - α) (β - t)), lt_min hε₀pos (lt_min (by linarith) (by linarith)), ?_⟩
  intro s hs x hsx
  have hsH : s ∉ (fun q : ℝ × ℝ => q.2) '' (K ∩ (Set.Icc (0 : ℝ) p ×ˢ Set.Icc α β)) := by
    have h1 : |s - t| < ε₀ := lt_of_lt_of_le hs (min_le_left _ _)
    have h2 : dist s t < ε₀ := by rw [Real.dist_eq]; exact h1
    exact hε₀ (Metric.mem_ball.mpr h2)
  have hsα : α ≤ s := by
    have h1 : |s - t| < t - α := lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [abs_lt] at h1
    linarith [h1.1]
  have hsβ : s ≤ β := by
    have h1 : |s - t| < β - t := lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [abs_lt] at h1
    linarith [h1.2]
  obtain ⟨k, hk⟩ := exists_Tz_mem_Icc hp ((x, s) : ℝ × ℝ)
  have hmem : (Tz p k ((x, s) : ℝ × ℝ)).2 = s := rfl
  have hmemK : Tz p k ((x, s) : ℝ × ℝ) ∈ K := (Tz_mem_iff hper k _).mpr hsx
  exact hsH ⟨Tz p k ((x, s) : ℝ × ℝ),
    ⟨hmemK, hk, by rw [hmem]; exact hsα, by rw [hmem]; exact hsβ⟩, hmem⟩

/-- **The collared crux in the *touching* case `a + ε = b - δ`** — equivalently, the crux when the
two wall pieces `K_A = VA \ VB` and `K_B = VB \ VA` are separated by a horizontal level (if
`K_A ⊆ {·.2 ≤ e}` and `K_B ⊆ {·.2 ≥ e}` for some `a < e < b`, then automatically `VA ⊇ {·.2 < e}` and
`VB ⊇ {·.2 > e}`, so this is exactly the hypothesis package below with `e = b - δ = a + ε`). -/
theorem collared_crux_touching {p a b δ ε : ℝ} (hp : 0 < p) (hab : a < b)
    (hδ : 0 < δ) (hε : 0 < ε) (htouch : a + ε = b - δ)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ stripS a b) (hsubB : VB ⊆ stripS a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z)) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (Tmap p z) ∧ JoinedIn VB z (Tmap p z) := by
  by_contra hcon
  have hno : Ess p VA ∩ Ess p VB = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzA, hzB⟩
    rw [mem_Ess] at hzA hzB
    exact hcon ⟨z, ⟨hzA.1, hzB.1⟩, hzA.2, hzB.2⟩
  have haδ : a < b - δ := by linarith
  have hc2 : b - δ < b := by linarith
  -- the two band inclusions: everything below the interface level is in `VA`, everything above in `VB`
  have hbandA : ∀ q : ℝ × ℝ, a < q.2 → q.2 < b - δ → q ∈ VA := by
    intro q h1 h2
    have hqΩ : q ∈ VA ∪ VB := hcover.symm ▸ (⟨h1, lt_trans h2 hc2⟩ : q ∈ stripS a b)
    rcases hqΩ with h | h
    · exact h
    · by_contra hqA
      have hge : a + ε ≤ q.2 := hKB ⟨h, hqA⟩
      rw [htouch] at hge
      linarith
  have hbandB : ∀ q : ℝ × ℝ, b - δ < q.2 → q.2 < b → q ∈ VB := by
    intro q h1 h2
    have hqΩ : q ∈ VA ∪ VB := hcover.symm ▸ (⟨lt_trans haδ h1, h2⟩ : q ∈ stripS a b)
    rcases hqΩ with h | h
    · by_contra hqB
      have hle : q.2 ≤ b - δ := hKA ⟨h, hqB⟩
      linarith
    · exact h
  -- `interface_cutting` kills the interface points lying in both sets
  have hcut : ∀ z : ℝ × ℝ, z.2 = b - δ → z ∈ VA → z ∈ VB → False := by
    intro z hzc hzA hzB
    rcases interface_cutting (p := p) hδ haδ htouch hVA hVB hperA hperB hcover hKA hKB hno
        hbandA hbandB hzA hzB hzc with ⟨q, hq1, hqQ⟩ | ⟨q, hq1, hqP⟩
    · have hqz : q = z := Prod.ext hq1 (by rw [hqQ.1, hzc])
      exact hqQ.2.2 (hqz ▸ hzA)
    · have hqz : q = z := Prod.ext hq1 (by rw [hqP.1, hzc])
      exact hqP.2.2 (hqz ▸ hzB)
  -- so the interface level is the disjoint union of the two traces
  have hPQ : ∀ x : ℝ, ((x, b - δ) : ℝ × ℝ) ∈ Ptrace b δ VA VB ∪ Qtrace b δ VA VB := by
    intro x
    have hxΩ : ((x, b - δ) : ℝ × ℝ) ∈ VA ∪ VB :=
      hcover.symm ▸ (⟨haδ, hc2⟩ : ((x, b - δ) : ℝ × ℝ) ∈ stripS a b)
    rcases hxΩ with h | h
    · by_cases hB : ((x, b - δ) : ℝ × ℝ) ∈ VB
      · exact absurd hB (hcut _ rfl h)
      · exact Or.inl ⟨rfl, h, hB⟩
    · by_cases hA : ((x, b - δ) : ℝ × ℝ) ∈ VA
      · exact absurd h (hcut _ rfl hA)
      · exact Or.inr ⟨rfl, h, hA⟩
  have hlevelpre : IsPreconnected {q : ℝ × ℝ | q.2 = b - δ} := by
    have h : {q : ℝ × ℝ | q.2 = b - δ} = (fun x : ℝ => ((x, b - δ) : ℝ × ℝ)) '' Set.univ := by
      ext q
      constructor
      · intro hq
        exact ⟨q.1, trivial, by rw [← hq]⟩
      · rintro ⟨x, -, rfl⟩
        rfl
    rw [h]
    exact isPreconnected_univ.image _ (by fun_prop)
  have hdisj : {q : ℝ × ℝ | q.2 = b - δ} ∩
      (closure (Ptrace b δ VA VB) ∩ closure (Qtrace b δ VA VB)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hq, hqP, hqQ⟩
    have hq2 : q.2 = b - δ := hq
    have hqS : q ∈ stripS a b := by
      show a < q.2 ∧ q.2 < b
      rw [hq2]; exact ⟨haδ, hc2⟩
    have hP : q ∈ Ptrace b δ VA VB := closure_Ptrace_inter_subset hVA hVB hcover ⟨hqP, hqS⟩
    have hQ : q ∈ Qtrace b δ VA VB := closure_Qtrace_inter_subset hVA hVB hcover ⟨hqQ, hqS⟩
    have hdis : Disjoint (Ptrace b δ VA VB) (Qtrace b δ VA VB) := by
      rw [Set.disjoint_left]
      intro w hwP hwQ
      exact hwP.2.2 hwQ.2.1
    exact Set.disjoint_left.mp hdis hP hQ
  have hcoverPQ : {q : ℝ × ℝ | q.2 = b - δ} ⊆
      closure (Ptrace b δ VA VB) ∪ closure (Qtrace b δ VA VB) := by
    intro q hq
    have hmem : ((q.1, b - δ) : ℝ × ℝ) ∈ Ptrace b δ VA VB ∪ Qtrace b δ VA VB := hPQ q.1
    have hqeq : ((q.1, b - δ) : ℝ × ℝ) = q := by rw [← hq]
    rw [hqeq] at hmem
    exact Set.union_subset_union subset_closure subset_closure hmem
  have hlevelsub : {q : ℝ × ℝ | q.2 = b - δ} ⊆ closure (Ptrace b δ VA VB) ∨
      {q : ℝ × ℝ | q.2 = b - δ} ⊆ closure (Qtrace b δ VA VB) :=
    (isPreconnected_iff_subset_of_disjoint_closed.mp hlevelpre)
      (closure (Ptrace b δ VA VB)) (closure (Qtrace b δ VA VB))
      isClosed_closure isClosed_closure hcoverPQ hdisj
  rcases hlevelsub with hlevP | hlevQ
  · -- the whole level lies in `VA \ VB`: `K_B` lives strictly above it and yet must meet it
    have hKBlev : ∀ x : ℝ, ((x, b - δ) : ℝ × ℝ) ∉ VB \ VA := by
      intro x hx
      have hmem : ((x, b - δ) : ℝ × ℝ) ∈ closure (Ptrace b δ VA VB) := hlevP rfl
      have hxS : ((x, b - δ) : ℝ × ℝ) ∈ stripS a b := ⟨haδ, hc2⟩
      exact (closure_Ptrace_inter_subset hVA hVB hcover ⟨hmem, hxS⟩).2.2 hx.1
    have hKBhigh : VB \ VA ⊆ {q : ℝ × ℝ | b - δ < q.2} := by
      intro q hq
      have hge : a + ε ≤ q.2 := hKB hq
      rw [htouch] at hge
      rcases lt_or_eq_of_le hge with h | h
      · exact h
      · exact absurd (show ((q.1, b - δ) : ℝ × ℝ) ∈ VB \ VA from
          (Prod.eta q).symm ▸ (by rw [h]; exact hq)) (hKBlev q.1)
    have hperKB : ∀ q : ℝ × ℝ, q ∈ VB \ VA ↔ Tmap p q ∈ VB \ VA := by
      intro q
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(hperB q).mp h1, fun hc => h2 ((hperA q).mpr hc)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(hperB q).mpr h1, fun hc => h2 ((hperA q).mp hc)⟩
    have hKBmeet : ∀ t : ℝ, b - δ < t → t < b → ∃ q : ℝ × ℝ, q ∈ VB \ VA ∧ q.2 = t := by
      intro t h1 h2
      by_contra hbad
      push Not at hbad
      exact hcon (crux_conclusion_of_free_level (p := p) (c := t) (by linarith) h2 hcover
        (fun x => by
          rintro (⟨hxA, hxB⟩ | ⟨hxB, hxA⟩)
          · exact absurd (hKA ⟨hxA, hxB⟩ : ((x, t) : ℝ × ℝ).2 ≤ b - δ) (not_le.mpr h1)
          · exact hbad _ ⟨hxB, hxA⟩ rfl))
    have hmid1 : b - δ < (b - δ + b) / 2 := by linarith
    have hmid2 : (b - δ + b) / 2 < b := by linarith
    obtain ⟨q, hqK, hqt⟩ := level_met_of_meets_between (K := VB \ VA) hp
      (fun q hq => hsubB hq.1) (saturated_of_open_cover hVA hVB hcover).2.1 hperKB
      haδ hmid1 hmid2 (fun t h1 h2 => hKBmeet t h1 (lt_trans h2 hmid2)) (b - δ) le_rfl
      (le_of_lt hmid1)
    have hmem : ((q.1, b - δ) : ℝ × ℝ) ∈ VB \ VA := by
      have h1 : ((q.1, q.2) : ℝ × ℝ) ∈ VB \ VA := (Prod.eta q).symm ▸ hqK
      rwa [hqt] at h1
    exact hKBlev q.1 hmem
  · -- symmetric: the whole level lies in `VB \ VA`, and `K_A` must meet it from below
    have hKAlev : ∀ x : ℝ, ((x, b - δ) : ℝ × ℝ) ∉ VA \ VB := by
      intro x hx
      have hmem : ((x, b - δ) : ℝ × ℝ) ∈ closure (Qtrace b δ VA VB) := hlevQ rfl
      have hxS : ((x, b - δ) : ℝ × ℝ) ∈ stripS a b := ⟨haδ, hc2⟩
      exact (closure_Qtrace_inter_subset hVA hVB hcover ⟨hmem, hxS⟩).2.2 hx.1
    have hKAlow : VA \ VB ⊆ {q : ℝ × ℝ | q.2 < b - δ} := by
      intro q hq
      have hle : q.2 ≤ b - δ := hKA hq
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (show ((q.1, b - δ) : ℝ × ℝ) ∈ VA \ VB from by
          have h1 : ((q.1, q.2) : ℝ × ℝ) ∈ VA \ VB := (Prod.eta q).symm ▸ hq
          rwa [h] at h1) (hKAlev q.1)
    have hperKA : ∀ q : ℝ × ℝ, q ∈ VA \ VB ↔ Tmap p q ∈ VA \ VB := by
      intro q
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(hperA q).mp h1, fun hc => h2 ((hperB q).mpr hc)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(hperA q).mpr h1, fun hc => h2 ((hperB q).mp hc)⟩
    have hKAmeet : ∀ t : ℝ, a < t → t < b - δ → ∃ q : ℝ × ℝ, q ∈ VA \ VB ∧ q.2 = t := by
      intro t h1 h2
      by_contra hbad
      push Not at hbad
      exact hcon (crux_conclusion_of_free_level (p := p) (c := t) h1 (lt_trans h2 hc2) hcover
        (fun x => by
          rintro (⟨hxA, hxB⟩ | ⟨hxB, hxA⟩)
          · exact hbad _ ⟨hxA, hxB⟩ rfl
          · exact absurd (hKB ⟨hxB, hxA⟩ : a + ε ≤ ((x, t) : ℝ × ℝ).2)
              (by rw [htouch]; exact not_le.mpr h2)))
    have hmid1 : a < (a + (b - δ)) / 2 := by linarith
    have hmid2 : (a + (b - δ)) / 2 < b - δ := by linarith
    obtain ⟨q, hqK, hqt⟩ := level_met_of_meets_between (K := VA \ VB) hp
      (fun q hq => hsubA hq.1) (saturated_of_open_cover hVA hVB hcover).1 hperKA
      hmid1 hmid2 hc2 (fun t h1 h2 => hKAmeet t (lt_trans hmid1 h1) h2) (b - δ)
      (le_of_lt hmid2) le_rfl
    have hmem : ((q.1, b - δ) : ℝ × ℝ) ∈ VA \ VB := by
      have h1 : ((q.1, q.2) : ℝ × ℝ) ∈ VA \ VB := (Prod.eta q).symm ▸ hqK
      rwa [hqt] at h1
    exact hKAlev q.1 hmem

/-- **The collared crux in the strict-overlap case `a + ε < b - δ`** — the residual of the collared
case (and, by the shrinkage calculus, the generic one). -/
theorem collared_crux_overlap {p a b δ ε : ℝ} (hp : 0 < p) (hab : a < b)
    (hδ : 0 < δ) (hε : 0 < ε) (hoverlap : a + ε < b - δ)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ stripS a b) (hsubB : VB ⊆ stripS a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z)) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (Tmap p z) ∧ JoinedIn VB z (Tmap p z) := by
  obtain ⟨z, hzA, hzB⟩ :=
    crux_of_finite_orbit_component hp hVA hVB hperA hperB
      (mv_obligation hp hab hVA hVB hsubA hsubB hperA hperB hcover hwindA hwindB)
  exact ⟨z, ⟨(mem_Ess.mp hzA).1, (mem_Ess.mp hzB).1⟩, (mem_Ess.mp hzA).2, (mem_Ess.mp hzB).2⟩

/-- **The collared residual, sharpened: the *overlapping* collar case `a + ε ≤ b - δ`.**  This is
what is left of the collared case: the two collars overlap (or touch), so the strip is *not* covered
by the two bands and there is no free level.  The touching half (`a + ε = b - δ`) is now proved
(`collared_crux_touching`); the strict half is `collared_crux_overlap`. -/
theorem collared_crux {p a b δ ε : ℝ} (hp : 0 < p) (hab : a < b)
    (hδ : 0 < δ) (hε : 0 < ε) (hoverlap : a + ε ≤ b - δ)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ stripS a b) (hsubB : VB ⊆ stripS a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z)) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (Tmap p z) ∧ JoinedIn VB z (Tmap p z) := by
  rcases lt_or_eq_of_le hoverlap with h | h
  · exact collared_crux_overlap hp hab hδ hε h hVA hVB hsubA hsubB hperA hperB hcover hKA hKB
      hwindA hwindB
  · exact collared_crux_touching hp hab hδ hε h hVA hVB hsubA hsubB hperA hperB hcover hKA
      hKB hwindA hwindB

/-- **The collared case assembles from its two halves.**  Either the collars are disjoint
(`b - δ < a + ε`), in which case `collared_crux_of_disjoint_collars` gives the conclusion outright, or
they overlap (`a + ε ≤ b - δ`), which is exactly the hypothesis package of `collared_crux`.  So the
single remaining obligation of the collared case is its overlapping half. -/
theorem collared_crux_of_halves {p a b δ ε : ℝ} (hp : 0 < p) (hab : a < b)
    (hδ : 0 < δ) (hε : 0 < ε)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ stripS a b) (hsubB : VB ⊆ stripS a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ Tmap p q ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ Tmap p q ∈ VB)
    (hcover : VA ∪ VB = stripS a b)
    (hKA : VA \ VB ⊆ {q : ℝ × ℝ | q.2 ≤ b - δ})
    (hKB : VB \ VA ⊆ {q : ℝ × ℝ | a + ε ≤ q.2})
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (Tmap p z))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (Tmap p z)) :
    ∃ z : ℝ × ℝ, z ∈ VA ∩ VB ∧ JoinedIn VA z (Tmap p z) ∧ JoinedIn VB z (Tmap p z) := by
  rcases lt_or_ge (b - δ) (a + ε) with h | h
  · exact collared_crux_of_disjoint_collars hp hab hδ hε h hVA hVB hsubA hsubB hperA hperB
      hcover hKA hKB hwindA hwindB
  · exact collared_crux hp hab hδ hε h hVA hVB hsubA hsubB hperA hperB
      hcover hKA hKB hwindA hwindB

end Commons.Topology.Strip
