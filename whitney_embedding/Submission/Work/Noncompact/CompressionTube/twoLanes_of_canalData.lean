import Mathlib
import Submission.Work.Noncompact.CompressionTube.LaneData
import Submission.Work.Noncompact.CompressionTube.immersedLine
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm
import Submission.Work.Noncompact.CompressionTube.germGlue
import Submission.Work.Noncompact.CompressionTube.pieceTraceCut
import Submission.Work.Noncompact.Routing.arcs_removal
import Submission.Work.Noncompact.Routing.spike_reach
import Submission.Work.Crux.contMDiffAt_Icc_globalize
import Submission.Work.Noncompact.Routing.CanalRegions
import Submission.Work.Noncompact.CompressionTube.oneStep_piece
import Submission.Work.Noncompact.CompressionTube.germ_middle_glue
import Submission.Work.Noncompact.CompressionTube.lineStageAux
import Submission.Work.CompressionTube.corridorChain_of_canalData
import Submission.Work.Noncompact.CompressionTube.twoLanes_of_canal


/-! ## TRAP: proved-but-VACUOUS lemmas (do not build on them)

Several lemmas in this workspace are *proved* and still **inconsistent in their hypotheses**, hence
say nothing at all.  The pattern is a "visit condition" combined with a germ-covering hypothesis:

* `Work.Noncompact.CompressionTube.hterm_of_trace_ball` (and `hterm_of_terminal_trace`, which calls
  it) assumes both `hballC : c.symm '' closedBall (c y) e' ⊆ C` and `htrace : Q t ∈ C →
  Q t ∈ c.symm '' ball (c y) ρ` with `ρ > e'`, plus `hroot : Q t ∈ ball (c y) ρ → t ∈ Icc (1-e') 1`
  and the germ `Q t = c.symm (c y + (t-1) • w)` on `Icc (1-e') 1`.  But `Q (1-e')` lies in the
  closed germ ball, hence in `C`; `C` is open, so `Q t ∈ C` for `t` slightly **below** `1-e'`
  (continuity), whence `htrace` and `hroot` force `t ≥ 1-e'` — contradiction.  So the lemma has no
  instance for `e' < 1`, and any interface whose only route to `hterm` is through it is dead.
* `Work.Noncompact.CompressionTube.inter_image_subset_singleton_of_corridor_visits` and
  `laneDatumStep_of_corridor_visits` carry the same shaped clause (`P t ∈ C' → t ∈ Icc (1-e) 1`,
  `Q t ∈ C → t ∈ Icc 0 e'`): it forces the recorded germ endpoint to lie *outside* the corridor it
  is supposed to leave, which is not automatic and usually fails.
* `Work.Noncompact.CompressionTube.twoLanes_of_corridorVisits` (`laneOfRoute.lean`), and every
  interface that ties **both** lanes to one and the same junction sequence `h.Q i` (e.g.
  `Work.Routing.twoLanes_corridorChain_core`, `CompressionTube/laneState_of_roundNeck.lean`), is
  unusable for the two-lane routing: both lane images contain `h.Q 1`, so `hcross` forces
  `h.Q 1 = b`, contradicting the seed condition `h.Q 0 ∉ h.C 1`.  As a conditional statement it is
  harmless; as a plan it is a trap.

The way out is `Work.Noncompact.CompressionTube.inter_image_subset_singleton_of_germ_ball`: give it
the covering **set** `B := C i ∩ C (i+1)` (not a chart ball), the two germ representations in one
chart, and the two *automatic* facts that the arriving piece's only visits to `B` are its terminal
germ and the departing piece's only visits to `B` are its initial germ — automatic because in the
`mid ⊔ spike` design the mid avoids the neighbouring corridor and the spike **is** the germ, whose
far end is chosen outside `B`.
-/


/-! ## THE DESIGN (worked out; implement in this order)

Every ingredient below is PROVED; what remains is one bookkeeping recursion.  The sizes are the ones
the proofs need — each is chosen at a stage, never a fixed point.

### The piece

A piece has the `mid ⊔ spike` shape of `CompressionTube/germ_middle_glue.lean` (PROVED, no sorry):
given a chart `c`, `σ ∈ c.source`, `u ≠ 0`, `L > 0`, a bump `φ` with `φ = t` on `(-1, L+1)` and
`c σ + φ t • u ∈ c.target` for all `t`, and a smooth mid `α` with `α 0 = c.symm (c σ + L • u)` whose
germ at `0` is the *same line* (`α s = c.symm (c (α 0) + s • u)` for small `s`), it yields
`P : ℝ → M`, `C^∞`, immersive on `[0, L+1]`, injective on `[0, L+1]`, with
`P 0 = σ`, `P L = α 0`, `P (L+1) = α 1`, `P t = c.symm (c σ + t • u)` on `[0, L]` and
`P t = α (t - L)` on `[L, L+1]`.  So `P` = straight spike `σ → p` (`p := c.symm (c σ + L • u)`),
then the mid to the next junction.  Reparametrise affinely to `[0,1]` (`affineReparam`) for `Lane`s.
The mid is produced by `immersedArcWithGerm` in an open preconnected region `U ∋ p` with the
prescribed chart `c`, direction `u` at `p`, and target the next junction.

### The stage

Junctions `w 0 = b`, `w (i+1) = z i`; stage `i` carries the piece `P i` from `w i` to `w (i+1)`,
its initial germ `(c i, u i)`, its terminal germ `(c (i+1), u (i+1))` (just the mid's terminal germ;
feed it in as the next stage's prescribed initial germ — straight-through), and the two numbers

* `ρ i > 0`, the rootedness radius of `P i` at `w (i+1)` from **`exists_trace_ball`** (PROVED),
* `ρ^α i > 0`, the rootedness radius of the mid `α i` at `w (i+1)`, likewise.

### Discharging the three hypotheses of `inter_image_subset_singleton_of_germ_ball`

At `y := w (i+1)`, with `P := P i`, `Q := P (i+1)`, chart `c := c (i+1)`, `u := u (i+1)`, and
`B := c.symm '' Metric.ball (c y) ρ`, `ρ := min (ρ i) (ρ^α i)` (positive, and known *before* `Q` is
built since both radii belong to stage `i`):

* `hProot` — `P`'s visits to `B` are terminal-germ visits: `B` is inside `P i`'s rootedness ball, and
  rootedness is antitone;
* `hQroot` — `Q`'s visits to `B` are initial-germ visits: `Q`'s spike *is* the germ and the mid's
  non-germ part avoids the mid's rootedness ball;
* `hcover` — `P '' Icc ∩ Q '' Icc ⊆ B`: a common point on the mid contradicts the region hypothesis
  `U ∩ P '' Icc = ∅`; a common point on the spike has chart parameter `t ∈ [0, L]`, so
  `‖c y + t • u - c y‖ = t * ‖u‖ ≤ L * ‖u‖`, hence lies in `B` provided
  **`L * ‖u‖ ≤ ρ i`: choose the spike shorter than the previous rootedness radius.**  (`L` is chosen
  after `ρ i` is computed and `immersedArcWithGerm` accepts any positive germ length, so this is
  free.)

Hence `P i '' Icc ∩ P (i+1) '' Icc ⊆ {y}` — the consecutive separation, with no radius matching and
no "visit to the whole corridor" clause (see the TRAP note above).

### Non-consecutive separation and escape

Invariant `P i ⊆ D (N+i)` and `P i ∩ D (N+i+2) = ∅`; then `j ≥ i+2` gives
`P j ⊆ D (N+j) ⊆ D (N+i+2)`, so `P i ∩ P j = ∅` — the PROVED `disjoint_of_D_confinement`.  Escape
from `P i ⊆ D (N+i) ⊆ (K (N+i))ᶜ` and cofinality of `K`.  (Alternatively a `CorridorChain` from
`corridorChain_of_canalData` with `CorridorChain.disjoint` / `escape`.)

### Reach

The mid's region for stage `i+1` must be open preconnected, contain the spike's far end and `w (i+2)`,
avoid `P i`'s image and the neighbouring shell, and contain the short forward germ — `oneStep_ambient`
(PROVED) supplies this after deleting the previous spike, and the canal regions give the cofinality
that keeps `w (i+2)` reachable.

### Assembly

`twoLanes_of_twoPiecesData` (PROVED, this file): two piece families with opposite base germs (from
`Routing.exists_base_germ`) and `(⋃P) ∩ (⋃Q) ⊆ {b}` give `Nonempty (TwoLanes n M b W)` outright.
The second family is the same recursion with the first family's images added to every removed set.
-/
namespace Work.Noncompact.CompressionTube

/-! ## Road map (the proof of `twoLanes_of_canalData`)

The target is the per-canal form of the routing crux.  The route implemented here is

    `twoLanes_of_line`  <--  a smooth injective proper immersion `γ : ℝ → M` with `γ 1 = b`

and `γ` is assembled from two *rays* with opposite straight germs at `b` (`ray_of_pieces_with_germs`
twice, then `line_of_two_germed_rays_pos`).  The pieces of a ray are built by induction with
`immersedArcWithGerm` in regions that are controlled by the canal data:

* **reach**: `canalRegion n K D N z j := connectedComponentIn (D N \ K (N + j)) (z j)` is open
  preconnected, lies in `D N \ K (N+j)`, is nested in `j`, contains `D (N+j)`, and contains every
  later junction (`z i ∈ canalRegion ` for `i ≥ j`, `Routing/CanalRegions.lean`);
* **the ambient of the next stage**: `oneStep_ambient` / `isOpen_isPreconnected_sdiff_spike`
  (PROVED) remove the previous piece's *spike* from an open preconnected corridor and keep the
  remainder open preconnected, containing the access point and the next junction (this is the
  reach of the step);
* **separation of two consecutive pieces**: `inter_image_subset_singleton_of_germ_ball`
  (PROVED, `germBodySeparation.lean`) with the covering *set* `B := C i ∩ C (i+1)`: the arriving
  piece visits `B` only along its terminal germ, the departing one only along its initial germ, and
  the two germs are the two halves of one straight chart line through the junction;
* **non-consecutive separation and escape**: confine the pieces to the corridors of a `CorridorChain`
  (`corridorChain_of_canalData`, PROVED) and use `CorridorChain.disjoint` / `CorridorChain.escape`;
* **assembly**: `ray_of_pieces_with_germs`, `line_of_two_germed_rays_pos`, `twoLanes_of_line`
  (all PROVED).

The bricks below are the elementary index bookkeeping that the induction needs. -/

section IndexBookkeeping

variable {M : Type*} [TopologicalSpace M]

/-- `D` is antitone from its successor-closure. -/
theorem antitone_D {D : ℕ → Set M} (hDmono : ∀ i, D (i + 1) ⊆ D i) : Antitone D :=
  antitone_nat_of_succ_le hDmono

/-- **The junctions are outside the later canal levels.**  For `m ≥ j + 1` the junction `z j` is
outside `D (N + m)`: it is already outside `D (N + j + 1)`, and the family decreases. -/
theorem z_notMem_D {D : ℕ → Set M} (hDmono : ∀ i, D (i + 1) ⊆ D i) {N : ℕ} {z : ℕ → M}
    (hznot : ∀ i, z i ∉ D (N + i + 1)) {j m : ℕ} (hm : j + 1 ≤ m) : z j ∉ D (N + m) :=
  fun hc => hznot j (antitone_D hDmono (by omega : N + j + 1 ≤ N + m) hc)

/-- **The junctions are outside the closures of the far canal levels.**  For `m ≥ j + 2` the
junction `z j` is outside `closure (D (N + m))`. -/
theorem z_notMem_closure_D {D : ℕ → Set M} (hDmono : ∀ i, D (i + 1) ⊆ D i) {N : ℕ}
    {z : ℕ → M} (hzcl : ∀ i, z i ∉ closure (D (N + i + 2))) {j m : ℕ} (hm : j + 2 ≤ m) :
    z j ∉ closure (D (N + m)) :=
  fun hc => hzcl j (closure_mono (antitone_D hDmono (by omega : N + j + 2 ≤ N + m)) hc)

/-- **A piece confined to `D (N + i)` and avoiding `D (N + i + 2)` avoids every later piece's
confining level.**  This is the invariant that turns the canal filtration into the non-consecutive
separation `P i ∩ P j = ∅` for `j ≥ i + 2`. -/
theorem disjoint_of_D_confinement {D : ℕ → Set M} {P : ℕ → Set M} {N : ℕ}
    (hDmono : ∀ i, D (i + 1) ⊆ D i)
    (hconf : ∀ i, P i ⊆ D (N + i)) (hav : ∀ i, Disjoint (P i) (D (N + i + 2)))
    {i j : ℕ} (hij : i + 2 ≤ j) : Disjoint (P i) (P j) :=
  by
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  exact Set.disjoint_left.mp (hav i) hx
    ((hconf j).trans (antitone_D hDmono (by omega : N + i + 2 ≤ N + j)) hx')

/-- **The base point is outside the far canal levels** (from `b ∉ closure (D (N + 2))`). -/
theorem b_notMem_D {D : ℕ → Set M} (hDmono : ∀ i, D (i + 1) ⊆ D i) {N : ℕ} {b : M}
    (hbcl : b ∉ closure (D (N + 2))) {m : ℕ} (hm : 2 ≤ m) : b ∉ D (N + m) :=
  fun hc => hbcl (closure_mono (antitone_D hDmono (by omega : N + 2 ≤ N + m)) (subset_closure hc))

end IndexBookkeeping


/-! ## The assembly: two piece-families give the two rays -/

section Assembly

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-- **Two rays from two piece-families with opposite base germs.**  Each family is the full
hypothesis list of `ray_of_pieces_with_germs` (smooth, immersive on `[0,1]`, injective on `[0,1]`,
joined at the junctions with matching straight germs, pairwise separated, escaping every compact
set), both lie in `W`, and their images meet only at `b`; the two base germs are the two halves of
one straight chart line through `b` (`c`, `u` versus `c`, `-u`).

The conclusion is (a superset of) the hypothesis list of `line_of_two_germed_rays_pos`, so the two
rays glue into a globally smooth injective proper immersion through `b`. -/
theorem exists_twoRays_of_twoPiecesData {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {W : Set M} {b : M} {P Q : ℕ → ℝ → M}
    (hsmP : ∀ i : ℕ, ContMDiff MCreal (MC n) smoothOrder (P i))
    (himmP : ∀ (i : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
      Function.Injective (mfderiv MCreal (MC n) (P i) t))
    (hinjP : ∀ i : ℕ, Set.InjOn (P i) (Set.Icc (0:ℝ) 1))
    (hjunP : ∀ i : ℕ, P i 1 = P (i + 1) 0)
    (hgermP : ∀ i : ℕ, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n)) (e' : ℝ),
        0 < e' ∧ c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ P i 1 ∈ c.source ∧
        (∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → P i t = c.symm (c (P i 1) + (t - 1) • u)) ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ e' → P (i + 1) t = c.symm (c (P (i + 1) 0) + t • u)))
    (hsepP : ∀ i j : ℕ, i < j →
      P i '' Set.Icc (0:ℝ) 1 ∩ P j '' Set.Icc (0:ℝ) 1 ⊆ {P i 1})
    (hescP : ∀ K : Set M, IsCompact K → ∃ I : ℕ, ∀ i : ℕ, I ≤ i →
      P i '' Set.Icc (0:ℝ) 1 ∩ K = ∅)
    (hWP : ∀ i : ℕ, P i '' Set.Icc (0:ℝ) 1 ⊆ W)
    (hP0 : P 0 0 = b)
    (hsmQ : ∀ i : ℕ, ContMDiff MCreal (MC n) smoothOrder (Q i))
    (himmQ : ∀ (i : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
      Function.Injective (mfderiv MCreal (MC n) (Q i) t))
    (hinjQ : ∀ i : ℕ, Set.InjOn (Q i) (Set.Icc (0:ℝ) 1))
    (hjunQ : ∀ i : ℕ, Q i 1 = Q (i + 1) 0)
    (hgermQ : ∀ i : ℕ, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n)) (e' : ℝ),
        0 < e' ∧ c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ Q i 1 ∈ c.source ∧
        (∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → Q i t = c.symm (c (Q i 1) + (t - 1) • u)) ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ e' → Q (i + 1) t = c.symm (c (Q (i + 1) 0) + t • u)))
    (hsepQ : ∀ i j : ℕ, i < j →
      Q i '' Set.Icc (0:ℝ) 1 ∩ Q j '' Set.Icc (0:ℝ) 1 ⊆ {Q i 1})
    (hescQ : ∀ K : Set M, IsCompact K → ∃ I : ℕ, ∀ i : ℕ, I ≤ i →
      Q i '' Set.Icc (0:ℝ) 1 ∩ K = ∅)
    (hWQ : ∀ i : ℕ, Q i '' Set.Icc (0:ℝ) 1 ⊆ W)
    (hQ0 : Q 0 0 = b)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n)}
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hu : u ≠ 0)
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) (hcsrc : b ∈ c.source)
    (hgrmP : ∀ t : ℝ, 0 ≤ t → t ≤ e → P 0 t = c.symm (c b + t • u))
    (hgrmQ : ∀ t : ℝ, 0 ≤ t → t ≤ e → Q 0 t = c.symm (c b + t • (-u)))
    (hcross : (⋃ i : ℕ, P i '' Set.Icc (0:ℝ) 1) ∩ (⋃ j : ℕ, Q j '' Set.Icc (0:ℝ) 1)
      ⊆ {b}) :
    ∃ r r' : ℝ → M,
      ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)) ∧
      ContMDiffOn MCreal (MC n) smoothOrder r' (Set.Ici (0:ℝ)) ∧
      r 0 = b ∧ r' 0 = b ∧
      Set.InjOn r (Set.Ici (0:ℝ)) ∧ Set.InjOn r' (Set.Ici (0:ℝ)) ∧
      IsProperMap (fun t : Set.Ici (0:ℝ) => r t) ∧
      IsProperMap (fun t : Set.Ici (0:ℝ) => r' t) ∧
      (∀ t : ℝ, 0 < t → Function.Injective (mfderiv MCreal (MC n) r t)) ∧
      (∀ t : ℝ, 0 < t → Function.Injective (mfderiv MCreal (MC n) r' t)) ∧
      (∀ x : M, x ∈ r '' Set.Ici (0:ℝ) → x ∈ r' '' Set.Ici (0:ℝ) → x = b) ∧
      r '' Set.Ici (0:ℝ) ⊆ W ∧ r' '' Set.Ici (0:ℝ) ⊆ W ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → r t = c.symm (c b + t • u)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → r' t = c.symm (c b + t • (-u))) := by
  classical
  obtain ⟨r, -, hrsm, hrinj, hrprop, hrimm, hrmem, hrger⟩ :=
    ray_of_pieces_with_germs (n := n) (M := M) hn P hsmP himmP hinjP hjunP hgermP hsepP hescP
      (c := c) (u := u) (e := e) he he1 hu hc (by rw [hP0]; exact hcsrc)
      (fun t ht hte => by rw [hP0]; exact hgrmP t ht hte)
  obtain ⟨r', -, hr'sm, hr'inj, hr'prop, hr'imm, hr'mem, hr'ger⟩ :=
    ray_of_pieces_with_germs (n := n) (M := M) hn Q hsmQ himmQ hinjQ hjunQ hgermQ hsepQ hescQ
      (c := c) (u := -u) (e := e) he he1 (neg_ne_zero.mpr hu) hc (by rw [hQ0]; exact hcsrc)
      (fun t ht hte => by rw [hQ0]; exact hgrmQ t ht hte)
  have hsrcP : P 0 0 ∈ c.source := by rw [hP0]; exact hcsrc
  have hsrcQ : Q 0 0 ∈ c.source := by rw [hQ0]; exact hcsrc
  have hr0 : r 0 = b := by
    rw [hrger 0 le_rfl he.le, zero_smul, add_zero, c.left_inv hsrcP, hP0]
  have hr'0 : r' 0 = b := by
    rw [hr'ger 0 le_rfl he.le, zero_smul, add_zero, c.left_inv hsrcQ, hQ0]
  have hbW : b ∈ W := by
    have hmem : b ∈ P 0 '' Set.Icc (0:ℝ) 1 := ⟨0, Set.left_mem_Icc.mpr zero_le_one, hP0⟩
    exact hWP 0 hmem
  refine ⟨r, r', hrsm, hr'sm, hr0, hr'0, hrinj, hr'inj, hrprop, hr'prop,
    fun t ht => hrimm t ht.le, fun t ht => hr'imm t ht.le, ?_, ?_, ?_, ?_, ?_⟩
  · -- the two rays meet only at `b`
    intro x hx hx'
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, hst⟩ := hx'
    rcases hrmem s hs with h1 | h1
    · rw [Set.mem_singleton_iff] at h1
      rw [h1, hP0]
    · rcases hr'mem t ht with h2 | h2
      · rw [Set.mem_singleton_iff] at h2
        rw [← hst, h2, hQ0]
      · have h2' : r s ∈ ⋃ j : ℕ, Q j '' Set.Icc (0:ℝ) 1 := by
          rw [← hst]; exact h2
        exact Set.mem_singleton_iff.mp (hcross ⟨h1, h2'⟩)
  · -- `r '' Ici 0 ⊆ W`
    rintro x ⟨s, hs, rfl⟩
    rcases hrmem s hs with h1 | h1
    · rw [Set.mem_singleton_iff] at h1
      rw [h1, hP0]; exact hbW
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
      exact hWP i hi
  · -- `r' '' Ici 0 ⊆ W`
    rintro x ⟨s, hs, rfl⟩
    rcases hr'mem s hs with h1 | h1
    · rw [Set.mem_singleton_iff] at h1
      rw [h1, hQ0]; exact hbW
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h1
      exact hWQ j hj
  · intro t ht0 hte
    rw [hrger t ht0 hte, hP0]
  · intro t ht0 hte
    rw [hr'ger t ht0 hte, hQ0]

/-- **Two piece-families with opposite base germs give the two lanes** (hence the target).  This is
`exists_twoRays_of_twoPiecesData` followed by the gluing `line_of_two_germed_rays_pos` and the last
mile `twoLanes_of_line`: it reduces the whole target to the construction of the two piece
families. -/
theorem twoLanes_of_twoPiecesData {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {W : Set M} {b : M} {P Q : ℕ → ℝ → M}
    (hsmP : ∀ i : ℕ, ContMDiff MCreal (MC n) smoothOrder (P i))
    (himmP : ∀ (i : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
      Function.Injective (mfderiv MCreal (MC n) (P i) t))
    (hinjP : ∀ i : ℕ, Set.InjOn (P i) (Set.Icc (0:ℝ) 1))
    (hjunP : ∀ i : ℕ, P i 1 = P (i + 1) 0)
    (hgermP : ∀ i : ℕ, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n)) (e' : ℝ),
        0 < e' ∧ c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ P i 1 ∈ c.source ∧
        (∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → P i t = c.symm (c (P i 1) + (t - 1) • u)) ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ e' → P (i + 1) t = c.symm (c (P (i + 1) 0) + t • u)))
    (hsepP : ∀ i j : ℕ, i < j →
      P i '' Set.Icc (0:ℝ) 1 ∩ P j '' Set.Icc (0:ℝ) 1 ⊆ {P i 1})
    (hescP : ∀ K : Set M, IsCompact K → ∃ I : ℕ, ∀ i : ℕ, I ≤ i →
      P i '' Set.Icc (0:ℝ) 1 ∩ K = ∅)
    (hWP : ∀ i : ℕ, P i '' Set.Icc (0:ℝ) 1 ⊆ W)
    (hP0 : P 0 0 = b)
    (hsmQ : ∀ i : ℕ, ContMDiff MCreal (MC n) smoothOrder (Q i))
    (himmQ : ∀ (i : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
      Function.Injective (mfderiv MCreal (MC n) (Q i) t))
    (hinjQ : ∀ i : ℕ, Set.InjOn (Q i) (Set.Icc (0:ℝ) 1))
    (hjunQ : ∀ i : ℕ, Q i 1 = Q (i + 1) 0)
    (hgermQ : ∀ i : ℕ, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n)) (e' : ℝ),
        0 < e' ∧ c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ Q i 1 ∈ c.source ∧
        (∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → Q i t = c.symm (c (Q i 1) + (t - 1) • u)) ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ e' → Q (i + 1) t = c.symm (c (Q (i + 1) 0) + t • u)))
    (hsepQ : ∀ i j : ℕ, i < j →
      Q i '' Set.Icc (0:ℝ) 1 ∩ Q j '' Set.Icc (0:ℝ) 1 ⊆ {Q i 1})
    (hescQ : ∀ K : Set M, IsCompact K → ∃ I : ℕ, ∀ i : ℕ, I ≤ i →
      Q i '' Set.Icc (0:ℝ) 1 ∩ K = ∅)
    (hWQ : ∀ i : ℕ, Q i '' Set.Icc (0:ℝ) 1 ⊆ W)
    (hQ0 : Q 0 0 = b)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n)}
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hu : u ≠ 0)
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) (hcsrc : b ∈ c.source)
    (hgrmP : ∀ t : ℝ, 0 ≤ t → t ≤ e → P 0 t = c.symm (c b + t • u))
    (hgrmQ : ∀ t : ℝ, 0 ≤ t → t ≤ e → Q 0 t = c.symm (c b + t • (-u)))
    (hcross : (⋃ i : ℕ, P i '' Set.Icc (0:ℝ) 1) ∩ (⋃ j : ℕ, Q j '' Set.Icc (0:ℝ) 1)
      ⊆ {b}) :
    Nonempty (TwoLanes n M b W) := by
  obtain ⟨r, r', hrsm, hr'sm, hr0, hr'0, hrinj, hr'inj, hrp, hr'p, hrimm, hr'imm, hmeet,
    hrW, hr'W, hrger, hr'ger⟩ :=
    exists_twoRays_of_twoPiecesData (n := n) (M := M) hn hsmP himmP hinjP hjunP hgermP hsepP
      hescP hWP hP0 hsmQ himmQ hinjQ hjunQ hgermQ hsepQ hescQ hWQ hQ0 he he1 hu hc hcsrc
      hgrmP hgrmQ hcross
  have hbW : b ∈ W := by
    have hmem : b ∈ P 0 '' Set.Icc (0:ℝ) 1 := ⟨0, Set.left_mem_Icc.mpr zero_le_one, hP0⟩
    exact hWP 0 hmem
  obtain ⟨γ, hγsm, hγinj, hγprop, hγimm, hγ1, hγrange⟩ :=
    line_of_two_germed_rays_pos (n := n) (M := M) hrsm hr'sm hr0 hr'0
      hrinj hr'inj hmeet hrp hr'p hrimm hr'imm
      ⟨c, u, e, he, hu, hc, hcsrc, hrger, hr'ger⟩
  exact twoLanes_of_line (n := n) (M := M) (b := b) (W := W) hbW hγsm hγinj hγprop hγimm hγ1
    (hγrange.trans (Set.union_subset hrW hr'W))

end Assembly

/-! ## The state of one stage -/

/-- **The state of one stage of a lane recursion.**

`w` is the junction sequence (`w 0 = b`), and the structure records everything one stage of the
recursion must hand to the next: the piece from `w i` to `w (i+1)`; its *incoming* germ datum at
`w i` (chart, direction, length — the datum the assembly `Lane.hgerm` reads off the pair of
consecutive pieces); its *outgoing* germ datum at `w (i+1)` (fed in as the next stage's prescribed
initial germ, which is what makes the gluing straight-through); and the *rootedness radius* `ρ` of
the piece at `w (i+1)`, which by `exists_trace_ball` always exists and which is the only size the
next stage has to respect: its spike must satisfy `L * ‖uout‖ < ρ`.

Nothing else about the piece is needed: the rootedness radius is computed *after* the piece exists
and *before* the next piece is built. -/
structure StageState (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] (w : ℕ → M) (i : ℕ) where
  /-- the piece, from `w i` to `w (i+1)` -/
  P : ℝ → M
  hsm : ContMDiff MCreal (MC n) smoothOrder P
  himm : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Function.Injective (mfderiv MCreal (MC n) P t)
  hinj : Set.InjOn P (Set.Icc (0:ℝ) 1)
  hP0 : P 0 = w i
  hP1 : P 1 = w (i + 1)
  /-- the incoming germ datum, at `w i` -/
  cin : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  uin : EuclideanSpace ℝ (Fin n)
  ein : ℝ
  hcin : cin ∈ IsManifold.maximalAtlas (MC n) smoothOrder M
  hsrin : w i ∈ cin.source
  hein : 0 < ein
  huin : uin ≠ 0
  hgin : ∀ t : ℝ, 0 ≤ t → t ≤ ein → P t = cin.symm (cin (w i) + t • uin)
  hintgt : ∀ t : ℝ, 0 ≤ t → t ≤ ein → cin (w i) + t • uin ∈ cin.target
  /-- the outgoing germ datum, at `w (i+1)`; it is the next stage's prescribed initial germ -/
  cout : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  uout : EuclideanSpace ℝ (Fin n)
  eout : ℝ
  hcout : cout ∈ IsManifold.maximalAtlas (MC n) smoothOrder M
  hsrot : w (i + 1) ∈ cout.source
  heout : 0 < eout
  huout : uout ≠ 0
  hgout : ∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 →
    P t = cout.symm (cout (w (i + 1)) + (t - 1) • uout)
  houttgt : ∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 →
    cout (w (i + 1)) + (t - 1) • uout ∈ cout.target
  /-- the rootedness radius of the piece at `w (i+1)` (`exists_trace_ball`): the visits of `P` to
  the chart ball of this radius are terminal-germ visits -/
  ρ : ℝ
  hρ : 0 < ρ
  hroot : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
    P t ∈ cout.symm '' Metric.ball (cout (w (i + 1))) ρ → t ∈ Set.Icc (1 - eout) 1

/-- **The germ matching between two consecutive stages.**  If the next stage's incoming datum *is*
this stage's outgoing datum, then the pair satisfies the junction clause of `Lane.hgerm` (the two
pieces are the two halves of one straight chart line through the junction). -/
theorem StageState.germ_pair {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] {w : ℕ → M} {i : ℕ}
    (S : StageState n M w i) (T : StageState n M w (i + 1))
    (hcin : T.cin = S.cout) (huin : T.uin = S.uout) (hP : T.P 0 = S.P 1) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (u : EuclideanSpace ℝ (Fin n)) (e : ℝ),
      0 < e ∧ c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ S.P 1 ∈ c.source ∧
      (∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → S.P t = c.symm (c (S.P 1) + (t - 1) • u)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → T.P t = c.symm (c (T.P 0) + t • u)) := by
  refine ⟨S.cout, S.uout, min S.eout T.ein, lt_min S.heout T.hein, S.hcout, ?_, ?_, ?_⟩
  · rw [S.hP1]; exact S.hsrot
  · intro t ht1 ht2
    have h1 : (1 : ℝ) - S.eout ≤ 1 - min S.eout T.ein := by
      linarith [min_le_left S.eout T.ein]
    rw [S.hP1]
    exact S.hgout t (le_trans h1 ht1) ht2
  · intro t ht1 ht2
    have h2 : t ≤ T.ein := le_trans ht2 (min_le_right S.eout T.ein)
    rw [T.hgin t ht1 h2, hcin, huin, hP, S.hP1]

/-! ## The clamp of the spike -/

/-- **The clamp `φ` of the spike.**  A smooth `φ` which is the identity on `(-1, L+1)` — in
particular on `[0,L]` — and globally bounded by `L + 3`.

It is the `φ` of `germ_middle_glue`: the clamped chart line `t ↦ c.symm (c σ + φ t • u)` is globally
`C^∞` (its chart argument stays in the chart target once `L + 3` is at most the chart radius of
`c σ`), while it agrees with the straight spike `t ↦ c.symm (c σ + t • u)` on `[0,L]`. -/
theorem exists_clamp (L : ℝ) (hL : 0 < L) :
    ∃ φ : ℝ → ℝ, (∀ k : ℕ∞, ContDiff ℝ (k : WithTop ℕ∞) φ) ∧
      (∀ t : ℝ, -1 < t → t < L + 1 → φ t = t) ∧
      (∀ t : ℝ, |φ t| ≤ L + 3) := by
  refine ⟨fun t => t * Real.smoothTransition (3 + 2 * t) *
    Real.smoothTransition (3 + 2 * (L + 1 - t)), ?_, ?_, ?_⟩
  · intro k
    exact (contDiff_id.mul (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop))
  · intro t ht1 ht2
    change t * Real.smoothTransition (3 + 2 * t) *
      Real.smoothTransition (3 + 2 * (L + 1 - t)) = t
    have hA : Real.smoothTransition (3 + 2 * t) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    have hB : Real.smoothTransition (3 + 2 * (L + 1 - t)) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    rw [hA, hB, mul_one, mul_one]
  · intro t
    change |t * Real.smoothTransition (3 + 2 * t) *
      Real.smoothTransition (3 + 2 * (L + 1 - t))| ≤ L + 3
    have hA0 : 0 ≤ Real.smoothTransition (3 + 2 * t) := Real.smoothTransition.nonneg _
    have hA1 : Real.smoothTransition (3 + 2 * t) ≤ 1 := Real.smoothTransition.le_one _
    have hB0 : 0 ≤ Real.smoothTransition (3 + 2 * (L + 1 - t)) := Real.smoothTransition.nonneg _
    have hB1 : Real.smoothTransition (3 + 2 * (L + 1 - t)) ≤ 1 := Real.smoothTransition.le_one _
    have habs : |t * Real.smoothTransition (3 + 2 * t) *
        Real.smoothTransition (3 + 2 * (L + 1 - t))| ≤ |t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hB0]
      calc |t| * Real.smoothTransition (3 + 2 * t) *
            Real.smoothTransition (3 + 2 * (L + 1 - t))
          ≤ |t| * Real.smoothTransition (3 + 2 * t) * 1 :=
            mul_le_mul_of_nonneg_left hB1 (mul_nonneg (abs_nonneg t) hA0)
        _ = |t| * Real.smoothTransition (3 + 2 * t) := by rw [mul_one]
        _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hA1 (abs_nonneg t)
        _ = |t| := by rw [mul_one]
    rcases le_or_gt t (-(3 / 2)) with h | h
    · have hz : Real.smoothTransition (3 + 2 * t) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [hz, mul_zero, zero_mul, abs_zero]
      linarith
    rcases le_or_gt (L + 5 / 2) t with h2 | h2
    · have hz : Real.smoothTransition (3 + 2 * (L + 1 - t)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [hz, mul_zero, abs_zero]
      linarith
    · have habs2 : |t| ≤ L + 3 := by
        rw [abs_le]
        constructor <;> linarith
      linarith

/-! ## The mid of a stage -/

/-- **The mid of one stage.**  Packaging of `immersedArcWithGerm` with the two rootedness radii the
stage needs and with the chart-target membership along the initial germ that `germ_middle_glue`
consumes.

Given an open preconnected region `U`, two distinct points `p, q ∈ U`, a chart `c` at `p` in the
maximal atlas and a direction `u ≠ 0` whose short forward germ from `p` lies in `U`, there is a mid
arc `α` from `p` to `q`, smooth, immersive everywhere, injective on `[0,1]`, lying in `U`, with

* the straight initial germ in `(c,u)` up to some `ε > 0`, *together with* the membership of the
  chart arguments in `c.target` (needed to glue with the clamped spike);
* a straight terminal germ `(c', wv, eout)` at `q`, again with the chart-target membership;
* the rootedness radius `ρin` of `α` at its *start* (`exists_trace_ball_initial`), and the
  rootedness radius `ρout` at its *end* (`exists_trace_ball`): the visits of `α` to the
  corresponding chart balls are initial-germ, respectively terminal-germ, visits. -/
theorem exists_mid_piece {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {U : Set M} (hUo : IsOpen U) (hUpc : IsPreconnected U) {p q : M}
    (hp : p ∈ U) (hq : q ∈ U) (hpq : p ≠ q)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) (hpc : p ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0)
    (hgerm : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e →
      c.symm (c p + t • u) ∈ U) :
    ∃ (α : ℝ → M) (ε : ℝ) (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (wv : EuclideanSpace ℝ (Fin n)) (eout ρin ρout : ℝ),
      α 0 = p ∧ α 1 = q ∧
      ContMDiff MCreal (MC n) smoothOrder α ∧
      (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) α t)) ∧
      Set.InjOn α (Set.Icc (0:ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → α t ∈ U) ∧
      0 < ε ∧ ε ≤ 1 ∧ (∀ s : ℝ, 0 ≤ s → s ≤ ε → α s = c.symm (c p + s • u)) ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ ε → c p + s • u ∈ c.target) ∧
      0 < eout ∧ eout ≤ 1 ∧ wv ≠ 0 ∧
      c' ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ q ∈ c'.source ∧
      (∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 → α t = c'.symm (c' q + (t - 1) • wv)) ∧
      (∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 → c' q + (t - 1) • wv ∈ c'.target) ∧
      0 < ρin ∧ (∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 →
        α s ∈ c.symm '' Metric.ball (c p) ρin → s ∈ Set.Icc (0:ℝ) ε) ∧
      0 < ρout ∧ (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        α t ∈ c'.symm '' Metric.ball (c' q) ρout → t ∈ Set.Icc (1 - eout) 1) := by
  obtain ⟨α, hα0, hα1, hαsm, hαimm, hαinj, hαU, ⟨ε₀, hε₀, hαgerm₀⟩, c', wv, e₀, he₀, hwv,
    hc', hqsrc, hαterm₀⟩ :=
    immersedArcWithGerm (n := n) (M := M) hn hUo hUpc hp hq hpq c hc hpc hu hgerm
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  -- shrink the initial germ so that its chart arguments stay in the chart target
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp c.open_target (c p) (c.map_source hpc)
  have hδu : 0 < δ / (2 * ‖u‖) := by positivity
  set ε : ℝ := min ε₀ (min 1 (δ / (2 * ‖u‖))) with hεdef
  have hε : 0 < ε := lt_min hε₀ (lt_min one_pos hδu)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεδ : ε * ‖u‖ < δ := by
    have h1 : ε ≤ δ / (2 * ‖u‖) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : ε * ‖u‖ ≤ δ / (2 * ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right h1 hu'.le
    have h3 : δ / (2 * ‖u‖) * ‖u‖ = δ / 2 := by field_simp
    rw [h3] at h2
    linarith
  have hαgerm : ∀ s : ℝ, 0 ≤ s → s ≤ ε → α s = c.symm (c p + s • u) :=
    fun s hs hse => hαgerm₀ s hs (hse.trans hεε₀)
  have htgt : ∀ s : ℝ, 0 ≤ s → s ≤ ε → c p + s • u ∈ c.target := by
    intro s hs hse
    refine hδsub ?_
    rw [Metric.mem_ball, dist_eq_norm,
      show c p + s • u - c p = s • u from by abel, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs]
    calc s * ‖u‖ ≤ ε * ‖u‖ := mul_le_mul_of_nonneg_right hse hu'.le
      _ < δ := hεδ
  obtain ⟨ρin, hρin, -, hρinroot⟩ :=
    exists_trace_ball_initial (n := n) (c := c) (Q := α) (s := p)
      hαsm.continuous hαinj hα0 hpc hε hε1 hαgerm (C := Set.univ) isOpen_univ (Set.mem_univ p)
  -- shrink the terminal germ so that its chart arguments stay in the chart target
  obtain ⟨δ', hδ', hδ'sub⟩ := Metric.isOpen_iff.mp c'.open_target (c' q) (c'.map_source hqsrc)
  have hwvn : (0 : ℝ) < ‖wv‖ := norm_pos_iff.mpr hwv
  have hδ'w : 0 < δ' / (2 * ‖wv‖) := by positivity
  set eout : ℝ := min (min e₀ 1) (δ' / (2 * ‖wv‖)) with heoutdef
  have heout : 0 < eout := lt_min (lt_min he₀ one_pos) hδ'w
  have heout1 : eout ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have heoute₀ : eout ≤ e₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hαterm : ∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 →
      α t = c'.symm (c' q + (t - 1) • wv) :=
    fun t ht1 ht2 => hαterm₀ t (by linarith [heoute₀]) ht2
  have htermtgt : ∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 →
      c' q + (t - 1) • wv ∈ c'.target := by
    intro t ht1 ht2
    refine hδ'sub ?_
    rw [Metric.mem_ball, dist_eq_norm,
      show c' q + (t - 1) • wv - c' q = (t - 1) • wv from by abel, norm_smul,
      Real.norm_eq_abs, abs_of_nonpos (by linarith [ht2])]
    have h1 : (1 : ℝ) - t ≤ eout := by linarith
    have h2 : (1 - t) * ‖wv‖ ≤ eout * ‖wv‖ := mul_le_mul_of_nonneg_right h1 hwvn.le
    have h3 : eout ≤ δ' / (2 * ‖wv‖) := min_le_right _ _
    have h4 : δ' / (2 * ‖wv‖) * ‖wv‖ = δ' / 2 := by field_simp
    have h5 : eout * ‖wv‖ ≤ δ' / 2 := by
      calc eout * ‖wv‖ ≤ δ' / (2 * ‖wv‖) * ‖wv‖ := mul_le_mul_of_nonneg_right h3 hwvn.le
        _ = δ' / 2 := h4
    linarith
  obtain ⟨ρout, hρout, -, hρoutroot⟩ :=
    exists_trace_ball (n := n) (c := c') (P := α) (s := q)
      hαsm.continuous hαinj hα1 hqsrc heout heout1 hαterm (C := Set.univ) isOpen_univ
      (Set.mem_univ q)
  exact ⟨α, ε, c', wv, eout, ρin, ρout, hα0, hα1, hαsm, hαimm, hαinj, hαU, hε, hε1,
    hαgerm, htgt, heout, heout1, hwv, hc', hqsrc, hαterm, htermtgt, hρin, hρinroot,
    hρout, hρoutroot⟩

/-! ## The consecutive separation in the `mid ⊔ spike` design -/

section MidSpikeSeparation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]

/-- **The consecutive separation, in the shape the stage actually produces.**

`P` is the arriving piece: continuous, injective on `[0,1]`, ending at `y = P 1`, with the straight
terminal germ `c.symm (c y + (t-1) • u)` on `[1-e,1]`, and *rooted* at the chart ball of radius `ρ`
around `y` (visits to that ball are terminal-germ visits — `exists_trace_ball`).  `Q` is the
departing piece in the `mid ⊔ spike` shape: the straight spike `c.symm (c y + t • u)` for
`t ∈ [0,L]` and the mid `α` afterwards, where the mid's image misses `P`'s image entirely.

If the spike is *shorter than the rootedness radius*, `L * ‖u‖ < ρ`, then the two images meet only at
the junction.

This is the `hcover` discharge of the design note: a common point on the spike has chart parameter
`t ∈ [0,L]`, hence chart distance `t * ‖u‖ ≤ L * ‖u‖ < ρ` from `c y`, so it lies in the rootedness
ball and both pieces are on the straight germ line there, where they can only meet at `y`; a common
point on the mid contradicts the region hypothesis `α '' Icc ∩ P '' Icc = ∅`. -/
theorem inter_image_subset_singleton_of_midSpike
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {y : M}
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) (hysrc : y ∈ c.source)
    {P : ℝ → M} {e ρ L : ℝ} (he : 0 < e) (hρ : 0 < ρ) (hL : 0 < L) (hLρ : L * ‖u‖ < ρ)
    (hP1 : P 1 = y)
    (hPtgt : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → c y + (t - 1) • u ∈ c.target)
    (hPgerm : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P t = c.symm (c y + (t - 1) • u))
    (hProot : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → P t ∈ c.symm '' Metric.ball (c y) ρ →
      t ∈ Set.Icc (1 - e) 1)
    {α : ℝ → M}
    (hαavoid : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 → α s ∉ P '' Set.Icc (0:ℝ) 1)
    (hytgt : ∀ t : ℝ, 0 ≤ t → t ≤ L → c y + t • u ∈ c.target) :
    P '' Set.Icc (0:ℝ) 1 ∩
        (fun t : ℝ => if t ≤ L then c.symm (c y + t • u) else α (t - L)) ''
          Set.Icc (0:ℝ) (L + 1)
      ⊆ {y} := by
  rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, htx⟩⟩
  have hinj : Set.InjOn c.symm c.target := by
    have h := c.symm.injOn
    rwa [OpenPartialHomeomorph.symm_source] at h
  by_cases htL : t ≤ L
  · -- a common point on the spike lies in the rootedness ball
    have hxt : P s = c.symm (c y + t • u) := by
      rw [← htx]; simp only [if_pos htL]
    have hmem : P s ∈ c.symm '' Metric.ball (c y) ρ := by
      rw [hxt]
      refine ⟨c y + t • u, ?_, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : c y + t • u - c y = t • u := by abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      have h2 : t * ‖u‖ ≤ L * ‖u‖ := mul_le_mul_of_nonneg_right htL (norm_nonneg u)
      linarith
    have hs' : s ∈ Set.Icc (1 - e) 1 := hProot s hs hmem
    have harg : c y + t • u = c y + (s - 1) • u :=
      hinj (hytgt t ht.1 htL) (hPtgt s hs'.1 hs'.2) (by rw [← hxt, hPgerm s hs'.1 hs'.2])
    have hteq : t = s - 1 := by
      have h1 : t • u = (s - 1) • u := add_left_cancel harg
      have h2 : (t - (s - 1)) • u = 0 := by rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · linarith
      · exact absurd h hu
    rw [Set.mem_singleton_iff, hPgerm s hs'.1 hs'.2,
      show (s - 1 : ℝ) = 0 from by linarith [hteq, ht.1, hs'.2], zero_smul, add_zero]
    exact c.left_inv hysrc
  · -- a common point on the mid contradicts the region hypothesis
    have hxt : P s = α (t - L) := by
      rw [← htx]; simp only [if_neg htL]
    have hmem : t - L ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith [not_le.mp htL], by linarith [ht.2]⟩
    exact absurd ⟨s, hs, hxt⟩ (hαavoid (t - L) hmem)

/-- The same with the mid assumed to avoid `P`'s image through its own rootedness ball and the
region, i.e. the two hypotheses `α '' Icc ∩ P '' Icc = ∅` come from a region `U` with
`U ∩ P '' Icc = ∅` and `α '' Icc ⊆ U`. -/
theorem inter_image_subset_singleton_of_midSpike_region
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {y : M}
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) (hysrc : y ∈ c.source)
    {P : ℝ → M} {e ρ L : ℝ} (he : 0 < e) (hρ : 0 < ρ) (hL : 0 < L) (hLρ : L * ‖u‖ < ρ)
    (hP1 : P 1 = y)
    (hPtgt : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → c y + (t - 1) • u ∈ c.target)
    (hPgerm : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P t = c.symm (c y + (t - 1) • u))
    (hProot : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → P t ∈ c.symm '' Metric.ball (c y) ρ →
      t ∈ Set.Icc (1 - e) 1)
    {α : ℝ → M} {U : Set M} (hαU : α '' Set.Icc (0:ℝ) 1 ⊆ U)
    (hUP : U ∩ P '' Set.Icc (0:ℝ) 1 = ∅)
    (hytgt : ∀ t : ℝ, 0 ≤ t → t ≤ L → c y + t • u ∈ c.target) :
    P '' Set.Icc (0:ℝ) 1 ∩
        (fun t : ℝ => if t ≤ L then c.symm (c y + t • u) else α (t - L)) ''
          Set.Icc (0:ℝ) (L + 1)
      ⊆ {y} := by
  refine inter_image_subset_singleton_of_midSpike hu hysrc he hρ hL hLρ hP1 hPtgt hPgerm hProot
    (fun s hs hmem => ?_) hytgt
  exact (Set.eq_empty_iff_forall_notMem.mp hUP) (α s) ⟨hαU ⟨s, hs, rfl⟩, hmem⟩

/-- **The mid meets the spike only at the glue point.**  This is `hsep` of `germ_middle_glue`,
derived from the region: if every point of the region `U` that lies on the spike is within the
*rootedness ball* of the mid at the glue point, then the mid can only meet the spike there.

The root point is `p = c.symm (c σ + L • u)`; the germ hypotheses are stated directly in the form of
the *vector* `c σ + (L + s) • u` (which is what `c.right_inv` turns the mid's germ datum into), so
that no `c.right_inv` call is needed.  Rootedness (`exists_trace_ball_initial`) then says that the
mid's visits to the rootedness ball are initial-germ visits, hence lie on the line *beyond* `p`,
while the spike is the line *below* `p`: the two meet only at `t = L`, i.e. at `p`. -/
theorem mid_avoids_spike {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M}
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) {L ε ρ : ℝ} (hL0 : 0 ≤ L) (hρ : 0 < ρ)
    (htgt : ∀ t : ℝ, 0 ≤ t → t ≤ L → c σ + t • u ∈ c.target)
    {α : ℝ → M} {U : Set M}
    (hαU : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 → α s ∈ U)
    (hsafe : ∀ x : M, x ∈ U →
      x ∈ c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L) →
      x ∈ c.symm '' Metric.ball (c σ + L • u) ρ)
    (hα0 : α 0 = c.symm (c σ + L • u))
    (hαgerm : ∀ s : ℝ, 0 ≤ s → s ≤ ε → α s = c.symm (c σ + (L + s) • u))
    (hαtgt : ∀ s : ℝ, 0 ≤ s → s ≤ ε → c σ + (L + s) • u ∈ c.target)
    (hroot : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 →
      α s ∈ c.symm '' Metric.ball (c σ + L • u) ρ → s ∈ Set.Icc (0:ℝ) ε) :
    ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 →
      α s ∈ c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L) → α s = α 0 := by
  intro s hs hmem
  -- the visit is in the rootedness ball
  have hb : α s ∈ c.symm '' Metric.ball (c σ + L • u) ρ := hsafe (α s) (hαU s hs) hmem
  have hsε : s ∈ Set.Icc (0:ℝ) ε := hroot s hs hb
  -- unpack the spike visit: the witness of `c.symm '' (⋯ '' Icc)` is a *vector*
  obtain ⟨y, ⟨t, ht, hty⟩, hyx⟩ := hmem
  subst hty
  have hgor : α s = c.symm (c σ + t • u) := by
    have h2 : c.symm (c σ + t • u) = α s := by
      simpa only [] using hyx
    exact h2.symm
  have hgle : α s = c.symm (c σ + (L + s) • u) := hαgerm s hsε.1 hsε.2
  have hinj : Set.InjOn c.symm c.target := by
    have h := c.symm.injOn
    rwa [OpenPartialHomeomorph.symm_source] at h
  have harg : c σ + t • u = c σ + (L + s) • u :=
    hinj (htgt t ht.1 ht.2) (hαtgt s hsε.1 hsε.2) (by rw [← hgor, hgle])
  have hts : t = L + s := by
    have h1 : t • u = (L + s) • u := add_left_cancel harg
    have h2 : (t - (L + s)) • u = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · linarith
    · exact absurd h hu
  have hs0 : s = 0 := by linarith [hts, ht.2, hsε.1]
  subst hs0
  have htL : t = L := by linarith [hts]
  calc α 0 = c.symm (c σ + t • u) := hgor
    _ = c.symm (c σ + L • u) := by rw [htL]
    _ = α 0 := hα0.symm

/-- **The rootedness radius of the reparametrised piece at the far junction.**  Packaging of
`exists_trace_ball` for a piece `Q` that ends at `q` with the straight terminal germ
`c'.symm (c' q + (t-1) • w)` on `[1-e,1]`: there is `ρ > 0` such that the visits of `Q` to the chart
ball of radius `ρ` around `q` are exactly terminal-germ visits.

This is the number the *next* stage must respect (its spike must be shorter than `ρ`), and it is
computed directly from `Q` — never derived from the mid's own rootedness, so that the spike-avoidance
bookkeeping stays out of it. -/
theorem exists_far_rooted {c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {Q : ℝ → M} (hQsm : ContMDiff MCreal (MC n) smoothOrder Q)
    (hQinj : Set.InjOn Q (Set.Icc (0:ℝ) 1))
    {q : M} (hQ1 : Q 1 = q) (hqsrc : q ∈ c'.source)
    {w : EuclideanSpace ℝ (Fin n)} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hgerm : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → Q t = c'.symm (c' q + (t - 1) • w)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
      Q t ∈ c'.symm '' Metric.ball (c' q) ρ → t ∈ Set.Icc (1 - e) 1 := by
  obtain ⟨ρ, hρ, -, hroot⟩ :=
    exists_trace_ball (n := n) (c := c') (P := Q) (s := q) hQsm.continuous hQinj hQ1 hqsrc
      he he1 hgerm (C := Set.univ) isOpen_univ (Set.mem_univ q)
  exact ⟨ρ, hρ, hroot⟩

end MidSpikeSeparation

/-! ## Reparametrising the glued piece to `[0,1]` -/

/-- **The glued piece reparametrised to `[0,1]`.**  A piece `P` on `[0, L+1]` (as produced by
`exists_gluedPiece`) is affinely reparametrised to `Q t = P ((L+1) * t)`, and the two straight germs
are carried through: the initial germ stays in the *same* chart and direction (`t • ((L+1) • u)`),
with the extent rescaled to `(L+ε)/(L+1)`; the terminal germ keeps its chart and direction rescaled
to `(L+1) • w`, with extent `eout/(L+1)`.

This is `affineReparam`'s three transports (`contMDiff_comp_affine`, the `smul`-form immersion
transport, `injOn_comp_smul_Icc`) together with the scalar identity
`(L+1) * t - L - 1 = (L+1) * (t-1)`. -/
theorem exists_reparametrized_piece {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M}
    {u : EuclideanSpace ℝ (Fin n)} {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (htgt : ∀ s : ℝ, 0 ≤ s → s ≤ L + ε → c σ + s • u ∈ c.target)
    {P : ℝ → M} (hPsm : ContMDiff MCreal (MC n) smoothOrder P)
    (hPimm : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) (L + 1) →
      Function.Injective (mfderiv MCreal (MC n) P t))
    (hPinj : Set.InjOn P (Set.Icc (0:ℝ) (L + 1)))
    (hP0 : P 0 = σ)
    (hgermP : ∀ s : ℝ, 0 ≤ s → s ≤ L + ε → P s = c.symm (c σ + s • u))
    {q : M} {c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {w : EuclideanSpace ℝ (Fin n)} {eout : ℝ}
    (heout : 0 < eout) (heout1 : eout ≤ 1) (hw : w ≠ 0) (hPq : P (L + 1) = q)
    (hgermP' : ∀ t : ℝ, L ≤ t → t ≤ L + 1 →
      P t = c'.symm (c' q + (t - L - 1) • w)) :
    ∃ Q : ℝ → M, ContMDiff MCreal (MC n) smoothOrder Q ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Function.Injective (mfderiv MCreal (MC n) Q t)) ∧
      Set.InjOn Q (Set.Icc (0:ℝ) 1) ∧
      Q 0 = σ ∧ Q 1 = q ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ (L + ε) / (L + 1) →
        Q t = c.symm (c σ + t • ((L + 1) • u))) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ (L + ε) / (L + 1) →
        c σ + t • ((L + 1) • u) ∈ c.target) ∧
      (∀ t : ℝ, 1 - eout / (L + 1) ≤ t → t ≤ 1 →
        Q t = c'.symm (c' q + (t - 1) • ((L + 1) • w))) := by
  have hL1 : (0:ℝ) < L + 1 := by linarith
  have hstep : ∀ t : ℝ, t • ((L + 1) • u) = ((L + 1) * t) • u := by
    intro t
    rw [smul_smul, mul_comm]
  refine ⟨fun t => P ((L + 1) * t), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [add_zero] using contMDiff_comp_affine (n := n) (M := M) hPsm (L + 1) 0
  · intro t ht
    refine injective_mfderiv_comp_smul_at (n := n) (M := M) hPsm (by linarith : (L + 1) ≠ 0)
      (h := hPimm ((L + 1) * t) ⟨by nlinarith [ht.1, hL], by nlinarith [ht.2, hL]⟩)
  · refine injOn_comp_smul_Icc (M := M) hL1 hPinj
  · show P ((L + 1) * 0) = σ
    rw [mul_zero]; exact hP0
  · show P ((L + 1) * 1) = q
    rw [mul_one]; exact hPq
  · intro t ht0 ht1
    have hs : 0 ≤ (L + 1) * t := by nlinarith [ht0, hL]
    have hs' : (L + 1) * t ≤ L + ε := by
      have h := mul_le_mul_of_nonneg_right ht1 hL1.le
      have h2 : ((L + ε) / (L + 1)) * (L + 1) = L + ε := by field_simp
      rw [h2] at h
      linarith
    simpa only [← hstep t] using hgermP ((L + 1) * t) hs hs'
  · intro t ht0 ht1
    have hs : 0 ≤ (L + 1) * t := by nlinarith [ht0, hL]
    have hs' : (L + 1) * t ≤ L + ε := by
      have h := mul_le_mul_of_nonneg_right ht1 hL1.le
      have h2 : ((L + ε) / (L + 1)) * (L + 1) = L + ε := by field_simp
      rw [h2] at h
      linarith
    simpa only [← hstep t] using htgt ((L + 1) * t) hs hs'
  · intro t ht1 ht2
    have hge : L ≤ (L + 1) * t := by
      have h : 1 - eout / (L + 1) ≤ t := ht1
      have h2 : (1 - eout / (L + 1)) * (L + 1) ≤ t * (L + 1) :=
        mul_le_mul_of_nonneg_right h hL1.le
      have h3 : (1 - eout / (L + 1)) * (L + 1) = L + 1 - eout := by
        field_simp
      rw [h3] at h2
      nlinarith [h2, heout1]
    have hle : (L + 1) * t ≤ L + 1 := by nlinarith [ht2, hL]
    show P ((L + 1) * t) = c'.symm (c' q + (t - 1) • ((L + 1) • w))
    rw [hgermP' ((L + 1) * t) hge hle]
    congr 2
    have hsm : (t - 1) • ((L + 1) • w) = ((L + 1) * (t - 1)) • w := by
      rw [smul_smul, mul_comm]
    rw [hsm]
    congr 1
    ring

/-· ## The mid avoids the spike (the `hsep` of the glue) ·-/

/-! ## The glued piece of one stage -/

/-- **The glued piece of one stage** (`spike ⊔ mid`).

Given the chart `c` and direction `u` of the shared germ at `σ`, a spike length `L > 0` whose
clamped chart line stays in `c.target` (`htgt`, automatically satisfiable by taking `L` within the
chart radius), a mid `α` from `p = c.symm (c σ + L • u)` with the same initial germ and with the
chart-argument membership, and the condition that the mid meets the spike only at its starting point
(`hsep`, supplied by the region), there is a piece `P`, globally `C^∞`, immersive on `[0, L+1]`,
injective on `[0, L+1]`, running from `σ` to `α 1` through the straight spike on `[0,L]` and then
following `α`, and staying in `U ∪ spike`.

This is `germ_middle_glue` with its clamp `φ` produced by `exists_clamp` and its `hφtgt` discharged
from the bound `|φ| ≤ L + 3`. -/
theorem exists_gluedPiece {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M)
    (hσ : σ ∈ c.source) {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) {L : ℝ} (hL : 0 < L)
    (htgt : ∀ s : ℝ, |s| ≤ L + 3 → c σ + s • u ∈ c.target)
    {α : ℝ → M} (hαsm : ContMDiff MCreal (MC n) smoothOrder α)
    (hαimm : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Function.Injective (mfderiv MCreal (MC n) α t))
    (hαinj : Set.InjOn α (Set.Icc (0:ℝ) 1))
    (hα0 : α 0 = c.symm (c σ + L • u))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hαgerm : ∀ s : ℝ, 0 ≤ s → s ≤ ε → α s = c.symm (c (α 0) + s • u))
    (hαtgt : ∀ s : ℝ, 0 ≤ s → s ≤ ε → c (α 0) + s • u ∈ c.target)
    (hsep : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 →
      α s ∈ c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L) → α s = α 0)
    {U : Set M} (hαU : α '' Set.Icc (0:ℝ) 1 ⊆ U) :
    ∃ P : ℝ → M, ContMDiff MCreal (MC n) smoothOrder P ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) (L + 1) →
        Function.Injective (mfderiv MCreal (MC n) P t)) ∧
      Set.InjOn P (Set.Icc (0:ℝ) (L + 1)) ∧
      P 0 = σ ∧ P L = α 0 ∧ P (L + 1) = α 1 ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ L → P t = c.symm (c σ + t • u)) ∧
      (∀ t : ℝ, L ≤ t → P t = α (t - L)) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) (L + 1) →
        P t ∈ U ∪ c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L)) := by
  obtain ⟨φ, hφsm, hφid, hφbd⟩ := exists_clamp L hL
  have hφtgt : ∀ t : ℝ, c σ + φ t • u ∈ c.target :=
    fun t => htgt (φ t) (hφbd t)
  have hgerm : ∀ s : ℝ, 0 ≤ s → s ≤ ε →
      α s = c.symm (c (α 0) + s • u) ∧ c (α 0) + s • u ∈ c.target :=
    fun s hs hse => ⟨hαgerm s hs hse, hαtgt s hs hse⟩
  exact germ_middle_glue (n := n) (M := M) hc hσ hu hL hφsm hφid hφtgt hαsm hαimm hαinj hα0
    hε hgerm hsep (X := U ∪ c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L))
    (fun x hx => Set.mem_union_right _ hx) (fun x hx => Set.mem_union_left _ (hαU hx))

end Work.Noncompact.CompressionTube
