import Mathlib
import Submission.Work.Noncompact.CompressionTube.LineBuild.nested_canals
import Submission.Work.Noncompact.Routing.exhaustion_tools
import Submission.Work.Noncompact.CompressionTube.LineBuild.ray_state

/-!
# The seed lies in the shell of the exhaustion, outside the next region

The junctions of the line construction are the spine's seeds `q b i`.  Two elementary facts about
them are used at every stage:

* `nc_seed_deep`: a set contained in `interior (K (i+1))` (for instance a small chart ball around
  the seed `q b i`) meets **none** of the regions `D m` with `m ≥ i + 1`.  This is what makes the
  access ball of a piece miss all the deeper regions (the "two shell" invariant).
* `nc_seed_notMem`: the seed `q b i` itself does not lie in `D (i+1)`, so the junction is *outside*
  the region of the next piece.
-/

namespace Work.Noncompact.Routing

open Set Topology
open scoped Topology
open Work.Noncompact.CompressionTube

variable {M : Type*} [TopologicalSpace M]

/-- **A set inside `interior (K (i+1))` misses every region `D m`, `m ≥ i+1`.** -/
theorem nc_seed_deep {K : ℕ → Set M} (hKmono : Monotone K) {D : ℕ → Set M}
    (hDK : ∀ i, D i ⊆ (K i)ᶜ) {U : Set M} {i : ℕ} (hU : U ⊆ interior (K (i + 1))) :
    ∀ m : ℕ, i + 1 ≤ m → Disjoint U (D m) := by
  intro m hm
  refine Set.disjoint_left.mpr fun x hxU hxD => ?_
  have hxK : x ∈ (K m)ᶜ := hDK m hxD
  exact hxK (hKmono hm (interior_subset (hU hxU)))

/-- **The seed is outside the next region.**  For `i > lev b` the seed `q b i` lies in
`interior (K (i+1))`, while `D (i+1) ⊆ (K (i+1))ᶜ`. -/
theorem nc_seed_notMem {K : ℕ → Set M} {B : Set M} {lev : B → ℕ} {q : B → ℕ → M}
    {γ : B → ℕ → ℝ → M} (h : SpineData K B lev q γ) {D : ℕ → Set M}
    (hDK : ∀ i, D i ⊆ (K i)ᶜ) {b : B} {i : ℕ} (hi : lev b < i) :
    q b i ∉ D (i + 1) := by
  intro hmem
  have hq : q b i ∈ interior (K (i + 1)) := (h.q_shell b i hi).1
  have hK : q b i ∈ (K (i + 1))ᶜ := hDK (i + 1) hmem
  exact hK (interior_subset hq)


/-- **The escaping condition `hdeep` of the assembly.**  If the piece at level `i` is confined to
the region `D i`, and `D i` avoids the level `K i` of an exhaustion, then the pieces at large level
miss every compact set: this is `hdeep` of `Work.Noncompact.ProperLine.rayAssembly_of_pieces`. -/
theorem nc_hdeep_of_confinement {K : ℕ → Set M} {D : ℕ → Set M} {P : ℕ → ℝ → M}
    (hKmono : ∀ i, K i ⊆ K (i + 1)) (hKint : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKu : (⋃ i, K i) = (Set.univ : Set M))
    (hDK : ∀ i, D i ⊆ (K i)ᶜ) (hPD : ∀ i, P i '' Set.Icc (0:ℝ) 1 ⊆ D i) :
    ∀ K' : Set M, IsCompact K' → ∃ I, ∀ i, I ≤ i → P i '' Set.Icc (0:ℝ) 1 ∩ K' = ∅ := by
  intro K' hK'
  obtain ⟨N, hN⟩ := exists_avoid_level hKmono hKint hKu hK'
  refine ⟨N, fun i hi => ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxP, hxK'⟩
  have hxD : x ∈ D i := hPD i hxP
  have hxK : x ∈ (K i)ᶜ := hDK i hxD
  exact hxK (monotone_nat_of_le_succ hKmono hi (hN hxK'))


/-- **The first-piece straightening: a chart ball at a shell point.**  If `z ∈ D m` lies outside
`closure (D (m+1))`, then (in the nested setting, with no spine at hand) there is a centred chart at
`z` and a radius `δ > 0` such that the ball `c.symm '' closedBall 0 δ` is contained in `D m` and is
disjoint from **every** `D k`, `k ≥ m+1`.

This is what makes the *terminal part* of a piece a single straight chart arc: the arrival ball is
placed inside the shell at the next junction, and by the two-shell confinement it is the only part
of the piece that meets the next region `D (m+1)`.
-/
theorem nc_shell_chartBall {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {D : ℕ → Set M} (hDo : ∀ i, IsOpen (D i)) (hDmono : ∀ i, D (i + 1) ⊆ D i)
    {m : ℕ} {z : M} (hzD : z ∈ D m) (hzcl : z ∉ closure (D (m + 1))) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (δ : ℝ),
      z ∈ c.source ∧ c z = 0 ∧ 0 < δ ∧
      c.symm '' Metric.closedBall 0 δ ⊆ D m ∧
      (∀ k : ℕ, m + 1 ≤ k → Disjoint (c.symm '' Metric.closedBall 0 δ) (D k)) := by
  have hmono : ∀ {a b : ℕ}, a ≤ b → D b ⊆ D a := by
    intro a b hab
    induction hab with
    | refl => exact subset_rfl
    | step _ ih => exact (hDmono _).trans ih
  have hUopen : IsOpen (D m ∩ (closure (D (m + 1)))ᶜ) :=
    (hDo m).inter isClosed_closure.isOpen_compl
  have hzU : z ∈ D m ∩ (closure (D (m + 1)))ᶜ := ⟨hzD, hzcl⟩
  have hU : D m ∩ (closure (D (m + 1)))ᶜ ∈ nhds z := hUopen.mem_nhds hzU
  obtain ⟨δ, hδ, hδsub⟩ :=
    ncChartBall_subset_nhds (n := n) (c := ncChartAt n z) (z := z)
      (ncChartAt_source (n := n) (M := M) z) (ncChartAt_self (n := n) (M := M) z) hU
  refine ⟨ncChartAt n z, δ, ncChartAt_source (n := n) (M := M) z,
    ncChartAt_self (n := n) (M := M) z, hδ, ?_, ?_⟩
  · exact hδsub.trans Set.inter_subset_left
  · intro k hk
    rw [Set.disjoint_left]
    rintro y hy hyD
    exact (hδsub hy).2 (subset_closure (hmono (by omega : m + 1 ≤ k) hyD))


/-- **The trace of a piece in the next region is its straight terminal germ.**  This is the transfer
from the engine's output to the trace control (T): if the piece's image lies in `X ∪ Bacc` (the
engine's `P '' Icc ⊆ X ∪ (access ball)`), the region `X` meets `D 1` only inside the arrival ball,
the access ball misses `D 1`, and the germ is the straight chart piece `G` of the arrival ball, then

  `P ∩ D 1 = G ∩ D 1`,

i.e. what the *next* stage sees of the drawn chain inside the next region is exactly one straight
chart arc — so `nc_sdiff_arcs_pathConnected` applies to `D 1 \ (G ∩ D 1)`. -/
theorem nc_trace_eq_germ {M : Type*} [TopologicalSpace M] {D : ℕ → Set M}
    {X Bacc Barr G P : Set M}
    (hPsub : P ⊆ X ∪ Bacc)
    (hX : X ∩ D 1 ⊆ Barr)
    (hacc : Disjoint Bacc (D 1))
    (hgerm : P ∩ Barr = G) :
    P ∩ D 1 = G ∩ D 1 := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxP, hxD⟩
    have hxBarr : x ∈ Barr := by
      rcases hPsub hxP with h | h
      · exact hX (Set.mem_inter h hxD)
      · exact absurd hxD (Set.disjoint_left.mp hacc h)
    have hxPG : x ∈ G := by
      have : x ∈ P ∩ Barr := ⟨hxP, hxBarr⟩
      rwa [hgerm] at this
    exact ⟨hxPG, hxD⟩
  · rintro x ⟨hxG, hxD⟩
    have hxP : x ∈ P := by
      have hxPB : x ∈ P ∩ Barr := by rwa [hgerm]
      exact hxPB.1
    exact ⟨hxP, hxD⟩


/-- **The offset-2 straightening: the interface the two-shell actually needs.**  If `z ∈ D m` lies
outside `closure (D (m+2))`, then there is a centred chart at `z` and `δ > 0` such that
`c.symm '' closedBall 0 δ ⊆ D m` and the ball is disjoint from `D k` for **all** `k ≥ m+2`.

This is the form used by the stage construction: the access ball at a junction at level `m` only has
to miss the regions two levels deeper (those are the only ones the two-shell invariant lets a piece
meet), and the hypothesis `z ∉ closure (D (m+2))` is the one supplied by
`nc_exists_junction`/the spine seeds — unlike the offset-1 shell condition, which can fail for the
nested hypotheses alone (see `NOTES.md`). -/
theorem nc_shell_chartBall' {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {D : ℕ → Set M} (hDo : ∀ i, IsOpen (D i)) (hDmono : ∀ i, D (i + 1) ⊆ D i)
    {m : ℕ} {z : M} (hzD : z ∈ D m) (hzcl : z ∉ closure (D (m + 2))) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (δ : ℝ),
      z ∈ c.source ∧ c z = 0 ∧ 0 < δ ∧
      c.symm '' Metric.closedBall 0 δ ⊆ D m ∧
      (∀ k : ℕ, m + 2 ≤ k → Disjoint (c.symm '' Metric.closedBall 0 δ) (D k)) := by
  have hmono : ∀ {a b : ℕ}, a ≤ b → D b ⊆ D a := by
    intro a b hab
    induction hab with
    | refl => exact subset_rfl
    | step _ ih => exact (hDmono _).trans ih
  have hUopen : IsOpen (D m ∩ (closure (D (m + 2)))ᶜ) :=
    (hDo m).inter isClosed_closure.isOpen_compl
  have hzU : z ∈ D m ∩ (closure (D (m + 2)))ᶜ := ⟨hzD, hzcl⟩
  have hU : D m ∩ (closure (D (m + 2)))ᶜ ∈ nhds z := hUopen.mem_nhds hzU
  obtain ⟨δ, hδ, hδsub⟩ :=
    ncChartBall_subset_nhds (n := n) (c := ncChartAt n z) (z := z)
      (ncChartAt_source (n := n) (M := M) z) (ncChartAt_self (n := n) (M := M) z) hU
  refine ⟨ncChartAt n z, δ, ncChartAt_source (n := n) (M := M) z,
    ncChartAt_self (n := n) (M := M) z, hδ, ?_, ?_⟩
  · exact hδsub.trans Set.inter_subset_left
  · intro k hk
    rw [Set.disjoint_left]
    rintro y hy hyD
    exact (hδsub hy).2 (subset_closure (hmono (by omega : m + 2 ≤ k) hyD))


/-- **A junction exists as soon as `D i` meets `interior (K (i+2))`.**  Such a point `x` is
automatically outside `closure (D (i+2))`, because a whole neighbourhood of `x` lies in
`interior (K (i+2))` while `D (i+2) ⊆ (K (i+2))ᶜ`, and `interior K ∩ Kᶜ = ∅`.

This is one of the two cases of the junction availability `(J₂)` of `NOTES.md`; the other case
(`D i` disjoint from `interior (K (i+2))`) is the remaining open point of the base step. -/
theorem nc_junction_of_meets_interior {M : Type*} [TopologicalSpace M] {D : ℕ → Set M}
    {K : ℕ → Set M} {i : ℕ} (hDK : D (i + 2) ⊆ (K (i + 2))ᶜ)
    (hx : (D i ∩ interior (K (i + 2))).Nonempty) :
    ∃ z ∈ D i, z ∉ closure (D (i + 2)) := by
  obtain ⟨x, hxD, hxK⟩ := hx
  refine ⟨x, hxD, ?_⟩
  intro hcl
  obtain ⟨y, hyU, hyD⟩ :=
    mem_closure_iff.mp hcl (interior (K (i + 2))) isOpen_interior hxK
  exact (hDK hyD) (interior_subset hyU)


/-- **The spine's seeds are junctions in the operational sense.**  For `m > lev b`:

* `q b m ∈ D b m` (so the seed lies in the region of level `m`), and
* `q b m ∉ closure (D b (m + 2))` (so `nc_shell_chartBall'` gives a chart ball at the seed inside
  `D b m` meeting **no** `D b k`, `k ≥ m + 2`).

This is step 2 of the base-step recipe in its final form, and it is what the nested family alone
cannot supply (see the punctured-family counterexample in `NOTES.md`): the seed sits in
`interior (K (m+1))`, whose points are free of every deeper region. -/
theorem nc_seed_junction {M : Type*} [TopologicalSpace M] {K : ℕ → Set M} (hKmono : Monotone K)
    {B : Set M} {lev : B → ℕ} {q : B → ℕ → M} {γ : B → ℕ → ℝ → M} (h : SpineData K B lev q γ)
    {D : B → ℕ → Set M} (hDK : ∀ (b : B) i, D b i ⊆ (K i)ᶜ)
    (htail : ∀ (b : B) (i : ℕ), lev b ≤ i →
      (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ D b i)
    {b : B} {m : ℕ} (hm : lev b + 1 ≤ m) :
    q b m ∈ D b m ∧ q b m ∉ closure (D b (m + 2)) := by
  have hlev : lev b < m := by omega
  constructor
  · have hmem : q b m ∈ ⋃ j : {j : ℕ // m ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1 :=
      Set.mem_iUnion.mpr ⟨⟨m, le_rfl⟩,
        ⟨0, Set.left_mem_Icc.mpr zero_le_one, (h.ends b m (le_of_lt hlev)).1⟩⟩
    exact htail b m (le_of_lt hlev) hmem
  · intro hcl
    have hq_int : q b m ∈ interior (K (m + 1)) := (h.q_shell b m hlev).1
    obtain ⟨y, hyU, hyD⟩ :=
      mem_closure_iff.mp hcl (interior (K (m + 1))) isOpen_interior hq_int
    exact (hDK b (m + 2) hyD) (hKmono (by omega : m + 1 ≤ m + 2) (interior_subset hyU))


/-- **The image form of the trace read-off** — the form the piece engine produces.  If a curve `P`
takes `[0,1]` into `X ∪ Bacc`, the region `X` meets `D 1` only inside the arrival ball `Barr`, the
access ball misses `D 1`, and the germ of `P` inside `Barr` is the straight chart arc `G`, then the
trace of the curve in the next region `D 1` is exactly `G ∩ D 1`: one chart-straight arc. -/
theorem nc_trace_eq_germ_image {M : Type*} [TopologicalSpace M] {D : ℕ → Set M}
    {X Bacc Barr G : Set M} {P : ℝ → M}
    (hPsub : ∀ t ∈ Set.Icc (0:ℝ) 1, P t ∈ X ∪ Bacc)
    (hX : X ∩ D 1 ⊆ Barr)
    (hacc : Disjoint Bacc (D 1))
    (hgerm : P '' Set.Icc (0:ℝ) 1 ∩ Barr = G) :
    P '' Set.Icc (0:ℝ) 1 ∩ D 1 = G ∩ D 1 :=
  nc_trace_eq_germ (P := P '' Set.Icc (0:ℝ) 1)
    (by rintro x ⟨t, ht, rfl⟩; exact hPsub t ht) hX hacc hgerm

end Work.Noncompact.Routing
