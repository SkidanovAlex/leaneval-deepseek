import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.DartGraph
import Submission.Work.HornSC.CellBoundaryJordan.exists_dart_ne
import Submission.Work.HornSC.CellBoundaryJordan.exists_gap_of_walk

namespace Work.HornSC.CellBoundaryJordan

/-- Deterministic choice of a successor of a dart.  Given a state `s = (a, b)` which is a dart of
`G`, `stepS` produces the state `(b, nextV)`, where `nextV` is a vertex with `(b, nextV) ∈ G.D`
and `nextV ≠ a`; the latter exists by `exists_dart_ne` because the degree of `b` is even and
positive.  Since `Classical.choose` is a function of the proposition `∃ c, (b,c) ∈ G.D ∧ c ≠ a`,
which itself depends only on `s`, the map `stepS` depends only on the state `s` (not on the way it
was reached): this is what makes the walk built from `stepS` eventually deterministic. -/
private noncomputable def stepS {α : Type*} [DecidableEq α] (G : DartGraph α)
    (hG : ∀ a, Even (G.deg a)) (s : {x : α × α // (x.1, x.2) ∈ G.D}) :
    {x : α × α // (x.1, x.2) ∈ G.D} :=
  ⟨(((s : α × α).2, Classical.choose (exists_dart_ne G hG s.2))),
   (Classical.choose_spec (exists_dart_ne G hG s.2)).1⟩

/-- Every nonempty `DartGraph` with all degrees even contains a cycle (of combinatorial
length `≥ 3`).  Strategy: pick a dart `a0 → a1`; every vertex appearing in `D` has even positive
degree, hence degree `≥ 2`, so one can build a walk `u` with `(u n, u (n+1)) ∈ D` for all `n`
which never immediately backtracks (`u (n+2) ≠ u n`).  Pigeonhole
(`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`) on the finite vertex set
`G.D.image Prod.fst ∪ G.D.image Prod.snd` gives two indices with equal image; let `m > 0` be the
minimal such difference (`Nat.find`).  Then `m ≥ 3` and `k ↦ u (i + k % m)` is a cycle of length
`m`. -/
theorem exists_cycle_of_even {α : Type*} [DecidableEq α] (G : DartGraph α)
    (h : ∀ a, Even (G.deg a)) (hne : G.D.Nonempty) : ∃ C : G.Cycle, C.darts ⊆ G.D := by
  classical
  obtain ⟨e0, he0⟩ := hne
  -- the walk: states are darts of `G`, starting from the dart `e0`
  let s0 : {x : α × α // (x.1, x.2) ∈ G.D} := ⟨(e0.1, e0.2), he0⟩
  let wlk : ℕ → {x : α × α // (x.1, x.2) ∈ G.D} := fun n => (stepS G h)^[n] s0
  let u : ℕ → α := fun n => ((wlk n : α × α)).1
  have hwlk : ∀ n, wlk (n+1) = stepS G h (wlk n) := by
    intro n
    show (stepS G h)^[n+1] s0 = stepS G h ((stepS G h)^[n] s0)
    rw [Function.iterate_succ_apply']
  -- the two defining properties of the step
  have hstep1 : ∀ n, ((wlk (n+1) : α × α)).1 = ((wlk n : α × α)).2 := by
    intro n
    rw [hwlk n]
    simp only [stepS]
  have hstep2 : ∀ n, ((wlk (n+1) : α × α)).2 ≠ ((wlk n : α × α)).1 := by
    intro n
    rw [hwlk n]
    simp only [stepS]
    exact (Classical.choose_spec (exists_dart_ne G h (wlk n).2)).2
  have hdart : ∀ n, (((wlk n : α × α)).1, ((wlk n : α × α)).2) ∈ G.D := by
    intro n
    exact (wlk n).2
  -- consecutive vertices are joined by a dart
  have hadj : ∀ n, (u n, u (n+1)) ∈ G.D := by
    intro n
    have hd := hdart n
    have h1 : u (n+1) = ((wlk n : α × α)).2 := by
      show ((wlk (n+1) : α × α)).1 = _
      exact hstep1 n
    rw [h1]
    exact hd
  -- the walk never immediately backtracks
  have hnb : ∀ n, u (n+2) ≠ u n := by
    intro n
    have h2 := hstep2 n
    have h3 : u (n+2) = ((wlk (n+1) : α × α)).2 := by
      show ((wlk (n+2) : α × α)).1 = _
      exact hstep1 (n+1)
    have h4 : u n = ((wlk n : α × α)).1 := by
      show ((wlk n : α × α)).1 = _
      rfl
    rw [h3, h4]
    exact h2
  -- all vertices of the walk lie in the finite set of vertices of `G`
  let V : Finset α := G.D.image Prod.fst ∪ G.D.image Prod.snd
  have hmem : ∀ n, u n ∈ V := by
    intro n
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨(wlk n : α × α), (wlk n).2, rfl⟩
  -- pigeonhole plus minimality of the repeat distance
  obtain ⟨L, i0, hL3, hclose, hcons⟩ := exists_gap_of_walk G V u hmem hadj hnb
  -- the periodic sequence of the cycle
  let W : ℕ → α := fun k => u (i0 + k % L)
  have hWmod : ∀ k, k < L → W k = u (i0 + k) := by
    intro k hk
    show u (i0 + k % L) = u (i0 + k)
    rw [Nat.mod_eq_of_lt hk]
  have hper : ∀ j, W (j + L) = W j := by
    intro j
    show u (i0 + (j + L) % L) = u (i0 + j % L)
    rw [Nat.add_mod_right]
  have hinj : ∀ i j, i < L → j < L → W i = W j → i = j := by
    intro a b ha hb hab
    rw [hWmod a ha, hWmod b hb] at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hab (hcons a b hlt hb)
    · exact absurd hab.symm (hcons b a hgt ha)
  have hadjW : ∀ j, j < L → (W j, W (j+1)) ∈ G.D := by
    intro k hk
    rcases lt_or_eq_of_le (show k + 1 ≤ L by omega) with hlt | heq
    · -- the step does not wrap around
      show (u (i0 + k % L), u (i0 + (k + 1) % L)) ∈ G.D
      rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt]
      have hh := hadj (i0 + k)
      have hh' : (u (i0 + k), u (i0 + (k + 1))) ∈ G.D := by
        simpa [show i0 + (k + 1) = i0 + k + 1 by omega] using hh
      exact hh'
    · -- the last step closes the block: `k + 1 = L`
      show (u (i0 + k % L), u (i0 + (k + 1) % L)) ∈ G.D
      rw [Nat.mod_eq_of_lt hk, heq, Nat.mod_self, Nat.add_zero]
      have hh := hadj (i0 + L - 1)
      rw [show i0 + L - 1 + 1 = i0 + L by omega] at hh
      have hk' : i0 + k = i0 + L - 1 := by omega
      rw [hk', hclose]
      exact hh
  exact ⟨{ L := L, hL := hL3, w := W, per := hper, inj := hinj, adj := hadjW },
    DartGraph.Cycle.darts_subset _⟩

end Work.HornSC.CellBoundaryJordan
