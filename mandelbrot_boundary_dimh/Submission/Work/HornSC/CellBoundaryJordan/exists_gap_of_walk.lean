import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.DartGraph

namespace Work.HornSC.CellBoundaryJordan

/-- **A non-backtracking walk in a finite graph revisits a vertex periodically.**

Let `u : ℕ → α` be a walk on a finite vertex set `V` (all values of `u` lie in `V`) whose
consecutive pairs `(u n, u (n+1))` are darts of `G`, and which never immediately backtracks,
i.e. `u (n+2) ≠ u n` for all `n`.  Then there are `L ≥ 3` and a starting index `i0` such that
`u i0 = u (i0 + L)` (the walk closes up at distance `L`) and such that the vertices
`u i0, u (i0+1), …, u (i0+L-1)` are pairwise distinct (the closed block is a simple cycle).

Proof.  Finiteness of `V` forces a repetition `u x = u y` with `x ≠ y`, so the set of positive
"repeat distances" `{L > 0 | ∃ i, u i = u (i + L)}` is nonempty; let `L` be its minimum and `i0`
a witness.  If moreover `u (i0 + a) = u (i0 + b)` for some `a < b < L`, then `b - a` is a positive
repeat distance properly smaller than `L`, contradicting minimality.  Finally `L ≠ 1` because
`G` has no loops (so consecutive vertices differ) and `L ≠ 2` because the walk does not
immediately backtrack. -/
theorem exists_gap_of_walk {α : Type*} [DecidableEq α] (G : DartGraph α) (V : Finset α)
    (u : ℕ → α) (hmem : ∀ n, u n ∈ V) (hadj : ∀ n, (u n, u (n + 1)) ∈ G.D)
    (hnb : ∀ n, u (n + 2) ≠ u n) :
    ∃ L i0, 3 ≤ L ∧ u i0 = u (i0 + L) ∧ ∀ a b, a < b → b < L → u (i0 + a) ≠ u (i0 + b) := by
  classical
  -- Finiteness of `V` gives a repetition: two distinct indices with equal image.
  have hex : ∃ L : ℕ, 0 < L ∧ ∃ i, u i = u (i + L) := by
    obtain ⟨x, -, y, -, hxy, heq⟩ :=
      Set.Infinite.exists_ne_map_eq_of_mapsTo (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
        (fun n _ => hmem n) (Finset.finite_toSet V)
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact ⟨y - x, Nat.sub_pos_of_lt hlt, x, by
        rw [Nat.add_sub_cancel' (le_of_lt hlt)]; exact heq⟩
    · exact ⟨x - y, Nat.sub_pos_of_lt hgt, y, by
        rw [Nat.add_sub_cancel' (le_of_lt hgt)]; exact heq.symm⟩
  -- Take the minimal positive repeat distance.
  have hspec := Nat.find_spec hex
  obtain ⟨i0, hi0⟩ := hspec.2
  refine ⟨Nat.find hex, i0, ?_, hi0, ?_⟩
  · -- the minimal repeat distance is at least `3`
    have hLpos : 0 < Nat.find hex := hspec.1
    by_contra hcon
    have h12 : Nat.find hex = 1 ∨ Nat.find hex = 2 := by omega
    rcases h12 with h1 | h2
    · -- `L = 1` would be a loop
      rw [h1] at hi0
      exact G.noLoop (u i0, u (i0 + 1)) (hadj i0) hi0
    · -- `L = 2` would be an immediate backtrack
      rw [h2] at hi0
      exact (hnb i0) hi0.symm
  · -- the block `u i0, …, u (i0+L-1)` is repetition free, by minimality of `L`
    intro a b hab hbL heqab
    have hP : 0 < b - a ∧ ∃ i, u i = u (i + (b - a)) := by
      refine ⟨Nat.sub_pos_of_lt hab, i0 + a, ?_⟩
      have hidx : i0 + a + (b - a) = i0 + b := by omega
      rw [hidx]; exact heqab
    exact Nat.find_min hex (lt_of_le_of_lt (Nat.sub_le b a) hbL) hP

end Work.HornSC.CellBoundaryJordan
