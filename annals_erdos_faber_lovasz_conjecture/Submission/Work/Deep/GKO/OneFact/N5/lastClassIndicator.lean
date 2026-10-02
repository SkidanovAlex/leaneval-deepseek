import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Basic

namespace Work.Deep.GKO.OneFact.N5

/-- The cross edges at `v` consumed by one completed class.  Let `Pl` be a matching whose edges
are either `K`-edges or `N`-edges, with the `N`-edges joining vertices inside one side of `(A,B)`
and the `K`-edges joining opposite sides.  Then the number `useCount K Pl v` of `K`-neighbours of
`v` that `Pl` uses is at most `1`, and whenever it equals `1` either `N` misses `v` entirely (so
the class contributes `1` to the miss count of `v`) or `Pl` re-matches `v` (so it contributes `1`
to the re-match count of `v`); that is, `useCount K Pl v ≤ crossUseInd N Pl v`. -/
theorem lastClassIndicator {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B)
    {N K Pl : SimpleGraph (Fin n)}
    (hNin : ∀ u v, N.Adj u v → Work.Deep.GKO.OneFact.N5.IsInsidePair A B u v)
    (hK : ∀ u v, K.Adj u v → Work.Deep.GKO.OneFact.N5.IsCrossPair A B u v)
    (hmatch : Work.Deep.GKO.IsMatching' Pl) (v : Fin n) :
    Work.Deep.GKO.OneFact.N5.useCount K Pl v ≤
      Work.Deep.GKO.OneFact.N5.crossUseInd N Pl v := by
  classical
  -- A matching uses at most one edge at `v`, so at most one `K`-neighbour of `v` is used.
  have hle1 : useCount K Pl v ≤ 1 := by
    rw [useCount, Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hmatch v a b ha.2 hb.2
  by_cases h1 : useCount K Pl v = 1
  · -- If some `K`-edge at `v` is used, then either `v ∈ uncov N`, or `Pl` re-matches `v`:
    -- otherwise `Pl` would use an `N`-edge at `v`, which is an inside pair, while the used
    -- `K`-edge `vw` is a cross pair.
    have hcu : crossUseInd N Pl v = 1 := by
      rw [crossUseInd]
      have hpos : 0 < useCount K Pl v := by omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨hKw, hPw⟩ := hw
      have hcross : IsCrossPair A B v w := hK v w hKw
      by_cases hv : v ∈ uncov N
      · simp [hv]
      · have hrem : Rematched N Pl v :=
          ⟨w, hPw, fun hN => not_inside_of_cross hAB hcross (hNin v w hN)⟩
        simp [hv, hrem]
    rw [h1, hcu]
  · have h0 : useCount K Pl v = 0 := by omega
    simp [h0]

end Work.Deep.GKO.OneFact.N5
