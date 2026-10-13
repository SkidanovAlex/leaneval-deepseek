import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.Endgame.frontier_restrat

namespace Work.WilE7.Endgame

set_option autoImplicit false
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

theorem E2_frontier_strata (h0 : FrontierRestrat) (F : ℕ) :
    ∃ (A : ℕ) (P : Polynomial ℕ),
      ∀ (D K n m : ℕ) (Pie : List (Stratum 0 (n + (m + 1)))),
        (∀ T ∈ Pie, T.Good) → (∀ T ∈ Pie, T.X.fmt ≤ F) → (∀ T ∈ Pie, T.deg ≤ D) →
        (∀ T ∈ Pie, n + (m + 1) - T.j ≤ K + 1) →
        ∃ (Lg : (Fin Pie.length) → List (Stratum 0 (n + (m + 1))))
          (Ly : (Fin Pie.length) → List (SemiPf (n + (m + 1)))),
          (∀ p : Fin Pie.length, (Lg p).length ≤ P.eval D ∧ (Ly p).length ≤ P.eval D ∧
            (∀ S ∈ Lg p, S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ A ∧ S.deg ≤ P.eval D ∧
              n + (m + 1) - S.j ≤ K ∧
              (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
              S.X.set ⊆ closure (Pie.get p).X.set \ (Pie.get p).X.set) ∧
            (∀ Y ∈ Ly p, Y.fmt ≤ A ∧ Y.deg ≤ P.eval D ∧
              NullDimLT (projFirst n (m + 1) '' Y.set) K) ∧
            closure (absSet (Pie.get p)) \ absSet (Pie.get p) ⊆
              (⋃ S ∈ Lg p, absSet S) ∪ ⋃ Y ∈ Ly p, Y.set) := by
  classical
  -- `h0` supplies, for the fixed format bound `F`, a uniform format bound `A` and a length /
  -- degree bound `B`; the list version uses the same `A` and `B + 1`
  -- (so that every `B.eval T.deg` with `T.deg ≤ D` is dominated by `(B+1).eval D`).
  obtain ⟨A, B, hB⟩ := h0 F
  refine ⟨A, B + 1, ?_⟩
  intro D K n m Pie hGood hFmt hDeg hDim
  have hget : ∀ p : Fin Pie.length, Pie.get p ∈ Pie := fun p => List.get_mem Pie p
  -- apply `hB` to each piece of the list
  have hex : ∀ p : Fin Pie.length,
      ∃ (Lg : List (Stratum 0 (n + (m + 1)))) (Ly : List (SemiPf (n + (m + 1)))),
        Lg.length ≤ B.eval D ∧ Ly.length ≤ B.eval D ∧
        (∀ S ∈ Lg, S.Good ∧ S.X.fmt ≤ A ∧ S.deg ≤ B.eval D ∧
          S.X.set ⊆ closure (Pie.get p).X.set \ (Pie.get p).X.set ∧
          n + (m + 1) - S.j ≤ K ∧
          ∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
        (∀ Y ∈ Ly, Y.fmt ≤ A ∧ Y.deg ≤ B.eval D ∧
          NullDimLT (projFirst n (m + 1) '' Y.set) K) ∧
        closure (absSet (Pie.get p)) \ absSet (Pie.get p) ⊆
          (⋃ S ∈ Lg, absSet S) ∪ ⋃ Y ∈ Ly, Y.set := by
    intro p
    exact hB n m K D (Pie.get p) (hGood _ (hget p)) (hFmt _ (hget p)) (hDeg _ (hget p))
      (hDim _ (hget p))
  choose Lg0 Ly0 hspec using hex
  -- drop the empty strata from `Lg`, so that the extra `Nonempty` clause holds
  refine ⟨fun p => (Lg0 p).filter (fun S => decide (S.X.set.Nonempty)), Ly0, ?_⟩
  intro p
  obtain ⟨hL0len, hY0len, hL0, hY0, hcov0⟩ := hspec p
  have hPev : (B + 1).eval D = B.eval D + 1 := by simp
  have hBle : B.eval D ≤ (B + 1).eval D := by rw [hPev]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- length of the filtered `Lg`
    exact le_trans (List.length_filter_le _ _) (le_trans hL0len hBle)
  · -- length of `Ly`
    exact le_trans hY0len hBle
  · -- the `Lg` clauses (the surviving strata keep their properties, and are nonempty)
    intro S hS
    have hS0 : S ∈ Lg0 p := (List.mem_filter.mp hS).1
    have hne : S.X.set.Nonempty := by
      have := (List.mem_filter.mp hS).2
      simpa using this
    obtain ⟨g, f, d, sub, jb, rank⟩ := hL0 S hS0
    exact ⟨g, hne, f, le_trans d hBle, jb, rank, sub⟩
  · -- the `Ly` clauses
    intro Y hY
    obtain ⟨f, d, nul⟩ := hY0 Y hY
    exact ⟨f, le_trans d hBle, nul⟩
  · -- the covering: a stratum of the original list that actually meets the frontier is nonempty,
    -- hence survives the filter, so the filtered union still covers
    intro x hx
    rcases hcov0 hx with h | h
    · left
      obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp h
      have hne : S.X.set.Nonempty := by
        simp only [absSet, Set.mem_image] at hxS
        exact ⟨hxS.choose, hxS.choose_spec.1⟩
      exact Set.mem_iUnion₂.mpr ⟨S, List.mem_filter.mpr ⟨hS, by simpa using hne⟩, hxS⟩
    · right
      exact h

end Work.WilE7.Endgame
