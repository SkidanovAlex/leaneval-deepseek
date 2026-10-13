import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.DimAPI.stratum_nullDimLE
import Submission.Work.WilE7.DimAPI.nullDimLE_mono_dim

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- **The pair-set Σ-piece.**  Given `E5` (fibrewise weak stratification) and a `Good` absolute
stratum `T` at the split `0 | n + (m+1)`, the decomposition of the pair set `absPairSet T` produced
by `E5` contains a sub-list of pieces of dimension `< n + (m+1) - T.j` which is exactly the set of
points of `absPairSet T` all of whose `Good` sub-strata-in-`absPairSet T` have that small dimension.

The sub-list is obtained from the `E5` decomposition by keeping the members `S` with
`pPair n m - S.j < n + (m+1) - T.j`; `dim S = pPair n m - S.j` and the projection to `ℝ^n` of such
a member has measure-dimension at most its dimension (`stratum_nullDimLE` + `NullDimLE.projFirst`
+ `nullDimLE_mono_dim`). -/
theorem sigmaOfPiece
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (n m : ℕ) (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good) (F : ℕ) (hF : (Work.WilE7.CoreStep.absPairSet T).fmt ≤ F) :
    ∃ Sl : List (WilkiesDesign.E.SemiPf (0 + Work.WilE7.CoreStep.pPair n m)),
      (∀ W ∈ Sl, ∃ W' : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m),
          W'.Good ∧ W'.X.set = W.set ∧
          Work.WilE7.CoreStep.pPair n m - W'.j < n + (m + 1) - T.j) ∧
      (∀ W ∈ Sl, Work.WilE7.MainDesign.NullDimLT
          (WilkiesDesign.E.projFirst n (m + 1) ''
            (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) ''
              (Work.WilE7.MainDesign.absPt '' W.set)))
          (n + (m + 1) - T.j + 1)) ∧
      (∀ z ∈ (Work.WilE7.CoreStep.absPairSet T).set,
        (∀ W' : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m),
            W'.Good → W'.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set →
            z ∈ W'.X.set → Work.WilE7.CoreStep.pPair n m - W'.j < n + (m + 1) - T.j) →
        ∃ W ∈ Sl, z ∈ W.set) := by
  obtain ⟨a, b, hb⟩ := hE5 F
  obtain ⟨L, hLlen, hLgood, hLcover, hLdisj⟩ :=
    hb 0 (Work.WilE7.CoreStep.pPair n m) (Work.WilE7.CoreStep.absPairSet T) hF
  refine ⟨(L.filter fun S => Work.WilE7.CoreStep.pPair n m - S.j < n + (m + 1) - T.j).map
    (fun S => S.X), ?_, ?_, ?_⟩
  · intro W hW
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hW
    obtain ⟨S, ⟨hSL, hSj⟩, rfl⟩ := hW
    exact ⟨S, (hLgood S hSL).2.2, rfl, hSj⟩
  · intro W hW
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hW
    obtain ⟨S, ⟨hSL, hSj⟩, rfl⟩ := hW
    have hGood : S.Good := (hLgood S hSL).2.2
    have hnd := Work.WilE7.DimAPI.stratum_nullDimLE (n := n + (m + 1)) (m := n + (m + 1))
      S hGood
    have hproj := Work.WilE7.MainDesign.NullDimLE.projFirst (n := n) (m := m + 1) hnd
    have hle : (n + (m + 1)) + (n + (m + 1)) - S.j ≤ n + (m + 1) - T.j := Nat.le_of_lt hSj
    have hmono := Work.WilE7.DimAPI.nullDimLE_mono_dim hproj hle
    exact hmono
  · intro z hz hgood
    rw [hLcover] at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨S, hSL, hzS⟩ := hz
    have hGood : S.Good := (hLgood S hSL).2.2
    have hsub : S.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set := by
      intro w hw
      rw [hLcover]
      exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hSL, hw⟩⟩
    have hineq : Work.WilE7.CoreStep.pPair n m - S.j < n + (m + 1) - T.j :=
      hgood S hGood hsub hzS
    refine ⟨S.X, ?_, hzS⟩
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨S, ⟨hSL, hineq⟩, rfl⟩

end Work.CoreStep
