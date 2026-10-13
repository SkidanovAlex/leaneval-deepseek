import Mathlib
import Submission.Work.WilE7.CoreStep.caseB
import Submission.Work.WilE7.CoreStep.localGraph_on_branch
import Submission.Work.CoreStep.branchDomain_open
import Submission.Work.WilE7.CoreStep.GermDefs

namespace Work.CoreStep

open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E

/-- The absolute set of a stratum is bounded, being contained in the cube `[-1,1]^N`. -/
private theorem absSet_isBounded' {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    Bornology.IsBounded (Work.WilE7.MainDesign.absSet S) :=
  (Work.CoreStep.cubeC_isCompact' N).isBounded.subset (Work.CoreStep.absSet_subset_cubeC S)

theorem sheets_over_cell_of_hrank {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)
    (hfin : ∀ x : Fin n → ℝ,
      (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite)
    (C : Set (Fin n → ℝ)) (hCell : WilkiesDesign.IsCell n C)
    (hCsub : C ⊆ WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T))
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T)
    (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hWlgood : ∀ W ∈ Wl, W.Good)
    (hWlsub : ∀ W ∈ Wl, W.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set)
    (hWlcov : (Work.WilE7.CoreStep.absPairSet T).set = ⋃ W ∈ Wl, W.X.set)
    (havoid : ∀ (u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ) (x₀ : Fin n → ℝ),
      u ∈ T.X.set → v ∈ T.X.set →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) = x₀ →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) = x₀ → x₀ ∈ C →
      Work.WilE7.CoreStep.absPtInv u ≠ Work.WilE7.CoreStep.absPtInv v →
      ∀ W ∈ Wl, Work.WilE7.CoreStep.pairPtUp u v ∈ W.X.set →
        n + (m + 1) - T.j ≤ Work.WilE7.CoreStep.pPair n m - W.j) :
    ∃ (k : ℕ) (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ)),
      (∀ j, ContinuousOn (s j) C) ∧
      (∀ x ∈ C, Function.Injective fun j : Fin k => s j x) ∧
      (∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
        Fin.append x (s j x) ∈ Work.WilE7.MainDesign.absSet T) ∧
      (∀ x ∈ C, (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).ncard = k) ∧
      (∀ z ∈ Work.WilE7.MainDesign.absSet T,
        WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst n (m + 1) z) =
          WilkiesDesign.E.projSnd n (m + 1) z) := by
  -- The absolute set is bounded (it lives in the cube).
  have hbdd : Bornology.IsBounded (Work.WilE7.MainDesign.absSet T) := absSet_isBounded' T
  -- The local branch through every point of `absSet T`, from the implicit function theorem
  -- `localGraph_on_branch` (which uses `hT` and `hrank`).
  have hbranch : ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ V ∈ nhds z, ∃ g : (Fin n → ℝ) → (Fin (m + 1) → ℝ),
        ContinuousOn g
          (WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T ∩ V)) ∧
        (∀ x ∈ WilkiesDesign.E.projFirst n (m + 1) ''
            (Work.WilE7.MainDesign.absSet T ∩ V),
          Fin.append x (g x) ∈ Work.WilE7.MainDesign.absSet T ∩ V) ∧
        (∀ w ∈ Work.WilE7.MainDesign.absSet T ∩ V,
          g (WilkiesDesign.E.projFirst n (m + 1) w) =
            WilkiesDesign.E.projSnd n (m + 1) w) := by
    intro z hz _
    obtain ⟨w, hw, hweq⟩ := hz
    subst hweq
    exact Work.WilE7.CoreStep.localGraph_on_branch T hT hrank w hw
  -- Branch cofinality: the branch through a point over `C` covers `C` near the base point.
  -- This is exactly `branchDomain_open`, whose hypotheses are those of the present statement.
  have hcof : ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → ∀ V ∈ nhds z,
        ∃ U ∈ nhds (WilkiesDesign.E.projFirst n (m + 1) z),
          C ∩ U ⊆ WilkiesDesign.E.projFirst n (m + 1) ''
            (Work.WilE7.MainDesign.absSet T ∩ V) := by
    intro z hz hzC V hV
    obtain ⟨w, hw, hweq⟩ := hz
    subst hweq
    exact branchDomain_open T hT hrank hfin C hCsub hclosed Wl hWlgood hWlsub hWlcov
      havoid w hw hzC V hV
  exact Work.WilE7.CoreStep.sheets_of_absStratum T hT C hCell hCsub hbdd hfin hclosed
    hbranch hcof

end Work.CoreStep
