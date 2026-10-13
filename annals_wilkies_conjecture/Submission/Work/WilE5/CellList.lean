/-
  WilE5 — the list of strata produced by the cell-wise construction (`theList`), and its basic API.

  This file only sets up the objects and the easy properties; the four quantitative/structural
  properties used by the assembly are `theList_len`, `theList_union`, `theList_good` and
  `theList_pairwise` in `Submission/Work/WilE5/Assembly/`.
-/
import Mathlib
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Profile
import Submission.Work.WilE5.Cells
import Submission.Work.WilE5.Pairwise
import Submission.Work.WilE5.Pairwise.uniqSetsSublist
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5
open WilkiesDesign WilkiesDesign.E

variable {p q : ℕ}

/-- The strata of one sign cell `C`: the leaves of the recursion on the cell's own `SemiPf` set
(with the test profile indexed by the cell's degree), deduplicated by underlying set. -/
def cellStrata (Me : Polynomial ℕ) (X : SemiPf (p + q)) (C : Basic (p + q) X.r) :
    List (Stratum p q) :=
  uniqSets (allStrataP (cellSemi X C) (MlOf Me (cellSemi X C).deg p q)
    (NPhi Me (cellSemi X C).deg p q) q)

/-- The full list of strata: over all sign cells of `X` that are nonempty and contained in `X.set`. -/
def theList (Me : Polynomial ℕ) (X : SemiPf (p + q)) : List (Stratum p q) :=
  (goodCells X).flatMap fun σ => cellStrata Me X (cell X σ)

/-- The degree of the single-disjunct set `cellSemi X C` is the degree of `C`. -/
theorem cellSemi_deg {k : ℕ} (X : SemiPf k) (C : Basic k X.r) :
    (cellSemi X C).deg = Basic.deg C := by
  simp [cellSemi, SemiPf.deg]

/-- Membership in `allStrataP`, spellt out. -/
theorem mem_allStrataP {X : SemiPf (p + q)} {Ml : ℕ → ℕ} {NΦ n : ℕ} {S : Stratum p q} :
    S ∈ allStrataP X Ml NΦ n ↔
      ∃ k ∈ List.range (n + 1), ∃ σ ∈ levelP X Ml NΦ k, S = flatStratumP X Ml NΦ σ := by
  simp only [allStrataP, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨k, hk, σ, hσ, rfl⟩
    exact ⟨k, hk, σ, hσ, rfl⟩
  · rintro ⟨k, hk, σ, hσ, rfl⟩
    exact ⟨k, hk, σ, hσ, rfl⟩

/-- Membership in `theList`, spellt out. -/
theorem mem_theList {Me : Polynomial ℕ} {X : SemiPf (p + q)} {S : Stratum p q} :
    S ∈ theList Me X ↔ ∃ σ ∈ goodCells X, S ∈ cellStrata Me X (cell X σ) := by
  simp only [theList, List.mem_flatMap]

/-- A member of `cellStrata` is a member of the cell's `allStrataP`. -/
theorem mem_cellStrata {Me : Polynomial ℕ} {X : SemiPf (p + q)} {C : Basic (p + q) X.r}
    {S : Stratum p q} (h : S ∈ cellStrata Me X C) :
    S ∈ allStrataP (cellSemi X C) (MlOf Me (cellSemi X C).deg p q)
      (NPhi Me (cellSemi X C).deg p q) q :=
  (Work.WilE5.Pairwise.uniqSetsSublist _).mem h

/-- A member of `cellStrata` is a leaf of the cell's recursion. -/
theorem exists_state_of_mem_cellStrata {Me : Polynomial ℕ} {X : SemiPf (p + q)}
    {C : Basic (p + q) X.r} {S : Stratum p q} (h : S ∈ cellStrata Me X C) :
    ∃ k ∈ List.range (q + 1), ∃ σ ∈ levelP (cellSemi X C) (MlOf Me (cellSemi X C).deg p q)
        (NPhi Me (cellSemi X C).deg p q) k,
      S = flatStratumP (cellSemi X C) (MlOf Me (cellSemi X C).deg p q)
        (NPhi Me (cellSemi X C).deg p q) σ :=
  (mem_allStrataP).mp (mem_cellStrata h)

/-- The format of a member of `theList` is the format of `X` (all pieces use the chain of `X`). -/
theorem theList_fmt (Me : Polynomial ℕ) (X : SemiPf (p + q)) :
    ∀ S ∈ theList Me X, SemiPf.fmt S.X ≤ SemiPf.fmt X := by
  intro S hS
  obtain ⟨σ, -, hS⟩ := (mem_theList).mp hS
  obtain ⟨k, -, τ, -, rfl⟩ := exists_state_of_mem_cellStrata hS
  rfl

/-- Every member of `theList` is contained in the cell it comes from. -/
theorem theList_subset_cell (Me : Polynomial ℕ) (X : SemiPf (p + q)) :
    ∀ S ∈ theList Me X, ∃ σ ∈ goodCells X, S.X.set ⊆ (cellSemi X (cell X σ)).set := by
  intro S hS
  obtain ⟨σ, hσ, hS⟩ := (mem_theList).mp hS
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨k, -, τ, -, rfl⟩ := exists_state_of_mem_cellStrata hS
  rw [flatStratumP_X, flatSemiPfP_eq, Work.WilE5.Strat.flatSemiPf_set_eq]
  exact Set.inter_subset_left

/-- Every member of `theList` lies inside `X.set`. -/
theorem theList_subset (Me : Polynomial ℕ) (X : SemiPf (p + q)) :
    ∀ S ∈ theList Me X, S.X.set ⊆ X.set := by
  intro S hS
  obtain ⟨σ, hσ, hsub⟩ := theList_subset_cell Me X S hS
  exact fun x hx => (of_decide_eq_true (List.mem_filter.mp hσ).2).2 (hsub hx)

end Work.WilE5
