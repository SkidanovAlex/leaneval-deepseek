/-
  Area E7 / `CoreLT_succ`, case B: from an absolute `Good` stratum to the sheets over a base cell.

  This file is the S34 skeleton of the case-B step.  It contains

  * `hgraph_of_branch`: the local graph of the *branch* through `z` (`hbranch`) together with
    the cofinality `hcof` ("the branch through `z` covers `C` locally") produce `hgraph`, the
    local-graph hypothesis of `Work.WilE7.DimAPI.sheets_of_localGraph` (E1);
  * `sheets_of_absStratum`: E1 applied to an absolute `Good` stratum, i.e. the global sheets over
    the cell `C` (this is the form in which the case-B step consumes them).

  The geometric inputs `hbranch` and `hcof` are supplied, in the assembly, by
  `CoreStep.localGraph_on_branch` (the `ℓ`/implicit-function-theorem argument) and by the
  `Σ`-avoidance argument of `NOTES_S34_coreLT_succ_caseB.md` §3.

  NOTE (S34): the translation from "the cells are compatible with the level graphs" (the
  conclusion of `Work.WilE7.SheetData.multiStrata_cellsX`) to "the cells are compatible with
  `projFirst (p+1) m '' P.set`" must be done in the *reindexed* picture
  (`SemiPf (p+(m+1)) ≃ SemiPf ((p+1)+m)`), because `p + (m+1)` and `(p+1) + m` are not
  definitionally equal and the naive statement does not even elaborate.  See
  `CoreStep.Basic.projFirst_one_eq_init` for the `Fin.init` form of the base projection.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.sheets_of_localGraph
import Submission.Work.WilE7.CoreStep.Basic
import Submission.Work.WilE7.DecompDefs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.CoreStep
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-! ## §1. From the branch graph plus cofinality to E1's `hgraph` -/

/-- **The local graph of the branch, transported to `C`.**

`hbranch` exhibits the branch of `X` through `z` as the graph of a continuous `g` over the
projection of that branch (`π '' (X ∩ V)`), and `hcof` says that the branch covers `C` locally
(every base point of `C` near `π z` is the projection of a point of `X ∩ V`, for every
neighbourhood `V` of `z`).  Together they give E1's `hgraph` hypothesis: a neighbourhood `V` of
`z` and a neighbourhood `U` of `π z` such that some continuous `g` parametrises `X ∩ V` over
`C ∩ U` and *all* points of `X ∩ V` over `C` lie on that graph. -/
theorem hgraph_of_branch {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ))
    (z : Fin (p + q) → ℝ) (hz : z ∈ X) (hzC : projFirst p q z ∈ C)
    (hbranch : ∃ V ∈ nhds z, ∃ g : (Fin p → ℝ) → (Fin q → ℝ),
      ContinuousOn g (projFirst p q '' (X ∩ V)) ∧
      (∀ x ∈ projFirst p q '' (X ∩ V), Fin.append x (g x) ∈ X ∩ V) ∧
      (∀ w ∈ X ∩ V, g (projFirst p q w) = projSnd p q w))
    (hcof : ∀ V ∈ nhds z, ∃ U ∈ nhds (projFirst p q z),
      C ∩ U ⊆ projFirst p q '' (X ∩ V)) :
    ∃ V ∈ nhds z, ∃ U ∈ nhds (projFirst p q z), ∃ g : (Fin p → ℝ) → (Fin q → ℝ),
      ContinuousOn g (C ∩ U) ∧ (∀ x ∈ C ∩ U, Fin.append x (g x) ∈ X ∩ V) ∧
      ∀ w ∈ X ∩ V, projFirst p q w ∈ C →
        projFirst p q w ∈ U ∧ g (projFirst p q w) = projSnd p q w := by
  classical
  obtain ⟨V₀, hV₀, g, hgcont, hggraph, hguniq⟩ := hbranch
  obtain ⟨U, hU, hUsub₀⟩ := hcof V₀ hV₀
  -- cut `V₀` down so that the projection of `X ∩ V` lies in `U`
  set V : Set (Fin (p + q) → ℝ) := V₀ ∩ (projFirst p q ⁻¹' U) with hVdef
  have hVmem : V ∈ nhds (z : Fin (p + q) → ℝ) :=
    Filter.inter_mem hV₀ ((continuous_projFirst p q).continuousAt.preimage_mem_nhds hU)
  have hVsubV₀ : V ⊆ V₀ := fun w hw => hw.1
  have hVU : ∀ w ∈ V, projFirst p q w ∈ U := fun w hw => hw.2
  -- the branch neighbourhood can be cut down to `V`
  have hUsub : C ∩ U ⊆ projFirst p q '' (X ∩ V) := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := hUsub₀ hx
    exact ⟨w, ⟨hw.1, hw.2, show projFirst p q w ∈ U from by rw [hwx]; exact hx.2⟩, hwx⟩
  refine ⟨V, hVmem, U, hU, g, ?_, ?_, ?_⟩
  · -- continuity on `C ∩ U ⊆ π '' (X ∩ V)`
    refine hgcont.mono fun x hx => ?_
    obtain ⟨w, hw, hwx⟩ := hUsub hx
    exact ⟨w, ⟨hw.1, hVsubV₀ hw.2⟩, hwx⟩
  · -- the graph point over `x ∈ C ∩ U`
    intro x hx
    obtain ⟨w, hw, hwx⟩ := hUsub hx
    have hgw : g (projFirst p q w) = projSnd p q w := hguniq w ⟨hw.1, hVsubV₀ hw.2⟩
    rw [← hwx, hgw, append_projFirst_projSnd]
    exact hw
  · -- uniqueness over `C`
    intro w hw hwC
    exact ⟨hVU w hw.2, hguniq w ⟨hw.1, hVsubV₀ hw.2⟩⟩

/-! ## §2. The sheets over a base cell, from an absolute `Good` stratum -/

/-- **The sheets over a cell `C` for an absolute stratum.**

All hypotheses of E1 (`Work.WilE7.DimAPI.sheets_of_localGraph`) are supplied: the cell, the
covering `C ⊆ π '' X`, boundedness of `X = absSet T` (inside the cube), finiteness of the
fibres, closedness of `X` over `C` (`hclosed`, which the assembly gets from the `Σ`-avoidance
of the frontier) and the local graph (`hgraph`, from the branch data `hbranch` and the
cofinality `hcof` via `hgraph_of_branch`).  The conclusion is E1's: `k` continuous sheets,
pointwise distinct, with values in `X`, covering every point of `X` over `C`, and `k` equal to
the cardinality of every fibre over `C`. -/
theorem sheets_of_absStratum {n q : ℕ} (T : Stratum 0 (n + q)) (hT : T.Good)
    (C : Set (Fin n → ℝ)) (hCell : WilkiesDesign.IsCell n C)
    (hCsub : C ⊆ projFirst n q '' (absSet T))
    (hbdd : Bornology.IsBounded (absSet T))
    (hfin : ∀ x : Fin n → ℝ, (fiber (absSet T) x).Finite)
    (hclosed : ∀ z ∈ closure (absSet T), projFirst n q z ∈ C → z ∈ absSet T)
    (hbranch : ∀ z ∈ absSet T, projFirst n q z ∈ C →
      ∃ V ∈ nhds z, ∃ g : (Fin n → ℝ) → (Fin q → ℝ),
        ContinuousOn g (projFirst n q '' (absSet T ∩ V)) ∧
        (∀ x ∈ projFirst n q '' (absSet T ∩ V), Fin.append x (g x) ∈ absSet T ∩ V) ∧
        (∀ w ∈ absSet T ∩ V, g (projFirst n q w) = projSnd n q w))
    (hcof : ∀ z ∈ absSet T, projFirst n q z ∈ C → ∀ V ∈ nhds z,
      ∃ U ∈ nhds (projFirst n q z), C ∩ U ⊆ projFirst n q '' (absSet T ∩ V)) :
    ∃ (k : ℕ) (s : Fin k → (Fin n → ℝ) → (Fin q → ℝ)),
      (∀ j, ContinuousOn (s j) C) ∧
      (∀ x ∈ C, Function.Injective fun j : Fin k => s j x) ∧
      (∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ absSet T) ∧
      (∀ x ∈ C, (fiber (absSet T) x).ncard = k) ∧
      (∀ z ∈ absSet T, projFirst n q z ∈ C →
        ∃ j : Fin k, s j (projFirst n q z) = projSnd n q z) :=
  DimAPI.sheets_of_localGraph (absSet T) C hCell hCsub hbdd
    (fun x _ => hfin x) hclosed
    (fun z hz hzC =>
      hgraph_of_branch (absSet T) C z hz hzC (hbranch z hz hzC) (hcof z hz hzC))

end Work.WilE7.CoreStep
