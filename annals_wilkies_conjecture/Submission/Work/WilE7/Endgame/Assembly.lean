/-
  Area E7 — the top-level assembly of the `CoreLT_succ` endgame (`Work.WilE7.Endgame`).

  This file is the *glue* of the endgame design `sources/wilkiesE7end/wilkies_e7_coreltsucc.md`
  (and its `_REVIEW.md`).  It contains no new mathematics: it instantiates the seven reviewed
  nodes, which are stated (with their proofs) in the sibling modules of `Submission/Work/WilE7/Endgame/`,
  and runs the lexicographic induction

    `Core n`  ⟶  `CoreLT n K` (all `K`)  ⟶  `Core (n+1)`  ⟶  `∀ n, Core n`

  ending at the frozen target `WilkiesDesign.E.E7_prop_main`.

  * `gcase_vertical_cell` is the plan's `GCaseVertical`, proved here from the three geometry nodes
    `attain_dichotomy_of_pairAvoid` (G1), `isOpen_projTopSet_inter_cyl_of_pairAvoid` (G2) and
    `cell_compat_of_levelGraphs` (G3).  The proof is the plan file's, with the plan's sorried
    nodes replaced by the proved `Endgame` ones.
  * `CoreLT_succ` is the plan's assembly `coreLT_succ_of_cellRefine h (cellRefine_of_nodes ...)`.
  * `CoreLT_all`, `Core_all` and `E7_prop_main_proved` are the induction skeleton.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.Endgame.CellRefineS
import Submission.Work.WilE7.Endgame.cell_compat_of_levelGraphs
import Submission.Work.WilE7.Endgame.attain_dichotomy_of_pairAvoid
import Submission.Work.WilE7.Endgame.isOpen_projTopSet_inter_cyl_of_pairAvoid
import Submission.Work.WilE7.Endgame.frontier_restrat
import Submission.Work.WilE7.Endgame.sigmaFamily_vpairs
import Submission.Work.WilE7.Endgame.sigmaFamily_len_unif
import Submission.Work.WilE7.Endgame.cellRefine_of_nodesB
import Submission.Work.WilE7.Endgame.CoreLTSuccOfCellRefineS
import Submission.Work.WilE7.CoreDefs
import Submission.Work.WilE7.DimAPI.CoreLT_zero
import Submission.Work.WilE7.DimAPI.Core_succ_of_CoreLT

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt)

/-! ## 1. The vertical row over a `G`-cell (plan §5, proved from G1–G3) -/

/-- The plan's `GCaseVertical`, proved from the three geometry nodes.  Note that the plan file's
own `gcase_vertical_cell` is *not* used (it is downstream of the seven `sorry`s of that file);
this is the same twenty-line proof against the proved `Endgame` nodes. -/
theorem gcase_vertical_cell : GCaseVertical := by
  intro n m r C hCpc S hS k s hcont hsub C' hC' hcompat T hT himm hvert t₀ hk₀ hrankR hdimR
    Wl hWgood hWsub hWcov hWlow Vl hVgood hVsub hVcov hlow htop hbound
  -- G2: relative openness of the image of `T`
  have hAopen := isOpen_projTopSet_inter_cyl_of_pairAvoid T (S t₀) hT (hS t₀) himm hvert hrankR
    hdimR C hk₀ (s t₀) (hcont t₀) (hsub t₀) Wl hWgood hWsub hWcov hWlow
  -- G1: every level graph is inside or outside the image of `T`
  have hgraph : ∀ t j, Work.WilE7.gr C (fun x => (s t j x) (Fin.last m)) ⊆ projTopSet T ∨
      Disjoint (Work.WilE7.gr C (fun x => (s t j x) (Fin.last m))) (projTopSet T) := by
    intro t j
    rcases attain_dichotomy_of_pairAvoid (S t) T (hS t) hT himm C hCpc (s t) (hcont t) (hsub t)
        (Vl t) (hVgood t) (hVsub t) (hVcov t) (hlow t) (htop t) j with h | h
    · exact Or.inl (Work.WilE7.CoreStep.gr_subset_or_disjoint_of_attain T C _ h)
    · exact Or.inr (Work.WilE7.CoreStep.gr_disjoint_of_not_attain T C _ h)
  -- G3: the clopen argument on each cell
  have hf : ∀ t j, ContinuousOn (fun x => (s t j x) (Fin.last m)) C := fun t j =>
    (continuous_apply (Fin.last m)).comp_continuousOn (hcont t j)
  exact cell_compat_of_levelGraphs hC' k (fun t j x => (s t j x) (Fin.last m)) hf hcompat
    (projTopSet T) hAopen hgraph hbound

/-! ## 2. `CoreLT_succ` -/

/-- The level-`(n+1)` step of the lexicographic induction, from the reviewed nodes.  The refinement
node is `cellRefine_of_nodesB` (the S56 repair of the plan's `cellRefine_of_nodes`, whose statement
is FALSE — see the header of `CellRefineS.lean`), consumed by the S56 repair of E3',
`coreLT_succ_of_cellRefineS`. -/
theorem CoreLT_succ (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5) (hE6 : HypE6) {n K : ℕ}
    (_hC : Work.WilE7.Core n) (h : CoreLT n K) : CoreLT n (K + 1) :=
  coreLT_succ_of_cellRefineS h
    (cellRefine_of_nodesB hFC hE2 hE5 hE6 (frontier_restrat hE5 hE6) (sigmaFamily_vpairs hE5 hE6)
      gcase_vertical_cell n K)

/-! ## 3. The two inductions -/

/-- `CoreLT n ·` for all `K`, from `Core n`. -/
theorem CoreLT_all (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5) (hE6 : HypE6) {n : ℕ}
    (hC : Work.WilE7.Core n) : ∀ K : ℕ, CoreLT n K := by
  intro K
  induction K with
  | zero => exact Work.WilE7.DimAPI.CoreLT_zero hC
  | succ K ih => exact CoreLT_succ hFC hE2 hE5 hE6 hC ih

/-- `Core n` for all `n`, from the four hypotheses. -/
theorem Core_all (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5) (hE6 : HypE6) :
    ∀ n : ℕ, Work.WilE7.Core n := by
  intro n
  induction n with
  | zero => exact Work.WilE7.Core_zero
  | succ n ih => exact Work.WilE7.DimAPI.Core_succ_of_CoreLT (n := n) (CoreLT_all hFC hE2 hE5 hE6 ih (n + 1))

/-! ## 4. The frozen target -/

/-- `E7_prop_main_proved`: the frozen statement `WilkiesDesign.E.E7_prop_main` of
`Submission/Work/WilE7/E7_prop_main_proved.lean`, from the four hypotheses. -/
theorem E7_prop_main_proved_of_hyp
    (hFC : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ)
      (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n m '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set)
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set) :
    ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf (n + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        ∃ C : Finset (Set (Fin n → ℝ)),
          WilkiesDesign.E.IsCylDecompOn n (WilkiesDesign.E.cubeC n) C ∧
          (∀ i, ∀ κ ∈ C,
            κ ⊆ WilkiesDesign.E.projFirst n m '' (X i).set ∨
              Disjoint κ (WilkiesDesign.E.projFirst n m '' (X i).set)) ∧
          C.card ≤ MvPolynomial.eval ![D, k] b ∧
          ∀ κ ∈ C, WilkiesDesign.E.Star a (c.eval D) n κ ∧ WilkiesDesign.E.SubPf n κ :=
  Work.WilE7.Core_all_imp_target (Core_all hFC hE2 hE5 hE6)

end Work.WilE7.Endgame
