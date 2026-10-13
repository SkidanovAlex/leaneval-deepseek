/-
  WilE5 — the assembly of `E5_strat` (fibrewise weak stratification).

  Main deliverable: `Work.WilE5.E5_strat_proved`, whose conclusion is the frozen
  `WilkiesDesign.E.E5_strat` verbatim, from the two frozen inputs
  * `E3_identity` (Gabrielov's bounded-order identity theorem, area E3), and
  * `E2_components` (Khovanskii's bound on the number of connected components of an EA set,
    area E2 — needed to bound the number of *consistent* sign cells by a polynomial).

  Construction (see DESIGN.md and `Cells.lean`):
  * the atoms of `X` are sign-decomposed into the cells of `goodCells X` (nonempty cells contained
    in `X.set`); the number of those cells is polynomial in `X.deg` by `Cells.khovCount`;
  * each cell is a single disjunct, and its own recursion (`levelP`, with the level-indexed test
    profile `MlOf Me (cell.deg) p q`) produces the flat leaves `allStrataP`;
  * a leaf of a state is `Good` (`Strat.flatLeafGoodP`) with the profile data supplied by
    `Strat.levelData` and the state invariants by `Strat.stateInvP`;
  * the leaves of the cell recursion cover the cell (`Strat.coverP`);
  * within one cell the leaves are disjoint or equal (`Cells.leafDisj`), and `uniqSets` turns that
    into a pairwise disjoint list (`Pairwise.filterProps`);
  * different cells are disjoint, and the leaves of different cells lie in different cells
    (`Cells.cellBasic`), giving pairwise disjointness of the concatenation
    (`Cells.flatMapProps`).
-/
import Mathlib
import Submission.Work.WilE5.CellList
import Submission.Work.WilE5.Cells.khovCount
import Submission.Work.WilE5.theListLen
import Submission.Work.WilE5.theListUnion
import Submission.Work.WilE5.theListDeg
import Submission.Work.WilE5.theListGood
import Submission.Work.WilE5.theListPairwise

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5
open WilkiesDesign WilkiesDesign.E

/-- The polynomial that bounds both the length of `theList` and the degree of its members: the
maximum over the finitely many `(p, q)` with `p + q ≤ F` of the per-format bound. -/
def bigB (Me bK : Polynomial ℕ) (F : ℕ) : Polynomial ℕ :=
  ∑ p' ∈ Finset.range (F + 1), ∑ q' ∈ Finset.range (F + 1),
    (bK * bCount Me p' q' + bDeg Me p' q' + Polynomial.C 1)

theorem eval_bigB (Me bK : Polynomial ℕ) (F D : ℕ) :
    (bigB Me bK F).eval D =
      ∑ p' ∈ Finset.range (F + 1), ∑ q' ∈ Finset.range (F + 1),
        (bK * bCount Me p' q' + bDeg Me p' q' + Polynomial.C 1).eval D := by
  rw [bigB, eval_finset_sum]
  exact Finset.sum_congr rfl fun p' _ => eval_finset_sum D _ _

/-- The finite sum dominates each of its terms. -/
theorem eval_bigB_ge (Me bK : Polynomial ℕ) {F p q D : ℕ} (hp : p ∈ Finset.range (F + 1))
    (hq : q ∈ Finset.range (F + 1)) :
    (bK * bCount Me p q + bDeg Me p q + Polynomial.C 1).eval D ≤ (bigB Me bK F).eval D := by
  rw [eval_bigB]
  refine le_trans (Finset.single_le_sum (f := fun q' => (bK * bCount Me p q' + bDeg Me p q' +
      Polynomial.C 1).eval D) (fun _ _ => Nat.zero_le _) hq) ?_
  exact Finset.single_le_sum (f := fun p' => ∑ q' ∈ Finset.range (F + 1),
      (bK * bCount Me p' q' + bDeg Me p' q' + Polynomial.C 1).eval D)
    (fun _ _ => Nat.zero_le _) hp

/-- **E5** (fibrewise weak stratification), from `E3_identity` and `E2_components` (both assumed
verbatim, as in the frozen `WilkiesDesign.E`). -/
theorem E5_strat_proved
    (hE3 : ∀ F : ℕ, ∃ M : Polynomial ℕ, ∀ (k r j : ℕ) (c : EAChain k r) (h : Fin j → EAPoly k r)
      (ι : Fin j → Fin k) (f : EAPoly k r) (x : Fin k → ℝ), k + r ≤ F →
      (∀ a, eaEval c (h a) x = 0) →
      (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) x).det ≠ 0 →
      (∀ m : Fin k → ℕ, (∀ a, m (ι a) = 0) →
        (∑ l, m l ≤ M.eval (∑ a, atomDeg (h a) + atomDeg f)) →
        eaEval c (opMono c h ι m f) x = 0) →
      ∀ᶠ y in nhds x, (∀ a, eaEval c (h a) y = 0) → eaEval c f y = 0)
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y) :
    ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
    ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
      (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
      X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set) := by
  intro F
  obtain ⟨Me, hMe⟩ := hE3 F
  obtain ⟨bK, hbK⟩ := Work.WilE5.Cells.khovCount hE2 F
  refine ⟨F, bigB Me bK F, ?_⟩
  intro p q X hX
  have hpq : p + q ≤ F := by
    have h := hX
    simp only [SemiPf.fmt] at h
    omega
  have hp : p ∈ Finset.range (F + 1) := Finset.mem_range.mpr (by omega)
  have hq : q ∈ Finset.range (F + 1) := Finset.mem_range.mpr (by omega)
  have hE3' : ∀ (j : ℕ) (h : Fin j → EAPoly (p + q) X.r) (ι : Fin j → Fin (p + q))
      (f : EAPoly (p + q) X.r) (x : Fin (p + q) → ℝ),
      (∀ a, eaEval X.c (h a) x = 0) →
      (Matrix.of fun a b => eaEval X.c (eaD X.c (ι b) (h a)) x).det ≠ 0 →
      (∀ m : Fin (p + q) → ℕ, (∀ a, m (ι a) = 0) →
        (∑ l, m l ≤ Me.eval (∑ a, atomDeg (h a) + atomDeg f)) →
        eaEval X.c (opMono X.c h ι m f) x = 0) →
      ∀ᶠ y in nhds x, (∀ a, eaEval X.c (h a) y = 0) → eaEval X.c f y = 0 :=
    fun j h ι f x => hMe (p + q) X.r j X.c h ι f x hX
  have hle : (bK * bCount Me p q + bDeg Me p q + Polynomial.C 1).eval X.deg ≤
      (bigB Me bK F).eval X.deg := eval_bigB_ge Me bK hp hq
  refine ⟨theList Me X, le_trans (theListLen Me X hX bK hbK) hle, ?_,
    (theListUnion Me X hX).symm, theListPairwise Me X hX⟩
  intro S hS
  exact ⟨le_trans (theList_fmt Me X S hS) hX, le_trans (theListDeg Me X hX bK hbK S hS) hle,
    theListGood Me X hX hE3' S hS⟩

end Work.WilE5
