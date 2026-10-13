import Mathlib
import Submission.Work.WilE5.CellList
import Submission.Work.WilE5.Cells.cellBasic
import Submission.Work.WilE5.Bounds.countP
import Submission.Work.WilE5.Cells.flatMapProps
import Submission.Work.WilE5.Pairwise.uniqSetsSublist

namespace Work.WilE5

/-- Sum of a constant list: `∑_{x ∈ l} c = |l| * c`. -/
private lemma sum_map_const_nat {α : Type*} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- `theList` is a `flatMap` over the good cells, so its length is the sum of the lengths of the
blocks. -/
private lemma theList_eq_flatMap {p q : ℕ} (Me : Polynomial ℕ) (X : WilkiesDesign.E.SemiPf (p + q)) :
    Work.WilE5.theList Me X = (Work.WilE5.goodCells X).flatMap
      (fun σ => Work.WilE5.cellStrata Me X (Work.WilE5.cell X σ)) := rfl

theorem theListLen {p q F : ℕ} (Me : Polynomial ℕ) (X : WilkiesDesign.E.SemiPf (p + q))
    (hX : X.fmt ≤ F) (bK : Polynomial ℕ)
    (hbK : ∀ (k : ℕ) (Y : WilkiesDesign.E.SemiPf k), Y.fmt ≤ F →
      (Work.WilE5.goodCells Y).length ≤ bK.eval Y.deg) :
    (Work.WilE5.theList Me X).length ≤
      (bK * Work.WilE5.bCount Me p q + Work.WilE5.bDeg Me p q + Polynomial.C 1).eval X.deg := by
  -- Each cell contributes at most `bCount Me p q` evaluated at the *cell's* degree, which is at
  -- most `bCount Me p q` evaluated at `X.deg` because a cell's degree is a sub-sum of `X.deg`.
  have hcell : ∀ σ ∈ Work.WilE5.goodCells X,
      (Work.WilE5.cellStrata Me X (Work.WilE5.cell X σ)).length ≤
        (Work.WilE5.bCount Me p q).eval X.deg := by
    intro σ _
    have h1 : (Work.WilE5.cellStrata Me X (Work.WilE5.cell X σ)).length ≤
        (Work.WilE5.allStrataP (Work.WilE5.cellSemi X (Work.WilE5.cell X σ))
          (Work.WilE5.MlOf Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q)
          (Work.WilE5.NPhi Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q) q).length :=
      (Work.WilE5.Pairwise.uniqSetsSublist _).length_le
    have h2 : (Work.WilE5.allStrataP (Work.WilE5.cellSemi X (Work.WilE5.cell X σ))
          (Work.WilE5.MlOf Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q)
          (Work.WilE5.NPhi Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q) q).length ≤
        (Work.WilE5.bCount Me p q).eval (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg :=
      (Work.WilE5.Bounds.countP (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)) Me).2
    have hdeg : (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg ≤ X.deg := by
      rw [Work.WilE5.cellSemi_deg]
      exact Work.WilE5.cell_deg_le X σ
    have h3 : (Work.WilE5.bCount Me p q).eval (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg ≤
        (Work.WilE5.bCount Me p q).eval X.deg :=
      Work.WilE5.eval_mono_nat hdeg
    exact h1.trans (h2.trans h3)
  have hlen : (Work.WilE5.theList Me X).length =
      ((Work.WilE5.goodCells X).map
        (fun σ => (Work.WilE5.cellStrata Me X (Work.WilE5.cell X σ)).length)).sum := by
    rw [theList_eq_flatMap, List.length_flatMap]
  have hsum : ((Work.WilE5.goodCells X).map
        (fun σ => (Work.WilE5.cellStrata Me X (Work.WilE5.cell X σ)).length)).sum ≤
      ((Work.WilE5.goodCells X).map (fun _ => (Work.WilE5.bCount Me p q).eval X.deg)).sum :=
    List.sum_le_sum hcell
  have hconst : ((Work.WilE5.goodCells X).map
        (fun _ => (Work.WilE5.bCount Me p q).eval X.deg)).sum =
      (Work.WilE5.goodCells X).length * (Work.WilE5.bCount Me p q).eval X.deg :=
    sum_map_const_nat _ _
  have hcells : (Work.WilE5.goodCells X).length ≤ bK.eval X.deg := hbK (p + q) X hX
  have hlast : bK.eval X.deg * (Work.WilE5.bCount Me p q).eval X.deg ≤
      (bK * Work.WilE5.bCount Me p q + Work.WilE5.bDeg Me p q + Polynomial.C 1).eval X.deg := by
    rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    omega
  rw [hlen]
  exact hsum.trans ((le_of_eq hconst).trans ((Nat.mul_le_mul_right _ hcells).trans hlast))

end Work.WilE5
