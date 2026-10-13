/-
  WilE4 / CAD — the cell-count recursion for families that are *closed under differentiation*.

  `Bounds.CadCells_length_le` bounds `(CadCells n H).length` by `(bCellLen n).eval (famDeg H)`, but
  it takes the type constancy `htc` for *all* families as a hypothesis, and that is not available:
  the type constancy of a family needs the family to be closed under `pderiv` in the last variable
  (`baseCell_type_const`).  Here the same recursion is carried out with the closure hypothesis
  threaded through, which is what the decomposition can actually supply: the family at each level
  below the top is a `projDataT`-image (`tower (projData H) ++ [0]`), hence closed by
  `projDataT_deriv_closed`.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Bounds
import Submission.Work.WilE4.CAD.BasePreconnected

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

/-- A `filterMap` that keeps the images of the elements satisfying a predicate has the length of the
`filter`. -/
theorem filterMap_ite_some_length {α β : Type*} (l : List α) (p : α → Prop) [DecidablePred p]
    (f : α → β) : (l.filterMap fun a => if p a then some (f a) else none).length = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.filterMap_cons, List.filter_cons]
    by_cases h : p a <;> simp [h, ih]

/-- `bCellLen 1` is `branchBound`. -/
theorem bCellLen_one_eval (E : ℕ) : (bCellLen 1).eval E = branchBound.eval E := by
  simp [bCellLen, Polynomial.eval_mul, Polynomial.eval_comp]
/-- **The cell count at level `n + 1`, for a family closed under differentiation.** -/
theorem CadCells_length_le_closed : ∀ (n : ℕ) (H : List (MvPolynomial (Fin (n + 1)) ℝ)),
    (∀ i : Fin H.length, ∃ j : Fin H.length,
      H.get j = MvPolynomial.pderiv (Fin.last n) (H.get i)) →
    (CadCells (n + 1) H).length ≤ (bCellLen (n + 1)).eval (famDeg H) := by
  intro n
  induction n with
  | zero =>
    intro H _
    -- the single base cell is `ℝ⁰`, whose set is a single point
    have htc : ∃ x ∈ (topCell 0 : SAd 0).set, ∀ w : Fin H.length → SignType,
        RealizedOn H (topCell 0) w → ∃ t : ℝ, ∀ i : Fin H.length,
          SignType.sign ((spec (H.get i) x).eval t) = w i := by
      refine ⟨fun i => i.elim0, by rw [topCell_set]; exact Set.mem_univ _, fun w hw => ?_⟩
      obtain ⟨x, -, t, ht⟩ := hw
      have hx : x = fun i => i.elim0 := Subsingleton.elim _ _
      exact ⟨t, fun i => by rw [← hx, spec_eval_snoc]; exact ht i⟩
    have hlen : (CadCells 1 H).length
        = ((allSign H.length).filter fun v => RealizedOn H (topCell 0) v).length := by
      have h1 : CadCells 1 H = (CadCells 0 (projDataT 0 H)).flatMap fun C =>
          (allSign H.length).filterMap fun v =>
            if RealizedOn H C v then some (cell C H v) else none := CadCells_succ_eq H
      rw [h1, show CadCells 0 (projDataT 0 H) = [topCell 0] from CadCells_zero (projDataT 0 H)]
      simp [filterMap_ite_some_length]
    rw [hlen]
    calc ((allSign H.length).filter fun v => RealizedOn H (topCell 0) v).length
        ≤ 2 * (famDeg H * famDeg H + 1) + 1 := card_realizedOn_le H (topCell 0) htc
      _ = branchBound.eval (famDeg H) := (eval_branchBound (famDeg H)).symm
      _ = (bCellLen 1).eval (famDeg H) := (bCellLen_one_eval (famDeg H)).symm
  | succ k ih =>
    intro H hclosed
    have hclosed' : ∀ i : Fin (projDataT (k + 1) H).length,
        ∃ j : Fin (projDataT (k + 1) H).length,
          (projDataT (k + 1) H).get j
            = MvPolynomial.pderiv (Fin.last k) ((projDataT (k + 1) H).get i) :=
      projDataT_deriv_closed (m := k) H
    have hcount : ∀ C ∈ CadCells (k + 1) (projDataT (k + 1) H),
        ((allSign H.length).filterMap fun v =>
          if RealizedOn H C v then some (cell C H v) else none).length
          ≤ branchBound.eval (famDeg H) := by
      intro C hC
      rw [filterMap_ite_some_length]
      calc ((allSign H.length).filter fun v => RealizedOn H C v).length
          ≤ 2 * (famDeg H * famDeg H + 1) + 1 :=
            card_realizedOn_le H C
              (baseCell_type_const H hclosed (projDataT_base_preconnected H) C hC)
        _ = branchBound.eval (famDeg H) := (eval_branchBound (famDeg H)).symm
    have hlen : (CadCells (k + 1 + 1) H).length
        = ((CadCells (k + 1) (projDataT (k + 1) H)).map fun C =>
            ((allSign H.length).filterMap fun v =>
              if RealizedOn H C v then some (cell C H v) else none).length).sum := by
      rw [CadCells_succ_eq, List.length_flatMap]
    rw [hlen]
    have hstep : ((CadCells (k + 1) (projDataT (k + 1) H)).map fun C =>
          ((allSign H.length).filterMap fun v =>
            if RealizedOn H C v then some (cell C H v) else none).length).sum
        ≤ (CadCells (k + 1) (projDataT (k + 1) H)).length * branchBound.eval (famDeg H) := by
      calc ((CadCells (k + 1) (projDataT (k + 1) H)).map fun C =>
              ((allSign H.length).filterMap fun v =>
                if RealizedOn H C v then some (cell C H v) else none).length).sum
          ≤ ((CadCells (k + 1) (projDataT (k + 1) H)).map fun _ =>
              branchBound.eval (famDeg H)).sum := List.sum_le_sum hcount
        _ = (CadCells (k + 1) (projDataT (k + 1) H)).length * branchBound.eval (famDeg H) := by
            simp [List.map_const', List.sum_replicate, nsmul_eq_mul]
    refine hstep.trans ?_
    have h1 : (CadCells (k + 1) (projDataT (k + 1) H)).length
        ≤ (bCellLen (k + 1)).eval (projDataTBound.eval (famDeg H)) :=
      (ih (projDataT (k + 1) H) hclosed').trans
        (polynomial_eval_mono (bCellLen (k + 1)) (famDeg_projDataT_le_bound H))
    calc (CadCells (k + 1) (projDataT (k + 1) H)).length * branchBound.eval (famDeg H)
        ≤ (bCellLen (k + 1)).eval (projDataTBound.eval (famDeg H)) * branchBound.eval (famDeg H) :=
          Nat.mul_le_mul_right _ h1
      _ = (bCellLen (k + 1 + 1)).eval (famDeg H) := by
          rw [show (bCellLen (k + 1 + 1))
              = (bCellLen (k + 1)).comp projDataTBound * branchBound from rfl]
          simp only [Polynomial.eval_mul, Polynomial.eval_comp]

end Work.WilE4.CAD
