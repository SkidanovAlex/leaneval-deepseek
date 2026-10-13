/-
  WilC1 — the graph of a term of `LRc` is `REx`.

  `GraphSet t ⊆ ℝ^{ι ⊕ Fin 1}` is the graph of the term function of `t` (last coordinate = value).
  This file proves `REx_graphSet_of_cases : REx (ι ⊕ Fin 1) (GraphSet t)` by induction on `t`.
  The four inductive cases (sum, product, negation, `rexp`) are supplied as hypotheses — they are
  proved in the sibling modules `REx_graph_tAdd`, `REx_graph_tMul`, `REx_graph_tNeg`,
  `REx_graph_tRexp` — so that this file can be built independently of them.
-/
import Submission.Work.WilC1.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture

/-! ## Realization of the nullary symbols with a general argument tuple -/

theorem realize_tConst_ts {ι : Type*} (v : ι → ℝ) (c : (constantsOn ℝ).Functions 0)
    (ts : Fin 0 → LRc.Term ι) :
    Term.realize v (Term.func (L := LRc) (α := ι) (l := 0) (Sum.inr c) ts) = c := by
  rw [show ts = (fun i : Fin 0 => i.elim0) from funext (fun i => i.elim0)]
  exact realize_tConst v c

theorem realize_tZero_ts {ι : Type*} (v : ι → ℝ) (ts : Fin 0 → LRc.Term ι) :
    Term.realize v (Term.func (L := LRc) (α := ι) (l := 0)
      (Sum.inl (Sum.inl Ring.zeroFunc)) ts) = 0 := by
  rw [show ts = (fun i : Fin 0 => i.elim0) from funext (fun i => i.elim0)]
  exact realize_tZero v

theorem realize_tOne_ts {ι : Type*} (v : ι → ℝ) (ts : Fin 0 → LRc.Term ι) :
    Term.realize v (Term.func (L := LRc) (α := ι) (l := 0)
      (Sum.inl (Sum.inl Ring.oneFunc)) ts) = 1 := by
  rw [show ts = (fun i : Fin 0 => i.elim0) from funext (fun i => i.elim0)]
  exact realize_tOne v

/-! ## The base cases of the graph induction -/

/-- The graph of a constant: a zero set. -/
theorem REx_graphSet_constVal {ι : Type*} (r : ℝ) :
    REx (ι ⊕ Fin 1) {x : (ι ⊕ Fin 1) → ℝ | x (Sum.inr 0) = r} := by
  refine (REx.zeroSet (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) -
    MvPolynomial.C r)).congr ?_
  ext x
  simp only [Set.mem_ofPred_eq, rexpEval_sub, rexpEval_X_inl, rexpEval_C, sub_eq_zero]

/-- The graph of a variable. -/
theorem REx_graphSet_var {ι : Type*} (i : ι) :
    REx (ι ⊕ Fin 1) (GraphSet (Term.var i)) := by
  refine (REx.zeroSet (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) -
    MvPolynomial.X (Sum.inl (Sum.inl i)))).congr ?_
  ext x
  simp only [Set.mem_ofPred_eq, GraphSet, rexpEval_sub, rexpEval_X_inl, sub_eq_zero,
    Term.realize_var, Function.comp_apply]

/-- The graph of a term whose head symbol is a constant symbol. -/
theorem REx_graphSet_constSym {ι : Type*} {l : ℕ} (c : (constantsOn ℝ).Functions l)
    (ts : Fin l → LRc.Term ι) :
    REx (ι ⊕ Fin 1) (GraphSet (Term.func (L := LRc) (α := ι) (l := l) (Sum.inr c) ts)) := by
  match l with
  | 0 =>
    refine (REx_graphSet_constVal (ι := ι) c).congr ?_
    ext x
    simp only [Set.mem_ofPred_eq, GraphSet, realize_tConst_ts]
  | k + 1 => exact (isEmpty_functions_constantsOn_succ (α := ℝ) (n := k)).elim c

/-- The graph of a term whose head symbol is the ring constant `0`. -/
theorem REx_graphSet_zeroSym {ι : Type*} (ts : Fin 0 → LRc.Term ι) :
    REx (ι ⊕ Fin 1) (GraphSet (Term.func (L := LRc) (α := ι) (l := 0)
      (Sum.inl (Sum.inl Ring.zeroFunc)) ts)) := by
  refine (REx_graphSet_constVal (ι := ι) 0).congr ?_
  ext x
  simp only [Set.mem_ofPred_eq, GraphSet, realize_tZero_ts]

/-- The graph of a term whose head symbol is the ring constant `1`. -/
theorem REx_graphSet_oneSym {ι : Type*} (ts : Fin 0 → LRc.Term ι) :
    REx (ι ⊕ Fin 1) (GraphSet (Term.func (L := LRc) (α := ι) (l := 0)
      (Sum.inl (Sum.inl Ring.oneFunc)) ts)) := by
  refine (REx_graphSet_constVal (ι := ι) 1).congr ?_
  ext x
  simp only [Set.mem_ofPred_eq, GraphSet, realize_tOne_ts]

/-! ## The induction -/

/-- Every term of `LRc` has an `REx` graph.  The four inductive cases are hypotheses. -/
theorem REx_graphSet_of_cases {ι : Type*}
    (hadd : ∀ {a b : LRc.Term ι}, REx (ι ⊕ Fin 1) (GraphSet a) →
      REx (ι ⊕ Fin 1) (GraphSet b) → REx (ι ⊕ Fin 1) (GraphSet (tAdd a b)))
    (hmul : ∀ {a b : LRc.Term ι}, REx (ι ⊕ Fin 1) (GraphSet a) →
      REx (ι ⊕ Fin 1) (GraphSet b) → REx (ι ⊕ Fin 1) (GraphSet (tMul a b)))
    (hneg : ∀ {a : LRc.Term ι}, REx (ι ⊕ Fin 1) (GraphSet a) →
      REx (ι ⊕ Fin 1) (GraphSet (tNeg a)))
    (hexp : ∀ {a : LRc.Term ι}, REx (ι ⊕ Fin 1) (GraphSet a) →
      REx (ι ⊕ Fin 1) (GraphSet (tRexp a)))
    (t : LRc.Term ι) : REx (ι ⊕ Fin 1) (GraphSet t) := by
  induction t using Term.rec with
  | var i => exact REx_graphSet_var i
  | func f ts ih =>
    rcases f with (g | h) | c
    · rcases g with _ | _ | _ | _ | _
      · -- addition
        have hts : ts = ![ts 0, ts 1] := by funext i; fin_cases i <;> rfl
        rw [hts]
        exact hadd (ih 0) (ih 1)
      · -- multiplication
        have hts : ts = ![ts 0, ts 1] := by funext i; fin_cases i <;> rfl
        rw [hts]
        exact hmul (ih 0) (ih 1)
      · -- negation
        have hts : ts = ![ts 0] := by funext i; fin_cases i <;> rfl
        rw [hts]
        exact hneg (ih 0)
      · -- zero
        exact REx_graphSet_zeroSym ts
      · -- one
        exact REx_graphSet_oneSym ts
    · -- rexp
      cases h
      have hts : ts = ![ts 0] := by funext i; fin_cases i <;> rfl
      rw [hts]
      exact hexp (ih 0)
    · -- constant symbols
      exact REx_graphSet_constSym c ts

end Work.WilC1
