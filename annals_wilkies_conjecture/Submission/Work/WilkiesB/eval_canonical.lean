import Mathlib
import Submission.Work.WilkiesB.Term
import Submission.Work.WilkiesB.Defs

/-!
# The canonical witness satisfies the node equations

This file proves `Work.WilkiesB.eval_canonical`: for the *canonical* witness vector `y`, whose
slots `k, …, k + numExp t - 1` hold `nodeVals c u t` (the arguments of the `exp`-nodes of `t`),
the constraint polynomial `csq c M t k h` vanishes and the value polynomial `valPoly c M t k h`
evaluates to the value `t.realize (Sum.elim c u)` of the term.

The proof is a structural induction on `t`.  The only technical obstacle is that `Lexp` is
`Language.ring.sum Language.exp` and `Language.ring`, `Language.exp` are semireducible
definitions; as a consequence `rw`/`simp` (which re-check the goal at `.implicit` transparency)
refuse to see applications of `Sum.inl`/`Sum.inr` symbols.  We disable that transparency bump
with `backward.isDefEq.respectTransparency false`, and we evaluate `Structure.funMap` through a
helper `funMapL` whose language argument is pinned by the *type* of the function symbol.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

noncomputable section

open FirstOrder FirstOrder.Language
open MvPolynomial

namespace Work.WilkiesB

/-! ## `Structure.funMap` of the language `Lexp` -/

/-- `Structure.funMap` for the language `Lexp = Language.ring.sum Language.exp` on `ℝ`, with the
language argument pinned by the *type* of the function symbol.  This wrapper is what allows
`rw`/`simp` to manipulate `funMap` of `Sum.inl`/`Sum.inr` symbols. -/
def funMapL {n : ℕ} (f : Lexp.Functions n) (x : Fin n → ℝ) : ℝ := Structure.funMap f x

theorem funMapL_eq {n : ℕ} (f : Lexp.Functions n) (x : Fin n → ℝ) :
    funMapL f x = Structure.funMap f x := rfl

theorem funMapL_add (x : Fin 2 → ℝ) :
    funMapL (Sum.inl ringFunc.add) x = x 0 + x 1 := by
  rw [funMapL_eq,
    funMap_sumInl (L₁ := Language.ring) (L₂ := WilkiesConjecture.Language.exp)
      (S := ℝ) (n := 2) (f := ringFunc.add)]
  exact Ring.CompatibleRing.funMap_add x

theorem funMapL_mul (x : Fin 2 → ℝ) :
    funMapL (Sum.inl ringFunc.mul) x = x 0 * x 1 := by
  rw [funMapL_eq,
    funMap_sumInl (L₁ := Language.ring) (L₂ := WilkiesConjecture.Language.exp)
      (S := ℝ) (n := 2) (f := ringFunc.mul)]
  exact Ring.CompatibleRing.funMap_mul x

theorem funMapL_neg (x : Fin 1 → ℝ) :
    funMapL (Sum.inl ringFunc.neg) x = -x 0 := by
  rw [funMapL_eq,
    funMap_sumInl (L₁ := Language.ring) (L₂ := WilkiesConjecture.Language.exp)
      (S := ℝ) (n := 1) (f := ringFunc.neg)]
  exact Ring.CompatibleRing.funMap_neg x

theorem funMapL_zero (x : Fin 0 → ℝ) :
    funMapL (Sum.inl ringFunc.zero) x = 0 := by
  rw [funMapL_eq,
    funMap_sumInl (L₁ := Language.ring) (L₂ := WilkiesConjecture.Language.exp)
      (S := ℝ) (n := 0) (f := ringFunc.zero)]
  exact Ring.CompatibleRing.funMap_zero x

theorem funMapL_one (x : Fin 0 → ℝ) :
    funMapL (Sum.inl ringFunc.one) x = 1 := by
  rw [funMapL_eq,
    funMap_sumInl (L₁ := Language.ring) (L₂ := WilkiesConjecture.Language.exp)
      (S := ℝ) (n := 0) (f := ringFunc.one)]
  exact Ring.CompatibleRing.funMap_one x

theorem funMapL_exp (x : Fin 1 → ℝ) :
    funMapL (Sum.inr WilkiesConjecture.expFunc.exp) x = Real.exp (x 0) := by
  rw [funMapL_eq,
    funMap_sumInr (L₁ := Language.ring) (L₂ := WilkiesConjecture.Language.exp)
      (S := ℝ) (n := 1) (f := WilkiesConjecture.expFunc.exp)]
  rfl

/-! ## Realization of the function symbols -/

theorem realize_funcL {A ι : Type*} {n : ℕ} (f : Lexp.Functions n) (v : A ⊕ ι → ℝ)
    (ts : Fin n → Lexp.Term (A ⊕ ι)) :
    (Term.func f ts).realize v = funMapL f (fun i => (ts i).realize v) := rfl

theorem realize_add {A ι : Type*} (v : A ⊕ ι → ℝ) (ts : Fin 2 → Lexp.Term (A ⊕ ι)) :
    (Term.func (Sum.inl ringFunc.add) ts).realize v
      = (ts 0).realize v + (ts 1).realize v := by
  rw [realize_funcL, funMapL_add]

theorem realize_mul {A ι : Type*} (v : A ⊕ ι → ℝ) (ts : Fin 2 → Lexp.Term (A ⊕ ι)) :
    (Term.func (Sum.inl ringFunc.mul) ts).realize v
      = (ts 0).realize v * (ts 1).realize v := by
  rw [realize_funcL, funMapL_mul]

theorem realize_neg {A ι : Type*} (v : A ⊕ ι → ℝ) (ts : Fin 1 → Lexp.Term (A ⊕ ι)) :
    (Term.func (Sum.inl ringFunc.neg) ts).realize v = -(ts 0).realize v := by
  rw [realize_funcL, funMapL_neg]

theorem realize_zero {A ι : Type*} (v : A ⊕ ι → ℝ) (ts : Fin 0 → Lexp.Term (A ⊕ ι)) :
    (Term.func (Sum.inl ringFunc.zero) ts).realize v = 0 := by
  rw [realize_funcL, funMapL_zero]

theorem realize_one {A ι : Type*} (v : A ⊕ ι → ℝ) (ts : Fin 0 → Lexp.Term (A ⊕ ι)) :
    (Term.func (Sum.inl ringFunc.one) ts).realize v = 1 := by
  rw [realize_funcL, funMapL_one]

theorem realize_exp {A ι : Type*} (v : A ⊕ ι → ℝ) (ts : Fin 1 → Lexp.Term (A ⊕ ι)) :
    (Term.func (Sum.inr WilkiesConjecture.expFunc.exp) ts).realize v
      = Real.exp ((ts 0).realize v) := by
  rw [realize_funcL, funMapL_exp]

/-! ## Unfolding lemmas for `nodeVals`, `csq` and `valPoly` -/

theorem nodeVals_add {A ι : Type*} (c : A → ℝ) (u : ι → ℝ) (ts : Fin 2 → Lexp.Term (A ⊕ ι)) :
    nodeVals c u (Term.func (Sum.inl ringFunc.add) ts)
      = Fin.append (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) := by
  funext j
  conv_lhs => rw [nodeVals.eq_def]

theorem nodeVals_mul {A ι : Type*} (c : A → ℝ) (u : ι → ℝ) (ts : Fin 2 → Lexp.Term (A ⊕ ι)) :
    nodeVals c u (Term.func (Sum.inl ringFunc.mul) ts)
      = Fin.append (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) := by
  funext j
  conv_lhs => rw [nodeVals.eq_def]

theorem nodeVals_neg {A ι : Type*} (c : A → ℝ) (u : ι → ℝ) (ts : Fin 1 → Lexp.Term (A ⊕ ι)) :
    nodeVals c u (Term.func (Sum.inl ringFunc.neg) ts) = nodeVals c u (ts 0) := by
  funext j
  conv_lhs => rw [nodeVals.eq_def]

theorem nodeVals_exp {A ι : Type*} (c : A → ℝ) (u : ι → ℝ) (ts : Fin 1 → Lexp.Term (A ⊕ ι)) :
    nodeVals c u (Term.func (Sum.inr WilkiesConjecture.expFunc.exp) ts)
      = snocReal (nodeVals c u (ts 0)) ((ts 0).realize (Sum.elim c u)) := by
  funext j
  conv_lhs => rw [nodeVals.eq_def]

theorem csq_add {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 2 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + (numExp (ts 0) + numExp (ts 1)) ≤ M) :
    csq c M (Term.func (Sum.inl ringFunc.add) ts) k h
      = csq c M (ts 0) k (by omega)
        + csq c M (ts 1) (k + numExp (ts 0)) (by omega) := by
  conv_lhs => rw [csq.eq_def]

theorem csq_mul {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 2 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + (numExp (ts 0) + numExp (ts 1)) ≤ M) :
    csq c M (Term.func (Sum.inl ringFunc.mul) ts) k h
      = csq c M (ts 0) k (by omega)
        + csq c M (ts 1) (k + numExp (ts 0)) (by omega) := by
  conv_lhs => rw [csq.eq_def]

theorem csq_neg {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 1 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + numExp (ts 0) ≤ M) :
    csq c M (Term.func (Sum.inl ringFunc.neg) ts) k h = csq c M (ts 0) k h := by
  conv_lhs => rw [csq.eq_def]

theorem csq_zero {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 0 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + 0 ≤ M) :
    csq c M (Term.func (Sum.inl ringFunc.zero) ts) k h = 0 := by
  conv_lhs => rw [csq.eq_def]

theorem csq_one {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 0 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + 0 ≤ M) :
    csq c M (Term.func (Sum.inl ringFunc.one) ts) k h = 0 := by
  conv_lhs => rw [csq.eq_def]

theorem valPoly_zero {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 0 → Lexp.Term (A ⊕ ι))
    (k : ℕ) (h : k + 0 ≤ M) :
    valPoly c M (Term.func (Sum.inl ringFunc.zero) ts) k h = 0 := by
  conv_lhs => rw [valPoly.eq_def]

theorem valPoly_one {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 0 → Lexp.Term (A ⊕ ι))
    (k : ℕ) (h : k + 0 ≤ M) :
    valPoly c M (Term.func (Sum.inl ringFunc.one) ts) k h = 1 := by
  conv_lhs => rw [valPoly.eq_def]

theorem valPoly_add {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 2 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + (numExp (ts 0) + numExp (ts 1)) ≤ M) :
    valPoly c M (Term.func (Sum.inl ringFunc.add) ts) k h
      = valPoly c M (ts 0) k (by omega)
        + valPoly c M (ts 1) (k + numExp (ts 0)) (by omega) := by
  conv_lhs => rw [valPoly.eq_def]

theorem valPoly_mul {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 2 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + (numExp (ts 0) + numExp (ts 1)) ≤ M) :
    valPoly c M (Term.func (Sum.inl ringFunc.mul) ts) k h
      = valPoly c M (ts 0) k (by omega)
        * valPoly c M (ts 1) (k + numExp (ts 0)) (by omega) := by
  conv_lhs => rw [valPoly.eq_def]

theorem valPoly_neg {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 1 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + numExp (ts 0) ≤ M) :
    valPoly c M (Term.func (Sum.inl ringFunc.neg) ts) k h
      = -valPoly c M (ts 0) k h := by
  conv_lhs => rw [valPoly.eq_def]

theorem valPoly_exp {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 1 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + (numExp (ts 0) + 1) ≤ M) :
    valPoly c M (Term.func (Sum.inr WilkiesConjecture.expFunc.exp) ts) k h
      = X (Sum.inr (Sum.inr (⟨k + numExp (ts 0), by omega⟩ : Fin M))) := by
  conv_lhs => rw [valPoly.eq_def]

theorem csq_exp {A ι : Type*} (c : A → ℝ) (M : ℕ) (ts : Fin 1 → Lexp.Term (A ⊕ ι)) (k : ℕ)
    (h : k + (numExp (ts 0) + 1) ≤ M) :
    csq c M (Term.func (Sum.inr WilkiesConjecture.expFunc.exp) ts) k h
      = csq c M (ts 0) k (by omega)
        + (X (Sum.inl (Sum.inr (⟨k + numExp (ts 0), by omega⟩ : Fin M)))
            - valPoly c M (ts 0) k (by omega)) ^ 2 := by
  conv_lhs => rw [csq.eq_def]

/-! ## The canonical witness -/

theorem eval_canonical {A ι : Type*} (c : A → ℝ) (u : ι → ℝ) (M : ℕ)
    (t : Lexp.Term (A ⊕ ι)) (k : ℕ) (h : k + numExp t ≤ M) (y : Fin M → ℝ)
    (hy : ∀ j : Fin (numExp t), y (shiftFin h j) = nodeVals c u t j) :
    expEval (Sum.elim u y) (csq c M t k h) = 0 ∧
    expEval (Sum.elim u y) (valPoly c M t k h) = t.realize (Sum.elim c u) := by
  have key : ∀ (t : Lexp.Term (A ⊕ ι)) (k : ℕ) (h : k + numExp t ≤ M) (y : Fin M → ℝ),
      (∀ j : Fin (numExp t), y (shiftFin h j) = nodeVals c u t j) →
      expEval (Sum.elim u y) (csq c M t k h) = 0 ∧
      expEval (Sum.elim u y) (valPoly c M t k h) = t.realize (Sum.elim c u) := by
    intro t
    induction t with
    | var v =>
      intro k h y hy
      rcases v with a | i
      · constructor
        · simp only [csq.eq_def, expEval_zero]
        · simp only [valPoly.eq_def, expEval_C, Term.realize_var, Sum.elim_inl]
      · constructor
        · simp only [csq.eq_def, expEval_zero]
        · simp only [valPoly.eq_def, expEval_X_inl, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    | func f ts ih =>
      intro k h y hy
      rcases f with g | e
      · rcases g with _ | _ | _ | _ | _
        · -- addition
          have h0 : k + numExp (ts 0) ≤ M := by
            simp only [numExp_func_add] at h; omega
          have h1 : (k + numExp (ts 0)) + numExp (ts 1) ≤ M := by
            simp only [numExp_func_add] at h; omega
          have hyA : ∀ j : Fin (numExp (ts 0) + numExp (ts 1)),
              y (shiftFin h j)
                = Fin.append (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) j := by
            intro j
            simpa only [numExp_func_add, nodeVals_add] using hy j
          have hy0 : ∀ j : Fin (numExp (ts 0)), y (shiftFin h0 j) = nodeVals c u (ts 0) j := by
            intro j
            have hh : shiftFin h0 j = shiftFin h (Fin.castAdd (numExp (ts 1)) j) := by
              ext; simp [shiftFin]
            rw [hh, hyA (Fin.castAdd (numExp (ts 1)) j)]
            exact Fin.append_left (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) j
          have hy1 : ∀ j : Fin (numExp (ts 1)), y (shiftFin h1 j) = nodeVals c u (ts 1) j := by
            intro j
            have hh : shiftFin h1 j = shiftFin h (Fin.natAdd (numExp (ts 0)) j) := by
              ext; simp [shiftFin, Fin.natAdd]; omega
            rw [hh, hyA (Fin.natAdd (numExp (ts 0)) j)]
            exact Fin.append_right (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) j
          obtain ⟨hc0, hv0⟩ := ih 0 k h0 y hy0
          obtain ⟨hc1, hv1⟩ := ih 1 (k + numExp (ts 0)) h1 y hy1
          constructor
          · rw [csq_add]
            simp only [expEval_add, hc0, hc1, add_zero]
          · rw [valPoly_add]
            simp only [expEval_add, hv0, hv1, ← realize_add]
        · -- multiplication
          have h0 : k + numExp (ts 0) ≤ M := by
            simp only [numExp_func_mul] at h; omega
          have h1 : (k + numExp (ts 0)) + numExp (ts 1) ≤ M := by
            simp only [numExp_func_mul] at h; omega
          have hyA : ∀ j : Fin (numExp (ts 0) + numExp (ts 1)),
              y (shiftFin h j)
                = Fin.append (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) j := by
            intro j
            simpa only [numExp_func_mul, nodeVals_mul] using hy j
          have hy0 : ∀ j : Fin (numExp (ts 0)), y (shiftFin h0 j) = nodeVals c u (ts 0) j := by
            intro j
            have hh : shiftFin h0 j = shiftFin h (Fin.castAdd (numExp (ts 1)) j) := by
              ext; simp [shiftFin]
            rw [hh, hyA (Fin.castAdd (numExp (ts 1)) j)]
            exact Fin.append_left (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) j
          have hy1 : ∀ j : Fin (numExp (ts 1)), y (shiftFin h1 j) = nodeVals c u (ts 1) j := by
            intro j
            have hh : shiftFin h1 j = shiftFin h (Fin.natAdd (numExp (ts 0)) j) := by
              ext; simp [shiftFin, Fin.natAdd]; omega
            rw [hh, hyA (Fin.natAdd (numExp (ts 0)) j)]
            exact Fin.append_right (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) j
          obtain ⟨hc0, hv0⟩ := ih 0 k h0 y hy0
          obtain ⟨hc1, hv1⟩ := ih 1 (k + numExp (ts 0)) h1 y hy1
          constructor
          · rw [csq_mul]
            simp only [expEval_add, hc0, hc1, add_zero]
          · rw [valPoly_mul]
            simp only [expEval_mul, hv0, hv1, ← realize_mul]
        · -- negation
          have hy0 : ∀ j : Fin (numExp (ts 0)), y (shiftFin h j) = nodeVals c u (ts 0) j := by
            intro j
            simpa only [numExp_func_neg, nodeVals_neg] using hy j
          obtain ⟨hc0, hv0⟩ := ih 0 k h y hy0
          constructor
          · rw [csq_neg]
            exact hc0
          · rw [valPoly_neg]
            simp only [expEval_neg, hv0, ← realize_neg]
        · -- zero
          constructor
          · simp only [csq_zero, expEval_zero]
          · simp only [valPoly_zero, expEval_zero]
            exact (realize_zero (Sum.elim c u) ts).symm
        · -- one
          constructor
          · simp only [csq_one, expEval_zero]
          · simp only [valPoly_one, expEval_one]
            exact (realize_one (Sum.elim c u) ts).symm
      · -- exponential
        cases e
        have h0 : k + numExp (ts 0) ≤ M := by
          simp only [numExp_func_exp] at h; omega
        have hs : k + numExp (ts 0) < M := by
          simp only [numExp_func_exp] at h; omega
        have hyA : ∀ j : Fin (numExp (ts 0) + 1),
            y (shiftFin h j)
              = snocReal (nodeVals c u (ts 0)) ((ts 0).realize (Sum.elim c u)) j := by
          intro j
          simpa only [numExp_func_exp, nodeVals_exp] using hy j
        have hy0 : ∀ j : Fin (numExp (ts 0)), y (shiftFin h0 j) = nodeVals c u (ts 0) j := by
          intro j
          have hh : shiftFin h0 j = shiftFin h (Fin.castSucc j) := by ext; simp [shiftFin]
          rw [hh, hyA (Fin.castSucc j), snocReal_castSucc]
        have hfin : (⟨k + numExp (ts 0), hs⟩ : Fin M)
            = shiftFin h (Fin.last (numExp (ts 0))) := by ext; simp [shiftFin]
        have hlast : y (⟨k + numExp (ts 0), hs⟩ : Fin M) = (ts 0).realize (Sum.elim c u) := by
          rw [hfin, hyA (Fin.last (numExp (ts 0))), snocReal_last]
        obtain ⟨hc0, hv0⟩ := ih 0 k h0 y hy0
        constructor
        · rw [csq_exp]
          simp only [expEval_add, expEval_pow, expEval_sub, expEval_X_inl, Sum.elim_inr,
            hc0, hv0, hlast]
          ring
        · rw [valPoly_exp]
          simp only [expEval_X_inr, Sum.elim_inr, hlast, ← realize_exp]
  exact key t k h y hy

end Work.WilkiesB
