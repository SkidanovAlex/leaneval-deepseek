import Mathlib
import Submission.Work.WilkiesB.Term
import Submission.Work.WilkiesB.Defs

/-!
# `expEval_csq_any`

The polynomial `csq c M t k h` is a sum of squares of the "defining equations" of the exponential
nodes of `t` (see `Submission/Work/WilkiesB/Term.lean`).  Consequently its evaluation is always
nonnegative, and whenever it vanishes the `k, …, k + numExp t - 1` slots of the witness vector
satisfy those equations, so that `valPoly c M t k h` evaluates to the value of `t`.

The main work is the auxiliary induction `csq_any_aux`, which proves the conjunction of the two
statements for all subterms simultaneously (the second statement for an `exp`-node needs the
first statement for its argument).
-/

set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language MvPolynomial

namespace Work.WilkiesB

/-- Joint induction underlying `expEval_csq_any`: `expEval` of `csq` is nonnegative, and if it
vanishes then `valPoly` evaluates to the value of the term. -/
theorem csq_any_aux {A ι : Type*} (c : A → ℝ) (u : ι → ℝ) (M : ℕ) (y : Fin M → ℝ) :
    ∀ (t : Lexp.Term (A ⊕ ι)) (k : ℕ) (h : k + numExp t ≤ M),
      (0 ≤ expEval (Sum.elim u y) (csq c M t k h)) ∧
      (expEval (Sum.elim u y) (csq c M t k h) = 0 →
        expEval (Sum.elim u y) (valPoly c M t k h) = t.realize (Sum.elim c u)) := by
  intro t
  induction t using Term.rec with
  | var a =>
    intro k h
    constructor
    · have hcsq : csq c M (Term.var a) k h = 0 := by rw [csq.eq_def]
      rw [hcsq]
      simp
    · intro _
      rcases a with a | i
      · have hvp : valPoly c M (Term.var (Sum.inl a)) k h = MvPolynomial.C (c a) := by
          rw [valPoly.eq_def]
        rw [hvp]
        simp [Term.realize_var]
      · have hvp : valPoly c M (Term.var (Sum.inr i)) k h = MvPolynomial.X (Sum.inl (Sum.inl i)) := by
          rw [valPoly.eq_def]
        rw [hvp]
        simp [Term.realize_var]
  | func f ts ih =>
    intro k h
    cases f with
    | inl g =>
      cases g with
      | add =>
        have h0 : k + numExp (ts 0) ≤ M := by simp only [numExp_func_add] at h; omega
        have h1 : k + numExp (ts 0) + numExp (ts 1) ≤ M := by
          simp only [numExp_func_add] at h; omega
        have hcsq : csq c M (Term.func (Sum.inl ringFunc.add) ts) k h =
            csq c M (ts 0) k h0 + csq c M (ts 1) (k + numExp (ts 0)) h1 := by rw [csq.eq_def]
        have hvp : valPoly c M (Term.func (Sum.inl ringFunc.add) ts) k h =
            valPoly c M (ts 0) k h0 + valPoly c M (ts 1) (k + numExp (ts 0)) h1 := by
          rw [valPoly.eq_def]
        have I0 := ih 0 k h0
        have I1 := ih 1 (k + numExp (ts 0)) h1
        constructor
        · rw [hcsq, expEval_add]
          exact add_nonneg I0.1 I1.1
        · intro hz
          rw [hcsq, expEval_add] at hz
          have e0 : expEval (Sum.elim u y) (csq c M (ts 0) k h0) = 0 := by linarith [I0.1]
          have e1 : expEval (Sum.elim u y) (csq c M (ts 1) (k + numExp (ts 0)) h1) = 0 := by
            linarith [I1.1]
          rw [hvp, expEval_add, I0.2 e0, I1.2 e1]
          erw [Term.realize_func, funMap_sumInl, Ring.CompatibleRing.funMap_add]
      | mul =>
        have h0 : k + numExp (ts 0) ≤ M := by simp only [numExp_func_mul] at h; omega
        have h1 : k + numExp (ts 0) + numExp (ts 1) ≤ M := by
          simp only [numExp_func_mul] at h; omega
        have hcsq : csq c M (Term.func (Sum.inl ringFunc.mul) ts) k h =
            csq c M (ts 0) k h0 + csq c M (ts 1) (k + numExp (ts 0)) h1 := by rw [csq.eq_def]
        have hvp : valPoly c M (Term.func (Sum.inl ringFunc.mul) ts) k h =
            valPoly c M (ts 0) k h0 * valPoly c M (ts 1) (k + numExp (ts 0)) h1 := by
          rw [valPoly.eq_def]
        have I0 := ih 0 k h0
        have I1 := ih 1 (k + numExp (ts 0)) h1
        constructor
        · rw [hcsq, expEval_add]
          exact add_nonneg I0.1 I1.1
        · intro hz
          rw [hcsq, expEval_add] at hz
          have e0 : expEval (Sum.elim u y) (csq c M (ts 0) k h0) = 0 := by linarith [I0.1]
          have e1 : expEval (Sum.elim u y) (csq c M (ts 1) (k + numExp (ts 0)) h1) = 0 := by
            linarith [I1.1]
          rw [hvp, expEval_mul, I0.2 e0, I1.2 e1]
          erw [Term.realize_func, funMap_sumInl, Ring.CompatibleRing.funMap_mul]
      | neg =>
        have h0 : k + numExp (ts 0) ≤ M := by simp only [numExp_func_neg] at h; omega
        have hcsq : csq c M (Term.func (Sum.inl ringFunc.neg) ts) k h = csq c M (ts 0) k h0 := by
          rw [csq.eq_def]
        have hvp : valPoly c M (Term.func (Sum.inl ringFunc.neg) ts) k h =
            -valPoly c M (ts 0) k h0 := by rw [valPoly.eq_def]
        have I0 := ih 0 k h0
        constructor
        · rw [hcsq]; exact I0.1
        · intro hz
          rw [hcsq] at hz
          rw [hvp, expEval_neg, I0.2 hz]
          erw [Term.realize_func, funMap_sumInl, Ring.CompatibleRing.funMap_neg]
      | zero =>
        have hcsq : csq c M (Term.func (Sum.inl ringFunc.zero) ts) k h = 0 := by rw [csq.eq_def]
        have hvp : valPoly c M (Term.func (Sum.inl ringFunc.zero) ts) k h = 0 := by
          rw [valPoly.eq_def]
        constructor
        · rw [hcsq]; simp
        · intro _
          rw [hvp]
          simp only [expEval_zero]
          erw [Term.realize_func, funMap_sumInl, Ring.CompatibleRing.funMap_zero]
      | one =>
        have hcsq : csq c M (Term.func (Sum.inl ringFunc.one) ts) k h = 0 := by rw [csq.eq_def]
        have hvp : valPoly c M (Term.func (Sum.inl ringFunc.one) ts) k h = 1 := by
          rw [valPoly.eq_def]
        constructor
        · rw [hcsq]; simp
        · intro _
          rw [hvp]
          simp only [expEval_one]
          erw [Term.realize_func, funMap_sumInl, Ring.CompatibleRing.funMap_one]
    | inr e =>
      cases e with
      | exp =>
        have h0 : k + numExp (ts 0) ≤ M := by simp only [numExp_func_exp] at h; omega
        have hfin : k + numExp (ts 0) < M := by simp only [numExp_func_exp] at h; omega
        have hcsq : csq c M (Term.func (Sum.inr WilkiesConjecture.expFunc.exp) ts) k h =
            csq c M (ts 0) k h0 +
              (MvPolynomial.X (Sum.inl (Sum.inr (⟨k + numExp (ts 0), hfin⟩ : Fin M))) -
                valPoly c M (ts 0) k h0) ^ 2 := by rw [csq.eq_def]
        have hvp : valPoly c M (Term.func (Sum.inr WilkiesConjecture.expFunc.exp) ts) k h =
            MvPolynomial.X (Sum.inr (Sum.inr (⟨k + numExp (ts 0), hfin⟩ : Fin M))) := by
          rw [valPoly.eq_def]
        have I0 := ih 0 k h0
        constructor
        · rw [hcsq, expEval_add, expEval_pow, expEval_sub, expEval_X_inl]
          exact add_nonneg I0.1 (sq_nonneg _)
        · intro hz
          rw [hcsq, expEval_add, expEval_pow, expEval_sub, expEval_X_inl] at hz
          have hsq : (Sum.elim u y (Sum.inr (⟨k + numExp (ts 0), hfin⟩ : Fin M)) -
              expEval (Sum.elim u y) (valPoly c M (ts 0) k h0)) ^ 2 = 0 := by
            linarith [I0.1, sq_nonneg (Sum.elim u y (Sum.inr (⟨k + numExp (ts 0), hfin⟩ : Fin M)) -
              expEval (Sum.elim u y) (valPoly c M (ts 0) k h0))]
          have e0 : expEval (Sum.elim u y) (csq c M (ts 0) k h0) = 0 := by
            linarith [I0.1, sq_nonneg (Sum.elim u y (Sum.inr (⟨k + numExp (ts 0), hfin⟩ : Fin M)) -
              expEval (Sum.elim u y) (valPoly c M (ts 0) k h0))]
          have hslot : Sum.elim u y (Sum.inr (⟨k + numExp (ts 0), hfin⟩ : Fin M)) =
              (ts 0).realize (Sum.elim c u) := by
            have h2 := sq_eq_zero_iff.mp hsq
            have h3 := I0.2 e0
            linarith
          rw [hvp, expEval_X_inr, hslot]
          erw [Term.realize_func, funMap_sumInr]
          rfl

/-- `expEval` of `csq` is nonnegative, and if it vanishes then `valPoly` evaluates to the value
of the term. -/
theorem expEval_csq_any {A ι : Type*} (c : A → ℝ) (u : ι → ℝ) (M : ℕ)
    (t : Lexp.Term (A ⊕ ι)) (k : ℕ) (h : k + numExp t ≤ M) (y : Fin M → ℝ) :
    0 ≤ expEval (Sum.elim u y) (csq c M t k h) ∧
    (expEval (Sum.elim u y) (csq c M t k h) = 0 →
      expEval (Sum.elim u y) (valPoly c M t k h) = t.realize (Sum.elim c u)) :=
  csq_any_aux c u M y t k h

end Work.WilkiesB
