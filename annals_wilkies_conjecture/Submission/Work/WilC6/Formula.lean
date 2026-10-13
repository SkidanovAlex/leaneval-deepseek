/-
  WilC6 — the `∀`-formula expressing the complement of an `ExpExist` set.

  Given an exp-polynomial `P` in `n + m` variables, `complFormula P` is the formula of `LEc` with
  free variables `Fin n` asserting `∀ y : Fin m → ℝ, P(x, y, e^{x,y}) ≠ 0`.  Its realization set
  is the complement of the projection of the zero set of `P`, which is exactly the shape in which
  `ExpExist` is stated.
-/
import Submission.Work.WilC6.Base
import Submission.Work.WilC6.PolyTerm.exists_polyTerm

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6

/-- The zero term of `LEc`. -/
def zeroTerm (α : Type*) : LEc.Term α :=
  Term.func (L := LEc) (Sum.inl (Sum.inl ringFunc.zero)) (fun i : Fin 0 => i.elim0)

@[simp] theorem realize_zeroTerm (α : Type*) (v : α → ℝ) :
    Term.realize v (zeroTerm α) = 0 := by
  simp only [zeroTerm, Term.realize, Fin.elim0]
  rfl

/-- The term of `LEc` evaluating the exp-polynomial `P` in the split variables `Fin n ⊕ Fin m`. -/
noncomputable def polyTerm {n m : ℕ} (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ) :
    LEc.Term (Fin n ⊕ Fin m) := Classical.choose (PolyTerm.exists_polyTerm P)

theorem realize_polyTerm {n m : ℕ} (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    Term.realize (Sum.elim x y) (polyTerm P) = expPolyEval P (Fin.append x y) :=
  Classical.choose_spec (PolyTerm.exists_polyTerm P) x y

/-- The formula asserting that the exp-polynomial `P` has no zero in the last `m` variables. -/
noncomputable def complFormula {n m : ℕ} (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ) :
    LEc.Formula (Fin n) :=
  (BoundedFormula.not (Term.bdEqual (polyTerm P) (zeroTerm (Fin n ⊕ Fin m)))).alls

theorem realize_complFormula {n m : ℕ} (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    (x : Fin n → ℝ) :
    (complFormula P).Realize x ↔ ∀ y : Fin m → ℝ, expPolyEval P (Fin.append x y) ≠ 0 := by
  simp only [complFormula, BoundedFormula.realize_alls, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, realize_polyTerm, realize_zeroTerm, ne_eq]

theorem realizeSet_complFormula {n m : ℕ} (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    {X : Set (Fin n → ℝ)}
    (hX : X = {x | ∃ y : Fin m → ℝ, expPolyEval P (Fin.append x y) = 0}) :
    realizeSet (complFormula P) = Xᶜ := by
  ext x
  rw [realizeSet, Set.mem_ofPred_eq, realize_complFormula, Set.mem_compl_iff, hX,
    Set.mem_ofPred_eq]
  simp only [not_exists, ne_eq]

end Work.WilC6
