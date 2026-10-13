/-
  WilC6 — PolyTerm: every exp-polynomial is the evaluation of a term of `LEc`.

  The language `LEc = (ring ⊕ exp)[[ℝ]]` has function symbols for `+`, `*`, `-`, `0`, `1`, the
  exponential and a constant for every real.  For `P : MvPolynomial (Fin (n+m) ⊕ Fin (n+m)) ℝ`
  we build a single `LEc`-term `t` with variables indexed by `Fin n ⊕ Fin m` such that, for all
  `x : Fin n → ℝ`, `y : Fin m → ℝ`,

      `Term.realize (Sum.elim x y) t = expPolyEval P (Fin.append x y)`,

  i.e. the variable `Sum.inl i` of the polynomial is read as `(Fin.append x y) i` and the
  variable `Sum.inr i` as `exp ((Fin.append x y) i)`.

  The construction is in two steps:

  * `exists_term_of_poly`: every polynomial in `σ` variables is the evaluation of a term whose
    free variables are `σ` (induction on the polynomial: constants, `+`, `* X n`);
  * the split form is obtained by `Term.subst` along `substMap`, which sends the variable
    `Sum.inl i` to the variable `idx i` of `Fin n ⊕ Fin m` and the variable `Sum.inr i` to
    `exp (idx i)`, where `idx = Fin.append Sum.inl Sum.inr` reindexes `Fin (n+m)`.

  The only semantic input is that the `LEc`-structure on `ℝ` interprets the ring symbols by the
  field operations, `exp` by `Real.exp` and the constants by themselves.
-/
import Mathlib
import Submission.Work.WilC6.Base

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6.PolyTerm

/-! ## 1. `LEc`-symbols and term constructors -/

/-- The symbol of `LEc` corresponding to a ring symbol.  `LEc = (ring ⊕ exp)[[ℝ]]`, so a ring
symbol sits at `Sum.inl (Sum.inl ·)`. -/
def ringSym {n : ℕ} (f : Language.ring.Functions n) : LEc.Functions n := Sum.inl (Sum.inl f)

/-- The symbol of `LEc` corresponding to the exponential. -/
def expSym {n : ℕ} (f : WilkiesConjecture.Language.exp.Functions n) : LEc.Functions n :=
  Sum.inl (Sum.inr f)

/-- Addition, as an `LEc`-term. -/
def eAdd {α : Type*} (t₁ t₂ : LEc.Term α) : LEc.Term α :=
  Term.func (ringSym Ring.addFunc) ![t₁, t₂]

/-- Multiplication, as an `LEc`-term. -/
def eMul {α : Type*} (t₁ t₂ : LEc.Term α) : LEc.Term α :=
  Term.func (ringSym Ring.mulFunc) ![t₁, t₂]

/-- The exponential, as an `LEc`-term. -/
def eExp {α : Type*} (t : LEc.Term α) : LEc.Term α :=
  Term.func (expSym WilkiesConjecture.expFunc.exp) ![t]

/-- The constant `r : ℝ`, as an `LEc`-term (with arbitrary variable type). -/
def eConst {α : Type*} (r : ℝ) : LEc.Term α :=
  Term.func (Sum.inr r : LEc.Functions 0) default

/-! ## 2. Realization of the constructors in the standard structure on `ℝ` -/

theorem addSym_real (x y : ℝ) :
    Structure.funMap (ringSym Ring.addFunc) ![x, y] = x + y := by
  show @Structure.funMap Language.ring ℝ _ 2 Ring.addFunc ![x, y] = x + y
  simp [Ring.CompatibleRing.funMap_add]

theorem mulSym_real (x y : ℝ) :
    Structure.funMap (ringSym Ring.mulFunc) ![x, y] = x * y := by
  show @Structure.funMap Language.ring ℝ _ 2 Ring.mulFunc ![x, y] = x * y
  simp [Ring.CompatibleRing.funMap_mul]

theorem expSym_real (x : ℝ) :
    Structure.funMap (expSym WilkiesConjecture.expFunc.exp) ![x] = Real.exp x := by
  show Real.exp (![x] (0 : Fin 1)) = Real.exp x
  simp

theorem constSym_real (r : ℝ) (x : Fin 0 → ℝ) :
    @Structure.funMap LEc ℝ _ 0 (Sum.inr r : LEc.Functions 0) x = r := by
  show @Structure.funMap (constantsOn ℝ) ℝ _ 0 r x = r
  rfl

theorem realize_eAdd {α : Type*} (v : α → ℝ) (t₁ t₂ : LEc.Term α) :
    Term.realize v (eAdd t₁ t₂) = Term.realize v t₁ + Term.realize v t₂ := by
  rw [eAdd, Term.realize_func]
  have h : (fun i => Term.realize v (![t₁, t₂] i)) =
      ![Term.realize v t₁, Term.realize v t₂] := by
    ext i
    fin_cases i <;> rfl
  rw [h, addSym_real]

theorem realize_eMul {α : Type*} (v : α → ℝ) (t₁ t₂ : LEc.Term α) :
    Term.realize v (eMul t₁ t₂) = Term.realize v t₁ * Term.realize v t₂ := by
  rw [eMul, Term.realize_func]
  have h : (fun i => Term.realize v (![t₁, t₂] i)) =
      ![Term.realize v t₁, Term.realize v t₂] := by
    ext i
    fin_cases i <;> rfl
  rw [h, mulSym_real]

theorem realize_eExp {α : Type*} (v : α → ℝ) (t : LEc.Term α) :
    Term.realize v (eExp t) = Real.exp (Term.realize v t) := by
  rw [eExp, Term.realize_func]
  have h : (fun i => Term.realize v (![t] i)) = ![Term.realize v t] := by
    ext i
    fin_cases i; rfl
  rw [h, expSym_real]

theorem realize_eConst {α : Type*} (v : α → ℝ) (r : ℝ) :
    Term.realize v (eConst (α := α) r) = r := by
  show @Structure.funMap LEc ℝ _ 0 (Sum.inr r : LEc.Functions 0)
      (fun i : Fin 0 => Term.realize v ((default : Fin 0 → LEc.Term α) i)) = r
  exact constSym_real r _

/-! ## 3. Every polynomial is the evaluation of a term -/

/-- **Polynomials are terms.**  For every polynomial `P` in the variables `σ` there is an
`LEc`-term `t` with the same free variables such that `Term.realize v t = eval v P` for every
assignment `v`. -/
lemma exists_term_of_poly {σ : Type*} (P : MvPolynomial σ ℝ) :
    ∃ t : LEc.Term σ, ∀ v : σ → ℝ, Term.realize v t = MvPolynomial.eval v P :=
  MvPolynomial.induction_on (motive := fun P => ∃ t : LEc.Term σ, ∀ v : σ → ℝ,
      Term.realize v t = MvPolynomial.eval v P) P
    (fun a => ⟨eConst (α := σ) a, fun v => by rw [realize_eConst, MvPolynomial.eval_C]⟩)
    (fun p q hp hq => by
      obtain ⟨tp, htp⟩ := hp
      obtain ⟨tq, htq⟩ := hq
      exact ⟨eAdd (α := σ) tp tq, fun v => by
        rw [realize_eAdd, htp v, htq v, map_add]⟩)
    (fun p s hp => by
      obtain ⟨tp, htp⟩ := hp
      exact ⟨eMul (α := σ) tp (Term.var s), fun v => by
        rw [realize_eMul, htp v, Term.realize_var, map_mul, MvPolynomial.eval_X]⟩)

/-! ## 4. Splitting the variables -/

/-- The reindexing `Fin (n+m) → Fin n ⊕ Fin m` sending the first block to `Sum.inl` and the
second to `Sum.inr`. -/
def idx {n m : ℕ} : Fin (n + m) → Fin n ⊕ Fin m :=
  Fin.append (fun a => Sum.inl a) (fun b => Sum.inr b)

@[simp] lemma idx_castAdd {n m : ℕ} (a : Fin n) : idx (Fin.castAdd m a) = Sum.inl a :=
  Fin.append_left (fun a : Fin n => Sum.inl a) (fun b : Fin m => Sum.inr b) a

@[simp] lemma idx_natAdd {n m : ℕ} (b : Fin m) : idx (Fin.natAdd n b) = Sum.inr b :=
  Fin.append_right (fun a : Fin n => Sum.inl a) (fun b : Fin m => Sum.inr b) b

/-- The two implementations of `Fin (n+m) → ℝ`, as `Sum.elim` along `idx`. -/
lemma append_eq_elim_idx {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    Fin.append x y = Sum.elim x y ∘ idx := by
  funext i
  refine Fin.addCases (motive := fun i => Fin.append x y i = (Sum.elim x y ∘ idx) i) ?_ ?_ i
  · intro a
    rw [Fin.append_left, Function.comp_apply, idx_castAdd, Sum.elim_inl]
  · intro b
    rw [Fin.append_right, Function.comp_apply, idx_natAdd, Sum.elim_inr]

/-- The variable substitution realizing the split form: the `inl` variable `i : Fin (n+m)` is
the value variable `idx i`, the `inr` variable is its exponential. -/
def substMap {n m : ℕ} : Fin (n + m) ⊕ Fin (n + m) → LEc.Term (Fin n ⊕ Fin m)
  | Sum.inl i => Term.var (idx i)
  | Sum.inr i => eExp (Term.var (idx i))

/-! ## 5. The split form of a polynomial -/

theorem exists_polyTerm {n m : ℕ} (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ) :
    ∃ t : WilkiesDesign.CG.LEc.Term (Fin n ⊕ Fin m), ∀ (x : Fin n → ℝ) (y : Fin m → ℝ),
      FirstOrder.Language.Term.realize (Sum.elim x y) t = WilkiesDesign.expPolyEval P (Fin.append x y) :=
  by
  obtain ⟨t₀, ht₀⟩ := exists_term_of_poly (σ := Fin (n + m) ⊕ Fin (n + m)) P
  refine ⟨t₀.subst (substMap (n := n) (m := m)), ?_⟩
  intro x y
  rw [Term.realize_subst]
  have hfun : (fun s => Term.realize (Sum.elim x y) (substMap (n := n) (m := m) s)) =
      Sum.elim (Fin.append x y) (fun i => Real.exp ((Fin.append x y) i)) := by
    funext s
    rcases s with i | i
    · change Term.realize (Sum.elim x y) (Term.var (idx i)) = (Fin.append x y) i
      rw [Term.realize_var]
      exact (congrFun (append_eq_elim_idx x y) i).symm
    · change Term.realize (Sum.elim x y) (eExp (Term.var (idx i))) =
        Real.exp ((Fin.append x y) i)
      rw [realize_eExp, Term.realize_var, congrFun (append_eq_elim_idx x y) i]
      rfl
  rw [hfun, ht₀]
  rfl

end Work.WilC6.PolyTerm
