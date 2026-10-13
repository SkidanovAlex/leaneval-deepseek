/-
  WilC5 — the syntactic translation from `LRc` to `LEc`.

  `LEc` is a *definitional expansion* of `LRc`: the extra symbols of `LEc` are the full
  exponential and it is the `rexp` symbol which is definable.  The translation is built here at
  the level of *terms*: for every `LRc`-term `t` (with free variables `β`) we produce the
  `LEc`-formula `termGraph t`, with one extra free variable `Sum.inr 0 : β ⊕ Fin 1`, whose
  realization says "the value of `t` is the extra variable".  The only non-trivial step is the
  function symbol `rexp`, which is replaced by the graph of the definable function `rexpFromExp`
  (`Bridge.lean`).  Atomic formulas `t₁ = t₂` are translated by conjoining the two graphs and
  existentially quantifying the shared value variable.

  The main result of this module is `formulaTrans_realize`: for every `LRc`-formula `φ`, the
  `LEc`-formula `formulaTrans φ` has exactly the same realizations.
-/
import Submission.Work.WilC5.Bridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

variable {M : Type} [LEc.Structure M]

/-! ## 1. Realization of the `LEc`-term constructors -/

@[simp] theorem realize_eAdd {α : Type} (v : α → M) (t₁ t₂ : LEc.Term α) :
    Term.realize v (eAdd t₁ t₂) = addE (Term.realize v t₁) (Term.realize v t₂) := by
  rw [eAdd, Term.realize_func, addE]
  congr 1
  ext i
  fin_cases i <;> rfl

@[simp] theorem realize_eMul {α : Type} (v : α → M) (t₁ t₂ : LEc.Term α) :
    Term.realize v (eMul t₁ t₂) = mulE (Term.realize v t₁) (Term.realize v t₂) := by
  rw [eMul, Term.realize_func, mulE]
  congr 1
  ext i
  fin_cases i <;> rfl

@[simp] theorem realize_eNeg {α : Type} (v : α → M) (t : LEc.Term α) :
    Term.realize v (eNeg t) = negE (Term.realize v t) := by
  rw [eNeg, Term.realize_func, negE]
  congr 1
  ext i
  fin_cases i
  rfl

@[simp] theorem realize_eZero {α : Type} (v : α → M) :
    Term.realize v (eZero : LEc.Term α) = zeroE := by
  rw [eZero, Term.realize_func, zeroE]
  congr 1
  ext i
  exact Fin.elim0 i

@[simp] theorem realize_eOne {α : Type} (v : α → M) :
    Term.realize v (eOne : LEc.Term α) = oneE := by
  rw [eOne, Term.realize_func, oneE]
  congr 1
  ext i
  exact Fin.elim0 i

@[simp] theorem realize_eSub {α : Type} (v : α → M) (t₁ t₂ : LEc.Term α) :
    Term.realize v (eSub t₁ t₂) = subE (Term.realize v t₁) (Term.realize v t₂) := by
  rw [eSub, subE, realize_eAdd, realize_eNeg]

@[simp] theorem realize_eExp {α : Type} (v : α → M) (t : LEc.Term α) :
    Term.realize v (eExp t) = expE (Term.realize v t) := by
  rw [eExp, Term.realize_func, expE]
  congr 1
  ext i
  fin_cases i
  rfl

/-! ## 2. The formula `|x| ≤ 1` with a quantified witness

`absLeOneForm t` is the ring formula `∃z, z*z = 1 - t ∧ ∃z, z*z = 1 + t`.  The witness `z` is
the *last* bound variable of the formula (so that `ex` removes it); `t` is pushed into the larger
variable type by relabelling the bound variables along `Fin.castSucc`. -/

/-- The witness `z = &0`, as a term in the context with one more bound variable. -/
def witTerm {β : Type} {l : ℕ} : LEc.Term (β ⊕ Fin (l + 1)) := Term.var (Sum.inr (Fin.last l))

@[simp] theorem realize_witTerm {β : Type} {l : ℕ} (w : β → M) (xs : Fin (l + 1) → M) :
    Term.realize (Sum.elim w xs) (witTerm (l := l)) = xs (Fin.last l) := by
  rw [witTerm, Term.realize_var]
  rfl

/-- Push a term into a context with one more bound variable at the end. -/
def pushTerm {β : Type} {l : ℕ} (t : LEc.Term (β ⊕ Fin l)) : LEc.Term (β ⊕ Fin (l + 1)) :=
  t.relabel (Sum.map id Fin.castSucc)

@[simp] theorem realize_pushTerm {β : Type} {l : ℕ} (t : LEc.Term (β ⊕ Fin l))
    (w : β → M) (xs : Fin (l + 1) → M) :
    Term.realize (Sum.elim w xs) (pushTerm t) =
      Term.realize (Sum.elim w (xs ∘ Fin.castSucc)) t := by
  rw [pushTerm, Term.realize_relabel]
  congr 1
  ext i
  rcases i with i | i
  · rfl
  · rfl

@[simp] theorem snoc_comp_castSucc {α : Type} {l : ℕ} (xs : Fin l → α) (a : α) :
    Fin.snoc xs a ∘ Fin.castSucc = xs := by
  funext i
  simp

/-- **The ring formula `∃z, z*z = 1 - t ∧ ∃z, z*z = 1 + t`**, i.e. `|t| ≤ 1`. -/
def absLeOneForm {β : Type} {l : ℕ} (t : LEc.Term (β ⊕ Fin l)) : LEc.BoundedFormula β l :=
  (Term.bdEqual (eMul (witTerm (l := l)) (witTerm (l := l))) (eSub eOne (pushTerm t))).ex ⊓
  (Term.bdEqual (eMul (witTerm (l := l)) (witTerm (l := l))) (eAdd eOne (pushTerm t))).ex

theorem absLeOneForm_realize_sub {β : Type} {l : ℕ} (t : LEc.Term (β ⊕ Fin l))
    (w : β → M) (xs : Fin l → M) :
    ((Term.bdEqual (eMul (witTerm (l := l)) (witTerm (l := l)))
        (eSub eOne (pushTerm t))).ex : LEc.BoundedFormula β l).Realize w xs ↔
      ∃ z : M, mulE z z = subE oneE (Term.realize (Sum.elim w xs) t) := by
  rw [BoundedFormula.realize_ex]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩

theorem absLeOneForm_realize_add {β : Type} {l : ℕ} (t : LEc.Term (β ⊕ Fin l))
    (w : β → M) (xs : Fin l → M) :
    ((Term.bdEqual (eMul (witTerm (l := l)) (witTerm (l := l)))
        (eAdd eOne (pushTerm t))).ex : LEc.BoundedFormula β l).Realize w xs ↔
      ∃ z : M, mulE z z = addE oneE (Term.realize (Sum.elim w xs) t) := by
  rw [BoundedFormula.realize_ex]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩

theorem absLeOneForm_realize {β : Type} {l : ℕ} (t : LEc.Term (β ⊕ Fin l))
    (w : β → M) (xs : Fin l → M) :
    (absLeOneForm t).Realize w xs ↔ absLeOne (Term.realize (Sum.elim w xs) t) := by
  simp only [absLeOneForm, BoundedFormula.realize_inf, absLeOne, isSquare,
    absLeOneForm_realize_sub, absLeOneForm_realize_add]

/-! ## 3. Finite conjunctions and the realization of terms in the reduct -/

/-- Conjunction of a finite family of formulas (over `Fin l`). -/
def finAnd {β : Type} {k : ℕ} : (l : ℕ) → (Fin l → LEc.BoundedFormula β k) → LEc.BoundedFormula β k
  | 0, _ => ⊤
  | (l + 1), f => finAnd l (fun i => f i.castSucc) ⊓ f (Fin.last l)

theorem finAnd_realize {β : Type} {k : ℕ} (l : ℕ) (f : Fin l → LEc.BoundedFormula β k)
    (w : β → M) (xs : Fin k → M) :
    (finAnd l f).Realize w xs ↔ ∀ i, (f i).Realize w xs := by
  induction l with
  | zero => simp [finAnd]
  | succ l ih =>
      rw [finAnd, BoundedFormula.realize_inf, ih]
      constructor
      · rintro ⟨h₁, h₂⟩ i
        exact Fin.lastCases h₂ (fun j => h₁ j) i
      · intro h
        exact ⟨fun j => h j.castSucc, h (Fin.last l)⟩

/-- **Realization of an `LRc`-term in the `rexp`-reduct of an `LEc`-structure.** -/
def rRealize {β : Type} (v : β → M) (t : LRc.Term β) : M :=
  @Term.realize LRc M (reductStruct M) β v t

/-- **Realization of an `LRc`-formula in the `rexp`-reduct of an `LEc`-structure.** -/
def rRealizeF {α : Type} {k : ℕ} (v : α → M) (xs : Fin k → M) (φ : LRc.BoundedFormula α k) : Prop :=
  @BoundedFormula.Realize LRc M (reductStruct M) α k φ v xs

theorem rRealizeF_iff {α : Type} {k : ℕ} (v : α → M) (xs : Fin k → M)
    (φ : LRc.BoundedFormula α k) :
    rRealizeF v xs φ ↔ @BoundedFormula.Realize LRc M (reductStruct M) α k φ v xs := Iff.rfl

@[simp] theorem rRealize_var {β : Type} (v : β → M) (a : β) :
    rRealize v (Term.var a : LRc.Term β) = v a := rfl

@[simp] theorem rRealize_func {β : Type} {l : ℕ} (v : β → M) (f : LRc.Functions l)
    (ts : Fin l → LRc.Term β) :
    rRealize v (Term.func f ts) = @Structure.funMap LRc M (reductStruct M) l f (fun i => rRealize v (ts i)) :=
  rfl

@[simp] theorem rRealizeF_bdEqual {α : Type} {k : ℕ} (v : α → M) (xs : Fin k → M)
    (t₁ t₂ : LRc.Term (α ⊕ Fin k)) :
    rRealizeF v xs (Term.bdEqual t₁ t₂ : LRc.BoundedFormula α k) ↔
      @Term.realize LRc M (reductStruct M) (α ⊕ Fin k) (Sum.elim v xs) t₁ =
        @Term.realize LRc M (reductStruct M) (α ⊕ Fin k) (Sum.elim v xs) t₂ :=
  Iff.rfl

theorem rRealizeF_equal {α : Type} {k : ℕ} (v : α → M) (xs : Fin k → M)
    (t₁ t₂ : LRc.Term (α ⊕ Fin k)) :
    rRealizeF v xs (BoundedFormula.equal t₁ t₂) ↔
      rRealize (Sum.elim v xs) t₁ = rRealize (Sum.elim v xs) t₂ := Iff.rfl

@[simp] theorem rRealizeF_falsum {α : Type} {k : ℕ} (v : α → M) (xs : Fin k → M) :
    rRealizeF v xs (⊥ : LRc.BoundedFormula α k) ↔ False := Iff.rfl

@[simp] theorem rRealizeF_imp {α : Type} {k : ℕ} (v : α → M) (xs : Fin k → M)
    (φ ψ : LRc.BoundedFormula α k) :
    rRealizeF v xs (φ.imp ψ) ↔ (rRealizeF v xs φ → rRealizeF v xs ψ) := Iff.rfl

@[simp] theorem rRealizeF_all {α : Type} {k : ℕ} (v : α → M) (xs : Fin k → M)
    (φ : LRc.BoundedFormula α (k + 1)) :
    rRealizeF v xs (φ.all) ↔ ∀ a : M, rRealizeF v (Fin.snoc xs a) φ := Iff.rfl

/-! ## 4. The graph of an `LRc`-term -/

/-- The free variable which holds the value of a term. -/
def valVar {β : Type} (l : ℕ) : LEc.Term ((β ⊕ Fin 1) ⊕ Fin l) := Term.var (Sum.inl (Sum.inr 0))

/-- The `i`-th fresh bound variable, which holds the value of the `i`-th subterm. -/
def argVar {β : Type} {l : ℕ} (i : Fin l) : LEc.Term ((β ⊕ Fin 1) ⊕ Fin l) := Term.var (Sum.inr i)

@[simp] theorem realize_valVar {β : Type} {l : ℕ} (w : (β ⊕ Fin 1) → M) (xs : Fin l → M) :
    Term.realize (Sum.elim w xs) (valVar (β := β) l) = w (Sum.inr 0) := rfl

@[simp] theorem realize_argVar {β : Type} {l : ℕ} (w : (β ⊕ Fin 1) → M) (xs : Fin l → M)
    (i : Fin l) :
    Term.realize (Sum.elim w xs) (argVar (β := β) i) = xs i := rfl

/-- The `rexp`-symbol, as a relation between the argument and the value in the reduct. -/
def rexpRel {β : Type} : {l : ℕ} → rexpL.Functions l → LEc.BoundedFormula (β ⊕ Fin 1) l
  | 1, .rexp =>
      (absLeOneForm (argVar (β := β) 0) ⊓ Term.bdEqual (valVar (β := β) 1) (eExp (argVar (β := β) 0)))
        ⊔ ((absLeOneForm (argVar (β := β) 0)).not ⊓ Term.bdEqual (valVar (β := β) 1) eZero)

/-- The constant symbol, as a relation between the (empty) argument list and the value. -/
def constRel {β : Type} {l : ℕ} (c : (constantsOn ℝ).Functions l) :
    LEc.BoundedFormula (β ⊕ Fin 1) l :=
  Term.bdEqual (valVar (β := β) l)
    (@Term.func LEc ((β ⊕ Fin 1) ⊕ Fin l) l (constSym c) (fun _ => valVar (β := β) l))

/-- **The relation between the value of a function symbol applied to the subterm values and the
value of the term.**  For a ring symbol it is the corresponding `LEc`-equation; for `rexp` it is
the graph of `rexpFromExp`; for a constant it is the constant. -/
def outerRel {β : Type} {l : ℕ} (f : LRc.Functions l) : LEc.BoundedFormula (β ⊕ Fin 1) l :=
  match f with
  | Sum.inl (Sum.inl g) => Term.bdEqual (valVar (β := β) l) (Term.func (ringSym g) (fun i => argVar i))
  | Sum.inl (Sum.inr r) => rexpRel (β := β) r
  | Sum.inr c => constRel (β := β) c

/-- Realization of an `LEc`-term built from a function symbol. -/
theorem realize_funcE {α : Type} {l : ℕ} (v : α → M) (f : LEc.Functions l)
    (ts : Fin l → LEc.Term α) :
    Term.realize v (Term.func f ts) = Structure.funMap f (fun i => Term.realize v (ts i)) :=
  @Term.realize_func LEc M _ α v l f ts

/-- Two maps out of `Fin 0` are equal. -/
theorem fin0_funext {α : Type} (f g : Fin 0 → α) : f = g := funext fun i => Fin.elim0 i

theorem outerRel_realize {β : Type} {l : ℕ} (f : LRc.Functions l)
    (w : (β ⊕ Fin 1) → M) (xs : Fin l → M) :
    (outerRel f).Realize w xs ↔
      @Structure.funMap LRc M (reductStruct M) l f xs = w (Sum.inr 0) := by
  rcases f with (g | c)
  · rcases g with (g | r)
    · -- ring symbol
      have h1 : Term.realize (Sum.elim w xs) (Term.func (ringSym g) (fun i => argVar (β := β) i))
          = @Structure.funMap LRc M (reductStruct M) l (Sum.inl (Sum.inl g)) xs := by
        rw [realize_funcE, reductStruct_funMap_ring]
        congr 1
      have hout : outerRel (β := β) (Sum.inl (Sum.inl g)) =
          Term.bdEqual (valVar (β := β) l) (Term.func (ringSym g) (fun i => argVar i)) := rfl
      rw [hout, BoundedFormula.realize_bdEqual, realize_valVar, h1, eq_comm]
    · -- the rexp symbol
      cases r
      have h1 : ((absLeOneForm (argVar (β := β) 0)) ⊓
            Term.bdEqual (valVar (β := β) 1) (eExp (argVar (β := β) 0))).Realize w xs ↔
          absLeOne (xs 0) ∧ w (Sum.inr 0) = expE (xs 0) := by
        simp only [BoundedFormula.realize_inf, absLeOneForm_realize, realize_argVar,
          BoundedFormula.realize_bdEqual, realize_valVar, realize_eExp]
      have h2 : (((absLeOneForm (argVar (β := β) 0)).not) ⊓
            Term.bdEqual (valVar (β := β) 1) eZero).Realize w xs ↔
          ¬ absLeOne (xs 0) ∧ w (Sum.inr 0) = zeroE := by
        simp only [BoundedFormula.realize_inf, BoundedFormula.realize_not, absLeOneForm_realize,
          realize_argVar, BoundedFormula.realize_bdEqual, realize_valVar, realize_eZero]
      have hout : outerRel (β := β) (Sum.inl (Sum.inr rexpFunc.rexp)) =
          rexpRel (β := β) rexpFunc.rexp := rfl
      rw [hout, rexpRel, BoundedFormula.realize_sup, h1, h2, reductStruct_funMap_rexp]
      by_cases h : absLeOne (xs 0)
      · rw [rexpFromExp_of_absLeOne h]
        simp [h, eq_comm]
      · rw [rexpFromExp_of_not_absLeOne h]
        simp [h, eq_comm]
  · -- a constant symbol (only `l = 0` is possible)
    cases l with
    | zero =>
        have h1 : Term.realize (Sum.elim w xs)
            (@Term.func LEc ((β ⊕ Fin 1) ⊕ Fin 0) 0 (constSym c) (fun _ => valVar (β := β) 0))
            = @Structure.funMap LRc M (reductStruct M) 0 (constSymL c) xs := by
          rw [realize_funcE, reductStruct_funMap_constSym]
          exact congrArg _ (fin0_funext _ _)
        have hout : outerRel (β := β) (Sum.inr c) = constRel (β := β) c := rfl
        rw [hout, constRel, BoundedFormula.realize_bdEqual, realize_valVar, h1, constSymL_eq,
          eq_comm]
    | succ l => exact isEmptyElim c

/-! ## 5. The graph of a term -/

/-- The free variables of a subterm graph mapped into fresh bound variables: the value variable
goes to the `i`-th fresh bound variable, everything else is untouched. -/
def freshMap {β : Type} {l : ℕ} (i : Fin l) : (β ⊕ Fin 1) → (β ⊕ Fin 1) ⊕ Fin l
  | Sum.inl b => Sum.inl (Sum.inl b)
  | Sum.inr _ => Sum.inr i

/-- **The graph of an `LRc`-term.**  `termGraph t` is an `LEc`-formula with free variables
`β ⊕ Fin 1`; it is realized by `w` iff the value of `t` (at `w ∘ Sum.inl`) is `w (Sum.inr 0)`. -/
def termGraph {β : Type} : LRc.Term β → LEc.Formula (β ⊕ Fin 1)
  | .var a => Term.equal (Term.var (Sum.inl a)) (Term.var (Sum.inr 0))
  | .func f ts =>
      (finAnd _ (fun i => BoundedFormula.relabel (freshMap i) (termGraph (ts i))) ⊓ outerRel f).exs

/-- The assignment of the graph of a subterm inside the graph of a compound term. -/
theorem freshMap_elim {β : Type} {l : ℕ} (i : Fin l) (w : (β ⊕ Fin 1) → M) (xs : Fin l → M) :
    (Sum.elim w (xs ∘ Fin.castAdd 0) ∘ freshMap i) =
      Sum.elim (w ∘ Sum.inl) (fun _ => xs i) := by
  funext z
  rcases z with (b | b)
  · rfl
  · simp only [Function.comp_apply, freshMap, Sum.elim_inr]
    congr 1

/-- All maps out of `Fin 0` are the default one. -/
theorem fin0_eq_default {α : Type} (f : Fin 0 → α) : f = default :=
  funext fun i => Fin.elim0 i

/-- `Formula.Realize` is `BoundedFormula.Realize` at the (empty) assignment `Fin 0 → M`. -/
theorem formulaRealize_of_bounded {α : Type} (φ : LEc.Formula α) (v : α → M)
    (ys : Fin 0 → M) : BoundedFormula.Realize φ v ys → φ.Realize v := by
  rw [Formula.Realize, fin0_eq_default ys]
  exact id

theorem bounded_of_formulaRealize {α : Type} (φ : LEc.Formula α) (v : α → M)
    (ys : Fin 0 → M) : φ.Realize v → BoundedFormula.Realize φ v ys := by
  rw [Formula.Realize, fin0_eq_default ys]
  exact id

theorem termGraph_realize {β : Type} (t : LRc.Term β) (w : (β ⊕ Fin 1) → M) :
    (termGraph t).Realize w ↔ rRealize (w ∘ Sum.inl) t = w (Sum.inr 0) := by
  revert w
  induction t with
  | var a =>
      intro w
      rw [termGraph, Term.equal, Formula.Realize, BoundedFormula.realize_bdEqual,
        Term.realize_relabel, Term.realize_relabel, Term.realize_var, Term.realize_var,
        rRealize_var]
      simp only [Function.comp_apply, Sum.elim_inl]
  | func f ts ih =>
      intro w
      rw [termGraph, BoundedFormula.realize_exs]
      constructor
      · rintro ⟨xs, hxs⟩
        rw [BoundedFormula.realize_inf, finAnd_realize] at hxs
        obtain ⟨hsub, hout⟩ := hxs
        have hval : ∀ i, rRealize (w ∘ Sum.inl) (ts i) = xs i := by
          intro i
          have hi := hsub i
          rw [BoundedFormula.realize_relabel, freshMap_elim i w xs] at hi
          exact (ih i (Sum.elim (w ∘ Sum.inl) (fun _ => xs i))).mp
            (formulaRealize_of_bounded (termGraph (ts i)) _ _ hi)
        have hout' := (outerRel_realize f w xs).mp hout
        rw [rRealize_func]
        rw [show (fun i => rRealize (w ∘ Sum.inl) (ts i)) = xs from funext hval]
        exact hout'
      · intro h
        refine ⟨fun i => rRealize (w ∘ Sum.inl) (ts i), ?_⟩
        rw [BoundedFormula.realize_inf, finAnd_realize]
        refine ⟨fun i => ?_, (outerRel_realize f w _).mpr ?_⟩
        · have hgoal : (termGraph (ts i)).Realize (Sum.elim (w ∘ Sum.inl)
              (fun _ => rRealize (w ∘ Sum.inl) (ts i))) :=
            (ih i (Sum.elim (w ∘ Sum.inl)
              (fun _ => rRealize (w ∘ Sum.inl) (ts i)))).mpr rfl
          rw [BoundedFormula.realize_relabel, freshMap_elim i w _]
          exact bounded_of_formulaRealize (termGraph (ts i)) _ _ hgoal
        · rw [rRealize_func] at h
          exact h

/-! ## 6. The translation of formulas -/

/-- The map of free variables used to translate an atomic formula: the `n` ambient variables stay
free, the `m` variables of the term become bound, and the value variable becomes the last bound
variable. -/
def atomMap {α : Type} {m : ℕ} : (α ⊕ Fin m) ⊕ Fin 1 → α ⊕ Fin (m + 1)
  | Sum.inl (Sum.inl i) => Sum.inl i
  | Sum.inl (Sum.inr j) => Sum.inr (Fin.castSucc j)
  | Sum.inr _ => Sum.inr (Fin.last m)

/-- The composite of `Sum.elim A B` with `Sum.inl` is `A`. -/
theorem elim_inl_comp {α β : Type} (A : α → M) (B : β → M) : Sum.elim A B ∘ Sum.inl = A := rfl

/-- `Sum.elim A B` at `Sum.inr 0`. -/
theorem elim_inr_zero {α : Type} (A : α → M) (B : Fin 1 → M) :
    Sum.elim A B (Sum.inr 0) = B 0 := rfl

/-- The assignment induced by `atomMap` on the atomic formula of `termGraph`. -/
theorem atomMap_elim {α : Type} {m : ℕ} (v : α → M) (xs : Fin m → M) (a : M) :
    (Sum.elim v ((Fin.snoc xs a) ∘ Fin.castAdd 0) ∘ atomMap (α := α) (m := m)) =
      Sum.elim (Sum.elim v xs) (fun _ => a) := by
  funext z
  rcases z with ((i | j) | b)
  · simp only [Function.comp_apply, atomMap, Sum.elim_inl]
  · simp only [Function.comp_apply, atomMap, Sum.elim_inl, Sum.elim_inr]
    rw [show (Fin.castAdd 0 (Fin.castSucc j) : Fin ((m + 1) + 0)) = Fin.castSucc j from
      Fin.ext rfl]
    simp
  · simp only [Function.comp_apply, atomMap, Sum.elim_inl, Sum.elim_inr]
    rw [show (Fin.castAdd 0 (Fin.last m) : Fin ((m + 1) + 0)) = Fin.last m from Fin.ext rfl]
    simp

/-- **The translation of `LRc`-formulas into `LEc`-formulas.** -/
def formulaTrans {α : Type} : ∀ {m : ℕ}, LRc.BoundedFormula α m → LEc.BoundedFormula α m
  | _, .falsum => ⊥
  | _, .equal t₁ t₂ => (BoundedFormula.relabel (atomMap (α := α)) (termGraph t₁ ⊓ termGraph t₂)).ex
  | _, .imp φ ψ => (formulaTrans φ).imp (formulaTrans ψ)
  | _, .all φ => (formulaTrans φ).all

theorem formulaTrans_realize {α : Type} {m : ℕ} (φ : LRc.BoundedFormula α m)
    (v : α → M) (xs : Fin m → M) :
    (formulaTrans φ).Realize v xs ↔ rRealizeF v xs φ := by
  revert v xs
  induction φ with
  | falsum =>
      intro v xs
      rw [formulaTrans, BoundedFormula.realize_bot]
      exact (rRealizeF_falsum v xs).symm
  | equal t₁ t₂ =>
      intro v xs
      simp only [formulaTrans, BoundedFormula.realize_ex, BoundedFormula.realize_relabel,
        BoundedFormula.realize_inf]
      rw [rRealizeF_equal]
      constructor
      · rintro ⟨a, h₁, h₂⟩
        rw [atomMap_elim] at h₁ h₂
        have h₁' : rRealize (Sum.elim v xs) t₁ = a := by
          have h := formulaRealize_of_bounded (termGraph t₁)
            (Sum.elim (Sum.elim v xs) (fun _ => a)) _ h₁
          rw [termGraph_realize] at h
          simpa only [elim_inl_comp, elim_inr_zero] using h
        have h₂' : rRealize (Sum.elim v xs) t₂ = a := by
          have h := formulaRealize_of_bounded (termGraph t₂)
            (Sum.elim (Sum.elim v xs) (fun _ => a)) _ h₂
          rw [termGraph_realize] at h
          simpa only [elim_inl_comp, elim_inr_zero] using h
        rw [h₁', h₂']
      · rintro h
        refine ⟨rRealize (Sum.elim v xs) t₁, ?_, ?_⟩
        · rw [atomMap_elim]
          refine bounded_of_formulaRealize (termGraph t₁) _ _ ((termGraph_realize t₁ _).mpr ?_)
          simp only [elim_inl_comp, elim_inr_zero]
        · rw [atomMap_elim]
          refine bounded_of_formulaRealize (termGraph t₂) _ _ ((termGraph_realize t₂ _).mpr ?_)
          simpa only [elim_inl_comp, elim_inr_zero] using h.symm
  | rel R _ =>
      intro v xs
      nomatch R
  | imp φ ψ ihφ ihψ =>
      intro v xs
      rw [formulaTrans, BoundedFormula.realize_imp, rRealizeF_imp, ihφ v xs, ihψ v xs]
  | all φ ih =>
      intro v xs
      rw [formulaTrans, BoundedFormula.realize_all, rRealizeF_all]
      exact forall_congr' fun a => ih v (Fin.snoc xs a)

end Work.WilC5
