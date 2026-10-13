/-
  WilC5 — area C5 of the Wilkie / van den Dries–Macintyre–Marker development.

  **The language bridge between `T_r` and `T_e`.**

  `TR = LRc.completeTheory ℝ` is the theory of `ℝ` with the *restricted* exponential (exp on
  `[-1,1]`, `0` outside), in the language `LRc` of ordered rings with `rexp` and a constant for
  every real.  `TE = LEc.completeTheory ℝ` is the theory of `ℝ_exp`, in the language `LEc` of
  ordered rings with the full exponential and a constant for every real.

  In every ordered exponential field the restricted exponential is *definable* from the full
  exponential, by the ring formula

      `rexpDef(x, w)  :=  (|x| ≤ 1 ∧ w = exp x) ∨ (|x| > 1 ∧ w = 0)`

  where `|x| ≤ 1` is the ring formula `∃z, z*z = 1 - x ∧ ∃z, z*z = 1 + x` (in an ordered field
  this is the interval `[-1,1]`; the order itself is the ring formula `x ≤ y ↔ ∃z, z*z = y - x`).

  This module provides
  * `LEc`-term/formula constructors (`eAdd`, `eMul`, ...) so that the `LEc`-formulas below can be
    written down;
  * `rexpFromExp`, the function defined by `rexpDef`, and `reductStruct`, the `LRc`-structure
    with `rexp` interpreted by `rexpFromExp` (the `rexp`-reduct of an `LEc`-structure);
  * the syntactic translation of `LRc`-formulas into `LEc`-formulas (`Translate.lean`) and the
    resulting model-theoretic consequences: every model of `TE` has a `rexp`-reduct which is a
    model of `TR` (`Reduct.lean`).
-/
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. Function symbols and terms of `LEc` -/

/-- The symbol of `LEc` corresponding to a ring symbol.  `LEc = (ring ⊕ exp)[[ℝ]]`, so a ring
symbol sits at `Sum.inl (Sum.inl ·)`. -/
def ringSym {n : ℕ} (f : Language.ring.Functions n) : LEc.Functions n := Sum.inl (Sum.inl f)

/-- The symbol of `LEc` corresponding to the exponential. -/
def expSym {n : ℕ} (f : (Language.exp).Functions n) : LEc.Functions n := Sum.inl (Sum.inr f)

@[simp] theorem ringSym_eq {n : ℕ} (f : Language.ring.Functions n) :
    ringSym f = (Sum.inl (Sum.inl f) : LEc.Functions n) := rfl

/-- The constant symbols of `LEc`, as a `def` so that the language is not left implicit. -/
def constSym {n : ℕ} (c : (constantsOn ℝ).Functions n) : LEc.Functions n := Sum.inr c

/-- The constant symbols of `LRc`.  These are the same symbols as those of `LEc`. -/
def constSymL {n : ℕ} (c : (constantsOn ℝ).Functions n) : LRc.Functions n := Sum.inr c

@[simp] theorem constSym_eq {n : ℕ} (c : (constantsOn ℝ).Functions n) :
    constSym c = (Sum.inr c : LEc.Functions n) := rfl

@[simp] theorem constSymL_eq {n : ℕ} (c : (constantsOn ℝ).Functions n) :
    constSymL c = (Sum.inr c : LRc.Functions n) := rfl

/-- Addition as an `LEc`-term. -/
def eAdd {α : Type} (t₁ t₂ : LEc.Term α) : LEc.Term α :=
  Term.func (ringSym Ring.addFunc) ![t₁, t₂]

/-- Multiplication as an `LEc`-term. -/
def eMul {α : Type} (t₁ t₂ : LEc.Term α) : LEc.Term α :=
  Term.func (ringSym Ring.mulFunc) ![t₁, t₂]

/-- Negation as an `LEc`-term. -/
def eNeg {α : Type} (t : LEc.Term α) : LEc.Term α :=
  Term.func (ringSym Ring.negFunc) ![t]

/-- The constant `0` as a term. -/
def eZero {α : Type} : LEc.Term α := Term.func (ringSym Ring.zeroFunc) default

/-- The constant `1` as a term. -/
def eOne {α : Type} : LEc.Term α := Term.func (ringSym Ring.oneFunc) default

/-- Subtraction as an `LEc`-term. -/
def eSub {α : Type} (t₁ t₂ : LEc.Term α) : LEc.Term α := eAdd t₁ (eNeg t₂)

/-- The exponential as an `LEc`-term. -/
def eExp {α : Type} (t : LEc.Term α) : LEc.Term α :=
  Term.func (expSym expFunc.exp) ![t]

/-! ## 2. `|x| ≤ 1` and the definable restricted exponential -/

section Semantics

variable {M : Type} [LEc.Structure M]

/-- Addition of an `LEc`-structure, extracted from the language. -/
def addE (x y : M) : M := Structure.funMap (ringSym Ring.addFunc) ![x, y]

/-- Multiplication of an `LEc`-structure. -/
def mulE (x y : M) : M := Structure.funMap (ringSym Ring.mulFunc) ![x, y]

/-- Negation of an `LEc`-structure. -/
def negE (x : M) : M := Structure.funMap (ringSym Ring.negFunc) ![x]

/-- The zero of an `LEc`-structure. -/
def zeroE : M := Structure.funMap (ringSym Ring.zeroFunc) default

/-- The one of an `LEc`-structure. -/
def oneE : M := Structure.funMap (ringSym Ring.oneFunc) default

/-- Subtraction in an `LEc`-structure. -/
def subE (x y : M) : M := addE x (negE y)

/-- The exponential of an `LEc`-structure. -/
def expE (x : M) : M := Structure.funMap (expSym expFunc.exp) ![x]

@[simp] theorem addE_def (x y : M) :
    addE x y = Structure.funMap (ringSym Ring.addFunc) ![x, y] := rfl

@[simp] theorem mulE_def (x y : M) :
    mulE x y = Structure.funMap (ringSym Ring.mulFunc) ![x, y] := rfl

@[simp] theorem expE_def (x : M) :
    expE x = Structure.funMap (expSym expFunc.exp) ![x] := rfl

/-- The ring formula `∃z, z*z = y`. -/
def isSquare (y : M) : Prop := ∃ z : M, mulE z z = y

/-- The ring formula `x ≤ y`, i.e. `∃z, z*z = y - x`, in an `LEc`-structure.  In a model of `TE`
this is the usual order (see `OrderFacts.lean`). -/
def leE (x y : M) : Prop := isSquare (subE y x)

/-- `|x| ≤ 1`: `∃z, z*z = 1 - x` and `∃z, z*z = 1 + x`. -/
def absLeOne (x : M) : Prop := isSquare (subE oneE x) ∧ isSquare (addE oneE x)

/-- **The restricted exponential, as a function definable in `LEc`**: `exp x` for `|x| ≤ 1` and
`0` otherwise.  This is the interpretation of the `rexp` symbol of `LRc` in the `rexp`-reduct of
an `LEc`-structure. -/
def rexpFromExp (x : M) : M := if absLeOne x then expE x else zeroE

@[simp] theorem rexpFromExp_of_absLeOne {x : M} (h : absLeOne x) :
    rexpFromExp x = expE x := by simp [rexpFromExp, h]

@[simp] theorem rexpFromExp_of_not_absLeOne {x : M} (h : ¬ absLeOne x) :
    rexpFromExp x = zeroE := by simp [rexpFromExp, h]

end Semantics

/-! ## 3. The `rexp`-reduct of an `LEc`-structure -/

/-- **The `rexp`-reduct.**  The `LRc`-structure on `M` whose ring and constant symbols are those
of the given `LEc`-structure and whose `rexp` symbol is interpreted by `rexpFromExp`. -/
@[instance_reducible]
def reductStruct (M : Type) [LEc.Structure M] : LRc.Structure M where
  funMap := fun {n} f xs =>
    match f with
    | Sum.inl (Sum.inl g) => @Structure.funMap LEc M _ n (ringSym g) xs
    | Sum.inl (Sum.inr r) => match n, r with
      | 1, rexpFunc.rexp => rexpFromExp (xs 0)
    | Sum.inr c => @Structure.funMap LEc M _ n (Sum.inr c) xs
  RelMap := fun {n} r _ => nomatch r

theorem reductStruct_funMap_ring (M : Type) [LEc.Structure M] {n : ℕ}
    (g : Language.ring.Functions n) (xs : Fin n → M) :
    @Structure.funMap LRc M (reductStruct M) n (Sum.inl (Sum.inl g)) xs =
      @Structure.funMap LEc M _ n (ringSym g) xs := rfl

theorem reductStruct_funMap_const (M : Type) [LEc.Structure M] {n : ℕ}
    (c : (constantsOn ℝ).Functions n) (xs : Fin n → M) :
    @Structure.funMap LRc M (reductStruct M) n (Sum.inr c) xs =
      @Structure.funMap LEc M _ n (Sum.inr c) xs := rfl

theorem reductStruct_funMap_constSym (M : Type) [LEc.Structure M] {n : ℕ}
    (c : (constantsOn ℝ).Functions n) (xs : Fin n → M) :
    @Structure.funMap LRc M (reductStruct M) n (constSymL c) xs =
      @Structure.funMap LEc M _ n (constSym c) xs := rfl

theorem reductStruct_funMap_rexp (M : Type) [LEc.Structure M] (xs : Fin 1 → M) :
    @Structure.funMap LRc M (reductStruct M) 1 (Sum.inl (Sum.inr rexpFunc.rexp)) xs =
      rexpFromExp (xs 0) := rfl

end Work.WilC5
