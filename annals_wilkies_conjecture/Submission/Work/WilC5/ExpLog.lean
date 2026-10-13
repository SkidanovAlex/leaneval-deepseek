/-
  WilC5 — the expanded language `LElog = LEc ⊕ {log, ≤}` and the definable logarithm.

  van den Dries–Macintyre–Marker prove model completeness of `Th(ℝ, exp)` (their (4.10)) by
  *quantifier elimination in an expansion of the language*: `(R̃, exp)` admits quantifier
  elimination in the language of `R̃` together with a symbol for `log` and symbols for the
  `∅`-definable functions of `R̃` (their Corollary 4.5).  For `R̃ = ℝ_rexp` this says that `TE`
  admits quantifier elimination after adding `log` (and the order) to the language.

  In this development the extra symbols are **definable in `LEc` itself**:

  * the order of a model of `TE` is the ring formula `leE x y  :=  ∃ z, z*z = y - x`
    (`Bridge.lean`, `ReductEmb.lean`);
  * `log` is the function defined by

        `logDefSet x y  :=  (0 < x ∧ exp y = x) ∨ (¬ 0 < x ∧ exp y = 1)`,

    which (by transfer from `ℝ`) is the graph of a total function in every model of `TE`; on `ℝ`
    it is the convention of van den Dries–Macintyre–Marker, `log x = log x` for `x > 0` and
    `log x = 0` otherwise.

  This module sets up the language `LElog`, the canonical `LElog`-structure `logStruct M` on every
  `LEc`-structure, and the definable logarithm `logFun`.  The facts about `logFun` in models of
  `TE` (`Work.WilC5.LogDefSetModel`, `Work.WilC5.LogFunReal`), the preservation of `logFun` by
  `LEc`-embeddings (`Work.WilC5.LogFunMap`) and the resulting `LElog`-embedding structure
  (`Work.WilC5.LogStructEmbedding`) are the statements of the companion modules.

  The *content* of the C5 route (vdDMM §4) is that every `LEc`-formula is equivalent, over the
  models of `TE`, to a quantifier-free `LElog`-formula: `Work.WilC5.DMM45_QE` in
  `Submission/Work/WilC5/Synthesis.lean`.  Once that is known, an `LEc`-embedding of models of
  `TE` is automatically an `LElog`-embedding and quantifier-free `LElog`-formulas are absolute for
  it; hence `TE` is model complete.
-/
import Submission.Work.WilC5.ReductEmb
import Mathlib.ModelTheory.Complexity

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The language `LElog = LEc ⊕ {log, ≤}` -/

/-- The `log` function symbol. -/
inductive logFunc : ℕ → Type
  | log : logFunc 1

/-- The order, as a binary relation symbol. -/
inductive ordRel : ℕ → Type
  | lt : ordRel 2

/-- The extra symbols of the expanded language. -/
def logExtra : Language where
  Functions := logFunc
  Relations := ordRel

/-- `LElog`: the expansion of `LEc` by the definable logarithm and the definable order. -/
abbrev LElog : Language := LEc.sum logExtra

/-! ## 2. The definable logarithm of an `LEc`-structure -/

section LogDef

variable {M : Type} [LEc.Structure M]

/-- The defining condition of the logarithm: `y = log x` iff `0 < x` and `exp y = x`, or `0 < x`
fails and `exp y = 1`.  (The strictness of the first clause is what makes the relation functional
at `x = 0`.) -/
def logDefSet (x y : M) : Prop :=
  ((leE zeroE x ∧ ¬ leE x zeroE) ∧ expE y = x) ∨
    (¬ (leE zeroE x ∧ ¬ leE x zeroE) ∧ expE y = oneE)

/-- **The definable logarithm.**  A `y` satisfying `logDefSet x y`, or `x` when there is none
(which does not happen in a model of `TE`: see `Work.WilC5.LogDefSetModel`). -/
def logFun (x : M) : M :=
  if h : ∃ y, logDefSet x y then Classical.choose h else x

/-- The `logExtra`-structure attached to an `LEc`-structure: `log` is the definable logarithm and
`u ≤ v` is the definable order `leE u v`. -/
instance logExtraStruct (M : Type) [LEc.Structure M] : logExtra.Structure M where
  funMap := fun {n} f xs => match n, f with
    | _, logFunc.log => logFun (xs 0)
  RelMap := fun {n} r xs => match n, r with
    | _, ordRel.lt => leE (xs 0) (xs 1)

/-- **The canonical `LElog`-structure on an `LEc`-structure**: the given `LEc`-structure together
with the definable logarithm and the definable order. -/
@[instance_reducible]
def logStruct (M : Type) [LEc.Structure M] : LElog.Structure M := inferInstance

@[simp] theorem logStruct_funMap_log (xs : Fin 1 → M) :
    @Structure.funMap LElog M (logStruct M) 1 (Sum.inr logFunc.log) xs = logFun (xs 0) := rfl

@[simp] theorem logStruct_relMap_lt (xs : Fin 2 → M) :
    @Structure.RelMap LElog M (logStruct M) 2 (Sum.inr ordRel.lt) xs ↔ leE (xs 0) (xs 1) :=
  Iff.rfl

@[simp] theorem logStruct_funMap_inl {n : ℕ} (f : LEc.Functions n) (xs : Fin n → M) :
    @Structure.funMap LElog M (logStruct M) n (Sum.inl f) xs =
      @Structure.funMap LEc M _ n f xs := rfl

@[simp] theorem logStruct_relMap_inl {n : ℕ} (r : LEc.Relations n) (xs : Fin n → M) :
    @Structure.RelMap LElog M (logStruct M) n (Sum.inl r) xs ↔
      @Structure.RelMap LEc M _ n r xs :=
  Iff.rfl

end LogDef

/-! ## 3. The theory `TElog = Th(ℝ, exp, log, ≤)`

The logarithm of the standard structure is the definable one; by `Work.WilC5.LogFunReal` it is the
vdDMM logarithm (`log x` for `x > 0`, `0` otherwise). -/

/-- **`T_e(exp, log)`**: the theory of the standard `LElog`-structure `logStruct ℝ`. -/
def TElog : LElog.Theory := @Language.completeTheory LElog ℝ (logStruct ℝ)

end Work.WilC5
