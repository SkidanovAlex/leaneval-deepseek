/-
  WilC5 — the `LEc`-vocabulary of the lemma `Work.WilC5.LogFunPowLtSelf`.

  The target is: in a model `K` of `TE = Th(ℝ_exp)` with the canonical `LEc`-data, an element
  `x` which is *infinite* (bigger than every natural number, `¬ IsFiniteVal x`) satisfies

      `(logFun x) ^ n < x`   for every `n : ℕ`.

  The mathematical content is the real-analysis fact

      `∃ N : ℕ, ∀ x : ℝ, N < x → (log x) ^ n < x`                        (`Work.WilC5.ExistsLogPowLtSelf`)

  together with the *transfer* of the corresponding `LEc`-sentence to `K`.  The sentence has to
  quantify over a *numeral* threshold, i.e. over a bound depending on `n`; a real constant of the
  language would be useless, because the hypotheses of `LogFunPowLtSelf` say nothing about how `K`
  interprets the constant symbols.  Hence the two term constructors defined here:

  * `numTerm N : LEc.Term α` — the numeral `1 + 1 + ⋯ + 1` (`N` ones), so that
    `Term.realize v (numTerm N) = (N : K)`;
  * `powTerm k t : LEc.Term α` — the term `t * t * ⋯ * t` (`k` factors), so that
    `Term.realize v (powTerm k t) = (Term.realize v t) ^ k`.

  The formula `logPowLtForm N k` is the `LEc`-sentence (with two bound variables `&0 = x`, `&1 = y`)

      `(x > N ∧ logDefSet x y) → y ^ k < x`

  whose real content is the real-analysis fact above, and whose transfer to `K` — instantiated at
  `y = logFun x` — is the target.  This module fixes the vocabulary and the (purely syntactic)
  realization lemmas; the real content of `logPowLtForm` is `Work.WilC5.LogPowLtFormReal`.

  Implementation notes:
  * `logDefSet &0 &1` is written out with `leForm`/`Term.bdEqual` exactly as in
    `logFun_one_add_rexp.lean` (`logPairForm`), the only difference being that the first bound
    variable itself — and not `1 + &0` — plays the role of the argument of the logarithm;
  * the conclusions are written with the *negation* of `≤` (i.e. `x > N` and `y^k < x`), so that
    the transfer gives the strict inequalities directly.
-/
import Mathlib
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.Translate

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The numeral term `1 + 1 + ⋯ + 1` and the power term `t * t * ⋯ * t` -/

/-- **The numeral `N` as an `LEc`-term**: `0`, `1`, `1+1`, …  (written from `eZero` and `eOne` by
repeated addition, so that it is interpreted by `(N : K)` in every `LEc`-structure whose `ring`
symbols agree with a field structure). -/
def numTerm {α : Type} : ℕ → LEc.Term α
  | 0 => eZero
  | (n + 1) => eAdd (numTerm n) eOne

/-- **The `k`-th power of a term**: `t * t * ⋯ * t` (`k` factors, `1` for `k = 0`). -/
def powTerm {α : Type} : ℕ → LEc.Term α → LEc.Term α
  | 0, _ => eOne
  | (k + 1), t => eMul (powTerm k t) t

/-- The numeral term evaluates to the natural number, on `ℝ`. -/
theorem numTerm_realize_real {α : Type} (v : α → ℝ) (N : ℕ) :
    Term.realize v (numTerm (α := α) N) = (N : ℝ) := by
  induction N with
  | zero => simp only [numTerm, realize_eZero, zeroE_real, Nat.cast_zero]
  | succ N ih =>
    simp only [numTerm, realize_eAdd, realize_eOne, ih, addE_real, oneE_real, Nat.cast_succ]

/-- The numeral term evaluates to the natural number, in a model of `TE` whose ring symbols agree
with the field structure (this is what needs `zeroE = 0`, i.e. `S4ExpF.zeroE_eq_zero`). -/
theorem numTerm_realize_of_model {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K] [rexpL.Structure K]
    [(constantsOn ℝ).Structure K]
    (hTE : K ⊨ TE) (hadd : ∀ x y : K, addE x y = x + y) (hone : (oneE : K) = 1)
    {α : Type} (v : α → K) (N : ℕ) :
    Term.realize v (numTerm (α := α) N) = (N : K) := by
  have h0 : (zeroE : K) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hTE hadd
  induction N with
  | zero => simp only [numTerm, realize_eZero, h0, Nat.cast_zero]
  | succ N ih =>
    simp only [numTerm, realize_eAdd, realize_eOne, ih, hadd, hone, Nat.cast_succ]

/-- The power term evaluates to the field power, on `ℝ`. -/
theorem powTerm_realize_real {α : Type} (v : α → ℝ) (t : LEc.Term α) (k : ℕ) :
    Term.realize v (powTerm k t) = (Term.realize v t) ^ k := by
  induction k with
  | zero => simp only [powTerm, realize_eOne, oneE_real, pow_zero]
  | succ k ih => simp only [powTerm, realize_eMul, ih, mulE_real, pow_succ]

/-- The power term evaluates to the field power, in a model of `TE` whose ring symbols agree with
the field structure. -/
theorem powTerm_realize_of_model {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K] [rexpL.Structure K]
    [(constantsOn ℝ).Structure K]
    (hmul : ∀ x y : K, mulE x y = x * y) (hone : (oneE : K) = 1)
    {α : Type} (v : α → K) (t : LEc.Term α) (k : ℕ) :
    Term.realize v (powTerm k t) = (Term.realize v t) ^ k := by
  induction k with
  | zero => simp only [powTerm, realize_eOne, hone, pow_zero]
  | succ k ih => simp only [powTerm, realize_eMul, ih, hmul, pow_succ]

/-! ## 2. The formulas `logDefSet &0 &1` and `(x > N ∧ logDefSet x y) → y^k < x` -/

/-- The formula `logDefSet &0 &1`, i.e. "the second bound variable is a definable logarithm of the
first".  This is `logPairForm` of `logFun_one_add_rexp.lean` with the *first* bound variable itself
in place of `1 + &0`. -/
def logDefForm : LEc.BoundedFormula Empty 2 :=
  ((leForm eZero (v2 0) ⊓ (leForm (v2 0) eZero).not) ⊓ Term.bdEqual (eExp (v2 1)) (v2 0)) ⊔
    (((leForm eZero (v2 0) ⊓ (leForm (v2 0) eZero).not).not) ⊓
      Term.bdEqual (eExp (v2 1)) eOne)

/-- **The master formula** (`&0 = x`, `&1 = y`):

    `x > N ∧ logDefSet x y  →  y ^ k < x`,

where `x > N` is the negation of the definable order `x ≤ N` (`N` being the numeral `numTerm N`)
and `y ^ k < x` is the negation of `x ≤ y ^ k`. -/
def logPowLtForm (N k : ℕ) : LEc.BoundedFormula Empty 2 :=
  (((leForm (v2 0) (numTerm N)).not) ⊓ logDefForm).imp
    ((leForm (v2 0) (powTerm k (v2 1))).not)

/-- Realization of the logarithm formula. -/
theorem logDefForm_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    logDefForm.Realize (emptyVar : Empty → M) xs ↔ logDefSet (xs 0) (xs 1) := by
  simp only [logDefForm, logDefSet, v2, Term.realize_var, Sum.elim_inr,
    BoundedFormula.realize_sup, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, leForm_realize, realize_eExp, realize_eZero, realize_eOne, leE]

/-- Realization of the master formula. -/
theorem logPowLtForm_realize {M : Type} [LEc.Structure M] (N k : ℕ) (xs : Fin 2 → M) :
    (logPowLtForm N k).Realize (emptyVar : Empty → M) xs ↔
      (¬ leE (xs 0) (Term.realize (Sum.elim (emptyVar : Empty → M) xs) (numTerm N)) ∧
        logDefSet (xs 0) (xs 1) →
      ¬ leE (xs 0) (Term.realize (Sum.elim (emptyVar : Empty → M) xs) (powTerm k (v2 1)))) := by
  simp only [logPowLtForm, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, logDefForm_realize, leForm_realize, leE, v2, Term.realize_var,
    Sum.elim_inr]

end Work.WilC5
