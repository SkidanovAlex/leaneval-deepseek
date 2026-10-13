/-
  WilC5 — `rexp` is the inverse of the definable logarithm near `1`.

  The definable logarithm `logFun` (`ExpLog.lean`) has the graph

      `logDefSet x y  =  (0 < x ∧ exp y = x) ∨ (¬ 0 < x ∧ exp y = 1)`,

  and `rexpFromExp` (`Bridge.lean`) is the definable restricted exponential
  `x ↦ if |x| ≤ 1 then exp x else 0`.  This module proves

      `rexpFromExp (logFun (1 + δ)) = 1 + δ`   whenever `|2δ| ≤ 1`,

  i.e. that `rexp` inverts `logFun` on the interval `[1/2, 3/2]` of its arguments (the logarithm
  of such an element lies in `[-1,1]`, where `rexp` agrees with `exp`).

  The proof is a *single transfer* (`Work.WilC5.transfer`, `ReductEmb.lean`): the whole statement
  is the `LEc`-formula

      `∀ δ y,  logDefSet (1+δ) y  →  (|2δ| ≤ 1)  →  rexpFromExp y = 1+δ`

  (all the functions involved — `1+·`, `2·`, `logDefSet`, `exp`, `rexpFromExp` — are `LEc`-definable
  and `|x| ≤ 1` is the ring formula `∃z, z*z = 1-x ∧ ∃z, z*z = 1+x`).  On `ℝ` the formula is the
  real-analysis fact

      `logDefSet (1+x) y → |2x| ≤ 1 → rexpFromExp y = 1+x`,

  which is `1/2 ≤ 1+x ≤ 3/2`, hence `|log (1+x)| ≤ 1` and `rexp (log (1+x)) = exp (log (1+x)) = 1+x`.
-/
import Mathlib
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.LogFunMap
import Submission.Work.WilC5.LogFunReal
import Submission.Work.WilC5.real_logDefSet_one_add_rexp

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The `LEc`-formulas

The transfer lemma `Work.WilC5.transfer` applies to formulas with `n` *bound* variables and no
free variables, so the parameter `δ` and the value `y` are both bound variables here: `&0 = δ` and
`&1 = y`. -/

section Formulas

/-- The term `1 + &0`, i.e. `1 + δ` where `δ` is the first bound variable. -/
def oneAddV : LEc.Term (Empty ⊕ Fin 2) := eAdd eOne (v2 0)

/-- The second bound variable `&1`, i.e. the value `y`. -/
def valV : LEc.Term (Empty ⊕ Fin 2) := v2 1

/-- The formula `logDefSet (1 + &0) &1`, i.e. "`&1` is the definable logarithm of `1 + &0`". -/
def logPairForm : LEc.BoundedFormula Empty 2 :=
  ((leForm eZero oneAddV ⊓ (leForm oneAddV eZero).not) ⊓ Term.bdEqual (eExp valV) oneAddV) ⊔
    ((leForm eZero oneAddV ⊓ (leForm oneAddV eZero).not).not ⊓
      Term.bdEqual (eExp valV) eOne)

/-- The formula `rexpFromExp &1 = 1 + &0`, written out with the `if` split. -/
def rexpEqForm : LEc.BoundedFormula Empty 2 :=
  (absLeOneForm valV ⊓ Term.bdEqual (eExp valV) oneAddV) ⊔
    ((absLeOneForm valV).not ⊓ Term.bdEqual eZero oneAddV)

/-- The hypothesis `|2δ| ≤ 1`, i.e. `absLeOne ((1+1) * &0)`. -/
def absLeTwoForm : LEc.BoundedFormula Empty 2 :=
  absLeOneForm (eMul (eAdd eOne eOne) (v2 0))

/-- **The master formula**: `logDefSet (1+δ) y → |2δ| ≤ 1 → rexpFromExp y = 1+δ`. -/
def mainForm : LEc.BoundedFormula Empty 2 :=
  logPairForm.imp (absLeTwoForm.imp rexpEqForm)

end Formulas

/-! ## 2. Realization of the formulas -/

section Realize

variable {M : Type} [LEc.Structure M]

theorem logPairForm_realize (xs : Fin 2 → M) :
    (logPairForm).Realize (emptyVar : Empty → M) xs ↔
      logDefSet (addE oneE (xs 0)) (xs 1) := by
  simp only [logPairForm, logDefSet, oneAddV, valV, v2, Term.realize_var, Sum.elim_inr,
    BoundedFormula.realize_sup, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, leForm_realize, realize_eExp, realize_eAdd, realize_eOne,
    realize_eZero, leE]

theorem rexpEqForm_realize (xs : Fin 2 → M) :
    (rexpEqForm).Realize (emptyVar : Empty → M) xs ↔
      rexpFromExp (xs 1) = addE oneE (xs 0) := by
  simp only [rexpEqForm, oneAddV, valV, v2, Term.realize_var, Sum.elim_inr,
    BoundedFormula.realize_sup, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, absLeOneForm_realize, realize_eExp, realize_eAdd,
    realize_eOne, realize_eZero]
  by_cases h : absLeOne (xs 1)
  · rw [rexpFromExp_of_absLeOne h]
    constructor
    · rintro (⟨_, he⟩ | ⟨h', _⟩)
      · exact he
      · exact absurd h h'
    · intro he
      exact Or.inl ⟨h, he⟩
  · rw [rexpFromExp_of_not_absLeOne h]
    constructor
    · rintro (⟨h', _⟩ | ⟨_, he⟩)
      · exact absurd h' h
      · exact he
    · intro he
      exact Or.inr ⟨h, he⟩

theorem absLeTwoForm_realize (xs : Fin 2 → M) :
    (absLeTwoForm).Realize (emptyVar : Empty → M) xs ↔
      absLeOne (mulE (addE oneE oneE) (xs 0)) := by
  simp only [absLeTwoForm, v2, Term.realize_var, Sum.elim_inr, absLeOneForm_realize,
    realize_eMul, realize_eAdd, realize_eOne]

theorem mainForm_realize (xs : Fin 2 → M) :
    (mainForm).Realize (emptyVar : Empty → M) xs ↔
      (logDefSet (addE oneE (xs 0)) (xs 1) →
        absLeOne (mulE (addE oneE oneE) (xs 0)) →
        rexpFromExp (xs 1) = addE oneE (xs 0)) := by
  simp only [mainForm, BoundedFormula.realize_imp, logPairForm_realize, absLeTwoForm_realize,
    rexpEqForm_realize]

end Realize

/-! ## 3. The formula holds in `ℝ` -/

section Real

/-- The real-analysis content (`Work.WilC5.real_logDefSet_one_add_rexp`, proved in
`real_logDefSet_one_add_rexp.lean`): on `ℝ` the definable logarithm of `1+x` lies in `[-1,1]`
whenever `|2x| ≤ 1`, so that `rexpFromExp` (which is `rexp`, `exp` on `[-1,1]` and `0` elsewhere)
inverts it. -/
theorem mainForm_real (xs : Fin 2 → ℝ) : (mainForm).Realize (emptyVar : Empty → ℝ) xs := by
  rw [mainForm_realize]
  exact fun hy hx => real_logDefSet_one_add_rexp hy hx

end Real

/-! ## 4. The theorem -/

theorem logFun_one_add_rexp {M : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LEc M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) {δ : M}
    (hδ : Work.WilC5.absLeOne
      (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) δ)) :
    Work.WilC5.rexpFromExp (Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ)) =
      Work.WilC5.addE Work.WilC5.oneE δ := by
  have hmain := transfer hM mainForm mainForm_real ![δ, logFun (addE oneE δ)]
  rw [mainForm_realize] at hmain
  have hspec : logDefSet (addE oneE δ) (logFun (addE oneE δ)) := logFun_spec_of_model hM _
  exact hmain hspec hδ

end Work.WilC5
