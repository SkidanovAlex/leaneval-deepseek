/-
  WilC5 — `(log x)^n < x` for `x` of infinite value in a model of `TE`.

  In a model `K` of `TE = Th(ℝ_exp)` (with the canonical `LEc`-data, i.e. the ring symbols of the
  language `LEc` agree with the field structure of `K`) an element `x` which is *infinite* — bigger
  than every natural number, `¬ IsFiniteVal x` — satisfies `(log x)^n < x` for every `n : ℕ`: the
  definable logarithm grows more slowly than any root of `x`.

  The proof is one transfer (`Work.WilC5.transfer`) of the `LEc`-sentence

      `x > N ∧ logDefSet x y  →  y ^ n < x`                              (`logPowLtForm N n`)

  from `ℝ` to `K`.  Its real content is the real-analysis fact

      `∃ N : ℕ, ∀ x : ℝ, N < x → (log x)^n < x`                          (`Work.WilC5.ExistsLogPowLtSelf`)

  (`(log·)^n = o(id)` at `+∞`), which is `Work.WilC5.LogPowLtFormReal` in the language of `LEc`.
  The threshold `N` is inserted into the sentence as the *numeral* term `1 + ⋯ + 1`
  (`numTerm`, `LogPwDefs.lean`), so that it is interpreted by `(N : K)`; this is what makes the
  transfer usable, because `x` is bigger than every numeral.  Finally
  `logDefSet x (logFun x)` holds in every model of `TE` (`logFun_spec_of_model`), which turns the
  transferred implication into the claim.

  Total work below: one transfer plus the bookkeeping identifying the realized terms with `(N : K)`
  and `(logFun x) ^ n`.
-/
import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.LogPwDefs
import Submission.Work.WilC5.LogPowLtFormReal
import Submission.Work.WilC5.ExistsLogPowLtSelf

set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem LogFunPowLtSelf
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {x : K} (hxpos : 0 < x) (hxinf : ¬ Work.WilC5.IsFiniteVal x) (n : ℕ) :
    (Work.WilC5.logFun x) ^ n < x := by
  -- The real-analysis threshold: `(log x)^n < x` for every real `x > N`.
  obtain ⟨N, hN⟩ := ExistsLogPowLtSelf n
  have hTE : K ⊨ TE := inferInstance
  -- Transfer the sentence `x > N ∧ logDefSet x y → y^n < x` to `K`.
  have hmain := transfer hTE (logPowLtForm N n) (LogPowLtFormReal N n hN)
  have hinst := hmain ![x, logFun x]
  rw [logPowLtForm_realize] at hinst
  -- `x` exceeds the numeral `N`, because `x` is of infinite value.
  have hlt : ¬ leE x (Term.realize (Sum.elim (emptyVar : Empty → K) ![x, logFun x])
      (numTerm (α := Empty ⊕ Fin 2) N)) := by
    rw [numTerm_realize_of_model hTE hadd hone, hleneg]
    intro hle
    exact hxinf ⟨N, by rw [abs_of_pos hxpos]; linarith⟩
  -- `logFun x` is a logarithm of `x` in every model of `TE`.
  have hres := hinst ⟨hlt, logFun_spec_of_model hTE x⟩
  -- Read off the conclusion: the realized power term is `(logFun x)^n`.
  rw [powTerm_realize_of_model hmul hone] at hres
  simp only [v2, Term.realize_var, Sum.elim_inr] at hres
  rw [hleneg] at hres
  exact not_le.mp hres

end Work.WilC5
