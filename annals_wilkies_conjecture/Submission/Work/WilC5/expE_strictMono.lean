/-
  WilC5 — strict monotonicity of the exponential in models of `TE`.

  `TE = Th(ℝ_exp)` is the complete theory of the standard exponential field, so every
  `LEc`-sentence true in `ℝ` holds in every model of `TE` (`Work.WilC5.transfer`,
  `ReductEmb.lean`).  The strict monotonicity of the exponential is such a sentence:

      `∀ x y, (leE x y ∧ ¬ leE y x) → (leE (exp x) (exp y) ∧ ¬ leE (exp y) (exp x))`,

  where `leE x y := ∃ z, z * z = y - x` is the definable order (`Bridge.lean`).  On `ℝ` this is
  the usual strict monotonicity of `Real.exp` (`Real.exp_lt_exp`), and the transfer lemma then
  gives the statement in an arbitrary model of `TE`.
-/
import Mathlib
import Submission.Work.WilC5.LogFunMap
import Submission.Work.WilC5.LogFunReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The sentence "`exp` is strictly increasing" -/

/-- The `LEc`-sentence `∀ x y, x < y → exp x < exp y`, where `x < y` is the definable strict
order `leE x y ∧ ¬ leE y x`. -/
def expStrictMonoForm : LEc.BoundedFormula Empty 2 :=
  (leForm (v2 0) (v2 1) ⊓ (leForm (v2 1) (v2 0)).not).imp
    (leForm (eExp (v2 0)) (eExp (v2 1)) ⊓ (leForm (eExp (v2 1)) (eExp (v2 0))).not)

theorem expStrictMonoForm_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    expStrictMonoForm.Realize (emptyVar : Empty → M) xs ↔
      (leE (xs 0) (xs 1) ∧ ¬ leE (xs 1) (xs 0) →
        leE (expE (xs 0)) (expE (xs 1)) ∧ ¬ leE (expE (xs 1)) (expE (xs 0))) := by
  rw [expStrictMonoForm, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    leForm_realize, leForm_realize, leForm_realize, leForm_realize]
  simp only [v2, Term.realize_var, Sum.elim_inr, realize_eExp, leE]

/-! ## 2. The sentence holds in `ℝ` -/

theorem expStrictMonoForm_real :
    ∀ xs : Fin 2 → ℝ, expStrictMonoForm.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [expStrictMonoForm_realize]
  rintro ⟨h1, h2⟩
  rw [leE_real] at h1 h2
  rw [leE_real, leE_real, expE_real, expE_real]
  exact ⟨Real.exp_le_exp.mpr h1, not_le.mpr (Real.exp_lt_exp.mpr (not_le.mp h2))⟩

/-! ## 3. Strict monotonicity in every model of `TE` -/

theorem expE_strictMono {M : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LEc M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) {x y : M}
    (hxy : Work.WilC5.leE x y ∧ ¬ Work.WilC5.leE y x) :
    Work.WilC5.leE (Work.WilC5.expE x) (Work.WilC5.expE y) ∧
      ¬ Work.WilC5.leE (Work.WilC5.expE y) (Work.WilC5.expE x) := by
  have h := transfer hM expStrictMonoForm expStrictMonoForm_real ![x, y]
  rw [expStrictMonoForm_realize] at h
  have hmain := h (by simpa using hxy)
  simpa using hmain

end Work.WilC5
