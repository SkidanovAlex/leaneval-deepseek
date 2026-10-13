/-
  WilC5 — `exp` and the definable logarithm are inverse at the level of `<`.

  For a strictly positive element `w` of a model `M ⊨ TE`, the strict order is preserved by the
  exponential:

      `w < exp x  ↔  log w < x`,

  where `<` is the definable strict order `a < b := leE a b ∧ ¬ leE b a` (`leE x y := ∃z, z*z = y-x`)
  and `logFun` is the definable logarithm of `ExpLog.lean`, whose graph in a model of `TE` is the
  *unique* solution of `logDefSet` (`LogFunMap.lean`).

  The proof has two ingredients, both transferred from `ℝ` by elementarity (since
  `TE = Th(ℝ_exp)` is complete):

  * `exp` is *strictly increasing*: the `LEc`-sentence `∀ a b, exp a < exp b ↔ a < b` holds in `ℝ`
    (`Real.exp_le_exp`), hence in every model of `TE` (`expLtIffForm`, `expLtIffForm_real`,
    `expLtIffForm_realize`, `expE_lt_expE_iff_of_model`);
  * for `w` with `0 < w` the chosen logarithm satisfies `exp (logFun w) = w`
    (`expE_logFun_of_pos_of_model`), which turns the goal into the monotonicity statement above.

  Everything is proved from the two imported modules; this file adds no new hypotheses.
-/
import Mathlib
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.LogFunMap

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The `LEc`-formula `a < b` and the strict monotonicity sentence of `exp` -/

/-- The strict-order `LEc`-formula `t₁ < t₂`, i.e. `t₁ ≤ t₂ ∧ ¬ t₂ ≤ t₁`. -/
def expLtForm {β : Type} {l : ℕ} (t₁ t₂ : LEc.Term (β ⊕ Fin l)) : LEc.BoundedFormula β l :=
  leForm t₁ t₂ ⊓ (leForm t₂ t₁).not

theorem expLtForm_realize {M : Type} [LEc.Structure M] {β : Type} {l : ℕ}
    (t₁ t₂ : LEc.Term (β ⊕ Fin l)) (v : β → M) (xs : Fin l → M) :
    (expLtForm t₁ t₂).Realize v xs ↔
      (leE (Term.realize (Sum.elim v xs) t₁) (Term.realize (Sum.elim v xs) t₂) ∧
       ¬ leE (Term.realize (Sum.elim v xs) t₂) (Term.realize (Sum.elim v xs) t₁)) := by
  rw [expLtForm, BoundedFormula.realize_inf, BoundedFormula.realize_not]
  simp only [leForm_realize, leE]

/-- **Strict monotonicity of `exp`**, as an `LEc`-sentence with two bound variables:
`exp a < exp b ↔ a < b`. -/
def expLtIffForm : LEc.BoundedFormula Empty 2 :=
  ((expLtForm (eExp (v2 0)) (eExp (v2 1))).imp (expLtForm (v2 0) (v2 1))) ⊓
  ((expLtForm (v2 0) (v2 1)).imp (expLtForm (eExp (v2 0)) (eExp (v2 1))))

theorem expLtIffForm_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    expLtIffForm.Realize (emptyVar : Empty → M) xs ↔
      ((leE (expE (xs 0)) (expE (xs 1)) ∧ ¬ leE (expE (xs 1)) (expE (xs 0))) ↔
        (leE (xs 0) (xs 1) ∧ ¬ leE (xs 1) (xs 0))) := by
  simp only [expLtIffForm, BoundedFormula.realize_inf, BoundedFormula.realize_imp,
    expLtForm_realize, v2, Term.realize_var, Sum.elim_inr, realize_eExp]
  constructor <;> intro h <;> exact ⟨h.1, h.2⟩

theorem expLtIffForm_real : ∀ xs : Fin 2 → ℝ, expLtIffForm.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [expLtIffForm_realize]
  simp only [leE, subE_real, expE_real, isSquare_real]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : xs 0 ≤ xs 1 := Real.exp_le_exp.mp (by linarith)
    refine ⟨by linarith, ?_⟩
    intro hb
    have hb' : xs 1 ≤ xs 0 := by linarith
    exact h2 (by have := Real.exp_le_exp.mpr hb'; linarith)
  · rintro ⟨h1, h2⟩
    have h1' : Real.exp (xs 0) ≤ Real.exp (xs 1) := Real.exp_le_exp.mpr (by linarith)
    refine ⟨by linarith, ?_⟩
    intro hb
    have hb' : Real.exp (xs 1) ≤ Real.exp (xs 0) := by linarith
    exact h2 (by have := Real.exp_le_exp.mp hb'; linarith)

/-- **`exp` is strictly increasing in every model of `TE`**: `exp a < exp b ↔ a < b`. -/
theorem expE_lt_expE_iff_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (a b : M) :
    (leE (expE a) (expE b) ∧ ¬ leE (expE b) (expE a)) ↔ (leE a b ∧ ¬ leE b a) := by
  have h := transfer hM expLtIffForm (fun xs => expLtIffForm_real xs) ![a, b]
  rw [expLtIffForm_realize] at h
  simpa using h

/-! ## 2. The logarithm of a positive element -/

/-- For `w` with `0 < w` the chosen logarithm satisfies `exp (logFun w) = w`. -/
theorem expE_logFun_of_pos_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) {w : M}
    (hw : leE zeroE w ∧ ¬ leE w zeroE) : expE (logFun w) = w := by
  have hspec := logFun_spec_of_model hM w
  rw [logDefSet] at hspec
  rcases hspec with ⟨-, he⟩ | ⟨hne, -⟩
  · exact he
  · exact absurd hw hne

/-! ## 3. The target -/

theorem expE_lt_iff_logFun_lt {M : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LEc M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) {w x : M}
    (hw : Work.WilC5.leE Work.WilC5.zeroE w ∧ ¬ Work.WilC5.leE w Work.WilC5.zeroE) :
    ((Work.WilC5.leE w (Work.WilC5.expE x) ∧ ¬ Work.WilC5.leE (Work.WilC5.expE x) w) ↔
      (Work.WilC5.leE (Work.WilC5.logFun w) x ∧ ¬ Work.WilC5.leE x (Work.WilC5.logFun w))) := by
  have hexp : expE (logFun w) = w := expE_logFun_of_pos_of_model hM hw
  have h := expE_lt_expE_iff_of_model hM (logFun w) x
  rw [hexp] at h
  exact h

end Work.WilC5
