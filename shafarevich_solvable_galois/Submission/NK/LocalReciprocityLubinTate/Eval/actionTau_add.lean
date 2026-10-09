import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Eval

open scoped ValuativeRel
open Polynomial MvPowerSeries

set_option linter.style.haveILetI false

universe u

/-- **Milne's evaluation at `τ`, unwound.**  The ring homomorphism
`evalTau : 𝒪[F]⟦X⟧ → T_n` of `Eval/TorsionAction.lean` is the evaluation `MvPowerSeries.eval₂`
at the point `τ ∈ T_n` (the class of `T` in `𝒪[F][T]/(f^{(n)}(T))`).

This is the form in which `MvPowerSeries.eval₂_subst` (the compatibility of evaluation with
substitution) can be applied to it. -/
theorem evalTau_eq_eval₂_act {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (φ : MvPowerSeries (Fin 1) (O F)) :
    evalTau π hπ q n hq φ
      = MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
        (fun _ : Fin 1 => LTtorsionRing.tau π q n) φ := by
  letI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  letI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  rw [evalTau, MvPowerSeries.coe_eval₂Hom]

/-- Every `[a]` has zero constant term: this is the Lubin–Tate congruence
`[a](X) ≡ aX (mod deg 2)` read off in degree `0`. -/
theorem constantCoeff_action {F : Type u} [Field F] [ValuativeRel F] (π : O F) (q : ℕ)
    (M : LubinTateModule (O F) π q) (a : O F) :
    MvPowerSeries.constantCoeff (M.action a) = 0 := by
  have h := M.action_linear a 0 (by simp [Finsupp.degree])
  simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_X] at h
  simpa using h

theorem actionTau_add {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π q)
    (a b : ↥(ValuativeRel.valuation F).integer) :
    NK.LocalReciprocityLubinTate.Eval.actionTau π hπ q n hq M (a + b)
      = MvPowerSeries.eval₂ (algebraMap (↥(ValuativeRel.valuation F).integer)
          (NK.LocalReciprocityLubinTate.Eval.LTtorsionRing F π q n))
        ![NK.LocalReciprocityLubinTate.Eval.actionTau π hπ q n hq M a,
          NK.LocalReciprocityLubinTate.Eval.actionTau π hπ q n hq M b]
        (M.toLaw.law : MvPowerSeries (Fin 2) (↥(ValuativeRel.valuation F).integer)) := by
  letI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  letI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  -- `[a]` and `[b]` have zero constant term, so the family `![[a],[b]]` can be substituted.
  have hsubst : MvPowerSeries.HasSubst
      (![M.action a, M.action b] : Fin 2 → MvPowerSeries (Fin 1) (O F)) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => ?_)
    fin_cases s <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, constantCoeff_action]
  -- the defining identity `[a+b] = F([a],[b])` of the module structure,
  rw [actionTau, M.action_add a b, evalTau_eq_eval₂_act]
  -- pulled back along `evalTau`, which commutes with substitution.
  rw [MvPowerSeries.eval₂_subst hsubst (hasEval_ltTorsionRing π q n hq)
    (M.toLaw.law : MvPowerSeries (Fin 2) (O F))]
  congr 1
  funext s
  fin_cases s <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, actionTau, evalTau_eq_eval₂_act]

end NK.LocalReciprocityLubinTate.Eval
