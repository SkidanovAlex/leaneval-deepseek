import Mathlib.RingTheory.AdjoinRoot
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Multiplicativity of Milne's evaluation of the Lubin–Tate series at `τ`

Milne, *Classical Field Theory*, §I.3: the `a`-multiplication series of the Lubin–Tate module
satisfy `[a·b] = [a] ∘ [b]`, hence, after evaluating at the torsion class `τ`, the point
`[a·b](τ)` is obtained from the point `[b](τ)` by substituting it into the power series `[a]`.

This is the multiplicativity axiom of the `𝒪[F]`-module structure on the `π^n`-torsion points,
transported from the series level (`LubinTateModule.action_mul`) by the compatibility of
Milne's evaluation with substitution (`MvPowerSeries.eval₂_subst`).
-/

open scoped ValuativeRel
open Polynomial MvPowerSeries

namespace NK.LocalReciprocityLubinTate.Eval

open LTtorsionRing

set_option linter.style.haveILetI false

universe u

/-- `[a · b](τ) = [a]([b](τ))`: the multiplicativity of the Lubin–Tate module structure, read at the
torsion class `τ` of `T` in `𝒪[F][T]/(f^{(n)}(T))`. -/
theorem actionTau_mul {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π q)
    (a b : ↥(ValuativeRel.valuation F).integer) :
    NK.LocalReciprocityLubinTate.Eval.actionTau π hπ q n hq M (a * b)
      = MvPowerSeries.eval₂ (algebraMap (↥(ValuativeRel.valuation F).integer)
          (NK.LocalReciprocityLubinTate.Eval.LTtorsionRing F π q n))
        ![NK.LocalReciprocityLubinTate.Eval.actionTau π hπ q n hq M b] (M.action a) := by
  letI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  letI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  -- `evalTau` is Milne's evaluation `MvPowerSeries.eval₂` at the class `τ` of `T`.
  have hE : ∀ f : MvPowerSeries (Fin 1) (O F),
      evalTau π hπ q n hq f = MvPowerSeries.eval₂ (algebraMap (O F) (LTtorsionRing F π q n))
        (fun _ : Fin 1 => LTtorsionRing.tau π q n) f := by
    intro f
    rw [evalTau, MvPowerSeries.coe_eval₂Hom]
  -- `[b](X) ≡ bX (mod deg 2)`, so `[b]` has zero constant term and can be substituted.
  have hc : MvPowerSeries.constantCoeff (M.action b) = 0 := by
    have h := M.action_linear b 0 (by simp [Finsupp.degree])
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_X] at h
    simpa using h
  have hsubst : MvPowerSeries.HasSubst (![M.action b] : Fin 1 → MvPowerSeries (Fin 1) (O F)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s; exact hc)
  -- the series identity `[a · b] = [a] ∘ [b]`, transported along the evaluation at `τ`.
  rw [actionTau, M.action_mul a b, hE (MvPowerSeries.subst ![M.action b] (M.action a)),
    MvPowerSeries.eval₂_subst hsubst (hasEval_ltTorsionRing π q n hq) (M.action a)]
  congr 1
  funext s
  fin_cases s
  simp [actionTau, hE]

end NK.LocalReciprocityLubinTate.Eval
