import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


universe u
namespace NK.LocalReciprocityLubinTate.Eval

/-- `evalTau` is Milne's power-series evaluation `MvPowerSeries.eval₂` at the family
`![τ]` of classes of `T`; the two only differ by the materialisation of `eval₂Hom`
as an ordinary function. -/
theorem evalTau_eq_eval₂ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (f : MvPowerSeries (Fin 1) (↥(ValuativeRel.valuation F).integer)) :
    evalTau π hπ q n hq f =
      MvPowerSeries.eval₂ (algebraMap (↥(ValuativeRel.valuation F).integer)
          (LTtorsionRing F π q n))
        (fun _ : Fin 1 => LTtorsionRing.tau π q n) f := by
  let : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  let : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  rw [evalTau, MvPowerSeries.coe_eval₂Hom]

theorem evalTau_subst {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (φ ψ : MvPowerSeries (Fin 1) (↥(ValuativeRel.valuation F).integer))
    (hψ : MvPowerSeries.HasSubst ![ψ]) :
    NK.LocalReciprocityLubinTate.Eval.evalTau π hπ q n hq (MvPowerSeries.subst ![ψ] φ)
      = MvPowerSeries.eval₂ (algebraMap (↥(ValuativeRel.valuation F).integer)
          (NK.LocalReciprocityLubinTate.Eval.LTtorsionRing F π q n))
        ![NK.LocalReciprocityLubinTate.Eval.evalTau π hπ q n hq ψ] φ := by
  let : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  let : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  rw [evalTau_eq_eval₂]
  rw [MvPowerSeries.eval₂_subst hψ (hasEval_ltTorsionRing π q n hq) φ]
  congr 1
  funext s
  fin_cases s
  simp [evalTau_eq_eval₂]

end NK.LocalReciprocityLubinTate.Eval
