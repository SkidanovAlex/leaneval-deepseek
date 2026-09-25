import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.Maximal.discAvgZC_multiplier_z

/-!
# The multiplier is additive in its symbol

The model realisation of KMSZ §6.3 compares `A_N ∘ Π` with the major-arc model: both are multipliers
on `ℓ²(ℤ) ≅ L²(𝕋)`, `opMul Φ` and `opMul Ψ`, and their difference is the multiplier with the
*difference* of the symbols, `opMul (Φ - Ψ)`.  This module records that identity (and hence the
error operator is a single multiplier — the object whose `ℓ²`-norm is controlled by Plancherel,
`Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le`).
-/

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The multiplier is additive in its symbol**: `opMul Φ f − opMul Ψ f = opMul (Φ − Ψ) f`. -/
theorem opMul_sub (Φ Ψ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ)
    (hf : Memℓp f 2) :
    opMul Φ f hf - opMul Ψ f hf = opMul (Φ - Ψ) f hf := by
  have h : Φ • ftLp f hf - Ψ • ftLp f hf = (Φ - Ψ) • ftLp f hf := by
    rw [sub_eq_add_neg, sub_eq_add_neg, Lp.smul_add Φ (-Ψ) (ftLp f hf),
      Lp.neg_smul Ψ (ftLp f hf)]
  have hkey : ((fourierBasis (T := 1)).repr (Φ • ftLp f hf) :
        lp (fun _ : ℤ => ℂ) 2) - (fourierBasis (T := 1)).repr (Ψ • ftLp f hf)
      = (fourierBasis (T := 1)).repr ((Φ - Ψ) • ftLp f hf) := by
    rw [← map_sub, h]
  funext n
  simp only [opMul, opMulLp, Pi.sub_apply]
  exact congrFun (congrArg Subtype.val hkey) n

end

end Work.BourgainPlan.IonescuWainger
