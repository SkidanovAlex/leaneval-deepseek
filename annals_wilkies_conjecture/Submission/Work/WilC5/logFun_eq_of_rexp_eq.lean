/-
  WilC5 — `rexp` is *injective* where it matters: `u` is the definable logarithm of `1 + δ`
  as soon as `rexpFromExp u = 1 + δ` and `|2δ| ≤ 1`.

  This is the converse of `Work.WilC5.logFun_one_add_rexp`.  Given `h : rexpFromExp u = 1 + δ`
  and `hδ : |2δ| ≤ 1`, the real argument (`Work.WilC5.real_rexp_eq_logDefSet`) is

  * `|2δ| ≤ 1` gives `1 + δ ≥ 1/2 > 0`;
  * hence `rexpFromExp u = 1 + δ ≠ 0`, so `u` cannot be outside `[-1,1]`;
  * therefore `rexpFromExp u = exp u = 1 + δ` and `logDefSet (1+δ) u` holds.

  The whole real statement is the single `LEc`-formula

      `rexpFromExp &1 = 1+&0  →  |2·&0| ≤ 1  →  logDefSet (1+&0) &1`,

  which is transferred to an arbitrary model of `TE` with `Work.WilC5.transfer`.  In the model,
  `logFun (1+δ)` is *the* element with `logDefSet (1+δ) ·` (`logFun_spec_of_model`), so
  uniqueness (`logDefSet_unique_of_model`) identifies it with `u`.
-/
import Mathlib
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.real_rexp_eq_logDefSet

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The `LEc`-formula and its realization

The pieces `rexpEqForm` (`rexpFromExp &1 = 1+&0`), `absLeTwoForm` (`|2·&0| ≤ 1`) and
`logPairForm` (`logDefSet (1+&0) &1`) are the ones built in `logFun_one_add_rexp.lean`. -/

/-- **The master formula** `rexpFromExp &1 = 1+&0 → |2·&0| ≤ 1 → logDefSet (1+&0) &1`. -/
def rexpInvForm : LEc.BoundedFormula Empty 2 :=
  rexpEqForm.imp (absLeTwoForm.imp logPairForm)

theorem rexpInvForm_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    rexpInvForm.Realize (emptyVar : Empty → M) xs ↔
      (rexpFromExp (xs 1) = addE oneE (xs 0) →
        absLeOne (mulE (addE oneE oneE) (xs 0)) →
        logDefSet (addE oneE (xs 0)) (xs 1)) := by
  simp only [rexpInvForm, BoundedFormula.realize_imp, rexpEqForm_realize, absLeTwoForm_realize,
    logPairForm_realize]

/-! ## 2. The formula holds in `ℝ` -/

theorem rexpInvForm_real (xs : Fin 2 → ℝ) :
    rexpInvForm.Realize (emptyVar : Empty → ℝ) xs := by
  rw [rexpInvForm_realize]
  exact fun hy hx => real_rexp_eq_logDefSet hy hx

/-! ## 3. The theorem -/

theorem logFun_eq_of_rexp_eq {M : Type} [WilkiesDesign.CG.LEc.Structure M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) {δ u : M}
    (hδ : Work.WilC5.absLeOne (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) δ))
    (h : Work.WilC5.rexpFromExp u = Work.WilC5.addE Work.WilC5.oneE δ) :
    u = Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ) := by
  -- Transfer the ℝ-fact `rexpFromExp y = 1+x → |2x| ≤ 1 → logDefSet (1+x) y` to `M`.
  have hmain := transfer hM rexpInvForm rexpInvForm_real ![δ, u]
  rw [rexpInvForm_realize] at hmain
  -- `u` is a logarithm of `1+δ`, and so is `logFun (1+δ)`; uniqueness identifies them.
  exact logDefSet_unique_of_model hM (hmain h hδ)
    (logFun_spec_of_model hM (addE oneE δ))

end Work.WilC5
