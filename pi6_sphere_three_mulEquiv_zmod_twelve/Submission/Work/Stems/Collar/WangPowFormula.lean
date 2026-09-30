import Mathlib
import Submission.Work.Stems.Collar.WangThetaCupMixed
import Submission.Work.StemsB.Rat.WangThetaCupLow
import Submission.Work.Stems.Collar.wangTheta_cup_three
import Submission.Work.Stems.Collar.wangTheta_pow

/-!
# The power formula for the Wang transgression, as a single `Prop`

*(Area STEMS.)*  `Work.Stems.Collar.wangTheta_pow` proves, for each Hurewicz-fibration-like datum
over the sphere model and each class `x` of the fibre, the multiplicativity of the Wang
transgression at every power:

  `θ(x^{k+2}) = (k+2) · (x^{k+1} ⌣ θ^{low}(x))`   (`b` odd).

The `C2` odd step needs this formula *uniformly* in the datum, so it is bundled here as a single
`Prop`, `Work.Stems.Collar.WangPowFormula`.  The bridge from the theorem is
`Work.Stems.Collar.wangPowFormula_of_wangTheta_pow`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems.Collar

open Work.StemsB.Rat
open Work.StemsB

noncomputable section

/-- **The power formula of the Wang transgression, uniformly in the fibration and the class.** -/
def WangPowFormula : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (hbodd : Odd b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ)
    (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty})),
    transT ↥(p ⁻¹' {OnePoint.infty})
        (by
          have hA : 0 < (b - 1) * (k + 1) := Nat.mul_pos (by omega) (by omega)
          rw [show (b - 1) * (k + 2) = (b - 1) * (k + 1) + (b - 1) from
            Nat.mul_succ (b - 1) (k + 1)]
          omega : ((b - 1) * (k + 2) - b) + 1 = (b - 1) * (k + 1))
        (wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)
          (transT ↥(p ⁻¹' {OnePoint.infty})
            (by
              refine (Nat.sub_add_cancel ?_).symm
              have h1 : (b - 1) * 2 ≤ (b - 1) * (k + 2) :=
                Nat.mul_le_mul_left (b - 1) (by omega : 2 ≤ k + 2)
              omega : (b - 1) * (k + 2) = ((b - 1) * (k + 2) - b) + b)
            (wangPow b hb E p d_G hT_G hT_O x (k + 1))))
      = (k + 2 : ℚ) •
          cupT ↥(p ⁻¹' {OnePoint.infty}) ((b - 1) * (k + 1)) 0
            (wangPow b hb E p d_G hT_G hT_O x k)
            (wangThetaLow b hb E p d_G hT_G hT_O x)

/-- **The power formula, from `Work.Stems.Collar.wangTheta_pow`.** -/
theorem wangPowFormula_of_wangTheta_pow : WangPowFormula :=
  fun b hb hbodd E _ p d_G hT_G hT_O k x => wangTheta_pow b hb hbodd E p d_G hT_G hT_O k x

end

end Work.Stems.Collar
