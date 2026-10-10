import Submission.Work.MotT.Defs
import Submission.Work.MotT.constantsOnly_twistK
import Submission.Work.MotT.rigidityK
import Submission.Work.MotT.certN3_of_linkCert
import Submission.Work.MotT.exists_kleinData_val
import Submission.Work.MotV.not_gen_of_certN

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Node T10 (`not_gen_three_of_val`): the T-route at `n = 3` for a valued field

The assembly of

* `Work.MotT.exists_kleinData_val` (node T7: Klein data with unit parameters at `v`),
* `Work.MotT.certN3_of_linkCert` (node T9),
* `Work.MotT.constantsOnly_twistK` (node T5),
* `Work.MotT.rigidityK` (node T6, from LAM = node T4, node C2 and the valuation lemma TP), and
* the link certificate input `Work.MotT.LinkCertTInput` (node T8, the K-route census),

concluding `¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 3` for any infinite field `𝕜` of
characteristic `≠ 5` carrying a valuation with `v π = vOne`.

`Work.MotT.not_gen_three_of_val_of_kleinData` is the same statement with the Klein model supplied
explicitly (it is the variant to use when the caller has its own model, or to avoid the parametric
`KDATA` import).
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- **T10, explicit Klein model.**  The T-route conclusion for an infinite field of
characteristic `≠ 5` with a valuation `v` (`v π = vOne`) and a Klein model whose parameters are
units at `v`. -/
theorem not_gen_three_of_val_of_kleinData (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (hk : ringChar 𝕜 ≠ 5) (hlink : LinkCertTInput 𝕜)
    (v : Valuation 𝕜 ℤᵐ⁰) {π : 𝕜} (hπ : v π = vOne) (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (ha : v D.a = 1) (hb : v D.b = 1) :
    ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 3 := by
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  obtain ⟨L⟩ := hlink D hD π hπ0
  obtain ⟨c⟩ := certN3_of_linkCert 𝕜 L (constantsOnly_twistK D hD hk π hπ0)
    (rigidityK D hD hk v ha hb hπ)
  exact Work.MotV.not_gen_of_certN c

/-- Node T7 in the packaged form `Work.MotT.KleinDataValued`. -/
theorem kleinDataValued_of_charNeFive {K : Type} [Field K] (hk : ringChar K ≠ 5) :
    KleinDataValued K := by
  intro v π hπ
  exact exists_kleinData_val hk v hπ

/-- **T10.**  The T-route conclusion for an infinite field of characteristic `≠ 5` with a valuation
with `v π = vOne`: nodes T7, C2, T5, T6 and T9 are discharged; only the K-route census
`Work.MotT.LinkCertTInput` (node T8) remains as an input. -/
theorem not_gen_three_of_val (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (hk : ringChar 𝕜 ≠ 5)
    (hlink : LinkCertTInput 𝕜) (v : Valuation 𝕜 ℤᵐ⁰) {π : 𝕜} (hπ : v π = vOne) :
    ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 3 := by
  obtain ⟨D, hD, ha, hb⟩ := exists_kleinData_val hk v hπ
  exact not_gen_three_of_val_of_kleinData 𝕜 hk hlink v hπ D hD ha hb

end

end Work.MotT
