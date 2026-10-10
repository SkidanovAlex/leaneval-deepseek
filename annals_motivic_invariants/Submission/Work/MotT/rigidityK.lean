import Submission.Work.MotT.Defs
import Submission.Work.MotT.twist_iso_pointK
import Submission.Work.MotT.C2Discharge
import Submission.Work.MotT.not_fifth_pow_of_vOne
import Submission.Work.MotV.tp

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Node T6 (`rigidityK`): rigidity of the T-twist field over an arbitrary base

An isomorphism `K(C_π) ≅ K(C_{π²})` of T-twist fields (with `π` a uniformizer, `v π = vOne`)
would produce, by LAM (node T4, `Work.MotT.twist_iso_pointK`), a nonzero `K`-point of the twisted
Klein curve `C_{π · π^{±2}}`, i.e. of `C_{π³}` or of `C_{π⁻¹}`; the twisted-point valuation lemma TP
(`Work.MotV.tp`) then makes `v π` (resp. `v π⁻¹`) a fifth power, contradicting T6a
(`Work.MotT.not_fifth_pow_of_vOne`).
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- **T6 (RIG over `K`).**  With unit Klein parameters and `v π = vOne`, the twist fields
`K(C_π)` and `K(C_{π²})` are not `K`-isomorphic. -/
theorem rigidityK {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (hk : ringChar K ≠ 5) (v : Valuation K ℤᵐ⁰) (ha : v D.a = 1)
    (hb : v D.b = 1) {π : K} (hπ : v π = vOne) :
    IsEmpty (twistFieldTK D π ≃ₐ[K] twistFieldTK D (π ^ 2)) := by
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  refine ⟨fun θ => ?_⟩
  obtain ⟨ε, y, hy, heq⟩ := twist_iso_pointK_of_good D hD hk hπ0 (pow_ne_zero 2 hπ0) θ
  have hh : π * (π ^ 2) ^ (ε : ℤ) ≠ 0 :=
    mul_ne_zero hπ0 (zpow_ne_zero _ (pow_ne_zero 2 hπ0))
  obtain ⟨u, hu⟩ := Work.MotV.tp v ha hb hh hy heq
  exact not_fifth_pow_of_vOne v hπ ε u hu

end

end Work.MotT
