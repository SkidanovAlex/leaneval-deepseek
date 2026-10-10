import Submission.Work.MotT.Defs
import Submission.Work.MotT.twist_iso_pointK
import Submission.Work.MotC2.All

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Discharging node C2 with `Work.MotC2.aut_functionField`

The `MotC2` chapter is complete (`Submission/Work/MotC2/All.lean`, axiom-clean): for an elliptic
Weierstrass curve `E` over a field `L` with `j ≠ 0, 1728`,

`Work.MotC2.aut_functionField L E hj0 hj Θ : ∃ (Q : E.toAffine.Point) (ε : Fin 2),
   Θ = transAlgEquiv E Q * (negAlgEquiv E) ^ (ε : ℕ)`

— exactly the corrected form of node C2 used in `Work.MotT.AutRigid` (see `C2_DEFECT.md`).

This file turns that theorem into the `AutRigid`-shaped conclusions:

* `Work.MotT.autRigidBaseChange_of_good` — `AutRigid` at the base-changed Klein model of a
  `D.Good`;
* `Work.MotT.autRigidInput` — `AutRigidInput K` for every field `K`;
* `Work.MotT.twist_iso_pointK_of_good` — LAM (node T4) with the C2 hypothesis discharged.
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- Node C2 at the base-changed Klein model of a `Good` datum, discharged by
`Work.MotC2.aut_functionField`. -/
theorem autRigidBaseChange_of_good {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) :
    autRigidBaseChange D hD := by
  intro Θ
  haveI := hD.elliptic
  haveI : DecidableEq (KbK K) := Classical.decEq _
  have hj0 : (D.E.map (algebraMap K (KbK K))).j ≠ 0 := by
    rw [WeierstrassCurve.map_j]
    exact fun h => hD.j_ne_zero ((algebraMap K (KbK K)).injective (by simpa using h))
  have hj : (D.E.map (algebraMap K (KbK K))).j ≠ 1728 := by
    rw [WeierstrassCurve.map_j]
    exact fun h => hD.j_ne ((algebraMap K (KbK K)).injective (by rw [h, map_ofNat]))
  exact Work.MotC2.aut_functionField (KbK K) (D.E.map (algebraMap K (KbK K))) hj0 hj Θ

/-- **`AutRigidInput` is a theorem**: node C2 for every Klein model over `K`. -/
theorem autRigidInput (K : Type) [Field K] : AutRigidInput K :=
  fun D hD => autRigidBaseChange_of_good D hD

/-- **LAM (node T4) with C2 discharged.** -/
theorem twist_iso_pointK_of_good {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (hk : ringChar K ≠ 5) {h₁ h₂ : K} (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0)
    (θ : twistFieldTK D h₁ ≃ₐ[K] twistFieldTK D h₂) :
    ∃ ε : ℤˣ, ∃ y : Fin 5 → K, y ≠ 0 ∧
      ∀ k, Work.MotV.kleinTw D.a D.b (h₁ * h₂ ^ (ε : ℤ)) y k = 0 :=
  twist_iso_pointK D hD hk (autRigidBaseChange_of_good D hD) h₁0 h₂0 θ

end

end Work.MotT
