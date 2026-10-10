import Submission.Work.MotT.RouteVBridge
import Submission.Work.MotT.twistFieldTK_descent
import Submission.Work.MotT.twistFieldTK_regular
import Submission.Work.MotT.C2Discharge
import Submission.Work.MotT.kleinDataBaseChange_good

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Route V corollaries: the generic nodes at `K = RatFunc 𝕜`

These are the *consumption* corollaries promised to `Submission/Work/MotV`: the generic nodes
`Work.MotT.twistFieldTK_descent` (T2 / `C1T`), `Work.MotT.twistFieldTK_regular` (T3 / `REG`) and
`Work.MotT.twist_iso_pointK` (T4 / `LAM`) transported to route V's vocabulary
(`Work.MotV.twistFieldT`, `Work.MotV.Kb`, `Work.MotV.Om`) through the `rfl`-bridge
`Work.MotT.twistFieldT_eq_twistFieldTK` and node B1 (`Work.MotT.kleinDataBaseChange_good`).

The point of these statements is that they are at `{𝕜 : Type}` (universe `0`), where route V's
`Work.MotV.twist_regular` is *false* (documented and refuted in
`Submission/Work/MotV/twist_regular.lean`: `KleinData.Good`'s coordinate fields quantifier over
`L : Type`, so they are vacuous at a base field in a higher universe).
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- `RatFunc 𝕜` has the same characteristic as `𝕜`. -/
theorem ringChar_ratFunc_ne_five {𝕜 : Type} [Field 𝕜] (hk : ringChar 𝕜 ≠ 5) :
    ringChar (RatFunc 𝕜) ≠ 5 := by
  intro h5
  haveI : CharP (RatFunc 𝕜) 5 := ringChar.of_eq h5
  have hzero : (5 : RatFunc 𝕜) = 0 := CharP.cast_eq_zero (RatFunc 𝕜) 5
  have hk5 : (5 : 𝕜) = 0 :=
    (algebraMap 𝕜 (RatFunc 𝕜)).injective (by rw [map_ofNat, hzero, map_zero])
  haveI : CharP 𝕜 5 := (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 5)).mpr hk5
  exact hk (ringChar.eq (R := 𝕜) 5)

/-- **Route V's `C1T`**: `Work.MotV.twistFieldT D h` is a `RatFunc 𝕜`-form of `K̄(E)` — it is
linearly disjoint from `K̄` and generates `K̄(E)` together with it. -/
theorem twistFieldT_descent {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (hk : ringChar 𝕜 ≠ 5) (h : RatFunc 𝕜) (hh : h ≠ 0) :
    (Work.MotV.twistFieldT D h).LinearDisjoint (Work.MotV.Kb 𝕜) ∧
      Work.MotV.twistFieldT D h ⊔
        (IsScalarTower.toAlgHom (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D)).fieldRange = ⊤ :=
  twistFieldTK_descent (kleinDataBaseChange D (RatFunc 𝕜)) (kleinDataBaseChange_good D hD)
    (ringChar_ratFunc_ne_five hk) h hh

/-- **Route V's `REG`**: `RatFunc 𝕜` is algebraically closed in the twist field
`Work.MotV.twistFieldT D h`, at `{𝕜 : Type}`. -/
theorem twistFieldT_regular {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (hk : ringChar 𝕜 ≠ 5) (h : RatFunc 𝕜) (hh : h ≠ 0) (r : Work.MotV.twistFieldT D h)
    (hr : IsAlgebraic (RatFunc 𝕜) r) :
    ∃ c : RatFunc 𝕜, algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h) c = r :=
  twistFieldTK_regular (kleinDataBaseChange D (RatFunc 𝕜)) (kleinDataBaseChange_good D hD)
    (ringChar_ratFunc_ne_five hk) h hh r hr

/-- **Route V's `LAM`**: a `RatFunc 𝕜`-isomorphism of two twist fields forces a `RatFunc 𝕜`-point of
one of the twisted Klein curves.  The C2 input is the one at the base-changed Klein model, i.e.
`Work.MotT.autRigidBaseChange (Work.MotT.kleinDataBaseChange D (RatFunc 𝕜)) …`. -/
theorem twistFieldT_lam {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (hk : ringChar 𝕜 ≠ 5) {h₁ h₂ : RatFunc 𝕜} (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0)
    (θ : Work.MotV.twistFieldT D h₁ ≃ₐ[RatFunc 𝕜] Work.MotV.twistFieldT D h₂) :
    ∃ ε : ℤˣ, ∃ y : Fin 5 → RatFunc 𝕜, y ≠ 0 ∧
      ∀ k, Work.MotV.kleinTw (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b)
        (h₁ * h₂ ^ (ε : ℤ)) y k = 0 :=
  twist_iso_pointK_of_good (kleinDataBaseChange D (RatFunc 𝕜)) (kleinDataBaseChange_good D hD)
    (ringChar_ratFunc_ne_five hk) h₁0 h₂0 θ

end

end Work.MotT
