import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.aut_functionField
import Submission.Work.MotC2.Translation
import Submission.Work.MotC5N3.Nodes.shiftOf_pow_five_eq_one
import Submission.Work.MotV5.Nodes.five_nsmul_eq_zero_of_transAlgEquiv_pow_eq_one
import Submission.Work.MotC5N3.Nodes.not_eq_transAlgEquiv_mul_negAlgEquiv
import Submission.Work.MotV5.exists_kleinData_shiftProj

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.Nodes
open Work.MotV5.Nodes
/-- **The projective fifth-torsion shift is a translation by a `5`-torsion point.**

`Work.MotC5N3.KleinData.ShiftOf D σS` says that the `Work.MotC5N3.KbA K`-automorphism `σS` of the function field
`Work.MotC5N3.OmA K D = K̄(E)` of the (base changed) elliptic curve permutes the Klein coordinates up to one scalar:
`σS κ_i = λ κ_{i+1}`, `λ ≠ 0`.  Every such automorphism is the translation by a `5`-torsion point.

The classification of automorphisms of the function field of an elliptic curve with `j ≠ 0, 1728`
(`Work.MotC2.aut_functionField`) writes `σS = τ_Q * (neg)^ε`, `ε : Fin 2`; its hypotheses on `j` are
inherited from `D.Good` by `WeierstrassCurve.map_j` (as
`D.E.baseChange (Work.MotC5N3.KbA K) = D.E.map (algebraMap 𝕜 (Work.MotC5N3.KbA K))`), and the base changed curve is elliptic
by hypothesis.  The two cases are then:

* `ε = 0`: `σS = τ_Q`, and the shift condition forces `σS ^ 5 = 1`
  (`Work.MotC5N3.Nodes.shiftOf_pow_five_eq_one`: `σS ^ 5` fixes the Klein field, hence each Klein ratio
  `κ_i / κ_0`, and by `KleinData.Generates` those ratios generate `Work.MotC5N3.OmA K D` over `Work.MotC5N3.KbA K`).  Then
  `τ_{5 • Q} = (τ_Q)^5 = σS ^ 5 = 1 = τ_0`, and injectivity of `Q ↦ τ_Q` gives `5 • Q = 0`
  (`Work.MotV5.Nodes.five_nsmul_eq_zero_of_transAlgEquiv_pow_eq_one`).
* `ε = 1`: `σS = τ_Q * neg` is the reflection `P ↦ Q - P`, an involution, which is incompatible
  with `σS ^ 5 = 1` and the quotient calculation `σS (κ_i / κ_0) = (κ_{i+1} / κ_0) / (κ_1 / κ_0)` of
  the shift condition together with `KleinData.Nonconstant`
  (`Work.MotC5N3.Nodes.not_eq_transAlgEquiv_mul_negAlgEquiv`). -/
theorem shiftOf_eq_transAlgEquiv (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    [DecidableEq (Work.MotC5N3.KbA K)] [hEll : (D.E.baseChange (Work.MotC5N3.KbA K)).IsElliptic]
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (hσS : Work.MotC5N3.KleinData.ShiftOf D σS) :
    ∃ T : (D.E.baseChange (Work.MotC5N3.KbA K)).toAffine.Point,
      σS = Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) T ∧ (5 : ℕ) • T = 0 := by
  classical
  haveI hEll' : (D.E.baseChange (Work.MotC5N3.KbA K)).IsElliptic := hEll
  have hGood : Work.MotV.KleinData.Good D := hD.1
  haveI hEell : D.E.IsElliptic := hGood.elliptic
  -- ## the base-changed curve has the same `j`-invariant, so the classification applies
  have hjmap : (D.E.baseChange (Work.MotC5N3.KbA K)).j =
      algebraMap 𝕜 (Work.MotC5N3.KbA K) (D.E.j) := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_j]
  have hj0 : (D.E.baseChange (Work.MotC5N3.KbA K)).j ≠ 0 := by
    rw [hjmap]
    exact fun hh => hGood.j_ne_zero ((algebraMap 𝕜 (Work.MotC5N3.KbA K)).injective (by simpa using hh))
  have hj1728 : (D.E.baseChange (Work.MotC5N3.KbA K)).j ≠ 1728 := by
    rw [hjmap]
    intro hh
    exact hGood.j_ne ((algebraMap 𝕜 (Work.MotC5N3.KbA K)).injective (by
      rw [map_ofNat]; exact hh))
  -- ## `σS ^ 5 = 1`
  -- The *projective shift* has order dividing `5`: `σS ^ 5` fixes the Klein field
  -- (`GenAux_sigmaS_pow_five_kleinField`), hence each Klein ratio `κ_i / κ_0`, and those ratios
  -- generate `Work.MotC5N3.OmA K D` over `Work.MotC5N3.KbA K` by `KleinData.Generates`.
  have hσS5 : σS ^ 5 = 1 := Work.MotC5N3.Nodes.shiftOf_pow_five_eq_one 𝕜 D hD σS hσS
  -- ## the classification of automorphisms of `K̄(E)`
  obtain ⟨Q, ε, hQε⟩ := Work.MotC2.aut_functionField (Work.MotC5N3.KbA K)
    (D.E.baseChange (Work.MotC5N3.KbA K)) hj0 hj1728 σS
  fin_cases ε
  · -- ## `ε = 0`: `σS` is the translation by `Q`
    have hσS_eq : σS = Work.MotC2.transAlgEquiv (D.E.baseChange (Work.MotC5N3.KbA K)) Q := by
      rw [hQε]; simp
    refine ⟨Q, hσS_eq, ?_⟩
    refine Work.MotV5.Nodes.five_nsmul_eq_zero_of_transAlgEquiv_pow_eq_one
      (D.E.baseChange (Work.MotC5N3.KbA K)) Q ?_
    rw [← hσS_eq, hσS5]
  · -- ## `ε = 1`: `σS` would be the reflection `P ↦ Q - P`, an involution, which is
    -- incompatible with `σS ^ 5 = 1` and the shift condition (a reflection cannot permute the
    -- Klein coordinates cyclically up to a scalar)
    exfalso
    exact Work.MotC5N3.Nodes.not_eq_transAlgEquiv_mul_negAlgEquiv 𝕜 D hD.2.1 σS hσS5 hσS Q
      (by rw [hQε]; norm_num)

end Work.MotC5N3.Nodes