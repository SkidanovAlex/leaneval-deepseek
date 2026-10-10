import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotV5.KleinData5Defs
import Submission.Work.MotV5.exists_kleinData5
import Submission.Work.MotV5.exists_kleinData_ASGood
import Submission.Work.MotV5.adjoin_genX_genY
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.genY_not_ratFunc_genX
import Submission.Work.MotV5.D11_shift_kp
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.exists_kleinData_shiftProj`

We exhibit Klein data in characteristic `5` satisfying `ASGood` and the (scaled) projective
fifth-torsion shift compatibility `ShiftCompatProj`: the datum is `D11` of
`Submission/Work/MotV5/exists_kleinData_ASGood.lean` (the curve `y² - y = x³ - x²` with the Klein
coordinates of the elliptic normal quintic), and the automorphism is the translation by the
`5`-torsion point `T = (0,0)`, which acts on the Klein coordinates by `κ_i ↦ κ_{i+1}/κ_1`
(the scalar `λ = 1/κ_1` of `ShiftCompatProj`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotV5

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

/-! ## §1 The translation by the origin `(0,0)` on `y² + a₃y = x³ + a₂x²` -/

variable {L : Type} [Field L] {E : WeierstrassCurve L}

/-- **The translation by the point `(0,0)`** of a Weierstrass curve `y² + a₃y = x³ + a₂x²`
(`a₁ = a₄ = a₆ = 0`, `a₂ = a₃ = -1`): it sends the generic point to
`(x, y) ↦ (y/x², 1/x - y/x³)`.  This is the `T = (0,0)` case of `Work.MotC2.transAlgEquiv`,
whose `X`- and `Y`-coordinate formulae we compute explicitly. -/
theorem transAlgEquiv_origin [DecidableEq L] [E.IsElliptic]
    (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = -1) (ha₃ : E.a₃ = -1) (ha₄ : E.a₄ = 0)
    (ha₆ : E.a₆ = 0) (h : Nonsingular E 0 0) :
    (Work.MotC2.transAlgEquiv E (Point.some 0 0 h)) (Work.MotC2.genX E) =
        Work.MotC2.genY E / (Work.MotC2.genX E) ^ 2 ∧
      (Work.MotC2.transAlgEquiv E (Point.some 0 0 h)) (Work.MotC2.genY E) =
        1 / Work.MotC2.genX E - Work.MotC2.genY E / (Work.MotC2.genX E) ^ 3 := by
  classical
  have hx : Work.MotC2.genX E ≠ 0 :=
    fun h0 => Work.MotC2.transcendental_genX E (h0 ▸ isAlgebraic_zero)
  have hba₁ : (Work.MotC2.baseE E).a₁ = 0 := by
    rw [Work.MotC2.baseE, WeierstrassCurve.map_a₁, ha₁, map_zero]
  have hba₂ : (Work.MotC2.baseE E).a₂ = -1 := by
    rw [Work.MotC2.baseE, WeierstrassCurve.map_a₂, ha₂, map_neg, map_one]
  have hba₃ : (Work.MotC2.baseE E).a₃ = -1 := by
    rw [Work.MotC2.baseE, WeierstrassCurve.map_a₃, ha₃, map_neg, map_one]
  have hba₄ : (Work.MotC2.baseE E).a₄ = 0 := by
    rw [Work.MotC2.baseE, WeierstrassCurve.map_a₄, ha₄, map_zero]
  have hrel := Work.MotC2.genX_genY_relation E
  rw [ha₁, ha₃, ha₂, ha₄, ha₆, map_zero, map_neg, map_one] at hrel
  simp only [zero_mul, add_zero, neg_mul, one_mul] at hrel
  constructor
  · rw [Work.MotC2.transAlgEquiv_genX E h, map_zero]
    unfold WeierstrassCurve.Affine.slope
    rw [ite_eq_right hx]
    rw [WeierstrassCurve.Affine.addX, hba₁, hba₂]
    simp only [sub_zero, div_one]
    field_simp
    linear_combination (norm := first | refl_ring1 | ring1) hrel
  · rw [Work.MotC2.transAlgEquiv_genY E h, map_zero]
    unfold WeierstrassCurve.Affine.slope
    rw [ite_eq_right hx]
    simp only [sub_zero, div_one]
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, hba₁, hba₃, hba₂]
    field_simp
    ring_nf
    linear_combination (norm := first | refl_ring1 | ring1) (-(Work.MotC2.genY E) - 1) * hrel

/-! ## §2 The curve `E_{1,1}` over `Kb 𝕜` -/

/-- The base change to `Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)` of the curve `E_{1,1}` of `D11`
(`y² - y = x³ - x²` in characteristic `5`). -/
abbrev ED11 (𝕜 : Type) [Field 𝕜] : WeierstrassCurve (Work.MotV.Kb 𝕜) :=
  (D11 𝕜).E.baseChange (Work.MotV.Kb 𝕜)

instance instIsEllipticED11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (ED11 𝕜).IsElliptic :=
  show ((D11 𝕜).E.map (algebraMap 𝕜 (Work.MotV.Kb 𝕜))).IsElliptic from inferInstance

theorem D11_shiftCompatProj (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    Work.MotV5.KleinData.ShiftCompatProj (D11 𝕜) := by
  classical
  haveI hchar : CharP (Work.MotV.Kb 𝕜) 5 :=
    charP_of_injective_algebraMap (algebraMap 𝕜 (Work.MotV.Kb 𝕜)).injective 5
  have ha₁ : (ED11 𝕜).a₁ = 0 := by
    show ((D11 𝕜).E.map (algebraMap 𝕜 (Work.MotV.Kb 𝕜))).a₁ = 0
    rw [WeierstrassCurve.map_a₁, show (D11 𝕜).E.a₁ = (0 : 𝕜) from rfl, map_zero]
  have ha₂ : (ED11 𝕜).a₂ = 4 := by
    show ((D11 𝕜).E.map (algebraMap 𝕜 (Work.MotV.Kb 𝕜))).a₂ = 4
    rw [WeierstrassCurve.map_a₂, show (D11 𝕜).E.a₂ = (4 : 𝕜) from rfl, map_ofNat]
  have ha₃ : (ED11 𝕜).a₃ = 4 := by
    show ((D11 𝕜).E.map (algebraMap 𝕜 (Work.MotV.Kb 𝕜))).a₃ = 4
    rw [WeierstrassCurve.map_a₃, show (D11 𝕜).E.a₃ = (4 : 𝕜) from rfl, map_ofNat]
  have ha₄ : (ED11 𝕜).a₄ = 0 := by
    show ((D11 𝕜).E.map (algebraMap 𝕜 (Work.MotV.Kb 𝕜))).a₄ = 0
    rw [WeierstrassCurve.map_a₄, show (D11 𝕜).E.a₄ = (0 : 𝕜) from rfl, map_zero]
  have ha₆ : (ED11 𝕜).a₆ = 0 := by
    show ((D11 𝕜).E.map (algebraMap 𝕜 (Work.MotV.Kb 𝕜))).a₆ = 0
    rw [WeierstrassCurve.map_a₆, show (D11 𝕜).E.a₆ = (0 : 𝕜) from rfl, map_zero]
  have h4 : (4 : Work.MotV.Kb 𝕜) = -1 := by
    have h5 : (5 : Work.MotV.Kb 𝕜) = 0 := CharP.cast_eq_zero _ 5
    linear_combination (norm := first | refl_ring1 | ring1) h5
  have ha₂' : (ED11 𝕜).a₂ = (-1 : Work.MotV.Kb 𝕜) := by rw [ha₂, h4]
  have ha₃' : (ED11 𝕜).a₃ = (-1 : Work.MotV.Kb 𝕜) := by rw [ha₃, h4]
  -- the point `(0,0)` is nonsingular
  have hns : Nonsingular (ED11 𝕜) 0 0 := by
    rw [nonsingular_iff]
    refine ⟨?_, Or.inr ?_⟩
    · rw [equation_iff, ha₁, ha₂, ha₃, ha₄, ha₆]
      first | refl_ring1 | ring
    · rw [ha₁]
      simp only [mul_zero, sub_zero, zero_sub]
      intro h
      rw [ha₃'] at h
      simp only [neg_zero, zero_sub, neg_neg] at h
      exact one_ne_zero h.symm
  let T : (ED11 𝕜).toAffine.Point := Point.some 0 0 hns
  let σS : Work.MotV.Om (D11 𝕜) ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om (D11 𝕜) :=
    Work.MotC2.transAlgEquiv (ED11 𝕜) T
  obtain ⟨hgx, hgy⟩ := transAlgEquiv_origin (E := ED11 𝕜) ha₁ ha₂' ha₃' ha₄ ha₆ hns
  have hx : σS (x11 𝕜 (Work.MotV.Kb 𝕜)) =
      y11 𝕜 (Work.MotV.Kb 𝕜) / (x11 𝕜 (Work.MotV.Kb 𝕜)) ^ 2 := hgx
  have hy : σS (y11 𝕜 (Work.MotV.Kb 𝕜)) =
      1 / x11 𝕜 (Work.MotV.Kb 𝕜) - y11 𝕜 (Work.MotV.Kb 𝕜) / (x11 𝕜 (Work.MotV.Kb 𝕜)) ^ 3 := hgy
  have hx0 : x11 𝕜 (Work.MotV.Kb 𝕜) ≠ 0 := by
    have hx0' : Work.MotC2.genX (ED11 𝕜) ≠ 0 :=
      fun h0 => Work.MotC2.transcendental_genX (ED11 𝕜) (h0 ▸ isAlgebraic_zero)
    exact hx0'
  have hrel : y11 𝕜 (Work.MotV.Kb 𝕜) ^ 2 - y11 𝕜 (Work.MotV.Kb 𝕜) -
      x11 𝕜 (Work.MotV.Kb 𝕜) ^ 3 + x11 𝕜 (Work.MotV.Kb 𝕜) ^ 2 = 0 :=
    W11_Wp 𝕜 (Work.MotV.Kb 𝕜)
  haveI : CharP (F11 𝕜 (Work.MotV.Kb 𝕜)) 5 := charP_F11 𝕜 (Work.MotV.Kb 𝕜)
  obtain ⟨hk0, hk1, hk2, hk3, hk4⟩ :=
    D11_shift_kp (x11 𝕜 (Work.MotV.Kb 𝕜)) (y11 𝕜 (Work.MotV.Kb 𝕜)) hrel hx0
  have e0 : σS (Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 0) *
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1 =
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1 := by
    rw [kleinCoord_zero, kp0, map_one, one_mul]
  have e1 : σS (Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1) *
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1 =
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 2 := by
    rw [kleinCoord_one, kleinCoord_two]
    simp only [kp1, kp2, map_add, map_mul, map_pow, map_one, map_ofNat, hx, hy]
    exact hk1
  have e2 : σS (Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 2) *
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1 =
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 3 := by
    rw [kleinCoord_one, kleinCoord_two, kleinCoord_three]
    simp only [kp1, kp2, kp3, map_add, map_mul, map_pow, map_one, map_ofNat, hx, hy]
    exact hk2
  have e3 : σS (Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 3) *
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1 =
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 4 := by
    rw [kleinCoord_one, kleinCoord_three, kleinCoord_four]
    simp only [kp1, kp3, kp4, map_add, map_mul, map_pow, map_one, map_ofNat, hx, hy]
    exact hk3
  have e4 : σS (Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 4) *
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1 =
      Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 0 := by
    rw [kleinCoord_one, kleinCoord_four, kleinCoord_zero]
    simp only [kp1, kp4, kp0, map_add, map_mul, map_pow, map_one, map_ofNat, hx, hy]
    exact hk4
  have key : ∀ i : Fin 5,
      σS (Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) i) *
        Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1 =
        Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) (i + 1) := by
    intro i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
  have hκ1 : Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1 ≠ 0 := by
    intro hzero
    have h1 : (0 : Work.MotV.Om (D11 𝕜)) =
        kp0 (x11 𝕜 (Work.MotV.Kb 𝕜)) (y11 𝕜 (Work.MotV.Kb 𝕜)) := by
      rw [← hk4, ← kleinCoord_one 𝕜 (Work.MotV.Kb 𝕜), hzero, mul_zero]
    exact zero_ne_one h1
  refine ⟨σS, (Work.MotV.kleinCoord (D11 𝕜) (Work.MotV.Kb 𝕜) 1)⁻¹, inv_ne_zero hκ1, ?_⟩
  intro i
  rw [eq_inv_mul_iff_mul_eq₀ hκ1, mul_comm]
  exact key i

theorem exists_kleinData_shiftProj (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] [CharP 𝕜 5] :
    ∃ D : Work.MotV.KleinData 𝕜,
      Work.MotV5.KleinData.ASGood D ∧ Work.MotV5.KleinData.ShiftCompatProj D :=
  ⟨D11 𝕜, ⟨good11 𝕜, nonconstant11 𝕜, generates11 𝕜, D11_smooth 𝕜⟩, D11_shiftCompatProj 𝕜⟩

end

end Work.MotV5
