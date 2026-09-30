import Mathlib
import Submission.Work.Space.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Topology
open unitInterval

namespace Work.Space

/-! ### Scalar multiples of points of the square -/

theorem nrm_smul {c : ℝ} (hc : 0 ≤ c) (p : E2) : nrm (c • p) = c * nrm p := by
  simp only [nrm]
  rw [show (c • p : E2) 0 = c * p 0 from by simp, show (c • p : E2) 1 = c * p 1 from by simp,
    abs_mul, abs_mul, abs_of_nonneg hc, mul_max_of_nonneg _ _ hc]

theorem abs_coord_le_nrm (p : E2) (i : Fin 2) : |p i| ≤ nrm p := by
  fin_cases i <;> simp [nrm]

theorem sqNorm_coe (p : SquarePt) : sqNorm p = nrm (p : E2) := rfl

theorem smul_mem_Sq {c : ℝ} (hc : 0 ≤ c) {p : E2} (hp : p ∈ Sq) (h : c * nrm p ≤ 1) :
    c • p ∈ Sq := by
  obtain ⟨hp0, hp1⟩ := hp
  constructor
  · rw [show (c • p : E2) 0 = c * p 0 from by simp, abs_mul, abs_of_nonneg hc]
    calc c * |p 0| ≤ c * nrm p := by
          gcongr
          exact abs_coord_le_nrm p 0
      _ ≤ 1 := h
  · rw [show (c • p : E2) 1 = c * p 1 from by simp, abs_mul, abs_of_nonneg hc]
    calc c * |p 1| ≤ c * nrm p := by
          gcongr
          exact abs_coord_le_nrm p 1
      _ ≤ 1 := h

/-- The point `c • p` of the square, when it stays inside. -/
def smulPt (c : ℝ) (hc : 0 ≤ c) (p : SquarePt) (h : c * sqNorm p ≤ 1) : SquarePt :=
  ⟨c • (p : E2), smul_mem_Sq hc p.2 h⟩

@[simp] theorem smulPt_coe (c : ℝ) (hc : 0 ≤ c) (p : SquarePt) (h : c * sqNorm p ≤ 1) :
    ((smulPt c hc p h : SquarePt) : E2) = c • (p : E2) := rfl

theorem sqNorm_smulPt (c : ℝ) (hc : 0 ≤ c) (p : SquarePt) (h : c * sqNorm p ≤ 1) :
    sqNorm (smulPt c hc p h) = c * sqNorm p := by
  show nrm (c • (p : E2)) = c * sqNorm p
  rw [nrm_smul hc, sqNorm_coe]

/-! ### The radial collapse and the straight-line homotopy on the square -/

theorem continuousOn_sqNorm_inv : ContinuousOn (fun p : SquarePt => (sqNorm p)⁻¹)
    {p : SquarePt | sqNorm p ≠ 0} :=
  ContinuousOn.inv₀ continuous_sqNorm.continuousOn fun _ hp => hp

/-- The interpolation coefficient of the radial homotopy, from `(sqNorm p)⁻¹` at `s = 0`
to `1` at `s = 1`. -/
def rayCoef (s : I) (p : SquarePt) : ℝ := (s : ℝ) + (1 - (s : ℝ)) * (sqNorm p)⁻¹

/-- The straight-line point of the homotopy. -/
def rayVal (s : I) (p : SquarePt) : E2 := rayCoef s p • (p : E2)

theorem rayCoef_zero (p : SquarePt) : rayCoef 0 p = (sqNorm p)⁻¹ := by simp [rayCoef]

theorem rayCoef_one (p : SquarePt) : rayCoef 1 p = 1 := by simp [rayCoef]

theorem rayCoef_nonneg (s : I) (p : SquarePt) : 0 ≤ rayCoef s p := by
  have hs : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hi : 0 ≤ (sqNorm p)⁻¹ := inv_nonneg.mpr (sqNorm_nonneg p)
  have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith [s.2.2]
  exact add_nonneg hs (mul_nonneg h1 hi)

theorem rayCoef_mul_sqNorm (s : I) (p : SquarePt) (hp : sqNorm p ≠ 0) :
    rayCoef s p * sqNorm p = (s : ℝ) * sqNorm p + (1 - (s : ℝ)) := by
  rw [rayCoef, add_mul, mul_assoc, inv_mul_cancel₀ hp, mul_one]

theorem rayCoef_mul_sqNorm_le_one (s : I) (p : SquarePt) (hp : sqNorm p ≠ 0) :
    rayCoef s p * sqNorm p ≤ 1 := by
  rw [rayCoef_mul_sqNorm s p hp]
  have h1 : (s : ℝ) ≤ 1 := s.2.2
  have h2 : sqNorm p ≤ 1 := sqNorm_le_one p
  nlinarith [s.2.1]

theorem rayVal_mem_Sq (s : I) (p : SquarePt) (hp : 1/4 < sqNorm p) : rayVal s p ∈ Sq := by
  have hz : sqNorm p ≠ 0 := by linarith
  exact smul_mem_Sq (rayCoef_nonneg s p) p.2 (rayCoef_mul_sqNorm_le_one s p hz)

/-- The straight-line point of the square, valid on the shell `1/4 < sqNorm p`. -/
def rayPt (s : I) (p : SquarePt) (hp : 1/4 < sqNorm p) : SquarePt :=
  ⟨rayVal s p, rayVal_mem_Sq s p hp⟩

/-- The radial collapse of `p` onto the boundary of the square. -/
def radPt (p : SquarePt) (hp : 1/4 < sqNorm p) : SquarePt := rayPt 0 p hp

theorem sqNorm_rayPt (s : I) (p : SquarePt) (hp : 1/4 < sqNorm p) :
    sqNorm (rayPt s p hp) = (s : ℝ) * sqNorm p + (1 - (s : ℝ)) := by
  show nrm (rayVal s p) = _
  rw [rayVal, nrm_smul (rayCoef_nonneg s p), ← sqNorm_coe p,
    rayCoef_mul_sqNorm s p (by linarith)]

theorem sqNorm_radPt (p : SquarePt) (hp : 1/4 < sqNorm p) : sqNorm (radPt p hp) = 1 := by
  rw [radPt, sqNorm_rayPt]
  simp

theorem sqNorm_rayPt_gt (s : I) (p : SquarePt) (hp : 1/4 < sqNorm p) :
    1/4 < sqNorm (rayPt s p hp) := by
  rw [sqNorm_rayPt]
  have hle : sqNorm p - 1 ≤ 0 := by linarith [sqNorm_le_one p]
  have hmul : sqNorm p - 1 ≤ (s : ℝ) * (sqNorm p - 1) := by
    calc sqNorm p - 1 = 1 * (sqNorm p - 1) := by ring
      _ ≤ (s : ℝ) * (sqNorm p - 1) := mul_le_mul_of_nonpos_right s.2.2 hle
  nlinarith [hmul, hp]

theorem rayPt_one (p : SquarePt) (hp : 1/4 < sqNorm p) : rayPt 1 p hp = p := by
  apply Subtype.ext
  show rayVal 1 p = (p : E2)
  rw [rayVal, rayCoef_one, one_smul]

theorem radPt_eq_self (p : SquarePt) (h : sqNorm p = 1) :
    radPt p (by rw [h]; norm_num) = p := by
  apply Subtype.ext
  show rayVal 0 p = (p : E2)
  rw [rayVal, rayCoef_zero, h, inv_one, one_smul]

/-- The open shell `1/4 < ‖p‖∞` of the square. -/
abbrev SS : Type := {p : SquarePt // 1/4 < sqNorm p}

theorem SS.sqNorm_gt (p : SS) : 1/4 < sqNorm p.1 := p.2

theorem SS.sqNorm_pos (p : SS) : 0 < sqNorm p.1 := by linarith [p.2]

/-! ### Continuity of the above -/

theorem continuous_inv_sqNorm : Continuous (fun p : SS => (sqNorm p.1)⁻¹) :=
  continuousOn_sqNorm_inv.comp_continuous continuous_subtype_val
    (fun p => ne_of_gt (by linarith [p.2]))

theorem continuous_rayCoefI : Continuous (fun q : I × SS => rayCoef q.1 q.2.1) := by
  have h1 : Continuous fun q : I × SS => ((q.1 : I) : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun q : I × SS => (1 : ℝ) - ((q.1 : I) : ℝ) :=
    continuous_const.sub h1
  have h3 : Continuous fun q : I × SS => (sqNorm q.2.1)⁻¹ :=
    continuous_inv_sqNorm.comp continuous_snd
  exact h1.add (h2.mul h3)

theorem continuous_rayValI : Continuous (fun q : I × SS => rayVal q.1 q.2.1) :=
  continuous_rayCoefI.smul
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))

theorem continuous_rayPtI : Continuous (fun q : I × SS => rayPt q.1 q.2.1 q.2.2) :=
  Continuous.subtype_mk continuous_rayValI (fun q => rayVal_mem_Sq q.1 q.2.1 q.2.2)

theorem continuous_radPt : Continuous (fun p : SS => radPt p.1 p.2) :=
  continuous_rayPtI.comp (continuous_const.prodMk continuous_id)

end Work.Space

