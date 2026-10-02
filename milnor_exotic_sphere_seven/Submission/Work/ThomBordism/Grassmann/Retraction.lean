import Mathlib
import Submission.Work.ThomBordism.Grassmann.PlaneCoord
import Submission.Work.ThomBordism.Grassmann.SphereCover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# The retraction of the "upper half" of the sphere bundle onto the fibre over `baseVec`

`Work.ThomBordism.Grassmann.evalVec` sends a point `x` of the zero complement of the tautological
bundle to the vector `evalVec x.1` of its plane, whose direction is `dirVec x`.  Rotating the point
by the rotation `rotMap (dirVec x) baseVec` (which carries its own direction to `baseVec`) moves it
into the fibre `Z = p⁻¹(baseVec)` over `baseVec`; `evalVec_rotE_dirVec` is the computation that makes
this work, and `sPlus` is the resulting map.

Everything here is conditional on the vector's direction lying in the upper hemisphere
`⟪dirVec x, baseVec⟫ > -1/2` (so that the rotation is well defined): that is the open set `upSet`.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- The unit direction of the vector of the plane at a point of the zero complement. -/
noncomputable def dirVec (x : ↥(incZero k m)) : Amb (k+m) :=
  (‖evalVec x.1‖)⁻¹ • evalVec x.1

theorem norm_evalVec_ne_zero (x : ↥(incZero k m)) : ‖evalVec x.1‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement x.1 x.2)

theorem norm_dirVec (x : ↥(incZero k m)) : ‖dirVec x‖ = 1 := by
  rw [dirVec, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_evalVec_ne_zero x)]

theorem dirVec_smul (x : ↥(incZero k m)) : ‖evalVec x.1‖ • dirVec x = evalVec x.1 := by
  rw [dirVec, smul_smul, mul_inv_cancel₀ (norm_evalVec_ne_zero x), one_smul]

/-- `rotLI v u` is multiplicative on scalars along `v`. -/
theorem rotLI_smul_self {v u : Amb (k+m)} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (h : 1 + inner ℝ v u ≠ 0) (c : ℝ) : rotLI v u hv hu h (c • v) = c • u := by
  rw [rotLI_apply, rotMap_smul_self hv hu]

/-- **The key computation of the retraction**: rotating the vector by the rotation that carries its
own direction to `baseVec` gives `‖evalVec x‖ • baseVec`. -/
theorem evalVec_rotE_dirVec (x : ↥(incZero k m)) (hb : ‖baseVec k m‖ = 1)
    (h : 1 + inner ℝ (dirVec x) (baseVec k m) ≠ 0) :
    evalVec (rotE (rotLI (dirVec x) (baseVec k m) (norm_dirVec x) hb h) x).1
      = ‖evalVec x.1‖ • baseVec k m := by
  have h1 : rotMap (dirVec x) (baseVec k m) (evalVec x.1)
      = ‖evalVec x.1‖ • baseVec k m := by
    conv_lhs => rw [← dirVec_smul x]
    rw [show rotMap (dirVec x) (baseVec k m) (‖evalVec x.1‖ • dirVec x)
        = ‖evalVec x.1‖ • rotMap (dirVec x) (baseVec k m) (dirVec x) from by
      have h2 := map_smul (rotLM (dirVec x) (baseVec k m)) (‖evalVec x.1‖) (dirVec x)
      simpa only [rotLM_apply] using h2]
    rw [rotMap_self (norm_dirVec x) hb]
  rw [evalVec_rotE, rotLI_apply, h1]


/-- The angle condition coming from membership in `upSet`: the direction of the vector of the plane
is in the upper hemisphere, so the rotation to `baseVec` is well defined and nondegenerate. -/
theorem upSet_angle (x : ↥(upSet k m)) :
    1 + inner ℝ (dirVec (x : ↥(incZero k m))) (baseVec k m) ≠ 0 := by
  have hn : (0 : ℝ) < ‖evalVec (x : ↥(incZero k m)).1‖ :=
    norm_pos_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement _ (x : ↥(incZero k m)).2)
  have hp : 0 < 2 * inner ℝ (evalVec (x : ↥(incZero k m)).1) (baseVec k m)
      + ‖evalVec (x : ↥(incZero k m)).1‖ := x.2
  have hd : inner ℝ (dirVec (x : ↥(incZero k m))) (baseVec k m)
      = (‖evalVec (x : ↥(incZero k m)).1‖)⁻¹
        * inner ℝ (evalVec (x : ↥(incZero k m)).1) (baseVec k m) := by
    rw [dirVec, inner_smul_left, starRingEnd_apply, star_trivial]
  rw [hd]
  have hsum : 0 < ‖evalVec (x : ↥(incZero k m)).1‖
      + inner ℝ (evalVec (x : ↥(incZero k m)).1) (baseVec k m) := by linarith
  have hid : (1 : ℝ) + (‖evalVec (x : ↥(incZero k m)).1‖)⁻¹
        * inner ℝ (evalVec (x : ↥(incZero k m)).1) (baseVec k m)
      = (‖evalVec (x : ↥(incZero k m)).1‖)⁻¹
        * (‖evalVec (x : ↥(incZero k m)).1‖
          + inner ℝ (evalVec (x : ↥(incZero k m)).1) (baseVec k m)) := by
    rw [mul_add, inv_mul_cancel₀ (ne_of_gt hn)]
  rw [hid]
  exact ne_of_gt (mul_pos (inv_pos.mpr hn) hsum)

/-- **The retraction of the "upper half" of the sphere bundle onto the fibre over `baseVec`**:
rotate the direction of the point's vector to `baseVec`, carrying the point with it. -/
noncomputable def sPlus (hk : 1 ≤ k) (x : ↥(upSet k m)) : ↥(incZero k m) :=
  rotE (rotLI (dirVec (x : ↥(incZero k m))) (baseVec k m) (norm_dirVec _)
    (norm_baseVec (by omega)) (upSet_angle x)) (x : ↥(incZero k m))

/-- **The vector of the plane at `sPlus x`** is `‖evalVec x‖ • baseVec` (in particular nonzero and
parallel to `baseVec`). -/
theorem evalVec_sPlus (hk : 1 ≤ k) (x : ↥(upSet k m)) :
    evalVec (sPlus hk x).1 = ‖evalVec (x : ↥(incZero k m)).1‖ • baseVec k m :=
  evalVec_rotE_dirVec _ (norm_baseVec (by omega)) (upSet_angle x)

/-- **`sPlus` lands in the fibre over `baseVec`**: its direction is `baseVec`. -/
theorem dirVec_sPlus (hk : 1 ≤ k) (x : ↥(upSet k m)) : dirVec (sPlus hk x) = baseVec k m := by
  have hn : (0 : ℝ) < ‖evalVec (x : ↥(incZero k m)).1‖ :=
    norm_pos_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement _ (x : ↥(incZero k m)).2)
  rw [dirVec, evalVec_sPlus hk x, norm_smul, Real.norm_eq_abs, abs_of_pos hn,
    norm_baseVec (by omega), mul_one, smul_smul, inv_mul_cancel₀ (ne_of_gt hn), one_smul]


end

end Work.ThomBordism.Grassmann
