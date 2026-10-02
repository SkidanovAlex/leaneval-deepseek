import Mathlib
import Submission.Work.ThomBordism.Grassmann.P2Base.Gauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-!
# The coefficients `aCoefL`, `bCoefL` of a plane vector

`aCoefL s`, `bCoefL s` extract the coefficients of a vector of `ℂ⁶` in the `ℂ`-basis
`(Λ(s), Λ'(s)) = (lamL s, lamR s)` of the plane of a representative `s : ℂ⁵` (see `P2Base.Gauge`).
This module proves that the pair of coefficients *is* the coordinate pair (reconstruction) and
records the scaling law under `s ↦ h • s`.
-/

namespace Work.ThomBordism.Grassmann.P2Base

open Work.TangentClasses

noncomputable section

/-! ## A scalar identity -/

/-- For `h ≠ 0`: `(‖h‖²)⁻¹ * conj h = h⁻¹`. -/
theorem inv_ofReal_normSq_mul_star {h : ℂ} (hh : h ≠ 0) :
    (((‖h‖ ^ 2)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) h = h⁻¹ := by
  have hsne : (starRingEnd ℂ) h ≠ 0 := by
    simpa only [starRingEnd_apply] using (star_ne_zero.mpr hh : star h ≠ 0)
  have hmul : (starRingEnd ℂ) h * h = (((‖h‖ ^ 2 : ℝ)) : ℂ) := by
    rw [mul_comm, starRingEnd_apply, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [Complex.ofReal_inv, ← hmul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hsne, mul_one]

/-- `conj (h / ‖h‖) = conj h * (‖h‖)⁻¹`, for `h : ℂ` (the norm is the complex norm of `h`). -/
theorem star_div_ofReal_norm (h : ℂ) :
    (starRingEnd ℂ) (h / ((‖h‖ : ℝ) : ℂ)) = (starRingEnd ℂ) h * (((‖h‖ : ℝ) : ℂ))⁻¹ := by
  rw [div_eq_mul_inv, map_mul, map_inv₀]
  congr 1
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]

/-- The key scalar identity for the scaling of `aCoefL`: for `h ≠ 0`,
`(‖h‖)⁻¹ * conj (h / ‖h‖) = h⁻¹`. -/
theorem key_scale (h : ℂ) (hh : h ≠ 0) :
    ((‖h‖⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (h / ((‖h‖ : ℝ) : ℂ)) = h⁻¹ := by
  rw [star_div_ofReal_norm]
  rw [show ((‖h‖⁻¹ : ℝ) : ℂ) * ((starRingEnd ℂ) h * (((‖h‖ : ℝ) : ℂ))⁻¹)
      = ((((‖h‖⁻¹ : ℝ) : ℂ)) * (((‖h‖⁻¹ : ℝ) : ℂ))) * (starRingEnd ℂ) h from by
    rw [Complex.ofReal_inv]; ring]
  rw [← Complex.ofReal_mul]
  have h1 : (‖h‖ : ℝ)⁻¹ * (‖h‖ : ℝ)⁻¹ = (‖h‖ ^ 2)⁻¹ := by
    rw [pow_two, mul_inv]
  rw [h1, inv_ofReal_normSq_mul_star hh]

/-! ## Scaling of `wVec` and `lamUnit` -/

theorem wVec_scale (s : E5) {h : ℂ} (hh : h ≠ 0) : wVec (h • s) = h • wVec s := by
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hz : ((‖h‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hnorm : (‖h‖ : ℝ) ≠ 0)
  have hmul : ((‖h‖ : ℝ) : ℂ) * (h / ((‖h‖ : ℝ) : ℂ)) = h := by
    rw [mul_comm]
    exact div_mul_cancel₀ h hz
  have hμ : ‖h / ((‖h‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div]
    have h1 : ‖((‖h‖ : ℝ) : ℂ)‖ = ‖h‖ := by simp
    rw [h1, div_self (ne_of_gt hnorm)]
  conv_lhs => rw [← hmul, ← smul_smul]
  rw [wVec_smul_ofReal _ hnorm, wVec_smul_unit _ hμ, smul_smul, hmul]

theorem lamUnit_scale (s : E5) {h : ℂ} (hh : h ≠ 0) :
    lamUnit (h • s) = (h / ((‖h‖ : ℝ) : ℂ)) • lamUnit s := by
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hz : ((‖h‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hnorm : (‖h‖ : ℝ) ≠ 0)
  have hmul : ((‖h‖ : ℝ) : ℂ) * (h / ((‖h‖ : ℝ) : ℂ)) = h := by
    rw [mul_comm]
    exact div_mul_cancel₀ h hz
  have hμ : ‖h / ((‖h‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div]
    have h1 : ‖((‖h‖ : ℝ) : ℂ)‖ = ‖h‖ := by simp
    rw [h1, div_self (ne_of_gt hnorm)]
  conv_lhs => rw [← hmul, ← smul_smul]
  rw [lamUnit_smul_ofReal _ hnorm, lamUnit_smul_unit _ hμ]

/-! ## The scaling laws of the coefficients -/

theorem bCoefLScale (s : E5) {h : ℂ} (hh : h ≠ 0) (v : E6) :
    bCoefL (h • s) v = h⁻¹ * bCoefL s v := by
  rw [bCoefL_apply, bCoefL_apply, wVec_scale s hh, norm_smul, inner_smul_left]
  have hC1 : ((((‖h‖ * ‖wVec s‖) ^ 2)⁻¹ : ℝ) : ℂ)
      = (((‖h‖ ^ 2)⁻¹ : ℝ) : ℂ) * (((‖wVec s‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [mul_pow, mul_inv, Complex.ofReal_mul]
  have hkey : (((‖h‖ ^ 2)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) h = h⁻¹ :=
    inv_ofReal_normSq_mul_star hh
  rw [hC1, ← hkey]
  ring

theorem aCoefLScale (s : E5) {h : ℂ} (hh : h ≠ 0) (v : E6) :
    aCoefL (h • s) v = h⁻¹ * aCoefL s v := by
  have hL : lamL (h • s) = h • lamL s := map_smul lamL h s
  have hR : lamR (h • s) = h • lamR s := map_smul lamR h s
  have hu := lamUnit_scale s hh
  rw [aCoefL_apply, aCoefL_apply, hL, hR, hu, norm_smul, bCoefLScale s hh v,
    inner_smul_left, inner_smul_left, inner_smul_right]
  have hC1 : ((((‖h‖ * ‖lamL s‖)⁻¹ : ℝ)) : ℂ)
      = (((‖h‖⁻¹ : ℝ) : ℂ)) * (((‖lamL s‖⁻¹ : ℝ) : ℂ)) := by
    rw [mul_inv, Complex.ofReal_mul]
  have hkey : ((‖h‖⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (h / ((‖h‖ : ℝ) : ℂ)) = h⁻¹ :=
    key_scale h hh
  have hinner : (starRingEnd ℂ) (h / ((‖h‖ : ℝ) : ℂ))
        * (h * (inner ℂ (lamUnit s) (lamR s)))
        * (h⁻¹ * (bCoefL s v))
      = (starRingEnd ℂ) (h / ((‖h‖ : ℝ) : ℂ)) * (inner ℂ (lamUnit s) (lamR s))
        * (bCoefL s v) := by
    rw [show (starRingEnd ℂ) (h / ((‖h‖ : ℝ) : ℂ)) * (h * (inner ℂ (lamUnit s) (lamR s)))
          * (h⁻¹ * (bCoefL s v))
        = (starRingEnd ℂ) (h / ((‖h‖ : ℝ) : ℂ)) * (inner ℂ (lamUnit s) (lamR s))
          * (bCoefL s v) * (h * h⁻¹) from by ring,
      mul_inv_cancel₀ hh, mul_one]
  rw [hC1, hinner, ← hkey]
  ring

/-! ## Reconstruction -/

/-- **The pair `(aCoefL s v, bCoefL s v)` is the coordinate pair of `v`** in the basis
`(Λ(s), Λ'(s))`. -/
theorem coefLRecon (s : E5) (hs : s ≠ 0) {v : E6}
    (hv : v ∈ Submodule.span ℂ ({lamL s, lamR s} : Set E6)) :
    aCoefL s v • lamL s + bCoefL s v • lamR s = v := by
  obtain ⟨a, b, h⟩ := Submodule.mem_span_pair.mp hv
  rw [← h, aCoefL_recon s hs a b, bCoefL_recon s hs a b]

end

end Work.ThomBordism.Grassmann.P2Base
