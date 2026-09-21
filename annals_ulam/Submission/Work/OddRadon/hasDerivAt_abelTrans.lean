import Mathlib
import Submission.Work.OddRadon.Abel
import Submission.Work.OddRadon.abelTrans_trig
import Submission.Work.OddRadon.hasDerivAt_integral_rpow_mul
import Submission.Work.OddRadon.integral_rpow_one_sub_sq_ibp

/-!
# The exponent-lowering recursion `T_α G' = 2α c T_{α-1} G` for the Abel-type transform

`abelTrans α G c = ∫_0^c G s (c²-s²)^α ds`.  This file proves that `abelTrans α G` has
derivative `2α c · abelTrans (α-1) G c` at every `c ∈ (0,1)`, for `G` of class `C¹` on `[0,1]`
and `α > 0`.  That is the recursion `T_α' = 2 α c T_{α-1}` used to reduce the exponent of the
odd-dimensional Radon inversion down to the classical Abel transform (`α = -1/2`).

The proof goes through the substitution `s = c t` (`c > 0`),
`abelTrans α G c = ∫_0^1 c^(2α+1) G(ct)(1-t²)^α dt`
(`abelTrans_eq_integral_comp_mul`), differentiation under the integral sign with respect to `c`
(`Work.OddRadon.hasDerivAt_integral_rpow_mul`), and the integration-by-parts identity
`(2α+1)∫_0^1 G(ct)(1-t²)^α + c∫_0^1 (deriv G)(ct) t (1-t²)^α = 2α∫_0^1 G(ct)(1-t²)^(α-1)`
(`Work.OddRadon.integral_rpow_one_sub_sq_ibp`).
-/

noncomputable section

open MeasureTheory
open scoped Interval Topology

namespace Work.OddRadon

/-- **The substitution `s = c t` in the forward Abel transform.** For `c > 0`,
`∫_0^c G s (c²-s²)^α ds = ∫_0^1 c^(2α+1) G (c t) (1-t²)^α dt`. -/
lemma abelTrans_eq_integral_comp_mul {α : ℝ} (G : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    abelTrans α G c
      = ∫ t in (0 : ℝ)..1, c ^ (2 * α + 1) * (G (c * t) * (1 - t ^ 2) ^ α) := by
  have h1 := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) (c := c)
      (fun s => G s * (c ^ 2 - s ^ 2) ^ α) (ne_of_gt hc)
  rw [mul_zero, mul_one] at h1
  have h2 : (∫ x in (0 : ℝ)..c, G x * (c ^ 2 - x ^ 2) ^ α)
      = c * ∫ x in (0 : ℝ)..1, G (c * x) * (c ^ 2 - (c * x) ^ 2) ^ α := by
    rw [h1, smul_eq_mul]
    field_simp
  show (∫ s in (0 : ℝ)..c, G s * (c ^ 2 - s ^ 2) ^ α) = _
  rw [h2, ← intervalIntegral.integral_const_mul c]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at ht
  beta_reduce
  have h1t : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hcs : c ^ 2 - (c * t) ^ 2 = c ^ 2 * (1 - t ^ 2) := by ring
  have hkey : (c ^ 2 : ℝ) ^ α = c ^ (2 * α) := by
    rw [← Real.rpow_natCast c 2, ← Real.rpow_mul (le_of_lt hc)]
    norm_num
  rw [hcs, Real.mul_rpow (by positivity) h1t, hkey]
  rw [Real.rpow_add hc (2 * α) 1, Real.rpow_one]
  ring

theorem hasDerivAt_abelTrans {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1)) {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (abelTrans α G) (2 * α * c * abelTrans (α - 1) G c) c := by
  -- the substituted expression agrees with `abelTrans α G` near `c` (`c > 0`)
  have hsub : abelTrans α G =ᶠ[𝓝 c]
      (fun x : ℝ => ∫ t in (0 : ℝ)..1, x ^ (2 * α + 1) * (G (x * t) * (1 - t ^ 2) ^ α)) :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hc.1)
      (fun x hx => abelTrans_eq_integral_comp_mul G hx)
  -- differentiate under the integral sign
  have hd := hasDerivAt_integral_rpow_mul hα hG hc
  set I2 : ℝ := ∫ t in (0 : ℝ)..1, G (c * t) * (1 - t ^ 2) ^ α with hI2
  set I1 : ℝ := ∫ t in (0 : ℝ)..1, deriv G (c * t) * t * (1 - t ^ 2) ^ α with hI1
  set I4 : ℝ := ∫ t in (0 : ℝ)..1, G (c * t) * (1 - t ^ 2) ^ (α - 1) with hI4
  have hkey := integral_rpow_one_sub_sq_ibp hα hG hc.1 hc.2
  rw [← hI2, ← hI1, ← hI4] at hkey
  have hd' : HasDerivAt
      (fun x : ℝ => ∫ t in (0 : ℝ)..1, x ^ (2 * α + 1) * (G (x * t) * (1 - t ^ 2) ^ α))
      ((2 * α + 1) * c ^ (2 * α) * I2 + c ^ (2 * α + 1) * I1) c := hd
  have e1 : (2 : ℝ) * (α - 1) + 1 = 2 * α - 1 := by ring
  have hcm : c * c ^ (2 * α - 1) = c ^ (2 * α) := by
    conv_rhs => rw [show (2 : ℝ) * α = (2 * α - 1) + 1 by ring]
    rw [Real.rpow_add hc.1 (2 * α - 1) 1, Real.rpow_one]
    ring
  have hcp : c ^ (2 * α + 1) = c ^ (2 * α) * c := by
    rw [Real.rpow_add hc.1 (2 * α) 1, Real.rpow_one]
  have hsubs := abelTrans_eq_integral_comp_mul (α := α - 1) G hc.1
  have hR : 2 * α * c * abelTrans (α - 1) G c = c ^ (2 * α) * (2 * α * I4) := by
    rw [hsubs, intervalIntegral.integral_const_mul, e1, ← hI4, ← hcm]
    ring
  have hL : (2 * α + 1) * c ^ (2 * α) * I2 + c ^ (2 * α + 1) * I1
      = c ^ (2 * α) * (2 * α * I4) := by
    rw [hcp]
    rw [show (2 * α + 1) * c ^ (2 * α) * I2 + c ^ (2 * α) * c * I1
        = c ^ (2 * α) * ((2 * α + 1) * I2 + c * I1) by ring, hkey]
  have hfinal : HasDerivAt
      (fun x : ℝ => ∫ t in (0 : ℝ)..1, x ^ (2 * α + 1) * (G (x * t) * (1 - t ^ 2) ^ α))
      (2 * α * c * abelTrans (α - 1) G c) c :=
    hd'.congr_deriv (hL.trans hR.symm)
  exact hsub.hasDerivAt_iff.mpr hfinal

end Work.OddRadon
