import Mathlib
import Submission.Work.MotV5.Contrib.AsResDefsA
import Submission.Work.MotC5N3.ASZChartSetupGen
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotV5.Contrib

open Work.MotAS (kleinPAS kleinPAS1 kleinPAS3 kleinPAS_smul kleinPAS1_smul kleinPAS3_smul
  kleinPAS1_decomp_u kleinPAS3_decomp_u)
open Work.MotC5N3 (asTwY)

theorem asZResRecoverySelfA {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K]
    [CharP K 5] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hz0 : Work.MotV5.Contrib.asZOmA D g 0 ≠ 0) :
    (Work.MotV5.Contrib.asZvA D g 1 = Work.MotV5.Contrib.asZOmA D g 0 * Work.MotV5.Contrib.asZwA1 D g ∧
      Work.MotV5.Contrib.asZvA D g 2 = Work.MotV5.Contrib.asZOmA D g 0 * Work.MotV5.Contrib.asZwA2 D g ∧
      Work.MotV5.Contrib.asZvA D g 3 = Work.MotV5.Contrib.asZOmA D g 0 * Work.MotV5.Contrib.asZwA3 D g ∧
      Work.MotV5.Contrib.asZvA D g 4 = Work.MotV5.Contrib.asZOmA D g 0 * Work.MotV5.Contrib.asZwA4 D g) ∧
    (Work.MotV5.Contrib.asZOmA D g 0)⁻¹ =
      -(Work.MotV5.Contrib.asZAA D g / Work.MotV5.Contrib.asZmuA D g) *
        (Work.MotAS.kleinPAS1 (Work.MotV5.Contrib.asZaA D g) (Work.MotV5.Contrib.asZbA D g)
            (Work.MotV5.Contrib.asZcA D g) (Work.MotV5.Contrib.asZwA D g) +
          (Work.MotV5.Contrib.asZlamA D g / Work.MotV5.Contrib.asZmuA D g) *
            Work.MotAS.kleinPAS3 (Work.MotV5.Contrib.asZaA D g) (Work.MotV5.Contrib.asZbA D g)
              (Work.MotV5.Contrib.asZcA D g) (Work.MotV5.Contrib.asZwA D g)) := by
  have hA : asZAA D g ≠ 0 := asZAA_ne_zero D g hD
  have hDv : asZDA D g ≠ 0 := asZDA_ne_zero D g hD
  have hE : asZEA D g ≠ 0 := asZEA_ne_zero D g hD
  have hmu : asZmuA D g ≠ 0 := asZmuA_ne_zero D g hD
  have hy0 : asTwY D g 0 ≠ 0 := by
    intro h0
    apply hz0
    rw [asZOmA_zero_eq]
    have hv1 : asZvA D g 1 = 0 := by simp only [asZvA, h0, div_zero]
    have hv3 : asZvA D g 3 = 0 := by simp only [asZvA, h0, div_zero]
    rw [hv1, hv3, mul_zero, mul_zero, add_zero]
  have hv0 : asZvA D g 0 = 1 := by
    show asTwY D g 0 / asTwY D g 0 = 1
    exact div_self hy0
  have hzr0 : asZAA D g * (asTwY D g 1 / asTwY D g 0)
      + asZBA D g * (asTwY D g 3 / asTwY D g 0) = asZOmA D g 0 := by
    simpa only [asZvA] using (asZOmA_zero_eq D g).symm
  have hzr1 : asZAA D g * (asTwY D g 2 / asTwY D g 0)
      + asZCA D g * (asTwY D g 4 / asTwY D g 0) = asZOmA D g 1 := by
    simpa only [asZvA] using (asZOmA_one_eq D g).symm
  have hzr2 : asZDA D g * (asTwY D g 3 / asTwY D g 0) = asZOmA D g 2 := by
    simpa only [asZvA] using (asZOmA_two_eq D g).symm
  have hzr3 : asZEA D g * (asTwY D g 4 / asTwY D g 0) = asZOmA D g 3 := by
    simpa only [asZvA] using (asZOmA_three_eq D g).symm
  have hz0' : asZAA D g * (asTwY D g 1 / asTwY D g 0)
      + asZBA D g * (asTwY D g 3 / asTwY D g 0) ≠ 0 := by
    rw [hzr0]; exact hz0
  have hz0a : asZAA D g * asTwY D g 1 + asZBA D g * asTwY D g 3 ≠ 0 := by
    rw [show asZAA D g * asTwY D g 1 + asZBA D g * asTwY D g 3
        = (asZAA D g * (asTwY D g 1 / asTwY D g 0)
            + asZBA D g * (asTwY D g 3 / asTwY D g 0)) * asTwY D g 0 from by
      field_simp [hy0]]
    exact mul_ne_zero hz0' hy0
  have hz0b : asTwY D g 1 * asZAA D g + asZBA D g * asTwY D g 3 ≠ 0 := by
    rw [mul_comm (asTwY D g 1) (asZAA D g)]
    exact hz0a
  have hz0c : asTwY D g 3 * asZBA D g + asZAA D g * asTwY D g 1 ≠ 0 := by
    rw [show asTwY D g 3 * asZBA D g + asZAA D g * asTwY D g 1
        = asZAA D g * asTwY D g 1 + asZBA D g * asTwY D g 3 from by ring]
    exact hz0a
  have hp1 : asZvA D g 1 = asZOmA D g 0 * asZwA1 D g := by
    show asTwY D g 1 / asTwY D g 0
      = asZOmA D g 0 * ((1 - asZBA D g * (asZOmA D g 2 / asZOmA D g 0 / asZDA D g))
          / asZAA D g)
    rw [← hzr0, ← hzr2]
    field_simp [hy0, hz0', hz0a, hz0b, hz0c, hDv, hA]
    try ring
    try (field_simp [hz0c, hz0a, hz0b, hz0', hy0, hDv, hA]; ring)
  have hp2 : asZvA D g 2 = asZOmA D g 0 * asZwA2 D g := by
    show asTwY D g 2 / asTwY D g 0
      = asZOmA D g 0 * ((asZOmA D g 1 / asZOmA D g 0
          - asZCA D g * (asZOmA D g 3 / asZOmA D g 0 / asZEA D g)) / asZAA D g)
    rw [← hzr0, ← hzr1, ← hzr3]
    field_simp [hy0, hz0', hz0a, hz0b, hz0c, hE, hA]
    try ring
    try (field_simp [hz0c, hz0a, hz0b, hz0', hy0, hE, hA]; ring)
  have hp3 : asZvA D g 3 = asZOmA D g 0 * asZwA3 D g := by
    show asTwY D g 3 / asTwY D g 0
      = asZOmA D g 0 * (asZOmA D g 2 / asZOmA D g 0 / asZDA D g)
    rw [← hzr0, ← hzr2]
    field_simp [hy0, hz0', hz0a, hz0b, hz0c, hDv, hA]
    try ring
    try (field_simp [hz0c, hz0a, hz0b, hz0', hy0, hDv, hA]; ring)
  have hp4 : asZvA D g 4 = asZOmA D g 0 * asZwA4 D g := by
    show asTwY D g 4 / asTwY D g 0
      = asZOmA D g 0 * (asZOmA D g 3 / asZOmA D g 0 / asZEA D g)
    rw [← hzr0, ← hzr3]
    field_simp [hy0, hz0', hz0a, hz0b, hz0c, hE, hA]
    try ring
    try (field_simp [hz0c, hz0a, hz0b, hz0', hy0, hE, hA]; ring)
  have hvec : asZvA D g = fun i => (asTwY D g 0)⁻¹ * asTwY D g i := by
    funext i
    show asTwY D g i / asTwY D g 0 = (asTwY D g 0)⁻¹ * asTwY D g i
    rw [div_eq_mul_inv, mul_comm]
  have hc1f : kleinPAS (asZaA D g) (asZbA D g) (asZcA D g) (asZvA D g) = 0 := by
    have h : kleinPAS (asZaA D g) (asZbA D g) (asZcA D g) (asTwY D g) = 0 :=
      Work.MotC5N3.kleinPAS_asTwY D hD.1 g
    rw [hvec, kleinPAS_smul (asZaA D g) (asZbA D g) (asZcA D g)
      ((asTwY D g 0)⁻¹) (asTwY D g), h]
    funext i
    simp
  have hc1 : kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g) (asZvA D g) = 0 := by
    have h1 := congrFun hc1f 1
    rw [show kleinPAS (asZaA D g) (asZbA D g) (asZcA D g) (asZvA D g) (1 : Fin 5)
        = kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g) (asZvA D g) from rfl] at h1
    exact h1
  have hc3 : kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g) (asZvA D g) = 0 := by
    have h3 := congrFun hc1f 3
    rw [show kleinPAS (asZaA D g) (asZbA D g) (asZcA D g) (asZvA D g) (3 : Fin 5)
        = kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g) (asZvA D g) from rfl] at h3
    exact h3
  have hvecU : asZvA D g = fun i => asZOmA D g 0 *
      ![(asZOmA D g 0)⁻¹, asZwA1 D g, asZwA2 D g, asZwA3 D g, asZwA4 D g] i := by
    funext i
    fin_cases i
    · show asZvA D g 0 = asZOmA D g 0 * (asZOmA D g 0)⁻¹
      rw [hv0, mul_inv_cancel₀ hz0]
    · show asZvA D g 1 = asZOmA D g 0 * asZwA1 D g
      exact hp1
    · show asZvA D g 2 = asZOmA D g 0 * asZwA2 D g
      exact hp2
    · show asZvA D g 3 = asZOmA D g 0 * asZwA3 D g
      exact hp3
    · show asZvA D g 4 = asZOmA D g 0 * asZwA4 D g
      exact hp4
  have hzU1 : kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g)
      ![(asZOmA D g 0)⁻¹, asZwA1 D g, asZwA2 D g, asZwA3 D g, asZwA4 D g] = 0 := by
    have hs := kleinPAS1_smul (asZaA D g) (asZbA D g) (asZcA D g) (asZOmA D g 0)
      ![(asZOmA D g 0)⁻¹, asZwA1 D g, asZwA2 D g, asZwA3 D g, asZwA4 D g]
    rw [hvecU, hs] at hc1
    exact (mul_eq_zero.mp hc1).resolve_left (pow_ne_zero 2 hz0)
  have hzU3 : kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g)
      ![(asZOmA D g 0)⁻¹, asZwA1 D g, asZwA2 D g, asZwA3 D g, asZwA4 D g] = 0 := by
    have hs := kleinPAS3_smul (asZaA D g) (asZbA D g) (asZcA D g) (asZOmA D g 0)
      ![(asZOmA D g 0)⁻¹, asZwA1 D g, asZwA2 D g, asZwA3 D g, asZwA4 D g]
    rw [hvecU, hs] at hc3
    exact (mul_eq_zero.mp hc3).resolve_left (pow_ne_zero 2 hz0)
  have hmu' : (2 : Work.MotC5N3.OmA K D) *
        (asZaA D g ^ 2 - asZaA D g * asZbA D g - asZbA D g ^ 2)
      = asZmuA D g := by
    rw [asZmuA, asZaA, asZbA]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  have hR1 : (asZOmA D g 0)⁻¹ *
        (asZmuA D g * asZwA1 D g - (asZaA D g ^ 2 + asZbA D g ^ 2) * asZwA3 D g)
      + kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g) = 0 := by
    have hdec := kleinPAS1_decomp_u (asZaA D g) (asZbA D g) (asZcA D g) (asZOmA D g 0)⁻¹
      (asZwA1 D g) (asZwA2 D g) (asZwA3 D g) (asZwA4 D g)
    rw [hzU1, hmu'] at hdec
    exact hdec.symm
  have hR3 : (asZOmA D g 0)⁻¹ * (asZmuA D g * asZwA3 D g)
      + kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g) = 0 := by
    have hdec := kleinPAS3_decomp_u (asZaA D g) (asZbA D g) (asZcA D g) (asZOmA D g 0)⁻¹
      (asZwA1 D g) (asZwA2 D g) (asZwA3 D g) (asZwA4 D g)
    rw [hzU3, hmu'] at hdec
    exact hdec.symm
  have hAw : asZAA D g * asZwA1 D g + asZBA D g * asZwA3 D g = 1 := by
    show asZAA D g * ((1 - asZBA D g * (asZOmA D g 2 / asZOmA D g 0 / asZDA D g))
        / asZAA D g)
      + asZBA D g * (asZOmA D g 2 / asZOmA D g 0 / asZDA D g) = 1
    field_simp [hA]
    first | refl_ring1 | ring
  have hlam : asZAA D g * asZlamA D g
      = asZmuA D g * asZBA D g + asZAA D g * (asZaA D g ^ 2 + asZbA D g ^ 2) := by
    rw [asZlamA]
    field_simp [hA]
  have hgoal : (asZOmA D g 0)⁻¹ =
      -(asZAA D g / asZmuA D g) * (kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g)
          (asZwA D g) +
        (asZlamA D g / asZmuA D g) * kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g)
          (asZwA D g)) := by
    have hkey : (asZOmA D g 0)⁻¹ * (asZmuA D g * asZmuA D g)
        + asZAA D g * asZmuA D g * kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g)
        + asZAA D g * asZlamA D g * kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g)
            (asZwA D g) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) (asZAA D g * asZmuA D g) * hR1
        + (asZAA D g * asZlamA D g) * hR3
        - (asZmuA D g * asZmuA D g * (asZOmA D g 0)⁻¹) * hAw
        - (asZmuA D g * asZwA3 D g * (asZOmA D g 0)⁻¹) * hlam
    have hμ2 : asZmuA D g * asZmuA D g ≠ 0 := mul_ne_zero hmu hmu
    have h4 : asZmuA D g * asZmuA D g * (asZOmA D g 0)⁻¹
        = -(asZAA D g) * (asZmuA D g * kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g)
              (asZwA D g)
          + asZlamA D g * kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g)) := by
      linear_combination (norm := first | refl_ring1 | ring1) hkey
    have h5 : (asZOmA D g 0)⁻¹
        = -(asZAA D g) * (asZmuA D g * kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g)
              (asZwA D g)
            + asZlamA D g * kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g))
          / (asZmuA D g * asZmuA D g) := by
      rw [eq_div_iff hμ2]
      linear_combination (norm := first | refl_ring1 | ring1) h4
    rw [h5]
    field_simp [hmu]
  exact ⟨⟨hp1, hp2, hp3, hp4⟩, hgoal⟩

end Work.MotV5.Contrib
