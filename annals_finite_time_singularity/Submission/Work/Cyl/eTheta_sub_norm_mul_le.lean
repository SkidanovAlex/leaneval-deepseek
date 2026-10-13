import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.norm_angularVec
import Submission.Work.Cyl.inner_angularVec
import Submission.Work.Cyl.abs_inner_angularVec_le
import Submission.Work.Cyl.radial_sq_sub_coord_le_dist_sq
import Submission.Work.Cyl.abs_radial_sub_le_dist
import Submission.Work.Cyl.scalar_arith_key

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Lipschitz bound for the angular frame vector `e_θ`

`e_θ(x) = r(x) e_θ(x) / r(x)` is a unit vector off the axis `r = 0`, but is `0` *on* the axis
(`eTheta` is defined as `(1/r) • angularVec` and `angularVec = 0` when `r = 0`), so it is
discontinuous there.  The geometric input needed by the paper is that the jump is controlled once
weighted by the radius: for all `x y : ℝ³`,

  `‖e_θ x - e_θ y‖ * r(y) ≤ 2 * dist x y`.

Proof.  Write `r = r(x)`, `s = r(y)`, `A = r e_θ(x) = (-x₁, x₀, 0)` and `B = r e_θ(y)`, so that
`e_θ(x) = (1/r) • A`, `e_θ(y) = (1/s) • B`, and `s • (e_θ x - e_θ y) = (s/r) • A - B`.

* If `r = 0` then `A = 0` and the left hand side is `‖B‖ = s ≤ |r - s| ≤ dist x y` (`r` is
  1-Lipschitz, `Work.Cyl.abs_radial_sub_le_dist`).
* If `r > 0`, multiplying by `r` reduces the claim to `‖s • A - r • B‖ ≤ 2 r * dist x y`.  Its
  square is `2 r² s² - 2 r s c` with `c = ⟪A,B⟫ = x₀y₀ + x₁y₁`, while
  `dist x y ² ≥ r² + s² - 2c`.  Comparing the two reduces the claim to the elementary arithmetic
  fact `0 ≤ 2r³ + r s² + c (s - 4r)` for `|c| ≤ r s` (`Work.Cyl.scalar_arith_key`), proved by a
  two-case linear argument in `c`.

The constant `2` is optimal but not attained: for `y = (1,0,0)` (so `e_θ y = (0,1,0)`) and
`x = ε • (-1,0,0)` (so `e_θ x = (0,-1,0)`) the two sides are `2` and `2(1+ε)`, whose ratio tends
to `1` as `ε → 0⁺`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix

namespace Work.Cyl

/-- `r e_θ = angularVec`: the angular frame vector scaled by the distance to the axis is the
(smooth) angular coordinate vector. -/
private lemma radial_smul_eTheta (x : R3) : radial x • eTheta x = angularVec x := by
  by_cases h : radial x = 0
  · have hA : angularVec x = 0 := by
      obtain ⟨h1, h2⟩ := (radial_eq_zero_iff x).mp h
      refine ext_coord ?_ ?_ ?_ <;> simp [angularVec, h1, h2]
    simp [eTheta, h, hA]
  · rw [eTheta, one_div, smul_smul, mul_inv_cancel₀ h, one_smul]

theorem eTheta_sub_norm_mul_le (x y : Work.Cyl.R3) :
    ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ * Work.Cyl.radial y ≤ 2 * dist x y := by
  have h1 : ‖eTheta x - eTheta y‖ * radial y = ‖radial y • (eTheta x - eTheta y)‖ := by
    rw [norm_smul_of_nonneg (radial_nonneg y), mul_comm]
  rw [h1]
  have hsmul : radial y • (eTheta x - eTheta y)
      = (radial y / radial x) • angularVec x - angularVec y := by
    rw [smul_sub]
    congr 1
    · simp only [eTheta, one_div, div_eq_mul_inv, one_mul, smul_smul]
    · rw [radial_smul_eTheta]
  rw [hsmul]
  by_cases h0 : radial x = 0
  · -- `x` is on the axis: `e_θ x = 0` and the claim is `r(y) ≤ 2 dist x y`
    have hA0 : angularVec x = 0 := by
      obtain ⟨h1, h2⟩ := (radial_eq_zero_iff x).mp h0
      refine ext_coord ?_ ?_ ?_ <;> simp [angularVec, h1, h2]
    rw [h0, hA0]
    simp only [div_zero, zero_smul, zero_sub, norm_neg]
    rw [norm_angularVec]
    have hb : radial y = |radial x - radial y| := by
      rw [h0, zero_sub, abs_neg, abs_of_nonneg (radial_nonneg y)]
    rw [hb]
    linarith [abs_radial_sub_le_dist x y, abs_nonneg (radial x - radial y)]
  · -- off the axis: reduce to a squared estimate
    have hpos : 0 < radial x := lt_of_le_of_ne (radial_nonneg x) (Ne.symm h0)
    have hcoef : radial x * (radial y * (radial x)⁻¹) = radial y := by
      rw [← mul_assoc, mul_comm (radial x) (radial y), mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
    have hkey : radial x • ((radial y / radial x) • angularVec x - angularVec y)
        = radial y • angularVec x - radial x • angularVec y := by
      rw [smul_sub, smul_smul, div_eq_mul_inv, hcoef]
    have hmain : ‖radial y • angularVec x - radial x • angularVec y‖
        ≤ 2 * radial x * dist x y := by
      have hc : |x 0 * y 0 + x 1 * y 1| ≤ radial x * radial y := by
        rw [← inner_angularVec]; exact abs_inner_angularVec_le x y
      have hscal := scalar_arith_key (radial x) (radial y) (x 0 * y 0 + x 1 * y 1)
        (radial_nonneg x) (radial_nonneg y) hc
      have hAA : inner ℝ (angularVec x) (angularVec x) = radial x ^ 2 := by
        rw [real_inner_self_eq_norm_sq, norm_angularVec]
      have hBB : inner ℝ (angularVec y) (angularVec y) = radial y ^ 2 := by
        rw [real_inner_self_eq_norm_sq, norm_angularVec]
      have hAB : inner ℝ (angularVec x) (angularVec y) = x 0 * y 0 + x 1 * y 1 :=
        inner_angularVec x y
      have hBA : inner ℝ (angularVec y) (angularVec x) = x 0 * y 0 + x 1 * y 1 := by
        rw [inner_angularVec]; ring
      have hsqL : ‖radial y • angularVec x - radial x • angularVec y‖ ^ 2
          = 2 * radial x ^ 2 * radial y ^ 2
            - 2 * radial x * radial y * (x 0 * y 0 + x 1 * y 1) := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
          real_inner_smul_right, hAA, hBB, hAB, hBA]
        ring
      have hβ := radial_sq_sub_coord_le_dist_sq x y
      have hX : 0 ≤ 2 * radial x * dist x y := by positivity
      have hβ' : 4 * radial x ^ 2
            * (radial x ^ 2 + radial y ^ 2 - 2 * (x 0 * y 0 + x 1 * y 1))
          ≤ 4 * radial x ^ 2 * dist x y ^ 2 :=
        mul_le_mul_of_nonneg_left hβ (by positivity)
      have hscal' : 0 ≤ 2 * radial x
          * (2 * radial x ^ 3 + radial x * radial y ^ 2
              + (x 0 * y 0 + x 1 * y 1) * (radial y - 4 * radial x)) :=
        mul_nonneg (by positivity) hscal
      have hsq : ‖radial y • angularVec x - radial x • angularVec y‖ ^ 2
          ≤ (2 * radial x * dist x y) ^ 2 := by
        rw [hsqL]
        nlinarith [hβ', hscal']
      rw [sq_le_sq] at hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hX] at hsq
    have hz : radial x * ‖(radial y / radial x) • angularVec x - angularVec y‖
        = ‖radial y • angularVec x - radial x • angularVec y‖ := by
      rw [← hkey, norm_smul_of_nonneg (le_of_lt hpos)]
    refine le_of_mul_le_mul_left ?_ hpos
    rw [hz]
    calc ‖radial y • angularVec x - radial x • angularVec y‖
        ≤ 2 * radial x * dist x y := hmain
      _ = radial x * (2 * dist x y) := by ring

end Work.Cyl
