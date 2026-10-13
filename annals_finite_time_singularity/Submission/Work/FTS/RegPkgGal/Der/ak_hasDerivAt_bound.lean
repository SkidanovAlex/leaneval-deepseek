import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs
import Submission.Work.FTS.NonlinRows.AkRhoJetBasic
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

/-! ## Bounding the `z`-derivative of `AK`

`AK α z θ = (Γ(θ)/c)(2z²/(1+z)³)` is the correction profile of the modulation
(`Work.Construction.AK`).  Its `z`-derivative is
`(Γ(θ)/c)·2z(2-z)/(1+z)⁴`, and the two factors are bounded by `10` (`0 ≤ Γ ≤ 1` and
`1/10 ≤ c ≤ 10`) and by `2` respectively. -/

/-- The radial factor `2z(2-z)/(1+z)⁴` of `∂_z AK` is bounded by `2` on `(0,∞)`. -/
theorem abs_akPsi_deriv_le_two {z : ℝ} (hz : 0 < z) :
    |2 * z * (2 - z) / (1 + z) ^ 4| ≤ 2 := by
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have hden : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ h1z
  have hpos : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  rcases le_or_gt z 2 with hz2 | hz2
  · have hnum : (0 : ℝ) ≤ 2 * z * (2 - z) := by nlinarith
    rw [abs_of_nonneg (div_nonneg hnum hpos.le), div_le_iff₀ hpos]
    have h2 : 2 * z * (2 - z) ≤ 2 := by nlinarith [sq_nonneg (z - 1)]
    nlinarith [h2, hden]
  · have hnum : 2 * z * (2 - z) ≤ 0 := by nlinarith
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum hpos.le), ← neg_div,
      div_le_iff₀ hpos]
    have hz1 : (1 : ℝ) ≤ z := by linarith
    have hsq : z ^ 2 ≤ (1 + z) ^ 4 :=
      le_trans (pow_le_pow_right₀ hz1 (by norm_num : 2 ≤ 4))
        (pow_le_pow_left₀ hz.le (by linarith) 4)
    have h1 : -(2 * z * (2 - z)) ≤ 2 * z ^ 2 := by nlinarith
    have h2 : 2 * z ^ 2 ≤ 2 * (1 + z) ^ 4 := by linarith
    linarith

/-- The coefficient `Γ(θ)/c` of `AK` is bounded by `10` in absolute value on `Iθ`. -/
theorem abs_gam_div_c_le_ten (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Gam a θ / Work.Spaces.c a| ≤ 10 := by
  have hG := Work.Spaces.Gam_bounds a θ ha hθ
  have hc := Work.Spaces.c_bounds a ha ha1
  have hcpos : (0 : ℝ) < Work.Spaces.c a := by linarith [hc.1]
  rw [abs_div, abs_of_nonneg hG.1, abs_of_pos hcpos, div_le_iff₀ hcpos]
  linarith [hG.2, hc.1]

theorem ak_hasDerivAt_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {θ z : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.AK a z' θ) d z ∧ |d| ≤ 20 := by
  have hz1 : z ≠ -1 := by intro h; linarith
  refine ⟨(Work.Spaces.Gam a θ / Work.Spaces.c a) * (2 * z * (2 - z) / (1 + z) ^ 4),
    ?_, ?_⟩
  · have hd : HasDerivAt
        (fun z' : ℝ => (Work.Spaces.Gam a θ / Work.Spaces.c a)
          * (2 * z' ^ 2 / (1 + z') ^ 3))
        ((Work.Spaces.Gam a θ / Work.Spaces.c a)
          * (2 * z * (2 - z) / (1 + z) ^ 4)) z :=
      (Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_akPsi hz1).const_mul _
    convert hd using 1
    funext z'
    rw [Work.Construction.AK]
  · rw [abs_mul]
    calc |Work.Spaces.Gam a θ / Work.Spaces.c a| * |2 * z * (2 - z) / (1 + z) ^ 4|
        ≤ 10 * 2 :=
          mul_le_mul (abs_gam_div_c_le_ten a ha ha1 hθ) (abs_akPsi_deriv_le_two hz)
            (abs_nonneg _) (by norm_num)
      _ = 20 := by norm_num

end Work.FTS.RegPkgGal.Der
