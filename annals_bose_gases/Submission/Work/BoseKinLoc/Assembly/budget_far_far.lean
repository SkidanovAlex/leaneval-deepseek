import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseKinLoc.Assembly.tprR_branches_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Assembly

/-- Pointwise quadratic bound: for `0 < a` and `(5/3) a ≤ Q` one has
`(Q - a)^2 + (7/3) a^2 ≤ Q^2`.  Equivalently `Q^2 - ((Q-a)^2 + (7/3)a^2) = 2a(Q - (5/3)a) ≥ 0`. -/
private lemma budget_far_far_quad (Q a : ℝ) (ha : 0 < a) (hQ : (5 / 3) * a ≤ Q) :
    (Q - a) ^ 2 + (7 / 3) * a ^ 2 ≤ Q ^ 2 := by
  have h2 : 0 ≤ Q - (5 / 3) * a := by linarith
  have h3 : 0 ≤ 2 * a * (Q - (5 / 3) * a) := by
    have : (0 : ℝ) ≤ 2 * a := by linarith
    exact mul_nonneg this h2
  have h4 : Q ^ 2 - ((Q - a) ^ 2 + (7 / 3) * a ^ 2) = 2 * a * (Q - (5 / 3) * a) := by ring
  linarith [h3, h4]

theorem budget_far_far (β q d s εT b : ℝ) (hβ : 0 < β)
    (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s) (hε : 0 ≤ εT) (hε1 : εT ≤ 1) (hb : 0 ≤ b)
    (hfar1 : (5 / 6) * (2 * s)⁻¹ ≤ q) (hfar2 : (5 / 6) * (2 * (d * s))⁻¹ ≤ q)
    (hslack : εT / d ^ 2 + b * β⁻¹
        ≤ (1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2) + εT * ((7 / 3) * ((4 * (d * s))⁻¹) ^ 2)) :
    εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) + b * β⁻¹ * (q ^ 2 / (q ^ 2 + β))
      + (1 - εT) * (q - (2 * (2 * s))⁻¹) ^ 2 + εT * (q - (2 * (2 * (d * s)))⁻¹) ^ 2
      ≤ q ^ 2 := by
  -- ### The two "far" cut-off positions and their positivity
  have ha : (0 : ℝ) < (2 * (2 * s))⁻¹ := by
    have : (0 : ℝ) < 2 * (2 * s) := by linarith
    exact inv_pos.mpr this
  have hc : (0 : ℝ) < (2 * (2 * (d * s)))⁻¹ := by
    have : (0 : ℝ) < 2 * (2 * (d * s)) := by positivity
    exact inv_pos.mpr this
  -- `(5/3)(2(2s))⁻¹ = (5/6)(2s)⁻¹` so `hfar1` is exactly the far condition for `a = (2(2s))⁻¹`
  have hqa : (5 / 3) * (2 * (2 * s))⁻¹ ≤ q := by
    have heq : (5 / 3) * (2 * (2 * s))⁻¹ = (5 / 6) * (2 * s)⁻¹ := by
      field_simp
      ring
    rw [heq]; exact hfar1
  have hqc : (5 / 3) * (2 * (2 * (d * s)))⁻¹ ≤ q := by
    have heq : (5 / 3) * (2 * (2 * (d * s)))⁻¹ = (5 / 6) * (2 * (d * s))⁻¹ := by
      field_simp
      ring
    rw [heq]; exact hfar2
  -- ### The two quadratic cut-off bounds `(q-a)² + (7/3)a² ≤ q²`
  have hq1 : (q - (2 * (2 * s))⁻¹) ^ 2 + (7 / 3) * ((4 * s)⁻¹) ^ 2 ≤ q ^ 2 := by
    have e1 : (4 * s)⁻¹ = (2 * (2 * s))⁻¹ := by
      rw [show (2 * (2 * s)) = 4 * s by ring]
    rw [e1]
    exact budget_far_far_quad q ((2 * (2 * s))⁻¹) ha hqa
  have hq2 : (q - (2 * (2 * (d * s)))⁻¹) ^ 2 + (7 / 3) * ((4 * (d * s))⁻¹) ^ 2 ≤ q ^ 2 := by
    have e2 : (4 * (d * s))⁻¹ = (2 * (2 * (d * s)))⁻¹ := by
      rw [show (2 * (2 * (d * s))) = 4 * (d * s) by ring]
    rw [e2]
    exact budget_far_far_quad q ((2 * (2 * (d * s)))⁻¹) hc hqc
  -- ### The two "localised" pieces are dominated by the slack terms
  have h1 : εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ εT / d ^ 2 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + d ^ 2 * q ^ 2)
      (by positivity : (0 : ℝ) < d ^ 2)]
    nlinarith [hε]
  have h2 : b * β⁻¹ * (q ^ 2 / (q ^ 2 + β)) ≤ b * β⁻¹ := by
    have hbβ : (0 : ℝ) ≤ b * β⁻¹ := by positivity
    have hr : q ^ 2 / (q ^ 2 + β) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < q ^ 2 + β)]
      linarith [hβ]
    simpa using mul_le_mul_of_nonneg_left hr hbβ
  -- ### Assembly
  have h1mE : (0 : ℝ) ≤ 1 - εT := by linarith
  have hs1 : (1 - εT) * ((q - (2 * (2 * s))⁻¹) ^ 2) + (1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2)
      ≤ (1 - εT) * q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hq1 h1mE
    nlinarith [this]
  have hs2 : εT * ((q - (2 * (2 * (d * s)))⁻¹) ^ 2) + εT * ((7 / 3) * ((4 * (d * s))⁻¹) ^ 2)
      ≤ εT * q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hq2 hε
    nlinarith [this]
  nlinarith [h1, h2, hslack, hs1, hs2]

end Work.BoseKinLoc.Assembly
