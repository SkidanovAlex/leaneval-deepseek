import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp

namespace Work.BourgainPlan.Maximal

/-- **Dyadic step decay of the polynomial profile.**

For `d = P.natDegree ≥ 2`, two dyadic scales `2^k ≤ 2^{k'}` have profiles differing by at most the
sharp decay bound at the *smaller* scale: writing `X = |β| · (2^k)^d`, for `X ≥ 1`,

`‖Φ_{2^{k'}}(β) - Φ_{2^k}(β)‖ ≤ C · X^{-1/d}`.

This is immediate from the sharp van der Corput decay `polyProfile_decay_sharp` (each scale is
`≲ X^{-1/d}`, because the *larger* scale `2^{k'}` only has stronger decay) plus the triangle
inequality. -/
theorem polyProfile_step_diff_decay (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k k' : ℕ), k ≤ k' → ∀ β : ℝ,
      1 ≤ |β| * ((2 : ℝ) ^ k) ^ P.natDegree →
      ‖polyProfile P (2 ^ k') β - polyProfile P (2 ^ k) β‖
        ≤ C * (|β| * ((2 : ℝ) ^ k) ^ P.natDegree) ^ (-(1 / (P.natDegree : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := polyProfile_decay_sharp P hd
  refine ⟨2 * C, by positivity, ?_⟩
  intro k k' hkk β hX
  have hdil : ∀ j : ℕ, polyDil P j = ((2 : ℝ) ^ j) ^ P.natDegree := fun j => rfl
  have hβpos : 0 < |β| := by
    have h2 : (0 : ℝ) < ((2 : ℝ) ^ k) ^ P.natDegree := by positivity
    nlinarith [hX, h2, abs_nonneg β]
  have hβ : β ≠ 0 := abs_pos.mp hβpos
  have hXk : 1 ≤ |β| * polyDil P k := by rw [hdil k]; exact hX
  have hle_dil : polyDil P k ≤ polyDil P k' := by
    rw [hdil k, hdil k']
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hkk) _
  have hXk' : 1 ≤ |β| * polyDil P k' :=
    le_trans hXk (mul_le_mul_of_nonneg_left hle_dil (abs_nonneg β))
  have h1 := hC β hβ k' hXk'
  have h2 := hC β hβ k hXk
  have hbase_pos : 0 < |β| * polyDil P k := lt_of_lt_of_le (by norm_num) hXk
  have hmono : (|β| * polyDil P k') ^ (-(1 / (P.natDegree : ℝ)))
      ≤ (|β| * polyDil P k) ^ (-(1 / (P.natDegree : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos hbase_pos
      (mul_le_mul_of_nonneg_left hle_dil (abs_nonneg β))
      (neg_nonpos.mpr (by positivity))
  calc ‖polyProfile P (2 ^ k') β - polyProfile P (2 ^ k) β‖
      ≤ ‖polyProfile P (2 ^ k') β‖ + ‖polyProfile P (2 ^ k) β‖ := norm_sub_le _ _
    _ ≤ C * (|β| * polyDil P k') ^ (-(1 / (P.natDegree : ℝ)))
          + C * (|β| * polyDil P k) ^ (-(1 / (P.natDegree : ℝ))) := add_le_add h1 h2
    _ ≤ C * (|β| * polyDil P k) ^ (-(1 / (P.natDegree : ℝ)))
          + C * (|β| * polyDil P k) ^ (-(1 / (P.natDegree : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left hmono hCpos.le) le_rfl
    _ = 2 * C * (|β| * polyDil P k) ^ (-(1 / (P.natDegree : ℝ))) := by ring
    _ = 2 * C * (|β| * ((2 : ℝ) ^ k) ^ P.natDegree) ^ (-(1 / (P.natDegree : ℝ))) := by
        rw [hdil k]

end Work.BourgainPlan.Maximal
