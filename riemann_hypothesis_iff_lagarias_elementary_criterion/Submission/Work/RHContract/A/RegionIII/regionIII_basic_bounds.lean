import Mathlib
import Submission.Work.RHContract.A.RegionIII.caRegionIIIDefs

/-!
# Region III: the basic quantitative bounds

For `ξ = caXiR ε ≥ 10^8` we record the elementary consequences of the definition
`caN ε = ⌊√(2.5 ξ)⌋₊ + 1` that the Region III estimates use: the size of `log ξ`,
the two-sided comparison of `log (caN ε)` with `log ξ / 2`, the two-sided
comparison of `caN ε` with `√ξ`, the lower bound `caN ε ≥ 15000`, the comparison
`caN ε ≤ caXi ε`, and `ξ ≤ (caN ε)²`.

The only non-elementary inputs are the decimal bounds on `log 2`, `log 5`
(Mathlib: `Real.log_two_gt_d9`, `Real.log_two_lt_d9`, `Real.log_five_gt_d9`,
`Real.log_five_lt_d9`) from which the rational bounds
`0.88 ≤ log 2.5 ≤ 0.92` and `log 1.6 ≤ 0.475` are derived.
-/

namespace Work.RHContract.A.RegionIII

noncomputable section

private lemma log_two_le_d10 : Real.log 2 ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
private lemma log_two_ge_d10 : 0.6931471803 ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
private lemma log_five_ge_d10 : 1.6094379123 ≤ Real.log 5 := le_of_lt Real.log_five_gt_d9
private lemma log_five_le_d10 : Real.log 5 ≤ 1.6094379126 := le_of_lt Real.log_five_lt_d9

/-- `log 2.5 ∈ [0.88, 0.92]`. -/
private lemma log_two_point_five_bounds : 0.88 ≤ Real.log 2.5 ∧ Real.log 2.5 ≤ 0.92 := by
  have h : Real.log 2.5 = Real.log 5 - Real.log 2 := by
    rw [show (2.5 : ℝ) = 5 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  constructor <;> linarith [h, log_two_le_d10, log_two_ge_d10, log_five_ge_d10, log_five_le_d10]

/-- `log 1.6 ≤ 0.475`. -/
private lemma log_one_point_six_le : Real.log 1.6 ≤ 0.475 := by
  have h : Real.log 1.6 = 3 * Real.log 2 - Real.log 5 := by
    rw [show (1.6 : ℝ) = 2 ^ 3 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  linarith [h, log_two_le_d10, log_five_ge_d10]

/-- `1.581138 ≤ √2.5`. -/
private lemma sqrt_two_point_five_lower : 1.581138 ≤ Real.sqrt 2.5 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- `√2.5 ≤ 1.58114`. -/
private lemma sqrt_two_point_five_upper : Real.sqrt 2.5 ≤ 1.58114 := by
  exact le_of_lt
    ((Real.sqrt_lt' (x := 2.5) (show (0 : ℝ) < 1.58114 by norm_num)).mpr (by norm_num))

/-- `10^4 ≤ √x` for `x ≥ 10^8`. -/
private lemma ten_pow_four_le_sqrt_self {x : ℝ} (hx : (10 : ℝ) ^ 8 ≤ x) :
    (10 : ℝ) ^ 4 ≤ Real.sqrt x := by
  have h1 : ((10 : ℝ) ^ 4) ^ 2 = (10 : ℝ) ^ 8 := by norm_num
  calc (10 : ℝ) ^ 4 = Real.sqrt (((10 : ℝ) ^ 4) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by rw [h1]; exact hx)

/-- `1.581138 √x ≤ √2.5 √x` for `x ≥ 0`. -/
private lemma le_sqrt_two_point_five_mul {x : ℝ} (hx : 0 ≤ x) :
    1.581138 * Real.sqrt x ≤ Real.sqrt 2.5 * Real.sqrt x := by
  have h1 := sqrt_two_point_five_lower
  have h2 := Real.sqrt_nonneg x
  nlinarith [h1, h2]

/-- `√2.5 √x ≤ 1.58114 √x` for `x ≥ 0`. -/
private lemma sqrt_two_point_five_mul_le {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt 2.5 * Real.sqrt x ≤ 1.58114 * Real.sqrt x := by
  have h1 := sqrt_two_point_five_upper
  have h2 := Real.sqrt_nonneg x
  nlinarith [h1, h2]

/-- `15000 < √2.5 √x` for `x ≥ 10^8`. -/
private lemma fifteen_thousand_lt_sqrt_mul {x : ℝ} (hx : (10 : ℝ) ^ 8 ≤ x) :
    (15000 : ℝ) < Real.sqrt 2.5 * Real.sqrt x := by
  have h1 := sqrt_two_point_five_lower
  have h2 := ten_pow_four_le_sqrt_self hx
  have h3 := Real.sqrt_nonneg x
  nlinarith [h1, h2, h3]

/-- `√2.5 √x < x - 1` for `x ≥ 10^8`. -/
private lemma sqrt_two_point_five_mul_sqrt_lt {x : ℝ} (hx : (10 : ℝ) ^ 8 ≤ x) :
    Real.sqrt 2.5 * Real.sqrt x < x - 1 := by
  have hxpos : 0 < x := by linarith
  have h1 := sqrt_two_point_five_upper
  have h2 := ten_pow_four_le_sqrt_self hx
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  have h4 := Real.sqrt_nonneg x
  nlinarith [h1, h2, h3, h4]

theorem regionIII_basic_bounds (ε : ℝ) (hξ : (10 : ℝ) ^ 8 ≤ Work.RHContract.A.RegionIII.caXiR ε) :
    18.2 ≤ Work.RHContract.A.RegionIII.caL ε
      ∧ (Work.RHContract.A.RegionIII.caL ε + 0.88) / 2 ≤ Real.log (Work.RHContract.A.RegionIII.caN ε)
      ∧ Real.log (Work.RHContract.A.RegionIII.caN ε) ≤ (Work.RHContract.A.RegionIII.caL ε + 0.95) / 2
      ∧ 1.581138 * Real.sqrt (Work.RHContract.A.RegionIII.caXiR ε) ≤ (Work.RHContract.A.RegionIII.caN ε : ℝ)
      ∧ (Work.RHContract.A.RegionIII.caN ε : ℝ) ≤ 1.58125 * Real.sqrt (Work.RHContract.A.RegionIII.caXiR ε)
      ∧ 15000 ≤ Work.RHContract.A.RegionIII.caN ε
      ∧ Work.RHContract.A.RegionIII.caN ε ≤ Work.RHPlan.caXi ε
      ∧ Work.RHContract.A.RegionIII.caXiR ε ≤ (Work.RHContract.A.RegionIII.caN ε : ℝ) ^ 2 := by
  obtain ⟨hlog25lo, _⟩ := log_two_point_five_bounds
  have hξpos : 0 < caXiR ε := by
    have : (0 : ℝ) < (10 : ℝ) ^ 8 := by norm_num
    linarith
  have hsqrtξ_nonneg : (0 : ℝ) ≤ Real.sqrt (caXiR ε) := Real.sqrt_nonneg _
  have hsqrtξ_ge : (10 : ℝ) ^ 4 ≤ Real.sqrt (caXiR ε) := ten_pow_four_le_sqrt_self hξ
  set s : ℝ := Real.sqrt (2.5 * caXiR ε) with hsdef
  have hNval : (caN ε : ℝ) = (Nat.floor s : ℝ) + 1 := by rw [caN]; push_cast; ring
  have hs_pos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr (by linarith)
  have hs_nonneg : (0 : ℝ) ≤ s := le_of_lt hs_pos
  have hNs : s < (caN ε : ℝ) := by rw [hNval]; exact Nat.lt_floor_add_one s
  have hNle : (caN ε : ℝ) ≤ s + 1 := by
    rw [hNval]
    have := Nat.floor_le hs_nonneg
    linarith
  have hN_pos : (0 : ℝ) < caN ε := by linarith
  have hs_eq : s = Real.sqrt 2.5 * Real.sqrt (caXiR ε) := by
    rw [hsdef, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2.5)]
  have hC1 : 18.2 ≤ caL ε := by
    have hlog10 : (18.2 : ℝ) ≤ Real.log ((10 : ℝ) ^ 8) := by
      rw [Real.log_pow, Real.log_ten_eq]
      have h2 := log_two_ge_d10
      have h5 := log_five_ge_d10
      push_cast
      linarith
    rw [caL]
    exact le_trans hlog10 (Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 8) hξ)
  have hC4 : 1.581138 * Real.sqrt (caXiR ε) ≤ (caN ε : ℝ) := by
    have h1 : 1.581138 * Real.sqrt (caXiR ε) ≤ s := by
      rw [hs_eq]
      exact le_sqrt_two_point_five_mul (le_of_lt hξpos)
    linarith
  have hC5 : (caN ε : ℝ) ≤ 1.58125 * Real.sqrt (caXiR ε) := by
    have h1 : s ≤ 1.58114 * Real.sqrt (caXiR ε) := by
      rw [hs_eq]
      exact sqrt_two_point_five_mul_le (le_of_lt hξpos)
    have h2 : (1 : ℝ) ≤ 0.00011 * Real.sqrt (caXiR ε) := by
      have := hsqrtξ_ge
      nlinarith
    nlinarith [hNle, h1, h2]
  have hC6 : 15000 ≤ caN ε := by
    have h : (15000 : ℝ) < (caN ε : ℝ) := by
      have h1 : (15000 : ℝ) < s := by
        rw [hs_eq]
        exact fifteen_thousand_lt_sqrt_mul hξ
      linarith
    exact_mod_cast h.le
  have hC2 : (caL ε + 0.88) / 2 ≤ Real.log (caN ε) := by
    have hlogN : Real.log s ≤ Real.log (caN ε) := Real.log_le_log hs_pos (le_of_lt hNs)
    have hlogs : Real.log s = Real.log 2.5 / 2 + caL ε / 2 := by
      rw [hs_eq, Real.log_mul (Real.sqrt_pos.mpr (by norm_num)).ne' (Real.sqrt_pos.mpr hξpos).ne',
        Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2.5), Real.log_sqrt (le_of_lt hξpos), caL]
    have : (caL ε + 0.88) / 2 ≤ Real.log s := by rw [hlogs]; linarith
    linarith
  have hC3 : Real.log (caN ε) ≤ (caL ε + 0.95) / 2 := by
    have hlogN : Real.log (caN ε) ≤ Real.log (s + 1) := Real.log_le_log hN_pos (by linarith)
    have hs1pos : 0 < Real.sqrt 2.5 + 1 / Real.sqrt (caXiR ε) := by
      have h1 : 0 < Real.sqrt 2.5 := Real.sqrt_pos.mpr (by norm_num)
      have h2 : 0 ≤ 1 / Real.sqrt (caXiR ε) := by positivity
      linarith
    have hs1 : s + 1 = Real.sqrt (caXiR ε) * (Real.sqrt 2.5 + 1 / Real.sqrt (caXiR ε)) := by
      rw [hs_eq]
      field_simp
    have hlogs1 : Real.log (s + 1)
        = caL ε / 2 + Real.log (Real.sqrt 2.5 + 1 / Real.sqrt (caXiR ε)) := by
      rw [hs1, Real.log_mul (Real.sqrt_pos.mpr hξpos).ne' hs1pos.ne', Real.log_sqrt (le_of_lt hξpos),
        caL]
    have hub : Real.sqrt 2.5 + 1 / Real.sqrt (caXiR ε) ≤ 1.6 := by
      have h1 := sqrt_two_point_five_upper
      have h2 : 1 / Real.sqrt (caXiR ε) ≤ 0.0001 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10 ^ 4) hsqrtξ_ge
        norm_num at h ⊢
        exact h
      linarith
    have hlogub : Real.log (Real.sqrt 2.5 + 1 / Real.sqrt (caXiR ε)) ≤ 0.475 := by
      have h := Real.log_le_log hs1pos hub
      have h2 := log_one_point_six_le
      linarith
    have : Real.log (s + 1) ≤ (caL ε + 0.95) / 2 := by rw [hlogs1]; linarith
    linarith
  have hC7 : caN ε ≤ Work.RHPlan.caXi ε := by
    have h : (caN ε : ℝ) ≤ caXiR ε := by
      have hs_le : s + 1 ≤ caXiR ε := by
        have hslt : s < caXiR ε - 1 := by
          rw [hs_eq]
          exact sqrt_two_point_five_mul_sqrt_lt hξ
        linarith
      linarith
    exact_mod_cast (show (caN ε : ℝ) ≤ ((Work.RHPlan.caXi ε : ℕ) : ℝ) from h)
  have hC8 : caXiR ε ≤ (caN ε : ℝ) ^ 2 := by
    have hs2 : s ^ 2 = 2.5 * caXiR ε := by
      rw [hsdef]; exact Real.sq_sqrt (by linarith)
    have : s ^ 2 < (caN ε : ℝ) ^ 2 := pow_lt_pow_left₀ hNs hs_nonneg (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  exact ⟨hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8⟩

end

end Work.RHContract.A.RegionIII
