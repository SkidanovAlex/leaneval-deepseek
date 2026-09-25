import Mathlib
import Submission.Work.LT.gb_num_defs
import Submission.Work.LT.gb_num_r5
import Submission.Work.LT.gb_num_x_bound

namespace Work.LT

/-- For `2 ≤ m ≤ r`, the exponent `gbNumE r m` is at most `gbNumE r 2 - (r/8)(m-2)`.
This is the pointwise comparison that converts the sum into a geometric series. -/
lemma gbNumE_pointwise (r m : ℕ) (hm2 : 2 ≤ m) (hmr : m ≤ r) :
    gbNumE r m ≤ gbNumE r 2 - (r:ℝ)/8 * ((m-2:ℕ):ℝ) := by
  have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
  have h_mr : (m:ℝ) ≤ (r:ℝ) := by exact_mod_cast hmr
  have hcast : ((m - (m+1)/2 : ℕ):ℝ) = (m:ℝ) - (((m+1)/2:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : (m+1)/2 ≤ m)]
  have hkg : (m:ℝ)/2 ≤ (((m+1)/2:ℕ):ℝ) := by
    have h : (m:ℕ) ≤ 2*((m+1)/2) := by omega
    have h2 : (m:ℝ) ≤ 2*(((m+1)/2:ℕ):ℝ) := by exact_mod_cast h
    linarith
  have hamgm : (((m+1)/2:ℕ):ℝ) * ((m-(m+1)/2:ℕ):ℝ) ≤ (m:ℝ)^2/4 := by
    rw [hcast]
    nlinarith [sq_nonneg ((m:ℝ) - 2*(((m+1)/2:ℕ):ℝ))]
  have hm2r : ((m-2:ℕ):ℝ) = (m:ℝ) - 2 := by
    rw [Nat.cast_sub hm2]; norm_num
  have hmul : (r:ℝ)*((m:ℝ)/2) ≤ (r:ℝ)*(((m+1)/2:ℕ):ℝ) := mul_le_mul_of_nonneg_left hkg hr0
  have h2 : (((2+1)/2:ℕ):ℝ) = 1 := by norm_num
  simp only [gbNumE, gbNumC]
  rw [hm2r]
  simp only [h2]
  nlinarith [hamgm, hmul, h_mr, hr0]

/-- The finite geometric sum `∑_{k<n} x^k` is at most `1/(1-x)` for `0 ≤ x < 1`. -/
lemma gbGeomLe {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, x^k ≤ 1/(1-x) := by
  have hpos : 0 < 1 - x := by linarith
  rw [le_div_iff₀ hpos]
  rw [geom_sum_mul_neg x n]
  have : (0:ℝ) ≤ x^n := by positivity
  linarith

/-- `∑_{m=a}^{b} x^(m-a) ≤ 1/(1-x)` for `0 ≤ x < 1`. -/
lemma gbSumIccPowLe {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (a b : ℕ) :
    ∑ m ∈ Finset.Icc a b, x^(m-a) ≤ 1/(1-x) := by
  have hIcc : Finset.Icc a b = Finset.Ico a (b+1) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have h1 : ∀ k, x^((a+k)-a) = x^k := by intro k; congr 1; omega
  simp only [h1]
  exact gbGeomLe hx0 hx1 _

/-- Numerical inequality behind the union bound in `gb_card_fail_star_alt`, with `k(m) = ⌈m/2⌉ = (m+1)/2`:
`∑_{m=1}^{r} 2^{v m + k(m)(m - k(m)) + 2 - r·k(m)} ≤ 2^{-r/8}` for `r ≥ 5`, `0 ≤ v ≤ (r-4)/8`.
Each summand is increasing in `v`, so take `v = (r-4)/8`. Let `E(m)` be the exponent and `e(m) = E(m) + r/8`. Then `E(1) ≤ -7r/8 + 3/2`, `E(2) ≤ 2 - 3r/4`, and for `3 ≤ m ≤ r`, `E(m) ≤ E(2) - (r/8)(m-2)` (from the piecewise-quadratic formulas `e(2j) = j² - j(3r+4)/4 + 2 + r/8` and `e(2j+1) = (r-4)(2j+1)/8 + (j+1)j + 2 - r(j+1) + r/8`). Hence for `r ≥ 6`, sum `≤ 2^{E(1)} + 2^{E(2)}/(1-2^{-r/8}) ≤ 2^{-r/8}`; for `r = 5` compute the five summands `2^{-18/8}+2^{-9/8}+2^{-40/8}+2^{-23/8}+2^{-46/8} ≤ 1` directly. -/
theorem gb_star_numeric_sum {r : ℕ} (hr : 5 ≤ r) {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ ((r : ℝ) - 4) / 8) :
    (∑ m ∈ (Finset.Icc 1 r : Finset ℕ),
      (2 : ℝ) ^ (v * (m : ℝ) + (((m + 1) / 2 : ℕ) : ℝ) * ((m - (m + 1) / 2 : ℕ) : ℝ)
        - (r : ℝ) * (((m + 1) / 2 : ℕ) : ℝ) + 2))
    ≤ (2 : ℝ) ^ (-(r : ℝ) / 8) := by
  have hvnonneg : (0:ℝ) ≤ v := hv0
  have hstep1 : (∑ m ∈ (Finset.Icc 1 r : Finset ℕ),
      (2 : ℝ) ^ (v * (m : ℝ) + (((m + 1) / 2 : ℕ) : ℝ) * ((m - (m + 1) / 2 : ℕ) : ℝ)
        - (r : ℝ) * (((m + 1) / 2 : ℕ) : ℝ) + 2))
      ≤ (∑ m ∈ (Finset.Icc 1 r : Finset ℕ), (2:ℝ)^(gbNumE r m)) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
    have hv' : v * (m:ℝ) ≤ ((r:ℝ)-4)/8 * (m:ℝ) := mul_le_mul_of_nonneg_right hv hm0
    have _ := hvnonneg
    have hexp : v * (m : ℝ) + (((m + 1) / 2 : ℕ) : ℝ) * ((m - (m + 1) / 2 : ℕ) : ℝ)
        - (r : ℝ) * (((m + 1) / 2 : ℕ) : ℝ) + 2 ≤ gbNumE r m := by
      simp only [gbNumE, gbNumC]
      linarith
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hexp
  refine le_trans hstep1 ?_
  have hsplit : (∑ m ∈ Finset.Icc 1 r, (2:ℝ)^(gbNumE r m))
      = (2:ℝ)^(gbNumE r 1) + ∑ m ∈ Finset.Icc 2 r, (2:ℝ)^(gbNumE r m) := by
    have hI : Finset.Icc 1 r = insert 1 (Finset.Icc 2 r) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      constructor
      · rintro ⟨h1,h2⟩
        by_cases hm : m = 1
        · exact Or.inl hm
        · right; omega
      · rintro (h|⟨h1,h2⟩)
        · subst h; omega
        · omega
    rw [hI, Finset.sum_insert (by simp [Finset.mem_Icc])]
  by_cases hr5 : r = 5
  · subst hr5
    exact gb_num_r5
  · have hr6 : 6 ≤ r := by omega
    set x : ℝ := (2:ℝ)^(-(r:ℝ)/8) with hxdef
    have hxpos : 0 < x := by rw [hxdef]; positivity
    have hx35 : x ≤ 3/5 := by
      rw [hxdef]
      calc (2:ℝ)^(-(r:ℝ)/8) ≤ (2:ℝ)^(-(6:ℝ)/8) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by
              have h6 : (6:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr6
              linarith)
        _ ≤ 3/5 := by
            have h : ((2:ℝ)^(-(6:ℝ)/8))^(4:ℝ) ≤ ((3:ℝ)/5)^(4:ℝ) := by
              rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
              norm_num
            exact (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0:ℝ) < 4)).mp h
    have hx1 : x < 1 := by linarith
    have hx_pow : ∀ n : ℕ, x^n = (2:ℝ)^((-(r:ℝ)/8)*(n:ℝ)) := by
      intro n
      rw [hxdef]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hpt : ∀ m ∈ Finset.Icc 2 r, (2:ℝ)^(gbNumE r m) ≤ (2:ℝ)^(gbNumE r 2) * x^(m-2) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hp := gbNumE_pointwise r m hm.1 hm.2
      calc (2:ℝ)^(gbNumE r m) ≤ (2:ℝ)^(gbNumE r 2 - (r:ℝ)/8*((m-2:ℕ):ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hp
        _ = (2:ℝ)^(gbNumE r 2) * x^(m-2) := by
            rw [show gbNumE r 2 - (r:ℝ)/8*((m-2:ℕ):ℝ) = gbNumE r 2 + (-(r:ℝ)/8)*((m-2:ℕ):ℝ) by ring]
            rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
            rw [← hx_pow (m-2)]
    have htail : ∑ m ∈ Finset.Icc 2 r, (2:ℝ)^(gbNumE r m)
        ≤ (2:ℝ)^(gbNumE r 2) * (1/(1-x)) := by
      calc ∑ m ∈ Finset.Icc 2 r, (2:ℝ)^(gbNumE r m)
          ≤ ∑ m ∈ Finset.Icc 2 r, (2:ℝ)^(gbNumE r 2) * x^(m-2) := Finset.sum_le_sum hpt
        _ = (2:ℝ)^(gbNumE r 2) * ∑ m ∈ Finset.Icc 2 r, x^(m-2) := by rw [Finset.mul_sum]
        _ ≤ (2:ℝ)^(gbNumE r 2) * (1/(1-x)) :=
            mul_le_mul_of_nonneg_left (gbSumIccPowLe (le_of_lt hxpos) hx1 2 r) (by positivity)
    have h1 : (2:ℝ)^(gbNumE r 1) ≤ 4 * x^7 := by
      rw [gbNumE_one]
      calc (2:ℝ)^(-(7:ℝ)/8 * (r:ℝ) + 3/2) ≤ (2:ℝ)^((2:ℝ) + (-(7:ℝ)/8 * (r:ℝ))) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith)
        _ = 4 * x^7 := by
            rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
            rw [show (2:ℝ)^(2:ℝ) = 4 by norm_num [Real.rpow_natCast]]
            rw [show (-(7:ℝ)/8 * (r:ℝ)) = (-(r:ℝ)/8)*7 by ring]
            rw [hx_pow 7]
            norm_num
    have h2e : (2:ℝ)^(gbNumE r 2) = 4 * x^6 := by
      rw [gbNumE_two]
      rw [show (2:ℝ) - (3:ℝ)/4 * (r:ℝ) = (2:ℝ) + (-((3:ℝ)/4) * (r:ℝ)) by ring]
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      rw [show (2:ℝ)^(2:ℝ) = 4 by norm_num [Real.rpow_natCast]]
      rw [show (-((3:ℝ)/4) * (r:ℝ)) = (-(r:ℝ)/8)*6 by ring]
      rw [hx_pow 6]
      norm_num
    have htail2 : ∑ m ∈ Finset.Icc 2 r, (2:ℝ)^(gbNumE r m) ≤ 4 * x^6 / (1-x) := by
      calc ∑ m ∈ Finset.Icc 2 r, (2:ℝ)^(gbNumE r m)
          ≤ (2:ℝ)^(gbNumE r 2) * (1/(1-x)) := htail
        _ = 4 * x^6 / (1-x) := by rw [h2e]; ring
    have hx := gb_num_x_bound hxpos hx35
    rw [hsplit]
    calc (2:ℝ)^(gbNumE r 1) + ∑ m ∈ Finset.Icc 2 r, (2:ℝ)^(gbNumE r m)
        ≤ 4 * x^7 + 4 * x^6 / (1-x) := by linarith [h1, htail2]
      _ ≤ x := hx

end Work.LT
