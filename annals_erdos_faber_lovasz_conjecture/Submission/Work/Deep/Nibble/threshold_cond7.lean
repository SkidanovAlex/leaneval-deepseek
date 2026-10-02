import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.threshold_tools

namespace Work.Deep.Nibble

/-- **Clause 7 of the asymptotic side conditions of `cor:sparse_egj`** (threshold form).
For every `κ > 0` and `R > 0` there is `N > 0` such that for all `n ≥ N` and all
`D ≥ n^{1/100}` one has `2 * n^(2 log n) * exp(-(3/8) κ² D^(1/20)/R) < 1`.

Route: write `u := (3/8) κ² D^(1/20)/R` and use
`Real.log_lt_iff_lt_exp` together with `Real.log_mul`/`Real.log_rpow`/`Real.log_exp`:
it suffices that `log 2 + 2 (log n)^2 < u`.  `Work.Deep.Nibble.two_log_sq_le` with
`a := 1/2000` gives `2 (log n)^2 ≤ 32·(2000)^2 * n^(1/4000)`, while
`D^(1/20) ≥ (n^{1/100})^(1/20) = n^(1/2000)`.  Hence it suffices to take
`N := ((16 R/(3 κ²)) * (32/(1/2000)^2 + Real.log 2)) ^ (4000)`, which makes
`log 2 + 2 (log n)^2 ≤ w` and `2 w ≤ u` for `w := (3 κ²/(16 R)) * n^(1/2000)`
(strictness: `w > 0`, so `≤ w < 2w ≤ u`). -/
theorem threshold_cond7 {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ N : ℝ, 0 < N ∧ ∀ n : ℕ, N ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      2 * (n : ℝ) ^ (2 * Real.log n) * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / R)) < 1 := by
  have hκ2 : 0 < κ ^ 2 := pow_pos hκ 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- The coefficient `c := (3/8) κ²/R/2`, so that `2c = (3/8) κ²/R`.
  obtain ⟨c, hc, h2c⟩ : ∃ c : ℝ, 0 < c ∧ 2 * c = 3 / 8 * κ ^ 2 / R :=
    ⟨3 / 8 * κ ^ 2 / R / 2,
      div_pos (div_pos (mul_pos (by norm_num) hκ2) hR) (by norm_num),
      by ring⟩
  -- The constant `C := 32 / (1/2000)^2` of the squared-log bound, at exponent `1/4000`.
  have ha : 0 < (1:ℝ)/2000 := by norm_num
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → 2 * (Real.log x) ^ 2 ≤ C * x ^ ((1:ℝ)/4000) :=
    ⟨32 / ((1:ℝ)/2000)^2, fun x hx => by
      have h := two_log_sq_le ha hx
      rwa [show (1:ℝ)/2000/2 = (1:ℝ)/4000 by norm_num] at h⟩
  -- The threshold `N := M ^ 4000`, `M := max 1 ((C + log 2)/c)`.
  have hM0 : 0 < max 1 ((C + Real.log 2) / c) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨(max 1 ((C + Real.log 2) / c)) ^ ((4000:ℝ)), Real.rpow_pos_of_pos hM0 _, ?_⟩
  intro n hn D hD
  -- `n ≥ 1`
  have hN1 : (1:ℝ) ≤ (max 1 ((C + Real.log 2) / c)) ^ ((4000:ℝ)) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) (le_max_left (1:ℝ) ((C + Real.log 2) / c))
      (by norm_num : (0:ℝ) ≤ (4000:ℝ))
    rwa [Real.one_rpow] at h
  have hn1 : (1:ℝ) ≤ (n:ℝ) := hN1.trans hn
  have hn0 : 0 < (n:ℝ) := lt_of_lt_of_le zero_lt_one hn1
  -- `t := n^(1/4000) ≥ M`
  have htM : max 1 ((C + Real.log 2) / c) ≤ (n:ℝ) ^ ((1:ℝ)/4000) := by
    have hNM : ((max 1 ((C + Real.log 2) / c)) ^ ((4000:ℝ))) ^ ((1:ℝ)/4000)
        = max 1 ((C + Real.log 2) / c) := by
      rw [← Real.rpow_mul hM0.le ((4000:ℝ)) ((1:ℝ)/4000),
        show (4000:ℝ) * ((1:ℝ)/4000) = 1 by norm_num, Real.rpow_one]
    have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hM0 _).le hn (by norm_num : (0:ℝ) ≤ (1:ℝ)/4000)
    rwa [hNM] at h
  have ht1 : (1:ℝ) ≤ (n:ℝ) ^ ((1:ℝ)/4000) := (le_max_left _ _).trans htM
  have htpos : 0 < (n:ℝ) ^ ((1:ℝ)/4000) := lt_of_lt_of_le zero_lt_one ht1
  -- the squared-log bound
  have h2log : 2 * (Real.log (n:ℝ)) ^ 2 ≤ C * (n:ℝ) ^ ((1:ℝ)/4000) := hC _ hn1
  -- `C + log 2 ≤ c * t`
  have hAct : C + Real.log 2 ≤ c * (n:ℝ) ^ ((1:ℝ)/4000) := by
    have h1 : (C + Real.log 2) / c ≤ max 1 ((C + Real.log 2) / c) := le_max_right _ _
    have h2 : C + Real.log 2 ≤ max 1 ((C + Real.log 2) / c) * c := (div_le_iff₀ hc).mp h1
    calc C + Real.log 2 ≤ max 1 ((C + Real.log 2) / c) * c := h2
      _ = c * max 1 ((C + Real.log 2) / c) := by ring
      _ ≤ c * (n:ℝ) ^ ((1:ℝ)/4000) := mul_le_mul_of_nonneg_left htM hc.le
  -- `t ^ 2 = n^(1/2000)`
  have htsq : ((n:ℝ) ^ ((1:ℝ)/4000)) ^ 2 = (n:ℝ) ^ ((1:ℝ)/2000) := by
    rw [pow_two, ← Real.rpow_add hn0, show (1:ℝ)/4000 + (1:ℝ)/4000 = (1:ℝ)/2000 by norm_num]
  -- `log 2 + C * t ≤ c * t ^ 2`
  have key : Real.log 2 + C * (n:ℝ) ^ ((1:ℝ)/4000) ≤ c * ((n:ℝ) ^ ((1:ℝ)/4000)) ^ 2 := by
    have h3 : Real.log 2 ≤ Real.log 2 * (n:ℝ) ^ ((1:ℝ)/4000) := by
      calc Real.log 2 = Real.log 2 * 1 := (mul_one _).symm
        _ ≤ Real.log 2 * (n:ℝ) ^ ((1:ℝ)/4000) := mul_le_mul_of_nonneg_left ht1 hlog2.le
    calc Real.log 2 + C * (n:ℝ) ^ ((1:ℝ)/4000)
        ≤ Real.log 2 * (n:ℝ) ^ ((1:ℝ)/4000) + C * (n:ℝ) ^ ((1:ℝ)/4000) := by linarith
      _ = (C + Real.log 2) * (n:ℝ) ^ ((1:ℝ)/4000) := by ring
      _ ≤ (c * (n:ℝ) ^ ((1:ℝ)/4000)) * (n:ℝ) ^ ((1:ℝ)/4000) :=
          mul_le_mul_of_nonneg_right hAct htpos.le
      _ = c * ((n:ℝ) ^ ((1:ℝ)/4000)) ^ 2 := by rw [pow_two]; ring
  -- `log 2 + 2 (log n)^2 ≤ w := c * n^(1/2000)`
  have hlogbound : Real.log 2 + 2 * (Real.log (n:ℝ)) ^ 2 ≤ c * (n:ℝ) ^ ((1:ℝ)/2000) := by
    calc Real.log 2 + 2 * (Real.log (n:ℝ)) ^ 2
        ≤ Real.log 2 + C * (n:ℝ) ^ ((1:ℝ)/4000) := add_le_add_right h2log _
      _ ≤ c * ((n:ℝ) ^ ((1:ℝ)/4000)) ^ 2 := key
      _ = c * (n:ℝ) ^ ((1:ℝ)/2000) := by rw [htsq]
  have hXpos : 0 < (n:ℝ) ^ ((1:ℝ)/2000) := Real.rpow_pos_of_pos hn0 _
  have hwpos : 0 < c * (n:ℝ) ^ ((1:ℝ)/2000) := mul_pos hc hXpos
  -- `D^(1/20) ≥ (n^(1/100))^(1/20) = n^(1/2000)`
  have hn100 : (1:ℝ) ≤ (n:ℝ) ^ ((1:ℝ)/100) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hn1 (by norm_num : (0:ℝ) ≤ (1:ℝ)/100)
    rwa [Real.one_rpow] at h
  have hn100pos : 0 < (n:ℝ) ^ ((1:ℝ)/100) := lt_of_lt_of_le zero_lt_one hn100
  have hXDp : (n:ℝ) ^ ((1:ℝ)/2000) ≤ D ^ ((1:ℝ)/20) := by
    have hmono : ((n:ℝ) ^ ((1:ℝ)/100)) ^ ((1:ℝ)/20) ≤ D ^ ((1:ℝ)/20) :=
      Real.rpow_le_rpow hn100pos.le hD (by norm_num : (0:ℝ) ≤ (1:ℝ)/20)
    have hexp : ((n:ℝ) ^ ((1:ℝ)/100)) ^ ((1:ℝ)/20) = (n:ℝ) ^ ((1:ℝ)/2000) := by
      rw [← Real.rpow_mul hn0.le ((1:ℝ)/100) ((1:ℝ)/20),
        show (1:ℝ)/100 * ((1:ℝ)/20) = (1:ℝ)/2000 by norm_num]
    rwa [hexp] at hmono
  -- `2 * w ≤ u`
  have hcoef : 0 ≤ 3 / 8 * κ ^ 2 / R :=
    div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hκ.le 2)) hR.le
  have hu_bound : 2 * (c * (n:ℝ) ^ ((1:ℝ)/2000)) ≤ 3 / 8 * κ ^ 2 * D ^ ((1:ℝ)/20) / R := by
    have h1 : (3 / 8 * κ ^ 2 / R) * (n:ℝ) ^ ((1:ℝ)/2000)
        ≤ (3 / 8 * κ ^ 2 / R) * D ^ ((1:ℝ)/20) :=
      mul_le_mul_of_nonneg_left hXDp hcoef
    calc 2 * (c * (n:ℝ) ^ ((1:ℝ)/2000))
        = (2 * c) * (n:ℝ) ^ ((1:ℝ)/2000) := by ring
      _ = (3 / 8 * κ ^ 2 / R) * (n:ℝ) ^ ((1:ℝ)/2000) := by rw [h2c]
      _ ≤ (3 / 8 * κ ^ 2 / R) * D ^ ((1:ℝ)/20) := h1
      _ = 3 / 8 * κ ^ 2 * D ^ ((1:ℝ)/20) / R := by ring
  -- take logarithms of the left-hand side
  have hP0 : 0 < 2 * (n:ℝ) ^ (2 * Real.log n) * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1:ℝ)/20) / R)) :=
    mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hn0 _)) (Real.exp_pos _)
  have hlogP : Real.log (2 * (n:ℝ) ^ (2 * Real.log n) * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1:ℝ)/20) / R)))
      = Real.log 2 + 2 * (Real.log (n:ℝ)) ^ 2 - (3 / 8 * κ ^ 2 * D ^ ((1:ℝ)/20) / R) := by
    rw [Real.log_mul (ne_of_gt (mul_pos (by norm_num) (Real.rpow_pos_of_pos hn0 _)))
        (ne_of_gt (Real.exp_pos _)),
      Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hn0 _)),
      Real.log_rpow hn0, Real.log_exp]
    ring
  have hlt : Real.log 2 + 2 * (Real.log (n:ℝ)) ^ 2 < 3 / 8 * κ ^ 2 * D ^ ((1:ℝ)/20) / R := by
    calc Real.log 2 + 2 * (Real.log (n:ℝ)) ^ 2 ≤ c * (n:ℝ) ^ ((1:ℝ)/2000) := hlogbound
      _ < 2 * (c * (n:ℝ) ^ ((1:ℝ)/2000)) := by linarith
      _ ≤ 3 / 8 * κ ^ 2 * D ^ ((1:ℝ)/20) / R := hu_bound
  have hlogP0 : Real.log (2 * (n:ℝ) ^ (2 * Real.log n)
      * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1:ℝ)/20) / R))) < 0 := by
    rw [hlogP]; linarith
  have hfin := (Real.log_lt_iff_lt_exp (y := (0:ℝ)) hP0).mp hlogP0
  exact hfin.trans_eq Real.exp_zero

end Work.Deep.Nibble
