import Submission.Work.ConeSwitch.MathlibNoHG

namespace Work.Deep.Conc.BruhnJoos

/-- Expansion of the difference of the two squared tails:
`4 * (u + 34w)² - (u + 50w)² - 16w² = 3u² + 172uw + 2108w²`. -/
private lemma bj_quad (u w : ℝ) :
    4 * (u + 34 * w) ^ 2 - (u + 50 * w) ^ 2 - 16 * w ^ 2
      = 3 * u ^ 2 + 172 * (u * w) + 2108 * w ^ 2 := by ring

/-- The elementary quadratic bound behind the tail comparison, with `t = u + 50w`
(so `u = t - 50w > 0`) and `w = c√s`:  `16w² ≤ 4(u+34w)² - (u+50w)²`. -/
private lemma bj_main_abstract {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    16 * w ^ 2 ≤ 4 * (u + 34 * w) ^ 2 - (u + 50 * w) ^ 2 := by
  have e := bj_quad u w
  have p : 0 ≤ 3 * u ^ 2 + 172 * (u * w) + 2108 * w ^ 2 := by
    nlinarith [sq_nonneg u, sq_nonneg w, mul_nonneg hu hw]
  linarith

theorem exp_tail_comparison {c : ℝ} (hc : 1 ≤ c) {s : ℕ} (hs : 1 ≤ s) {t : ℝ}
    (ht : 50 * c * Real.sqrt (s : ℝ) < t) :
    8 * Real.exp (-(t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ)))
      ≤ 4 * Real.exp (-t ^ 2 / (16 * c ^ 2 * (s : ℝ))) := by
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < (s : ℝ) := by
    have h : (0 : ℕ) < s := by omega
    exact_mod_cast h
  have hsq : (Real.sqrt (s : ℝ)) ^ 2 = (s : ℝ) := Real.sq_sqrt hs0.le
  have hw : 0 < c * Real.sqrt (s : ℝ) := mul_pos hc0 (Real.sqrt_pos.mpr hs0)
  -- normalise the hypothesis `50 * c * √s < t` to `50 * (c * √s) < t`
  have ht' : 50 * (c * Real.sqrt (s : ℝ)) < t := by simpa only [mul_assoc] using ht
  have hu0 : 0 ≤ t - 50 * (c * Real.sqrt (s : ℝ)) := sub_nonneg.mpr ht'.le
  have hw0 : 0 ≤ c * Real.sqrt (s : ℝ) := hw.le
  -- the numerical core: 16 c²s ≤ 4(t - 16c√s)² - t²
  have main : 16 * c ^ 2 * (s : ℝ) ≤ 4 * (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 - t ^ 2 := by
    have hma := bj_main_abstract hu0 hw0
    have e1 : 16 * (c * Real.sqrt (s : ℝ)) ^ 2 = 16 * c ^ 2 * (s : ℝ) := by
      rw [mul_pow, hsq]; ring
    have e2 : (t - 50 * (c * Real.sqrt (s : ℝ))) + 34 * (c * Real.sqrt (s : ℝ))
        = t - 16 * c * Real.sqrt (s : ℝ) := by ring
    have e3 : (t - 50 * (c * Real.sqrt (s : ℝ))) + 50 * (c * Real.sqrt (s : ℝ)) = t := by ring
    rw [e1, e2, e3] at hma
    exact hma
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero (ne_of_gt hc0)
  have pos : 0 < 16 * c ^ 2 * (s : ℝ) := mul_pos (mul_pos (by norm_num) hc2) hs0
  have ln2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  -- `log 2 * (16c²s) ≤ 4(t-16c√s)² - t²`
  have master : Real.log 2 * (16 * c ^ 2 * (s : ℝ))
      ≤ 4 * (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 - t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right ln2 pos.le
    linarith
  -- `log 2 ≤ (t-16c√s)²/(4c²s) - t²/(16c²s)`
  have key : Real.log 2 ≤ (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ))
      - t ^ 2 / (16 * c ^ 2 * (s : ℝ)) := by
    have e2 : (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ))
        = 4 * (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (16 * c ^ 2 * (s : ℝ)) := by
      have h4ne : (4 : ℝ) ≠ 0 := by norm_num
      have hD : 4 * (4 * c ^ 2 * (s : ℝ)) = 16 * c ^ 2 * (s : ℝ) := by ring
      calc (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ))
          = 4 * (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * (4 * c ^ 2 * (s : ℝ))) :=
            (mul_div_mul_left _ _ h4ne).symm
        _ = 4 * (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (16 * c ^ 2 * (s : ℝ)) := by rw [hD]
    rw [e2, div_sub_div_same, le_div_iff₀ pos]
    exact master
  have hsub : Real.log 2 - (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ))
      ≤ -t ^ 2 / (16 * c ^ 2 * (s : ℝ)) := by
    have hneg : -(t ^ 2) / (16 * c ^ 2 * (s : ℝ)) = -(t ^ 2 / (16 * c ^ 2 * (s : ℝ))) := by ring
    rw [hneg]
    linarith
  have h2 : Real.exp (Real.log 2 - (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ)))
      ≤ Real.exp (-t ^ 2 / (16 * c ^ 2 * (s : ℝ))) := Real.exp_le_exp.mpr hsub
  have hexp2 : Real.exp (Real.log 2) = 2 := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hEq2 : Real.exp (Real.log 2 - (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ)))
      = 2 * Real.exp (-(t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by
    have s1 : Real.log 2 - (t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ))
        = Real.log 2 + (-(t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by
      have hnegA : -(t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ))
          = -((t - 16 * c * Real.sqrt (s : ℝ)) ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by ring
      rw [hnegA, sub_eq_add_neg]
    rw [s1, Real.exp_add, hexp2]
  linarith

end Work.Deep.Conc.BruhnJoos
