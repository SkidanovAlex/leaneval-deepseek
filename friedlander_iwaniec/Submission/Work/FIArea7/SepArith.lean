import Mathlib
import Submission.Work.FIArea7.SepK

namespace Work.FIArea7

/-!
## Elementary real-analytic and numerical bounds

The main analytic ingredient is `log_one_add_ge`: `log (1+x) ≥ 2x/(x+2)` for `x ≥ 0`.
-/

lemma pi_gt_314 : (3.14 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]

lemma two_div_pi_lt : 2 / Real.pi < 0.637 := by
  rw [div_lt_iff₀ Real.pi_pos]
  linarith [pi_gt_314]

lemma log_two_ge : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]

lemma log_two_le : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]

/-- For `x ≥ 0` one has `log (1+x) ≥ 2x/(x+2)`. -/
lemma log_one_add_ge (x : ℝ) (hx : 0 ≤ x) : 2*x/(x+2) ≤ Real.log (1+x) := by
  have hderiv : ∀ y ∈ Set.Ioi (0:ℝ),
      deriv (fun z : ℝ => Real.log (1+z) - 2 + 4/(z+2)) y = y^2/((1+y)*(y+2)^2) := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    have h1 : (0:ℝ) < 1+y := by linarith
    have h2 : (0:ℝ) < y+2 := by linarith
    have hd : HasDerivAt (fun z : ℝ => Real.log (1+z) - 2 + 4/(z+2)) (y^2/((1+y)*(y+2)^2)) y := by
      have hlog : HasDerivAt (fun z : ℝ => Real.log (1+z) - 2) (1 * (1+y)⁻¹) y := by
        have h : HasDerivAt (fun z : ℝ => 1 + z) 1 y := by
          simpa using (hasDerivAt_id y).const_add (1:ℝ)
        simpa using (h.log (by linarith)).sub_const 2
      have h4 : HasDerivAt (fun z : ℝ => (4:ℝ)/(z+2)) ((0*(y+2) - 4*1)/(y+2)^2) y := by
        have hd2 : HasDerivAt (fun z : ℝ => z + 2) 1 y := by
          simpa using (hasDerivAt_id y).add_const (2:ℝ)
        exact (hasDerivAt_const y (4:ℝ)).div hd2 (by linarith)
      have hsum : HasDerivAt ((fun z : ℝ => Real.log (1+z) - 2) + fun z : ℝ => 4/(z+2))
          (1 * (1+y)⁻¹ + (0*(y+2) - 4*1)/(y+2)^2) y := hlog.add h4
      have hfun : ((fun z : ℝ => Real.log (1+z) - 2) + fun z : ℝ => 4/(z+2))
          = (fun z : ℝ => Real.log (1+z) - 2 + 4/(z+2)) := by
        funext z
        simp only [Pi.add_apply]
      have hder : (1 * (1+y)⁻¹ + (0*(y+2) - 4*1)/(y+2)^2) = y^2/((1+y)*(y+2)^2) := by
        rw [one_mul, zero_mul, zero_sub, neg_div]
        field_simp
        ring
      rw [hfun, hder] at hsum
      exact hsum
    exact hd.deriv
  have hmono : MonotoneOn (fun z : ℝ => Real.log (1+z) - 2 + 4/(z+2)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · refine (ContinuousOn.log ?_ ?_ |>.sub continuousOn_const).add ?_
      · exact continuousOn_const.add continuousOn_id
      · intro z hz; have : (0:ℝ) ≤ z := hz; linarith
      · exact continuousOn_const.div (continuousOn_id.add continuousOn_const)
          (fun z hz => by have : (0:ℝ) ≤ z := hz; linarith)
    · rw [interior_Ici]
      refine (DifferentiableOn.log ?_ ?_ |>.sub (differentiableOn_const 2)).add ?_
      · exact (differentiableOn_const 1).add differentiableOn_id
      · intro z hz; have : (0:ℝ) < z := hz; linarith
      · exact (differentiableOn_const 4).div (differentiableOn_id.add (differentiableOn_const 2))
          (fun z hz => by have : (0:ℝ) < z := hz; linarith)
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : (0:ℝ) < y := hy
      rw [hderiv y hy]
      positivity
  have h0 : (fun z : ℝ => Real.log (1+z) - 2 + 4/(z+2)) 0 = 0 := by norm_num
  have hle := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [h0] at hle
  have hkey : (2:ℝ)*x/(x+2) = 2 - 4/(x+2) := by
    field_simp
    ring
  rw [hkey]
  linarith

lemma log_three_ge : (1.09 : ℝ) ≤ Real.log 3 := by
  have h32 : (2/5 : ℝ) ≤ Real.log (3/2) := by
    have h := log_one_add_ge (1/2) (by norm_num)
    norm_num at h
    linarith
  have h : Real.log 3 = Real.log 2 + Real.log (3/2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [h]
  linarith [log_two_ge]

lemma log_six_ge : (1.78 : ℝ) ≤ Real.log 6 := by
  have h : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [h]
  linarith [log_two_ge, log_three_ge]

/-- `(π/2 - 1) y - log y ≥ 0.4` for `y > 0`. -/
lemma c_sub_log_ge (y : ℝ) (hy : 0 < y) : 0.4 ≤ (Real.pi/2 - 1) * y - Real.log y := by
  have hc : (0.57:ℝ) < Real.pi/2 - 1 := by linarith [Real.pi_gt_d20]
  have hc0 : (0:ℝ) < Real.pi/2 - 1 := by linarith
  have hexp : (1.8:ℝ) ≤ Real.exp (0.6) := by
    have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 0.6 by norm_num) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlogc : (-0.6:ℝ) ≤ Real.log (Real.pi/2 - 1) := by
    rw [Real.le_log_iff_exp_le hc0]
    rw [Real.exp_neg]
    calc (Real.exp 0.6)⁻¹ ≤ (1.8:ℝ)⁻¹ := inv_anti₀ (by norm_num) hexp
      _ ≤ Real.pi/2 - 1 := by linarith
  have hcy : 0 < (Real.pi/2 - 1) * y := by positivity
  have h1 : Real.log ((Real.pi/2 - 1) * y) ≤ (Real.pi/2 - 1) * y - 1 :=
    Real.log_le_sub_one_of_pos hcy
  have h2 : Real.log ((Real.pi/2 - 1) * y) = Real.log (Real.pi/2 - 1) + Real.log y :=
    Real.log_mul (by linarith) (ne_of_gt hy)
  linarith

/-! ## The ratio `16 λ / (15 ε)` -/

/-- `16 λ / (15 ε) = (16/15) * (1 + 2 log M / (log (M+1) - log M))`. -/
lemma ratio_id (M : ℕ) (hM : 1 ≤ M) :
    16 * sepLam M / (15 * sepEps M) =
      (16/15) * (1 + 2 * Real.log M / (Real.log (M+1) - Real.log M)) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hlam : sepLam M = (Real.log (M:ℝ) + Real.log ((M:ℝ)+1))/(4*Real.pi) := by
    unfold sepLam; ring
  have heps : sepEps M = (Real.log ((M:ℝ)+1) - Real.log (M:ℝ))/(4*Real.pi) := by
    unfold sepEps; ring
  have hne : Real.log ((M:ℝ)+1) - Real.log (M:ℝ) ≠ 0 := by
    have h : Real.log (M:ℝ) < Real.log ((M:ℝ)+1) := Real.log_lt_log hM0 (by linarith)
    linarith
  rw [hlam, heps]
  field_simp
  ring

/-- `log (M+1) - log M ≥ 2/(2M+1)`. -/
lemma beta_ge (M : ℕ) (hM : 1 ≤ M) : 2/(2*(M:ℝ)+1) ≤ Real.log (M+1) - Real.log M := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hu : (0:ℝ) ≤ 1/(M:ℝ) := by positivity
  have h1 : 2*(1/(M:ℝ))/(1/(M:ℝ)+2) ≤ Real.log (1 + 1/(M:ℝ)) := log_one_add_ge _ hu
  have h2 : 2*(1/(M:ℝ))/(1/(M:ℝ)+2) = 2/(2*(M:ℝ)+1) := by
    field_simp <;> ring
  have h3 : Real.log ((M:ℝ)+1) - Real.log (M:ℝ) = Real.log (1 + 1/(M:ℝ)) := by
    rw [← Real.log_div (by positivity : ((M:ℝ)+1) ≠ 0) (by positivity : (M:ℝ) ≠ 0)]
    congr 1
    field_simp <;> ring
  rw [h3, ← h2]
  exact h1

/-- Bound for `16 λ / (15 ε)`. -/
lemma ratio_le (M : ℕ) (hM : 1 ≤ M) :
    16 * sepLam M / (15 * sepEps M) ≤ (16/15) * (1 + (2*(M:ℝ)+1) * Real.log M) := by
  have hA0 : (0:ℝ) ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hβ := beta_ge M hM
  have hβpos : 0 < Real.log (M+1) - Real.log M := lt_of_lt_of_le (by positivity) hβ
  rw [ratio_id M hM]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hstep : 2 * Real.log M / (Real.log (M+1) - Real.log M) ≤ (2*(M:ℝ)+1) * Real.log M := by
    rw [div_le_iff₀ hβpos]
    have h2 : (2:ℝ) ≤ (2*(M:ℝ)+1) * (Real.log (M+1) - Real.log M) := by
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 2*(M:ℝ)+1)).mp hβ
      linarith
    nlinarith [hA0, h2]
  linarith

/-! ## The numerical core -/

/-- Case `M = 1`. -/
lemma key_one :
    (2/Real.pi) * (2 + 1/15 + Real.log (1 + (2*(1:ℝ)+1) * Real.log (1:ℝ))) <
      Real.log (6*(1:ℝ)) := by
  have h1 : Real.log (1 + (2*(1:ℝ)+1) * Real.log (1:ℝ)) = 0 := by simp
  rw [h1]
  have h3 : (2/Real.pi) * (2 + 1/15 + 0) < 0.637 * (2 + 1/15 + 0) := by
    have := two_div_pi_lt
    nlinarith [show (0:ℝ) < 2 + 1/15 + 0 by norm_num]
  have h4 : (0.637:ℝ) * (2 + 1/15 + 0) < Real.log (6*(1:ℝ)) := by
    norm_num
    linarith [log_six_ge]
  linarith

/-- Case `M = 2`. -/
lemma key_two :
    (2/Real.pi) * (2 + 1/15 + Real.log (1 + (2*(2:ℝ)+1) * Real.log 2)) <
      Real.log (6*(2:ℝ)) := by
  have h1 : Real.log (1 + (2*(2:ℝ)+1) * Real.log 2) ≤ 1.5114 := by
    have h5 : (0:ℝ) < 1 + 5 * Real.log 2 := by linarith [log_two_ge]
    have h6 : 1 + 5 * Real.log 2 ≤ 4.5 := by linarith [log_two_le]
    have h7 : Real.log (1 + 5 * Real.log 2) ≤ Real.log 4.5 := Real.log_le_log h5 h6
    have h8 : Real.log 4.5 ≤ 1.5114 := by
      have h9 : Real.log 4.5 = Real.log 4 + Real.log (9/8) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      have h10 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
        norm_num
      have h11 : Real.log (9/8) ≤ 1/8 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 9/8 by norm_num)
        linarith
      rw [h9, h10]
      linarith [log_two_le]
    linarith
  have h2 : (2/Real.pi) * (2 + 1/15 + 1.5114) < Real.log (6*(2:ℝ)) := by
    have h3 : (2/Real.pi) * (2 + 1/15 + 1.5114) < 0.637 * (2 + 1/15 + 1.5114) := by
      have := two_div_pi_lt
      nlinarith [show (0:ℝ) < 2 + 1/15 + 1.5114 by norm_num]
    have h4 : (0.637:ℝ) * (2 + 1/15 + 1.5114) < Real.log (6*(2:ℝ)) := by
      have h5 : Real.log (6*(2:ℝ)) = Real.log 6 + Real.log 2 :=
        Real.log_mul (by norm_num) (by norm_num)
      rw [h5]
      linarith [log_six_ge, log_two_ge]
    linarith
  have hmul : (2/Real.pi) * (2 + 1/15 + Real.log (1 + (2*(2:ℝ)+1) * Real.log 2))
      ≤ (2/Real.pi) * (2 + 1/15 + 1.5114) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith [hmul, h2]

/-- Case `M ≥ 3`. -/
lemma key_ge3 (M : ℕ) (hM : 3 ≤ M) :
    (2/Real.pi) * (2 + 1/15 + Real.log (1 + (2*(M:ℝ)+1) * Real.log M)) <
      Real.log (6*(M:ℝ)) := by
  set A := Real.log (M:ℝ) with hAdef
  have hM3 : (3:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hM0 : (0:ℝ) < (M:ℝ) := by linarith
  have hA1 : 1 ≤ A := by
    have h1 : Real.log 3 ≤ A := by
      rw [hAdef]; exact Real.log_le_log (by norm_num) hM3
    linarith [log_three_ge]
  have hA0 : 0 < A := by linarith
  have hz7 : (7:ℝ) ≤ (2*(M:ℝ)+1) * A := by nlinarith
  have hz0 : 0 < (2*(M:ℝ)+1) * A := by linarith
  have hz1 : (1:ℝ) ≤ (2*(M:ℝ)+1) * A := by linarith
  -- Step 1
  have hs1 : Real.log (1 + (2*(M:ℝ)+1)*A) ≤ Real.log ((2*(M:ℝ)+1)*A) + 1/((2*(M:ℝ)+1)*A) := by
    have hlog : Real.log (1 + (2*(M:ℝ)+1)*A)
        = Real.log ((2*(M:ℝ)+1)*A) + Real.log (1 + 1/((2*(M:ℝ)+1)*A)) := by
      rw [show 1 + ((2*(M:ℝ)+1)*A) = ((2*(M:ℝ)+1)*A) * (1 + 1/((2*(M:ℝ)+1)*A)) by
        field_simp; ring]
      rw [Real.log_mul (ne_of_gt hz0) (by positivity)]
    rw [hlog]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/((2*(M:ℝ)+1)*A) by positivity)
    linarith
  -- Step 2
  have hs2 : Real.log ((2*(M:ℝ)+1)*A) = Real.log (2*(M:ℝ)+1) + Real.log A := by
    rw [Real.log_mul (by positivity) (ne_of_gt hA0)]
  -- Step 3
  have hs3 : Real.log (2*(M:ℝ)+1) ≤ A + 0.86 := by
    have hfac : (2*(M:ℝ)+1) = (M:ℝ) * (2 + 1/(M:ℝ)) := by
      field_simp
    have h1 : Real.log (2*(M:ℝ)+1) = A + Real.log (2 + 1/(M:ℝ)) := by
      rw [hfac, Real.log_mul (ne_of_gt hM0) (by positivity), ← hAdef]
    rw [h1]
    have h2 : Real.log (2 + 1/(M:ℝ)) ≤ Real.log (7/3) := by
      apply Real.log_le_log (by positivity)
      have h3 : 1/(M:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) hM3
      linarith
    have h3 : Real.log (7/3) ≤ 0.86 := by
      have h4 : Real.log (7/3) = Real.log 2 + Real.log (7/6) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      have h5 : Real.log (7/6) ≤ 1/6 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 7/6 by norm_num)
        linarith
      rw [h4]
      linarith [log_two_le]
    linarith
  -- Step 4
  have hs4 : 1/((2*(M:ℝ)+1)*A) ≤ 1/7 := one_div_le_one_div_of_le (by norm_num) hz7
  -- Step 5
  have hs5 : Real.log (1 + (2*(M:ℝ)+1)*A) ≤ A + Real.log A + 1.003 := by
    linarith [hs1, hs2, hs3, hs4]
  -- Step 6
  have key6 : 2 + 1/15 + (A + Real.log A + 1.003) < (Real.pi/2) * (Real.log 6 + A) := by
    have hπ6 : (2.796:ℝ) ≤ (Real.pi/2) * Real.log 6 := by
      nlinarith [Real.pi_gt_d20, log_six_ge]
    have hclog : 0.4 ≤ (Real.pi/2 - 1) * A - Real.log A := c_sub_log_ge A hA0
    have hsplit : (Real.pi/2) * (Real.log 6 + A) = (Real.pi/2) * Real.log 6 + (Real.pi/2) * A := by ring
    rw [hsplit]
    nlinarith [hπ6, hclog]
  have hinv : (0:ℝ) < 2/Real.pi := by positivity
  have h6 : (2/Real.pi) * ((Real.pi/2) * (Real.log 6 + A)) = Real.log 6 + A := by
    field_simp
  have hlt := mul_lt_mul_of_pos_left key6 hinv
  rw [h6] at hlt
  -- combine
  have hcomb : (2/Real.pi) * (2 + 1/15 + Real.log (1 + (2*(M:ℝ)+1) * Real.log M))
      ≤ (2/Real.pi) * (2 + 1/15 + (A + Real.log A + 1.003)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [hs5]
  have hfin : Real.log (6*(M:ℝ)) = Real.log 6 + A := by
    rw [show (6:ℝ)*(M:ℝ) = 6 * (M:ℝ) by ring, Real.log_mul (by norm_num) (ne_of_gt hM0), hAdef]
  linarith [hcomb, hlt, hfin]

end Work.FIArea7

/-! ## The target -/

namespace Work.FIArea7

/-- Arithmetic core of *FI* Lemma 26.1: with `λ = (log M + log (M+1))/(4π)` and
`ε = (log (M+1) - log M)/(4π)` one has `(2/π)(2 + log (16λ/(15ε))) < log 6M` for `M ≥ 1`. -/
theorem SepArith (M : ℕ) (hM : 1 ≤ M) :
    (2 / Real.pi) * (2 + Real.log (16 * sepLam M / (15 * sepEps M))) < Real.log (6 * M) := by
  have hε := sepEps_pos hM
  have hlam := sepLam_nonneg hM
  have hratio := ratio_le M hM
  have hlam_pos : 0 < sepLam M := lt_of_lt_of_le hε (sepEps_le_sepLam hM)
  have hpos : 0 < 16 * sepLam M / (15 * sepEps M) := by positivity
  have hpos2 : 0 < (16/15) * (1 + (2*(M:ℝ)+1) * Real.log M) := by
    have h1 : (0:ℝ) ≤ (2*(M:ℝ)+1) * Real.log M :=
      mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hM))
    exact mul_pos (by norm_num) (by linarith)
  have hpos3 : (0:ℝ) < 1 + (2*(M:ℝ)+1) * Real.log M := by
    have h1 : (0:ℝ) ≤ (2*(M:ℝ)+1) * Real.log M :=
      mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hM))
    linarith
  have h1 : Real.log (16 * sepLam M / (15 * sepEps M)) ≤
      1/15 + Real.log (1 + (2*(M:ℝ)+1) * Real.log M) := by
    have h := Real.log_le_log hpos hratio
    have h2 : Real.log ((16/15) * (1 + (2*(M:ℝ)+1) * Real.log M))
        = Real.log (16/15) + Real.log (1 + (2*(M:ℝ)+1) * Real.log M) :=
      Real.log_mul (by norm_num) (ne_of_gt hpos3)
    rw [h2] at h
    have h3 : Real.log (16/15) ≤ 1/15 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 16/15 by norm_num)
      linarith
    linarith
  have h3 : (2/Real.pi) * (2 + 1/15 + Real.log (1 + (2*(M:ℝ)+1) * Real.log M)) <
      Real.log (6*(M:ℝ)) := by
    rcases lt_or_ge M 3 with h | h
    · interval_cases M
      · simpa using key_one
      · simpa using key_two
    · exact key_ge3 M h
  have h4 : (2/Real.pi) * (2 + Real.log (16 * sepLam M / (15 * sepEps M)))
      ≤ (2/Real.pi) * (2 + 1/15 + Real.log (1 + (2*(M:ℝ)+1) * Real.log M)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  exact lt_of_le_of_lt h4 h3

end Work.FIArea7
