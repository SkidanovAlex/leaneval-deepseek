import Mathlib
import Submission.Commons.Analysis.Perron.riesz_perron_bound

noncomputable section

open Complex MeasureTheory intervalIntegral Filter
open scoped Topology BigOperators

namespace Commons.Analysis.Perron

open Commons.Analysis.Complex
open Commons.Analysis.Integral

theorem riesz_perron_bound_pos (a : ℕ → ℝ) (ha : ∀ n : ℕ, 0 ≤ a n) (c x T : ℝ)
    (hc : 1 ≤ c) (hx : 0 < x) (hT : 1 ≤ T)
    (hS : Summable (fun n : ℕ => (a n) / (n : ℝ) ^ c)) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (a n : ℂ) * (((x - (n : ℝ)) : ℝ) : ℂ))
      - (1 / (2 * Real.pi)) * (∫ y in (-T)..T,
          (∑' n : ℕ, (a n : ℂ) * (n : ℂ) ^ (-((c : ℂ) + (y : ℂ) * Complex.I)))
          * (x : ℂ) ^ ((c : ℂ) + (y : ℂ) * Complex.I + 1)
          / (((c : ℂ) + (y : ℂ) * Complex.I) * (((c + 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)))‖
      ≤ x ^ (c + 1) / T * (∑' n : ℕ, (a n) / (n : ℝ) ^ c) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hx0 : 0 < x := hx
  have hTle : -T ≤ T := by linarith
  let w : ℝ → ℂ := fun y => (c : ℂ) + (y : ℂ) * Complex.I
  let den : ℝ → ℂ := fun y =>
    ((c : ℂ) + (y : ℂ) * Complex.I) * (((c + 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  let G : ℕ → ℝ → ℂ := fun n y =>
    (a n : ℂ) * (n : ℂ) ^ (-(w y)) * (x : ℂ) ^ (w y + 1) / den y
  let F : ℝ → ℂ := fun y =>
    (∑' n : ℕ, (a n : ℂ) * (n : ℂ) ^ (-(w y))) * (x : ℂ) ^ (w y + 1) / den y
  let K : ℕ → ℂ := fun n =>
    (1 / (2 * Real.pi)) * (∫ y in (-T)..T, rieszKern (x / (n : ℝ)) c y)
  let Θ : ℕ → ℂ := fun n => (a n : ℂ) * (x : ℂ) * K n
  let Ψ : ℕ → ℂ := fun n => if n = 0 then 0 else (a n : ℂ) * (((max (x - (n : ℝ)) 0 : ℝ)) : ℂ)
  let C0 : ℝ := x ^ (c + 1) / (c * (c + 1))
  let g : ℕ → ℝ := fun n => 2 * T * (C0 * (a n / (n : ℝ) ^ c))
  change ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (a n : ℂ) * (((x - (n : ℝ)) : ℝ) : ℂ))
      - (1 / (2 * Real.pi)) * (∫ y in (-T)..T, F y)‖
      ≤ x ^ (c + 1) / T * (∑' n : ℕ, (a n) / (n : ℝ) ^ c)
  have hC0nn : 0 ≤ C0 := by
    simp only [C0]
    positivity
  have hgnonneg : ∀ n : ℕ, 0 ≤ a n / (n : ℝ) ^ c :=
    fun n => div_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) c)

  -- the exponent at `n = 0` does not vanish
  have hw_ne : ∀ y : ℝ, -(w y) ≠ 0 := by
    intro y h
    have h1 : (-(w y)).re = -c := by
      simp [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have h2 : (-(w y)).re = 0 := by rw [h, Complex.zero_re]
    linarith

  -- (a) the summand of the series is `a n * x` times the Riesz kernel
  have hG_eq : ∀ n y, n ≠ 0 →
      G n y = (a n : ℂ) * (x : ℂ) * rieszKern (x / (n : ℝ)) c y := by
    intro n y hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hkey : (n : ℂ) ^ (-(w y)) * (x : ℂ) ^ (w y + 1)
        = (x : ℂ) * (((x / (n : ℝ) : ℝ)) : ℂ) ^ (w y) :=
      cpow_shift_mul x hx0 n hn1 (w y)
    calc G n y
        = ((a n : ℂ) * ((n : ℂ) ^ (-(w y)) * (x : ℂ) ^ (w y + 1))) * (den y)⁻¹ := by
          simp only [G, div_eq_mul_inv]
          ring
      _ = ((a n : ℂ) * ((x : ℂ) * (((x / (n : ℝ) : ℝ)) : ℂ) ^ (w y))) * (den y)⁻¹ := by
          rw [hkey]
      _ = (a n : ℂ) * (x : ℂ) * rieszKern (x / (n : ℝ)) c y := by
          simp only [rieszKern, den, div_eq_mul_inv]
          ring

  -- (b) each summand is continuous
  have hG_zero : G 0 = fun _ : ℝ => 0 := by
    funext y
    have hz : ((0 : ℕ) : ℂ) ^ (-(w y)) = 0 := by
      rw [Nat.cast_zero]
      exact Complex.zero_cpow (hw_ne y)
    simp only [G, hz, mul_zero, zero_mul, zero_div]
  have hG_cont : ∀ n, Continuous (G n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [hG_zero]
      exact continuous_const
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hcont : Continuous (rieszKern (x / (n : ℝ)) c) :=
        continuous_rieszKern (x / (n : ℝ)) c (div_pos hx0 hnpos) hc0
      have h2 : Continuous (fun y : ℝ => (a n : ℂ) * (x : ℂ) * rieszKern (x / (n : ℝ)) c y) :=
        (((continuous_const : Continuous fun _ : ℝ => (a n : ℂ)).mul
          (continuous_const : Continuous fun _ : ℝ => (x : ℂ))).mul hcont)
      rw [show G n = fun y : ℝ => (a n : ℂ) * (x : ℂ) * rieszKern (x / (n : ℝ)) c y from
        funext fun y => hG_eq n y hn]
      exact h2

  -- (c) pointwise bound on each summand
  have hG_bound : ∀ n y, ‖G n y‖ ≤ C0 * (a n / (n : ℝ) ^ c) := by
    intro n y
    by_cases hn : n = 0
    · subst hn
      have h0 : G 0 y = 0 := congrFun hG_zero y
      have h1 : (((0 : ℕ) : ℝ)) ^ c = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow hc0.ne']
      have hR : C0 * (a 0 / (((0 : ℕ) : ℝ) ^ c)) = 0 := by
        rw [h1, div_zero, mul_zero]
      rw [h0, norm_zero, hR]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [hG_eq n y hn, norm_mul, norm_mul, norm_ofReal_nonneg (a n) (ha n),
        norm_ofReal_nonneg x hx0.le]
      have h1 : ‖rieszKern (x / (n : ℝ)) c y‖ ≤ (x / (n : ℝ)) ^ c / (c * (c + 1)) :=
        rieszKern_uniform_bound (x / (n : ℝ)) c y (div_pos hx0 hnpos) hc
      have h2 : (x / (n : ℝ)) ^ c = x ^ c / (n : ℝ) ^ c := Real.div_rpow hx0.le hnpos.le c
      simp only [C0]
      calc a n * x * ‖rieszKern (x / (n : ℝ)) c y‖
          ≤ a n * x * ((x / (n : ℝ)) ^ c / (c * (c + 1))) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg (ha n) hx0.le)
        _ = x ^ (c + 1) / (c * (c + 1)) * (a n / (n : ℝ) ^ c) := by
            rw [h2, Real.rpow_add hx0 c 1, Real.rpow_one]
            ring

  -- (d) the dominating sequence is summable
  have hg_summable : Summable g := by
    have h1 : Summable (fun n : ℕ => C0 * (a n / (n : ℝ) ^ c)) := hS.mul_left C0
    exact h1.mul_left (2 * T)

  -- (e) the integrand equals the series of summands
  have hsummand_summable : ∀ y : ℝ,
      Summable (fun n : ℕ => (a n : ℂ) * (n : ℂ) ^ (-(w y))) := by
    intro y
    apply Summable.of_norm_bounded hS
    intro n
    by_cases hn : n = 0
    · subst hn
      have hz : ((0 : ℕ) : ℂ) ^ (-(w y)) = 0 := by
        rw [Nat.cast_zero]
        exact Complex.zero_cpow (hw_ne y)
      have h1 : (((0 : ℕ) : ℝ)) ^ c = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow hc0.ne']
      simp only [hz, mul_zero, norm_zero, h1, div_zero]
      exact le_refl 0
    · have hnorm : ‖(n : ℂ) ^ (-(w y))‖ = (n : ℝ) ^ (-c) := by
        have hre : (-(w y)).re = -c := by
          simp [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
        rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hre]
      rw [norm_mul, norm_ofReal_nonneg (a n) (ha n), hnorm,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hF_eq : ∀ y : ℝ, F y = ∑' n : ℕ, G n y := by
    intro y
    have hsum := hsummand_summable y
    calc F y
        = (∑' n : ℕ, (a n : ℂ) * (n : ℂ) ^ (-(w y))) * ((x : ℂ) ^ (w y + 1) / den y) := by
          simp only [F, div_eq_mul_inv, mul_assoc]
      _ = ∑' n : ℕ, (a n : ℂ) * (n : ℂ) ^ (-(w y)) * ((x : ℂ) ^ (w y + 1) / den y) :=
          (hsum.tsum_mul_right _).symm
      _ = ∑' n : ℕ, G n y :=
          tsum_congr (fun n => by simp only [G, div_eq_mul_inv, mul_assoc])

  -- (f) interchange integration and summation
  have hbd : ∀ n y, y ∈ Set.Icc (-T) T → ‖G n y‖ ≤ g n := by
    intro n y _
    have h1 := hG_bound n y
    have h2 : 0 ≤ C0 * (a n / (n : ℝ) ^ c) := mul_nonneg hC0nn (hgnonneg n)
    have h3 : 1 ≤ 2 * T := by linarith
    have h4 : C0 * (a n / (n : ℝ) ^ c) ≤ 2 * T * (C0 * (a n / (n : ℝ) ^ c)) :=
      le_mul_of_one_le_left h2 h3
    exact le_trans h1 h4
  have hInt : ∫ y in (-T)..T, F y = ∑' n : ℕ, ∫ y in (-T)..T, G n y := by
    have h1 : (∫ y in (-T)..T, F y) = ∫ y in (-T)..T, (∑' n : ℕ, G n y) :=
      intervalIntegral.integral_congr (fun y _ => hF_eq y)
    rw [h1]
    exact intervalIntegral_tsum_of_dominated hTle G g hG_cont hg_summable hbd
  have hIntGnorm_bound : ∀ n, ‖∫ y in (-T)..T, G n y‖ ≤ g n := by
    intro n
    calc ‖∫ y in (-T)..T, G n y‖ ≤ ∫ y in (-T)..T, ‖G n y‖ :=
          intervalIntegral.norm_integral_le_integral_norm hTle
      _ ≤ ∫ y in (-T)..T, (C0 * (a n / (n : ℝ) ^ c)) := by
          refine intervalIntegral.integral_mono_on hTle ?_ ?_ ?_
          · exact ((hG_cont n).norm).intervalIntegrable _ _
          · exact intervalIntegrable_const
          · intro y _
            exact hG_bound n y
      _ = (T - (-T)) * (C0 * (a n / (n : ℝ) ^ c)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ = g n := by
          simp only [g]
          ring
  have hSumIntGnorm : Summable (fun n => ‖∫ y in (-T)..T, G n y‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hIntGnorm_bound hg_summable
  have hSumIntG : Summable (fun n => ∫ y in (-T)..T, G n y) := hSumIntGnorm.of_norm

  -- (g) the individual integrals
  have hK0 : K 0 = 0 := by
    have hzero : (fun y : ℝ => rieszKern (x / ((0 : ℕ) : ℝ)) c y) = fun _ : ℝ => 0 := by
      funext y
      have hx0' : x / ((0 : ℕ) : ℝ) = 0 := by simp
      rw [hx0']
      have hne : ((c : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have h1 : (((c : ℂ) + (y : ℂ) * Complex.I)).re = c := by
          simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
        have h2 : (((c : ℂ) + (y : ℂ) * Complex.I)).re = 0 := by rw [h, Complex.zero_re]
        linarith
      simp [rieszKern, Complex.zero_cpow hne]
    simp only [K]
    rw [hzero]
    simp
  have hIntG : ∀ n, (1 / (2 * Real.pi)) * (∫ y in (-T)..T, G n y) = Θ n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have h0 : ∫ y in (-T)..T, G 0 y = 0 := by
        rw [hG_zero]
        simp
      have hTheta0 : Θ 0 = 0 := by simp [Θ, hK0]
      rw [h0, hTheta0, mul_zero]
    · have h1 : (∫ y in (-T)..T, G n y)
          = ∫ y in (-T)..T, ((a n : ℂ) * (x : ℂ)) * rieszKern (x / (n : ℝ)) c y := by
        refine intervalIntegral.integral_congr (fun y _ => ?_)
        rw [hG_eq n y hn]
      rw [h1, intervalIntegral.integral_const_mul]
      simp only [Θ, K]
      ring

  -- (h) termwise comparison with the main term
  have hPoint : ∀ n, ‖Θ n - Ψ n‖ ≤ (x ^ (c + 1) / T) * (a n / (n : ℝ) ^ c) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hTheta0 : Θ 0 = 0 := by simp [Θ, hK0]
      have hP0 : Ψ 0 = 0 := by simp [Ψ]
      have h1 : (((0 : ℕ) : ℝ)) ^ c = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow hc0.ne']
      rw [hTheta0, hP0, sub_zero, norm_zero, h1, div_zero, mul_zero]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hmax : max (x - (n : ℝ)) 0 = x * max (1 - (n : ℝ) / x) 0 := by
        rw [mul_max_of_nonneg _ _ hx0.le, mul_zero]
        congr 1
        field_simp
      have hPsi : Ψ n = (a n : ℂ) * (x : ℂ) * (((max (1 - (n : ℝ) / x) 0 : ℝ)) : ℂ) := by
        simp only [Ψ, if_neg hn]
        rw [hmax, Complex.ofReal_mul]
        ring
      have hdev := rieszKernel_deviation c T (x / (n : ℝ)) hc hT (div_pos hx0 hnpos)
      have hdiv : 1 / (x / (n : ℝ)) = (n : ℝ) / x := one_div_div _ _
      rw [hdiv] at hdev
      have hK : ‖K n - (((max (1 - (n : ℝ) / x) 0 : ℝ)) : ℂ)‖ ≤ (x / (n : ℝ)) ^ c / T := by
        simpa only [K, rieszKern] using hdev
      have hdiff : Θ n - Ψ n
          = ((a n : ℂ) * (x : ℂ)) * (K n - (((max (1 - (n : ℝ) / x) 0 : ℝ)) : ℂ)) := by
        rw [hPsi]
        simp only [Θ]
        ring
      rw [hdiff, norm_mul,
        show ‖((a n : ℂ) * (x : ℂ))‖ = a n * x from by
          rw [← Complex.ofReal_mul, norm_ofReal_nonneg _ (mul_nonneg (ha n) hx0.le)]]
      calc a n * x * ‖K n - (((max (1 - (n : ℝ) / x) 0 : ℝ)) : ℂ)‖
          ≤ a n * x * ((x / (n : ℝ)) ^ c / T) :=
            mul_le_mul_of_nonneg_left hK (mul_nonneg (ha n) hx0.le)
        _ = x ^ (c + 1) / T * (a n / (n : ℝ) ^ c) :=
            riesz_term_algebra (a n) x T (n : ℝ) c hx0 hnpos

  -- (i) summability of the two series
  have hSumTheta : Summable Θ := by
    have h1 : (fun n : ℕ => (1 / (2 * Real.pi)) * (∫ y in (-T)..T, G n y)) = Θ :=
      funext (fun n => hIntG n)
    rw [← h1]
    exact hSumIntG.mul_left _
  have hvanish : ∀ b ∉ Finset.Icc 1 ⌊x⌋₊, Ψ b = 0 := by
    intro b hb
    by_cases hb0 : b = 0
    · simp [Ψ, hb0]
    · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
      have hbfloor : ⌊x⌋₊ < b := by
        by_contra hcon
        exact hb (Finset.mem_Icc.mpr ⟨hb1, by omega⟩)
      have hxb : x < (b : ℝ) := by
        have h1 : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ (b : ℝ) := by
          have h2 : ⌊x⌋₊ + 1 ≤ b := by omega
          exact_mod_cast h2
        have h2 := Nat.lt_floor_add_one x
        linarith
      simp only [Ψ, if_neg hb0,
        max_eq_right (show x - (b : ℝ) ≤ 0 by linarith), Complex.ofReal_zero, mul_zero]
  have hSumPsi : Summable Ψ := (hasSum_sum_of_ne_finset_zero hvanish).summable
  have hBnd : Summable (fun n : ℕ => x ^ (c + 1) / T * (a n / (n : ℝ) ^ c)) :=
    hS.mul_left _

  -- (j) the Perron integral equals the sum of the main terms
  have hmain : (1 / (2 * Real.pi)) * (∫ y in (-T)..T, F y) = ∑' n : ℕ, Θ n := by
    rw [hInt]
    have h2 : (∑' n : ℕ, (1 / (2 * Real.pi)) * (∫ y in (-T)..T, G n y)) = ∑' n : ℕ, Θ n :=
      tsum_congr (fun n => hIntG n)
    rw [← h2]
    exact (hSumIntG.tsum_mul_left (1 / (2 * Real.pi) : ℂ)).symm

  -- (k) the finite sum equals the series of main terms
  have hfin : (∑' n : ℕ, Ψ n)
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (a n : ℂ) * (((x - (n : ℝ)) : ℝ) : ℂ) := by
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) hvanish]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    have hnx : (n : ℝ) ≤ x := by
      have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hn).2
      have h2 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0.le
      calc (n : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ x := h2
    simp only [Ψ, if_neg hn0,
      max_eq_left (show (0:ℝ) ≤ x - (n : ℝ) by linarith)]

  -- final assembly
  have hdiffnorm : Summable (fun n : ℕ => ‖Θ n - Ψ n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hPoint hBnd
  have hkey : ‖∑' n : ℕ, Θ n - ∑' n : ℕ, Ψ n‖
      ≤ x ^ (c + 1) / T * (∑' n : ℕ, (a n) / (n : ℝ) ^ c) := by
    rw [← Summable.tsum_sub hSumTheta hSumPsi]
    calc ‖∑' n : ℕ, (Θ n - Ψ n)‖ ≤ ∑' n : ℕ, ‖Θ n - Ψ n‖ :=
          norm_tsum_le_tsum_norm hdiffnorm
      _ ≤ ∑' n : ℕ, x ^ (c + 1) / T * (a n / (n : ℝ) ^ c) :=
          Summable.tsum_le_tsum hPoint hdiffnorm hBnd
      _ = x ^ (c + 1) / T * (∑' n : ℕ, (a n) / (n : ℝ) ^ c) :=
          tsum_mul_left
  calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (a n : ℂ) * (((x - (n : ℝ)) : ℝ) : ℂ))
        - (1 / (2 * Real.pi)) * (∫ y in (-T)..T, F y)‖
      = ‖(1 / (2 * Real.pi)) * (∫ y in (-T)..T, F y)
        - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (a n : ℂ) * (((x - (n : ℝ)) : ℝ) : ℂ))‖ :=
        norm_sub_rev _ _
    _ = ‖∑' n : ℕ, Θ n - ∑' n : ℕ, Ψ n‖ := by rw [hmain, hfin]
    _ ≤ x ^ (c + 1) / T * (∑' n : ℕ, (a n) / (n : ℝ) ^ c) := hkey

end Commons.Analysis.Perron
