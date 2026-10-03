import Mathlib
import Submission.Work.FITop3.Defs3

namespace Work.FIArea6

noncomputable section
open Real

set_option maxHeartbeats 4000000

/-- `log n ≤ n/48000` for `n ≥ 1e8`. -/
private lemma log_le_div_48000 (n : ℝ) (hn : (1e8:ℝ) ≤ n) : Real.log n ≤ n / 48000 := by
  have hn0 : 0 < n := by linarith
  have hlog := Real.log_le_rpow_div (le_of_lt hn0) (show (0:ℝ) < 1/4 by norm_num)
  set m : ℝ := n ^ (1/4:ℝ) with hm
  have hmpos : 0 < m := by rw [hm]; exact Real.rpow_pos_of_pos hn0 _
  have hdiv : n ^ (1/4:ℝ) / (1/4:ℝ) = 4 * m := by rw [hm]; ring
  rw [hdiv] at hlog
  have hpow4 : m ^ 4 = n := by
    rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hn0)]
    norm_num
  have h100 : ((1e8:ℝ)) ^ (1/4:ℝ) = 100 := by
    have h : ((100:ℝ)) ^ (4:ℕ) = (1e8:ℝ) := by norm_num
    rw [← h, ← Real.rpow_natCast (100:ℝ) 4,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 100)]
    norm_num
  have hm100 : (100:ℝ) ≤ m := by
    rw [hm, ← h100]
    exact Real.rpow_le_rpow (by norm_num) hn (by norm_num)
  have hm3 : (192000:ℝ) ≤ m^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 100) hm100 3
    norm_num at h
    linarith
  have key : (192000:ℝ) * m ≤ m ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hm3 (le_of_lt hmpos)
    have h4 : m^3 * m = m^4 := by ring
    linarith
  have hmn : (192000:ℝ) * m ≤ n := by rw [← hpow4]; exact key
  have h4m : 4 * m ≤ n / 48000 := by linarith
  linarith [hlog, h4m]

/-- Bound on the exponential factor `F`. -/
private lemma F_bound (n y : ℝ) (hn1 : (1:ℝ) ≤ n) (hy2 : 2 ≤ y)
    (hy : Real.log y ≤ n/2) (hy1 : Real.log y + 1 ≤ n) :
    (Real.log y + 1) * Real.exp (4000 * (Real.log (Real.log y) + 1))
      ≤ (2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) * Real.exp 4000 := by
  have hly0 : 0 < Real.log y := Real.log_pos (by linarith)
  have hexp : Real.exp (4000 * (Real.log (Real.log y) + 1))
      = (Real.log y)^(4000:ℝ) * Real.exp 4000 := by
    have h1 : 4000 * (Real.log (Real.log y) + 1)
        = 4000 * Real.log (Real.log y) + 4000 := by ring
    rw [h1, Real.exp_add]
    congr 1
    rw [mul_comm 4000, ← Real.rpow_def_of_pos hly0 (4000:ℝ)]
  have hstep1 : (Real.log y)^(4000:ℝ) ≤ (n/2)^(4000:ℝ) :=
    Real.rpow_le_rpow (le_of_lt hly0) hy (by norm_num)
  have hhalf : (1/2:ℝ)^(4000:ℝ) = (2:ℝ)^(-4000:ℝ) := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  have hstep2 : (n/2)^(4000:ℝ) = (2:ℝ)^(-4000:ℝ) * n^(4000:ℝ) := by
    rw [show n/2 = n * (1/2) by ring, Real.mul_rpow (by linarith) (by norm_num), hhalf]
    ring
  have hn401 : n * n^(4000:ℝ) = n^(4001:ℝ) := by
    have h : n * n^(4000:ℝ) = n^(1:ℝ) * n^(4000:ℝ) := by rw [Real.rpow_one]
    rw [h, ← Real.rpow_add (by linarith : (0:ℝ) < n)]
    norm_num
  have hstep3 : (Real.log y + 1) * (Real.log y)^(4000:ℝ) ≤ (2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) := by
    have h2 : (0:ℝ) ≤ (Real.log y)^(4000:ℝ) := Real.rpow_nonneg (le_of_lt hly0) _
    have h3 : (0:ℝ) ≤ n := by linarith
    have hb : (Real.log y + 1) * (Real.log y)^(4000:ℝ) ≤ n * (Real.log y)^(4000:ℝ) :=
      mul_le_mul_of_nonneg_right hy1 h2
    have ha : n * (Real.log y)^(4000:ℝ) ≤ n * (n/2)^(4000:ℝ) :=
      mul_le_mul_of_nonneg_left hstep1 h3
    have hc : n * (n/2)^(4000:ℝ) = (2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) := by
      rw [hstep2,
          show n * ((2:ℝ)^(-4000:ℝ) * n^(4000:ℝ)) = (2:ℝ)^(-4000:ℝ) * (n * n^(4000:ℝ)) by ring,
          hn401]
    linarith [hb, ha, hc]
  rw [hexp]
  calc (Real.log y + 1) * ((Real.log y)^(4000:ℝ) * Real.exp 4000)
      = ((Real.log y + 1) * (Real.log y)^(4000:ℝ)) * Real.exp 4000 := by ring
    _ ≤ ((2:ℝ)^(-4000:ℝ) * n^(4001:ℝ)) * Real.exp 4000 :=
        mul_le_mul_of_nonneg_right hstep3 (Real.exp_pos 4000).le
    _ = (2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) * Real.exp 4000 := by ring

/-- `80·2^{1/3}·2^{-4000}·e^{4000}·n^{3998} ≤ e^{n/6}` for `n ≥ 1e8`. -/
private lemma exp_beta (n : ℝ) (hn : (1e8:ℝ) ≤ n) :
    (80:ℝ) * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ) * Real.exp 4000 * n^(3998:ℝ)
      ≤ Real.exp (n/6) := by
  have hn0 : 0 < n := by linarith
  have hconst : (80:ℝ) * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ) ≤ 160 := by
    have h1 : (2:ℝ)^(1/3:ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (show (1:ℝ)/3 ≤ 1 by norm_num)
      simpa [Real.rpow_one] using this
    have h2 : (2:ℝ)^(-4000:ℝ) ≤ 1 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (show (-4000:ℝ) ≤ 0 by norm_num)
      simpa [Real.rpow_zero] using this
    have h2n : (0:ℝ) ≤ (2:ℝ)^(-4000:ℝ) := Real.rpow_nonneg (by norm_num) _
    have h1n : (0:ℝ) ≤ (2:ℝ)^(1/3:ℝ) := Real.rpow_nonneg (by norm_num) _
    have hmm : (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ) ≤ 2 := by
      have := mul_le_mul h1 h2 h2n (by norm_num : (0:ℝ) ≤ 2)
      simpa using this
    calc (80:ℝ) * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ)
        = 80 * ((2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ)) := by ring
      _ ≤ 80 * 2 := by linarith [hmm]
      _ = 160 := by norm_num
  have hlog160 : Real.log 160 ≤ 160 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 160); linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
  have hmain : Real.log 160 + 4000 + 3998 * Real.log n ≤ n/6 := by
    have hlogn := log_le_div_48000 n hn
    have h1 : 3998 * Real.log n ≤ 3998 * (n/48000) :=
      mul_le_mul_of_nonneg_left hlogn (by norm_num)
    nlinarith [hlog160, h1, hn]
  have hexp : 160 * Real.exp 4000 * n^(3998:ℝ) ≤ Real.exp (n/6) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 160)]
    rw [show Real.exp (Real.log 160) * Real.exp 4000 = Real.exp (Real.log 160 + 4000) by
        rw [Real.exp_add]]
    rw [Real.rpow_def_of_pos hn0 (3998:ℝ), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hmain]
  calc (80:ℝ) * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ) * Real.exp 4000 * n^(3998:ℝ)
      = ((80:ℝ) * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ)) * (Real.exp 4000 * n^(3998:ℝ)) := by ring
    _ ≤ 160 * (Real.exp 4000 * n^(3998:ℝ)) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = 160 * Real.exp 4000 * n^(3998:ℝ) := by ring
    _ ≤ Real.exp (n/6) := hexp

/-- `100·2^{-(2^20+4000)}·e^{4000} ≤ 1`. -/
private lemma alpha_const : (100:ℝ) * (2:ℝ)^(-((2:ℝ)^20 + 4000 : ℝ)) * Real.exp 4000 ≤ 1 := by
  have h100exp : (100:ℝ) ≤ Real.exp 6 := by
    have h1 : (100:ℝ) ≤ (2.7:ℝ)^6 := by norm_num
    have h2 : (2.7:ℝ)^6 ≤ (Real.exp 1)^6 :=
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7)
        (by linarith [Real.exp_one_gt_d9] : (2.7:ℝ) ≤ Real.exp 1) 6
    have h3 : (Real.exp 1)^6 = Real.exp 6 := by
      rw [← Real.exp_nat_mul 1 6]; norm_num
    linarith
  have hnum : (100:ℝ) * Real.exp 4000 ≤ (2:ℝ)^(((2:ℝ)^20) + 4000 : ℝ) := by
    have h2 : (100:ℝ) * Real.exp 4000 ≤ Real.exp 6 * Real.exp 4000 :=
      mul_le_mul_of_nonneg_right h100exp (Real.exp_pos 4000).le
    rw [← Real.exp_add] at h2
    have h3 : Real.exp (6 + 4000) ≤ Real.exp (524288:ℝ) := Real.exp_le_exp.mpr (by norm_num)
    have h4 : Real.exp (524288:ℝ) ≤ (2:ℝ)^(((2:ℝ)^20) : ℝ) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) (((2:ℝ)^20) : ℝ)]
      apply Real.exp_le_exp.mpr
      have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith
    have h5 : (2:ℝ)^(((2:ℝ)^20) : ℝ) ≤ (2:ℝ)^(((2:ℝ)^20) + 4000 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith
  have hden : (0:ℝ) < (2:ℝ)^(((2:ℝ)^20) + 4000 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (100:ℝ) * ((2:ℝ) ^ (((2:ℝ)^20) + 4000 : ℝ))⁻¹ * Real.exp 4000
        = ((100:ℝ) * Real.exp 4000) * ((2:ℝ) ^ (((2:ℝ)^20) + 4000 : ℝ))⁻¹ by ring]
  rw [← div_eq_mul_inv, div_le_one hden]
  exact hnum

/-- `16·2^{2/3}·2^{-4000} ≤ n²` for `n ≥ 1e8`. -/
private lemma gamma_const (n : ℝ) (hn : (1e8:ℝ) ≤ n) :
    (16:ℝ) * (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-4000:ℝ) ≤ n^2 := by
  have h1 : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show (2:ℝ)/3 ≤ 1 by norm_num)
    simpa [Real.rpow_one] using this
  have h2 : (2:ℝ)^(-4000:ℝ) ≤ 1 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show (-4000:ℝ) ≤ 0 by norm_num)
    simpa [Real.rpow_zero] using this
  have h2n : (0:ℝ) ≤ (2:ℝ)^(-4000:ℝ) := Real.rpow_nonneg (by norm_num) _
  have h1n : (0:ℝ) ≤ (2:ℝ)^(2/3:ℝ) := Real.rpow_nonneg (by norm_num) _
  have h16 : (16:ℝ) * (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-4000:ℝ) ≤ 32 := by
    have hmm : (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-4000:ℝ) ≤ 2 := by
      have := mul_le_mul h1 h2 h2n (by norm_num : (0:ℝ) ≤ 2)
      simpa using this
    calc (16:ℝ) * (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-4000:ℝ)
        = 16 * ((2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-4000:ℝ)) := by ring
      _ ≤ 16 * 2 := by linarith [hmm]
      _ = 32 := by norm_num
  nlinarith [h16, hn, sq_nonneg n]

theorem lattice_numeric_final (Pa : Work.FITop.Params) (Y : ℕ) (hY2 : 2 ≤ Y)
    (hYbound : (Y:ℝ) ≤ 2 * (((2 * Pa.N : ℝ)) ^ (1/3:ℝ)) + 2)
    (hu20 : 20 < Real.log (Real.log (Pa.x : ℝ)))
    (hlogN : (1e8:ℝ) < Real.log (Pa.N : ℝ)) (hN1 : (1:ℝ) ≤ Pa.N) (hθ0 : 0 < Pa.θ)
    (hA' : Pa.A' * Real.log (Real.log (Pa.x : ℝ))
      ≤ Real.log (Pa.N) / 3 - 4000 * (1 + Real.log (Real.log (Pa.N : ℝ)))) :
    100 * (100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y ^ 2)
      * ((Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1)))
      ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
  set nr : ℝ := Pa.N with hnr
  set xr : ℝ := (Pa.x : ℝ) with hxr
  set L : ℝ := Real.log xr with hL
  set LL : ℝ := Real.log L with hLL
  set n : ℝ := Real.log nr with hn
  set y : ℝ := (Y : ℝ) with hy
  set t : ℝ := Pa.θ with ht
  set ap : ℝ := Pa.A' with hap
  set F : ℝ := (Real.log y + 1) * Real.exp (4000 * (Real.log (Real.log y) + 1)) with hFdef
  set D : ℝ := (Real.log (2 + nr)) ^ 3 with hDdef
  have hnr0 : (0:ℝ) < nr := by rw [hnr]; linarith [hN1]
  have hnr1 : (1:ℝ) ≤ nr := by rw [hnr]; exact hN1
  have hn8 : (1e8:ℝ) < n := by rw [hn]; exact hlogN
  have hn0 : (0:ℝ) < n := by linarith
  have hnn : (0:ℝ) ≤ n := le_of_lt hn0
  have hxr3 : (3:ℝ) ≤ xr := by rw [hxr]; exact_mod_cast Pa.hx
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hLL20 : 20 < LL := hu20
  have hLLpos : 0 < LL := by linarith
  have hy2 : (2:ℝ) ≤ y := by rw [hy]; exact_mod_cast hY2
  have hy0 : 0 < y := by linarith
  have hlogNhi : n < Real.log (xr ^ ((1:ℝ)/2) * L ^ (-Pa.B)) := by
    rw [hn]
    exact Real.log_lt_log hnr0 Pa.hNhi
  have hlog_split : Real.log (xr ^ ((1:ℝ)/2) * L ^ (-Pa.B)) = L/2 - Pa.B * LL := by
    have hu : (0:ℝ) < xr ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < xr) (1/2)
    have hv : (0:ℝ) < L ^ (-Pa.B) := Real.rpow_pos_of_pos hLpos (-Pa.B)
    rw [Real.log_mul (ne_of_gt hu) (ne_of_gt hv),
        Real.log_rpow (by linarith : (0:ℝ) < xr) (1/2),
        Real.log_rpow hLpos (-Pa.B)]
    rw [← hL, ← hLL]
    ring
  have hLgt : 2 * n < L := by
    have hB : 0 < Pa.B := Pa.hB
    have : 0 < Pa.B * LL := mul_pos hB hLLpos
    linarith [hlogNhi, hlog_split]
  have hlogNlo : (1/4 + Pa.η) * L < n := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < xr) _) Pa.hNlo
    rw [Real.log_rpow (by linarith : (0:ℝ) < xr), ← hL, ← hn] at h
    exact h
  have hLlt : L < 4 * n := by
    have hη : 0 < Pa.η := Pa.hη
    nlinarith [hlogNlo]
  have ht_eq : t = Real.exp (-(ap * LL)) := by
    have hh : t = L ^ (-ap) := by rw [ht]; exact Pa.hθ
    rw [hh, Real.rpow_def_of_pos hLpos (-ap), ← hLL]
    congr 1
    ring
  have hA'hyp : ap * LL ≤ n/3 - 4000 * (1 + Real.log n) := hA'
  have hlog2n : 0 < Real.log (2*n) := Real.log_pos (by linarith)
  have hLLge : Real.log (2*n) ≤ LL := by
    rw [hLL]; exact le_of_lt (Real.log_lt_log (by linarith : (0:ℝ) < 2*n) hLgt)
  have hap_ge : (2:ℝ)^20 ≤ ap := by
    rw [hap]; nlinarith [Pa.hA', Pa.hA]
  have ht_le : t ≤ Real.exp (-((2:ℝ)^20 * Real.log (2*n))) := by
    rw [ht_eq]
    apply Real.exp_le_exp.mpr
    have h1 : (2:ℝ)^20 * Real.log (2*n) ≤ (2:ℝ)^20 * LL :=
      mul_le_mul_of_nonneg_left hLLge (by positivity)
    have h2 : (2:ℝ)^20 * LL ≤ ap * LL :=
      mul_le_mul_of_nonneg_right hap_ge (le_of_lt hLLpos)
    linarith [h1, h2]
  have ht_lower : Real.exp (-(n/3) + 4000 * (1 + Real.log n)) ≤ t := by
    rw [ht_eq]
    apply Real.exp_le_exp.mpr
    linarith [hA'hyp]
  have hybound : y ≤ 4 * (2:ℝ)^(1/3:ℝ) * nr^(1/3:ℝ) := by
    have h1 := hYbound
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hnr0)] at h1
    have h2 : (2:ℝ) ≤ 2 * ((2:ℝ)^(1/3:ℝ) * nr^(1/3:ℝ)) := by
      have ha : (1:ℝ) ≤ (2:ℝ)^(1/3:ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
      have hb : (1:ℝ) ≤ nr^(1/3:ℝ) := Real.one_le_rpow hnr1 (by norm_num)
      have hp : (1:ℝ) ≤ (2:ℝ)^(1/3:ℝ) * nr^(1/3:ℝ) := by
        simpa using mul_le_mul ha hb (by norm_num) (le_trans zero_le_one ha)
      linarith
    linarith [h1, h2]
  have hpow13 : nr^(1/3:ℝ) = Real.exp (n/3) := by
    rw [Real.rpow_def_of_pos hnr0, ← hn]
    congr 1; ring
  have hsqrt : Real.sqrt nr = Real.exp (n/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnr0, ← hn]
    congr 1; ring
  have hy_exp : y ≤ 4 * (2:ℝ)^(1/3:ℝ) * Real.exp (n/3) := by
    rw [← hpow13]; exact hybound
  have hylog_le : Real.log y ≤ n/3 + 4 := by
    have h := Real.log_le_log hy0 hybound
    have hsplit : Real.log (4 * (2:ℝ)^(1/3:ℝ) * nr^(1/3:ℝ))
        = Real.log 4 + Real.log ((2:ℝ)^(1/3:ℝ)) + Real.log (nr^(1/3:ℝ)) := by
      rw [Real.log_mul (by positivity)
            (ne_of_gt (Real.rpow_pos_of_pos hnr0 _)),
          Real.log_mul (by norm_num : (4:ℝ) ≠ 0)
            (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _))]
    rw [hsplit, Real.log_rpow (by norm_num : (0:ℝ) < 2) (1/3),
        Real.log_rpow hnr0 (1/3), ← hn] at h
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  have hylog_half : Real.log y ≤ n/2 := by linarith [hylog_le, hn8]
  have hylog_1 : Real.log y + 1 ≤ n := by linarith [hylog_le, hn8]
  have hFbound : F ≤ (2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) * Real.exp 4000 := by
    rw [hFdef]
    exact F_bound n y (by linarith) hy2 hylog_half hylog_1
  have hFnonneg : (0:ℝ) ≤ F := by rw [hFdef]; positivity
  have hlog_ge_n : n ≤ Real.log (2 + nr) := by
    rw [hn]
    exact Real.log_le_log hnr0 (by linarith)
  have hD1 : (1:ℝ) ≤ D := by
    rw [hDdef]
    have h1 : (1:ℝ) ≤ Real.log (2 + nr) := by linarith [hlog_ge_n, hn8]
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h1 3
  have hDn3 : n^3 ≤ D := by
    rw [hDdef]; exact pow_le_pow_left₀ hnn hlog_ge_n 3
  have hD0 : (0:ℝ) ≤ D := by linarith [hD1]
  have halpha : 100 * t * F ≤ D := by
    have htF : t * F ≤ (100:ℝ)⁻¹ := by
      have hstep1 : t * F ≤ Real.exp (-((2:ℝ)^20 * Real.log (2*n))) *
          ((2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) * Real.exp 4000) :=
        mul_le_mul ht_le hFbound hFnonneg (Real.exp_nonneg _)
      have h2 : Real.exp (-((2:ℝ)^20 * Real.log (2*n))) = (2*n)^(-(2:ℝ)^20) := by
        rw [show -((2:ℝ)^20 * Real.log (2*n)) = Real.log (2*n) * (-(2:ℝ)^20) by ring,
            ← Real.rpow_def_of_pos (by positivity : (0:ℝ) < 2*n) (-(2:ℝ)^20)]
      rw [h2] at hstep1
      have h3 : (2*n)^(-(2:ℝ)^20) = (2:ℝ)^(-(2:ℝ)^20) * n^(-(2:ℝ)^20) :=
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hn0)
      rw [h3] at hstep1
      have hcomb : (2:ℝ)^(-(2:ℝ)^20) * n^(-(2:ℝ)^20) *
            ((2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) * Real.exp 4000)
          = (2:ℝ)^(-((2:ℝ)^20 + 4000)) * n^(4001 - (2:ℝ)^20) * Real.exp 4000 := by
        rw [show (2:ℝ)^(-((2:ℝ)^20 + 4000)) = (2:ℝ)^(-(2:ℝ)^20) * (2:ℝ)^(-4000:ℝ) by
              rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
              congr 1; ring,
            show n^(4001 - (2:ℝ)^20) = n^(-(2:ℝ)^20) * n^(4001:ℝ) by
              rw [← Real.rpow_add hn0]
              congr 1; ring]
        ring
      rw [hcomb] at hstep1
      have h4 : n^(4001 - (2:ℝ)^20) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1:ℝ) ≤ n) (by norm_num)
      have h5 : (0:ℝ) ≤ (2:ℝ)^(-((2:ℝ)^20 + 4000)) * Real.exp 4000 :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _)
      have h6 : (2:ℝ)^(-((2:ℝ)^20 + 4000)) * n^(4001 - (2:ℝ)^20) * Real.exp 4000
          ≤ (2:ℝ)^(-((2:ℝ)^20 + 4000)) * Real.exp 4000 := by
        calc (2:ℝ)^(-((2:ℝ)^20 + 4000)) * n^(4001 - (2:ℝ)^20) * Real.exp 4000
            = (2:ℝ)^(-((2:ℝ)^20 + 4000)) * Real.exp 4000 * n^(4001 - (2:ℝ)^20) := by ring
          _ ≤ (2:ℝ)^(-((2:ℝ)^20 + 4000)) * Real.exp 4000 * 1 :=
              mul_le_mul_of_nonneg_left h4 h5
          _ = (2:ℝ)^(-((2:ℝ)^20 + 4000)) * Real.exp 4000 := by ring
      have h7 : (2:ℝ)^(-((2:ℝ)^20 + 4000)) * Real.exp 4000 ≤ (100:ℝ)⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ (by norm_num : (0:ℝ) < 100)]
        linarith [alpha_const]
      calc t * F ≤ (2:ℝ)^(-((2:ℝ)^20 + 4000)) * n^(4001 - (2:ℝ)^20) * Real.exp 4000 := hstep1
        _ ≤ (2:ℝ)^(-((2:ℝ)^20 + 4000)) * Real.exp 4000 := h6
        _ ≤ (100:ℝ)⁻¹ := h7
    have h1 : 100 * t * F ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left htF (by norm_num : (0:ℝ) ≤ 100)
      have h100 : (100:ℝ) * (100:ℝ)⁻¹ = 1 := by norm_num
      calc 100 * t * F = 100 * (t * F) := by ring
        _ ≤ 100 * (100:ℝ)⁻¹ := h
        _ = 1 := h100
    linarith [h1, hD1]
  have keya : 100 * (100 * t^2 * nr) * F ≤ 100 * t * nr * D := by
    have hpos : (0:ℝ) ≤ 100 * t * nr :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hθ0)) (le_of_lt hnr0)
    have h := mul_le_mul_of_nonneg_left halpha hpos
    calc 100 * (100 * t^2 * nr) * F = (100 * t * nr) * (100 * t * F) := by ring
      _ ≤ (100 * t * nr) * D := h
      _ = 100 * t * nr * D := by ring
  have hbeta0 : 20 * y * F ≤ Real.sqrt nr * D := by
    have h1 : 20 * y * F ≤ 80 * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ) * Real.exp 4000
        * n^(4001:ℝ) * Real.exp (n/3) := by
      have ha : 20 * y ≤ 20 * (4 * (2:ℝ)^(1/3:ℝ) * Real.exp (n/3)) :=
        mul_le_mul_of_nonneg_left hy_exp (by norm_num)
      have hb : (0:ℝ) ≤ 20 * (4 * (2:ℝ)^(1/3:ℝ) * Real.exp (n/3)) :=
        mul_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
            (Real.exp_nonneg _))
      have h := mul_le_mul ha hFbound hFnonneg hb
      calc 20 * y * F
          ≤ (20 * (4 * (2:ℝ)^(1/3:ℝ) * Real.exp (n/3))) *
              ((2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) * Real.exp 4000) := h
        _ = 80 * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ) * Real.exp 4000 * n^(4001:ℝ)
              * Real.exp (n/3) := by ring
    have h2 : 80 * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ) * Real.exp 4000 * n^(4001:ℝ)
        * Real.exp (n/3) ≤ Real.exp (n/2) * n^3 := by
      have hb := exp_beta n (le_of_lt hn8)
      have hn401 : n^(4001:ℝ) = n^(3998:ℝ) * n^3 := by
        rw [← Real.rpow_natCast n 3, ← Real.rpow_add hn0]
        congr 1; norm_num
      rw [hn401]
      have hne : (0:ℝ) ≤ n^3 * Real.exp (n/3) :=
        mul_nonneg (pow_nonneg hnn 3) (Real.exp_nonneg _)
      calc 80 * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ) * Real.exp 4000 * (n^(3998:ℝ) * n^3)
            * Real.exp (n/3)
          = (80 * (2:ℝ)^(1/3:ℝ) * (2:ℝ)^(-4000:ℝ) * Real.exp 4000 * n^(3998:ℝ))
              * (n^3 * Real.exp (n/3)) := by ring
        _ ≤ Real.exp (n/6) * (n^3 * Real.exp (n/3)) :=
            mul_le_mul_of_nonneg_right hb hne
        _ = n^3 * (Real.exp (n/6) * Real.exp (n/3)) := by ring
        _ = n^3 * Real.exp (n/2) := by rw [← Real.exp_add]; congr 1; ring
        _ = Real.exp (n/2) * n^3 := by ring
    have h3 : Real.exp (n/2) * n^3 ≤ Real.exp (n/2) * D :=
      mul_le_mul_of_nonneg_left hDn3 (Real.exp_nonneg _)
    have h4 : Real.exp (n/2) * D = Real.sqrt nr * D := by rw [hsqrt]
    linarith [h1, h2, h3, h4]
  have keyb : 100 * (20 * t * Real.sqrt nr * y) * F ≤ 100 * t * nr * D := by
    have hs : (0:ℝ) ≤ Real.sqrt nr := Real.sqrt_nonneg _
    have hsq : Real.sqrt nr * Real.sqrt nr = nr := by
      rw [← sq]; exact Real.sq_sqrt (le_of_lt hnr0)
    have h := mul_le_mul_of_nonneg_left hbeta0 hs
    have h' : 20 * Real.sqrt nr * y * F ≤ nr * D := by nlinarith [h, hsq]
    have ht0 : (0:ℝ) ≤ 100 * t := mul_nonneg (by norm_num) (le_of_lt hθ0)
    have := mul_le_mul_of_nonneg_left h' ht0
    nlinarith [this]
  have hgamma : y^2 * F ≤ t * nr * D := by
    have hy2b : y^2 ≤ 16 * (2:ℝ)^(2/3:ℝ) * Real.exp (2*n/3) := by
      have h1 := pow_le_pow_left₀ (le_of_lt hy0) hy_exp 2
      have h2 : (4 * (2:ℝ)^(1/3:ℝ) * Real.exp (n/3))^2
          = 16 * (2:ℝ)^(2/3:ℝ) * Real.exp (2*n/3) := by
        have hA : ((2:ℝ)^(1/3:ℝ))^2 = (2:ℝ)^(2/3:ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
          congr 1; norm_num
        have hB : (Real.exp (n/3))^2 = Real.exp (2*n/3) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [show (4 * (2:ℝ)^(1/3:ℝ) * Real.exp (n/3))^2
              = 16 * ((2:ℝ)^(1/3:ℝ))^2 * (Real.exp (n/3))^2 by ring, hA, hB]
      rwa [h2] at h1
    have hnr_exp : nr = Real.exp n := by rw [hn, Real.exp_log hnr0]
    have ht_lower2 : Real.exp (2*n/3) * Real.exp 4000 * n^(4000:ℝ) ≤ t * nr := by
      rw [hnr_exp]
      have h1 : Real.exp (-(n/3) + 4000 * (1 + Real.log n)) * Real.exp n
          = Real.exp (2*n/3) * Real.exp 4000 * n^(4000:ℝ) := by
        rw [← Real.exp_add]
        rw [show -(n/3) + 4000 * (1 + Real.log n) + n
              = 2*n/3 + 4000 + 4000 * Real.log n by ring]
        rw [Real.exp_add, Real.exp_add]
        congr 1
        rw [show Real.exp (4000 * Real.log n) = n^(4000:ℝ) by
              rw [mul_comm, ← Real.rpow_def_of_pos hn0 (4000:ℝ)]]
      rw [← h1]
      exact mul_le_mul_of_nonneg_right ht_lower (Real.exp_pos n).le
    have h1 : y^2 * F ≤ (16 * (2:ℝ)^(2/3:ℝ) * Real.exp (2*n/3)) *
        ((2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) * Real.exp 4000) := by
      have hb : (0:ℝ) ≤ 16 * (2:ℝ)^(2/3:ℝ) * Real.exp (2*n/3) :=
        mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) (Real.exp_nonneg _)
      exact mul_le_mul hy2b hFbound hFnonneg hb
    have h2 : (16 * (2:ℝ)^(2/3:ℝ) * Real.exp (2*n/3)) *
        ((2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) * Real.exp 4000) ≤ t * nr * D := by
      have hc := gamma_const n (le_of_lt hn8)
      have hCn : (16 * (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-4000:ℝ)) * n^(4001:ℝ)
          ≤ n^(4000:ℝ) * D := by
        have h1 : (16 * (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-4000:ℝ)) * n^(4001:ℝ)
            ≤ n^2 * n^(4001:ℝ) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hnn _)
        have hrw1 : n^2 * n^(4001:ℝ) = n^(4003:ℝ) := by
          rw [← Real.rpow_natCast n 2, ← Real.rpow_add hn0]; congr 1; norm_num
        have hrw2 : n^(4003:ℝ) = n^(4000:ℝ) * n^3 := by
          rw [← Real.rpow_natCast n 3, ← Real.rpow_add hn0]; congr 1; norm_num
        have hge : n^(4000:ℝ) * n^3 ≤ n^(4000:ℝ) * D :=
          mul_le_mul_of_nonneg_left hDn3 (Real.rpow_nonneg hnn _)
        calc (16 * (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-4000:ℝ)) * n^(4001:ℝ)
            ≤ n^2 * n^(4001:ℝ) := h1
          _ = n^(4003:ℝ) := hrw1
          _ = n^(4000:ℝ) * n^3 := hrw2
          _ ≤ n^(4000:ℝ) * D := hge
      have hE : (0:ℝ) ≤ Real.exp (2*n/3) * Real.exp 4000 :=
        mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
      calc (16 * (2:ℝ)^(2/3:ℝ) * Real.exp (2*n/3)) *
            ((2:ℝ)^(-4000:ℝ) * n^(4001:ℝ) * Real.exp 4000)
          = (16 * (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-4000:ℝ)) * n^(4001:ℝ)
              * (Real.exp (2*n/3) * Real.exp 4000) := by ring
        _ ≤ (n^(4000:ℝ) * D) * (Real.exp (2*n/3) * Real.exp 4000) :=
            mul_le_mul_of_nonneg_right hCn hE
        _ = (Real.exp (2*n/3) * Real.exp 4000 * n^(4000:ℝ)) * D := by ring
        _ ≤ t * nr * D := mul_le_mul_of_nonneg_right ht_lower2 hD0
    linarith [h1, h2]
  have keyc : 100 * y^2 * F ≤ 100 * t * nr * D := by
    have h := mul_le_mul_of_nonneg_left hgamma (by norm_num : (0:ℝ) ≤ 100)
    linarith [h]
  have hsum : 100 * (100 * t^2 * nr + 20 * t * Real.sqrt nr * y + y^2) * F
      ≤ 1000 * (t * nr + Real.sqrt nr + 1) * D := by
    have e1 : 100 * (100 * t^2 * nr + 20 * t * Real.sqrt nr * y + y^2) * F
        = 100 * (100 * t^2 * nr) * F + 100 * (20 * t * Real.sqrt nr * y) * F
          + 100 * y^2 * F := by ring
    rw [e1]
    have h3 : 100 * (100 * t^2 * nr) * F + 100 * (20 * t * Real.sqrt nr * y) * F + 100 * y^2 * F
        ≤ 100 * t * nr * D + 100 * t * nr * D + 100 * t * nr * D := by
      linarith [keya, keyb, keyc]
    have hT : (0:ℝ) ≤ t * nr * D :=
      mul_nonneg (mul_nonneg (le_of_lt hθ0) (le_of_lt hnr0)) hD0
    have h4 : 100 * t * nr * D + 100 * t * nr * D + 100 * t * nr * D
        ≤ 1000 * (t * nr + Real.sqrt nr + 1) * D := by
      nlinarith [hT, hD0, Real.sqrt_nonneg nr]
    linarith [h3, h4]
  exact hsum

end

end Work.FIArea6
