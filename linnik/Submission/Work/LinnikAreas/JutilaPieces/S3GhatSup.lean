import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3FloorDefs
import Submission.Work.LinnikAreas.JutilaPieces.S3LogExpansion
import Submission.Work.LinnikAreas.JutilaPieces.S3BracketExpandBounded

set_option maxHeartbeats 2000000

namespace Work.LinnikAreas.JutilaPieces

/-- Under the range hypotheses of `S3GhatSup`, one has `q*r*t ≤ N`. -/
lemma s3Ghat_qrt_le (q r t z N : ℕ) (hq : 1 ≤ q) (hr1 : 1 ≤ r) (hz : 2 ≤ z) (hN : N < z*z)
    (hr : r ≤ N / (q*z)) (ht : t ≤ N / (q*z)) : q*r*t ≤ N := by
  have hqz : 0 < q*z := by positivity
  have hr' : r*(q*z) ≤ N := (Nat.le_div_iff_mul_le hqz).mp hr
  have ht' : t*(q*z) ≤ N := (Nat.le_div_iff_mul_le hqz).mp ht
  have hNpos : 0 < N :=
    lt_of_lt_of_le (by positivity : 0 < q*z)
      (le_trans (le_mul_of_one_le_left (Nat.zero_le (q*z)) hr1) hr')
  have hb : 0 < q*z*z := by positivity
  have hmul : (r*(q*z))*(t*(q*z)) ≤ N*N := Nat.mul_le_mul hr' ht'
  have heq : (r*(q*z))*(t*(q*z)) = (q*r*t)*(q*z*z) := by ring
  rw [heq] at hmul
  have hNz : N < q*z*z := by
    have h1 : z*z ≤ q*z*z := by nlinarith [hq]
    linarith
  have h2 : N*N < N*(q*z*z) := Nat.mul_lt_mul_of_pos_left hNz hNpos
  by_contra hcon
  push_neg at hcon
  have h3 : N*(q*z*z) < (q*r*t)*(q*z*z) := Nat.mul_lt_mul_of_pos_right hcon hb
  omega

/-- If `y ∈ [1/z, z]` then `|log y| ≤ log z`. -/
lemma s3_abs_log_le (y z : ℝ) (hzpos : 0 < z) (hy1 : 1/z ≤ y) (hy2 : y ≤ z)
    (hLz0 : 0 ≤ Real.log z) : |Real.log y| ≤ Real.log z := by
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy1
  have h1 : Real.log (1/z) ≤ Real.log y := Real.log_le_log (by positivity) hy1
  rw [Real.log_div one_ne_zero hzpos.ne', Real.log_one] at h1
  have h2 : Real.log y ≤ Real.log z := Real.log_le_log hypos hy2
  rw [abs_le]
  constructor <;> linarith

/-- `log (x*t/z) = log x - log (z/t)` for positive reals. -/
lemma s3_log_div_eq (x t z : ℝ) (hx : 0 < x) (ht : 0 < t) (hz : 0 < z) :
    Real.log (x * t / z) = Real.log x - Real.log (z / t) := by
  rw [Real.log_div (mul_ne_zero hx.ne' ht.ne') hz.ne', Real.log_mul hx.ne' ht.ne',
      Real.log_div hz.ne' ht.ne']
  ring

theorem S3GhatSup :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N q r t : ℕ), 2 ≤ z → N < z * z →
      1 ≤ q → 1 ≤ r → 1 ≤ t → r ≤ N / (q * z) → t ≤ N / (q * z) →
      |Work.LinnikAreas.JutilaPieces.s3Ghat z N q r t|
        ≤ C * (r : ℝ) * (Real.log (z : ℝ) + 2) ^ 2 := by
  refine ⟨9, by norm_num, ?_⟩
  intro z N q r t hz hN hq hr ht hrR htR
  have hqrt : q*r*t ≤ N := s3Ghat_qrt_le q r t z N hq hr hz hN hrR htR
  have hqrtpos : 0 < q*r*t := by positivity
  have hqR : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (by omega)
  have hrRn : (0:ℝ) < (r:ℝ) := Nat.cast_pos.mpr (by omega)
  have htRn : (0:ℝ) < (t:ℝ) := Nat.cast_pos.mpr (by omega)
  have hzR : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have hNR : (0:ℝ) < (N:ℝ) := by
    have h0 : 0 < N := lt_of_lt_of_le hqrtpos hqrt
    exact_mod_cast h0
  have hqrtR : (0:ℝ) < (q:ℝ)*(r:ℝ)*(t:ℝ) := by positivity
  have hLz0 : 0 ≤ Real.log (z:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
  have hNcast : (N:ℝ) < (z:ℝ)*(z:ℝ) := by exact_mod_cast hN
  have hqrt_le : ((q:ℝ)*(r:ℝ)*(t:ℝ)) ≤ (N:ℝ) := by
    have h : ((q*r*t:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hqrt
    rwa [show ((q*r*t:ℕ):ℝ) = (q:ℝ)*(r:ℝ)*(t:ℝ) by push_cast; ring] at h
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have ht1 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hr1R : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have htlt : (t:ℝ) < (z:ℝ) := by
    have ht' : ((t*(q*z):ℕ):ℝ) ≤ (N:ℝ) := by
      exact_mod_cast (Nat.le_div_iff_mul_le (by positivity : 0 < q*z)).mp htR
    have h2 : ((t*(q*z):ℕ):ℝ) = (t:ℝ)*(q:ℝ)*(z:ℝ) := by push_cast; ring
    rw [h2] at ht'
    have htz : (t:ℝ)*(q:ℝ) < (z:ℝ) := by
      have h1 : ((t:ℝ)*(q:ℝ)*(z:ℝ))/(z:ℝ) < (z:ℝ) := by
        rw [div_lt_iff₀ hzR]; linarith [ht', hNcast]
      rwa [mul_div_cancel_right₀ _ hzR.ne'] at h1
    have hle : (t:ℝ) ≤ (t:ℝ)*(q:ℝ) := by nlinarith [htRn, hq1]
    linarith
  have hrlt : (r:ℝ) < (z:ℝ) := by
    have hr' : ((r*(q*z):ℕ):ℝ) ≤ (N:ℝ) := by
      exact_mod_cast (Nat.le_div_iff_mul_le (by positivity : 0 < q*z)).mp hrR
    have h2 : ((r*(q*z):ℕ):ℝ) = (r:ℝ)*(q:ℝ)*(z:ℝ) := by push_cast; ring
    rw [h2] at hr'
    have hrz : (r:ℝ)*(q:ℝ) < (z:ℝ) := by
      have h1 : ((r:ℝ)*(q:ℝ)*(z:ℝ))/(z:ℝ) < (z:ℝ) := by
        rw [div_lt_iff₀ hzR]; linarith [hr', hNcast]
      rwa [mul_div_cancel_right₀ _ hzR.ne'] at h1
    have hle : (r:ℝ) ≤ (r:ℝ)*(q:ℝ) := by nlinarith [hrRn, hq1]
    linarith
  obtain ⟨hXle0, hXlt0⟩ := div_cast_bounds N (q*r*t) hqrtpos
  rw [show ((q*r*t:ℕ):ℝ) = (q:ℝ)*(r:ℝ)*(t:ℝ) by push_cast; ring] at hXle0 hXlt0
  set X : ℝ := ((N / (q*r*t) : ℕ) : ℝ) with hX
  set x : ℝ := (N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ)) with hx
  have hXle : X ≤ x := hXle0
  have hXlt : x < X + 1 := hXlt0
  have hXge0 : 0 ≤ X := by rw [hX]; positivity
  have hX1 : (1:ℝ) ≤ X := by
    rw [hX]
    exact_mod_cast ((Nat.le_div_iff_mul_le hqrtpos).mpr (by simpa using hqrt))
  have hxge1 : (1:ℝ) ≤ x := by
    rw [hx, le_div_iff₀ hqrtR]
    linarith [hqrt_le]
  have hqr1 : (1:ℝ) ≤ (q:ℝ)*(r:ℝ) := by
    have h := mul_le_mul hq1 hr1R (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (q:ℝ))
    simpa using h
  have hqt1 : (1:ℝ) ≤ (q:ℝ)*(t:ℝ) := by
    have h := mul_le_mul hq1 ht1 (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (q:ℝ))
    simpa using h
  have hqrtR1 : (1:ℝ) ≤ (q:ℝ)*(r:ℝ)*(t:ℝ) := by
    have h := mul_le_mul hqr1 ht1 (by norm_num : (0:ℝ) ≤ 1)
      (by linarith : (0:ℝ) ≤ (q:ℝ)*(r:ℝ))
    simpa using h
  have hxlez : x ≤ (z:ℝ)*(z:ℝ) := by
    rw [hx, div_le_iff₀ hqrtR]
    nlinarith [hNcast, hqrtR1]
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hxge1
  have hlogxz : Real.log x ≤ 2 * Real.log (z:ℝ) := by
    have h := Real.log_le_log (lt_of_lt_of_le zero_lt_one hxge1) hxlez
    rw [Real.log_mul hzR.ne' hzR.ne'] at h
    linarith
  have hlogzt0 : 0 ≤ Real.log ((z:ℝ)/(t:ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ htRn]
    linarith
  have hlogztle : Real.log ((z:ℝ)/(t:ℝ)) ≤ Real.log (z:ℝ) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ htRn]
    nlinarith [htRn, ht1, hzR]
  have hlogzr0 : 0 ≤ Real.log ((z:ℝ)/(r:ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hrRn]
    linarith
  have hlogzrle : Real.log ((z:ℝ)/(r:ℝ)) ≤ Real.log (z:ℝ) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hrRn]
    nlinarith [hrRn, hr1R, hzR]
  set K : ℝ := 2 * Real.log (z:ℝ) + 1 with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  set a : ℝ := Real.log x - Real.log ((z:ℝ)/(t:ℝ)) with ha
  set b : ℝ := Real.log x - Real.log ((z:ℝ)/(r:ℝ)) with hb
  have ha1 : |a - 1| ≤ K := by
    rw [abs_le, hK]
    constructor <;> rw [ha] <;> linarith [hlogx0, hlogxz, hlogzt0, hlogztle, hLz0]
  have ha2 : |b - 1| ≤ K := by
    rw [abs_le, hK]
    constructor <;> rw [hb] <;> linarith [hlogx0, hlogxz, hlogzr0, hlogzrle, hLz0]
  set A : ℝ := Real.log (((N / (q*r*t) : ℕ) : ℝ) * (t:ℝ)/(z:ℝ)) with hA
  set B : ℝ := Real.log (((N / (q*r*t) : ℕ) : ℝ) * (r:ℝ)/(z:ℝ)) with hB
  set ε : ℝ := 2 * (((q:ℝ)*(r:ℝ)*(t:ℝ)) / (N:ℝ)) with hε
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hlogA : |A - a| ≤ ε := by
    rw [hA, ha, hε]
    exact S3LogExpansion hq hr ht hz hqrt
  have hlogB0 := S3LogExpansion (N := N) (q := q) (r := t) (t := r) (z := z) hq ht hr hz
    (by linarith [hqrt])
  rw [show q*t*r = q*r*t by ring,
      show ((q:ℝ)*(t:ℝ)*(r:ℝ)) = ((q:ℝ)*(r:ℝ)*(t:ℝ)) by ring] at hlogB0
  have hlogB : |B - b| ≤ ε := by
    rw [hB, hb, hε]
    exact hlogB0
  have hε2 : ε ≤ 2 := by
    rw [hε, ← mul_div_assoc, div_le_iff₀ hNR]
    linarith [hqrt_le]
  have hxe : x * ε = 2 := by
    have h1 : ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) * (((q:ℝ)*(r:ℝ)*(t:ℝ))/(N:ℝ)) = 1 := by
      rw [div_mul_div_comm, mul_comm (N:ℝ) ((q:ℝ)*(r:ℝ)*(t:ℝ))]
      exact div_self (ne_of_gt (by positivity : (0:ℝ) < ((q:ℝ)*(r:ℝ)*(t:ℝ))*N))
    rw [hε, hx]
    nlinarith [h1]
  have hXe : X * ε ≤ 2 := by
    have h1 : X * ε ≤ x * ε := mul_le_mul_of_nonneg_right hXle hε0
    linarith
  have hfloor : s3Bfloor z N q r t = (A-1)*(B-1) + 1 := by
    rw [s3Bfloor, ← hA, ← hB]
  have hcont : s3Bcont z N q r t = (a-1)*(b-1) + 1 := by
    rw [s3Bcont,
        s3_log_div_eq ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) (t:ℝ) (z:ℝ) (by positivity) htRn hzR,
        s3_log_div_eq ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) (r:ℝ) (z:ℝ) (by positivity) hrRn hzR,
        ← ha, ← hb]
  have hBdiff : |s3Bfloor z N q r t - s3Bcont z N q r t| ≤ ε * (2*K + ε) := by
    have h := S3BracketExpandBounded (A := A) (B := B) (a := a) (b := b) (ε := ε) (K := K)
      hlogA hlogB ha1 ha2 hε0 hK0
    have he : (A-1)*(B-1)+1 - ((a-1)*(b-1)+1) = (A-1)*(B-1) - (a-1)*(b-1) := by ring
    rw [hfloor, hcont, he]
    exact h
  have hbx : |s3Bcont z N q r t| ≤ (Real.log (z:ℝ) + 1)^2 + 1 := by
    have hxt_low : (1:ℝ) ≤ x * (t:ℝ) := by nlinarith [hxge1, ht1]
    have hxt_high : x * (t:ℝ) ≤ (z:ℝ)*(z:ℝ) := by
      have hxtN : x * (t:ℝ) ≤ (N:ℝ) := by
        rw [hx, div_mul_eq_mul_div, div_le_iff₀ hqrtR]
        have htqr : (t:ℝ) ≤ (q:ℝ)*(r:ℝ)*(t:ℝ) := by nlinarith [hqr1, htRn]
        nlinarith [htqr, hNR]
      linarith [hxtN, hNcast]
    have hxr_low : (1:ℝ) ≤ x * (r:ℝ) := by nlinarith [hxge1, hr1R]
    have hxr_high : x * (r:ℝ) ≤ (z:ℝ)*(z:ℝ) := by
      have hxrN : x * (r:ℝ) ≤ (N:ℝ) := by
        rw [hx, div_mul_eq_mul_div, div_le_iff₀ hqrtR]
        have hrqt : (r:ℝ) ≤ (q:ℝ)*(r:ℝ)*(t:ℝ) := by nlinarith [hqt1, hrRn]
        nlinarith [hrqt, hNR]
      linarith [hxrN, hNcast]
    have hge1 : (1:ℝ)/(z:ℝ) ≤ x * (t:ℝ)/(z:ℝ) := by
      rw [div_le_div_iff₀ hzR hzR]; nlinarith [hxt_low, hzR]
    have hle1 : x * (t:ℝ)/(z:ℝ) ≤ (z:ℝ) := by
      rw [div_le_iff₀ hzR]; linarith [hxt_high]
    have hge2 : (1:ℝ)/(z:ℝ) ≤ x * (r:ℝ)/(z:ℝ) := by
      rw [div_le_div_iff₀ hzR hzR]; nlinarith [hxr_low, hzR]
    have hle2 : x * (r:ℝ)/(z:ℝ) ≤ (z:ℝ) := by
      rw [div_le_iff₀ hzR]; linarith [hxr_high]
    have hl1 : |Real.log (x * (t:ℝ)/(z:ℝ))| ≤ Real.log (z:ℝ) :=
      s3_abs_log_le _ _ hzR hge1 hle1 hLz0
    have hl2 : |Real.log (x * (r:ℝ)/(z:ℝ))| ≤ Real.log (z:ℝ) :=
      s3_abs_log_le _ _ hzR hge2 hle2 hLz0
    have h1 : |Real.log (x * (t:ℝ)/(z:ℝ)) - 1| ≤ Real.log (z:ℝ) + 1 := by
      have h4 : |Real.log (x * (t:ℝ)/(z:ℝ)) - 1| ≤ |Real.log (x * (t:ℝ)/(z:ℝ))| + 1 := by
        calc |Real.log (x * (t:ℝ)/(z:ℝ)) - 1|
            = |Real.log (x * (t:ℝ)/(z:ℝ)) + (-1)| := by ring_nf
          _ ≤ |Real.log (x * (t:ℝ)/(z:ℝ))| + |(-1:ℝ)| := abs_add_le _ _
          _ = |Real.log (x * (t:ℝ)/(z:ℝ))| + 1 := by rw [abs_neg, abs_one]
      linarith [h4, hl1]
    have h2 : |Real.log (x * (r:ℝ)/(z:ℝ)) - 1| ≤ Real.log (z:ℝ) + 1 := by
      have h4 : |Real.log (x * (r:ℝ)/(z:ℝ)) - 1| ≤ |Real.log (x * (r:ℝ)/(z:ℝ))| + 1 := by
        calc |Real.log (x * (r:ℝ)/(z:ℝ)) - 1|
            = |Real.log (x * (r:ℝ)/(z:ℝ)) + (-1)| := by ring_nf
          _ ≤ |Real.log (x * (r:ℝ)/(z:ℝ))| + |(-1:ℝ)| := abs_add_le _ _
          _ = |Real.log (x * (r:ℝ)/(z:ℝ))| + 1 := by rw [abs_neg, abs_one]
      linarith [h4, hl2]
    rw [s3Bcont]
    have h5 : |(Real.log (x * (t:ℝ)/(z:ℝ)) - 1) * (Real.log (x * (r:ℝ)/(z:ℝ)) - 1)|
        ≤ (Real.log (z:ℝ) + 1) * (Real.log (z:ℝ) + 1) := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith [hLz0])
    calc |(Real.log (x * (t:ℝ)/(z:ℝ)) - 1) * (Real.log (x * (r:ℝ)/(z:ℝ)) - 1) + 1|
        ≤ |(Real.log (x * (t:ℝ)/(z:ℝ)) - 1) * (Real.log (x * (r:ℝ)/(z:ℝ)) - 1)| + |(1:ℝ)| :=
          abs_add_le _ _
      _ ≤ (Real.log (z:ℝ) + 1) * (Real.log (z:ℝ) + 1) + 1 := by linarith [h5]
      _ = (Real.log (z:ℝ) + 1)^2 + 1 := by ring
  have hXX : |X * s3Bfloor z N q r t - x * s3Bcont z N q r t| ≤ 9 * (Real.log (z:ℝ) + 2)^2 := by
    have hdec : X * s3Bfloor z N q r t - x * s3Bcont z N q r t
        = X * (s3Bfloor z N q r t - s3Bcont z N q r t) + (X - x) * s3Bcont z N q r t := by ring
    rw [hdec]
    have h1 : |X * (s3Bfloor z N q r t - s3Bcont z N q r t)| ≤ 2 * (2*K + ε) := by
      rw [abs_mul, abs_of_nonneg hXge0]
      have h2 : X * |s3Bfloor z N q r t - s3Bcont z N q r t| ≤ X * (ε*(2*K+ε)) :=
        mul_le_mul_of_nonneg_left hBdiff hXge0
      have h4 : X * (ε*(2*K+ε)) = (X*ε)*(2*K+ε) := by ring
      have h5 : 0 ≤ 2*K + ε := by linarith
      have h6 : (X*ε)*(2*K+ε) ≤ 2*(2*K+ε) := mul_le_mul_of_nonneg_right hXe h5
      linarith [h2, h4, h6]
    have h2 : |(X - x) * s3Bcont z N q r t| ≤ 1 * ((Real.log (z:ℝ)+1)^2+1) := by
      rw [abs_mul]
      have habs : |X - x| ≤ 1 := by
        rw [abs_sub_le_iff]; constructor <;> linarith
      exact mul_le_mul habs hbx (abs_nonneg _) (by norm_num)
    have h3 : 2 * (2*K + ε) ≤ 8 * (Real.log (z:ℝ) + 2) := by
      linarith [hε2, hLz0, hK]
    have h4 : (Real.log (z:ℝ)+1)^2 + 1 ≤ (Real.log (z:ℝ)+2)^2 := by nlinarith [hLz0]
    have h5 : 8 * (Real.log (z:ℝ) + 2) ≤ 8 * (Real.log (z:ℝ) + 2)^2 := by nlinarith [hLz0]
    calc |X * (s3Bfloor z N q r t - s3Bcont z N q r t) + (X - x) * s3Bcont z N q r t|
        ≤ |X * (s3Bfloor z N q r t - s3Bcont z N q r t)| + |(X - x) * s3Bcont z N q r t| :=
          abs_add_le _ _
      _ ≤ 2 * (2*K + ε) + 1 * ((Real.log (z:ℝ)+1)^2+1) := add_le_add h1 h2
      _ ≤ 8 * (Real.log (z:ℝ) + 2) + (Real.log (z:ℝ)+2)^2 := by linarith [h3, h4]
      _ ≤ 9 * (Real.log (z:ℝ) + 2)^2 := by linarith [h5]
  have hghat : s3Ghat z N q r t = (r:ℝ) * (X * s3Bfloor z N q r t - x * s3Bcont z N q r t) := by
    rw [s3Ghat]
  rw [hghat, abs_mul, abs_of_nonneg (Nat.cast_nonneg r)]
  calc (r:ℝ) * |X * s3Bfloor z N q r t - x * s3Bcont z N q r t|
      ≤ (r:ℝ) * (9 * (Real.log (z:ℝ) + 2)^2) :=
        mul_le_mul_of_nonneg_left hXX (Nat.cast_nonneg r)
    _ = 9 * (r:ℝ) * (Real.log (z:ℝ) + 2)^2 := by ring

end Work.LinnikAreas.JutilaPieces
