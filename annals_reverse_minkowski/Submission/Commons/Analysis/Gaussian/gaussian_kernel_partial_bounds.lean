import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Commons.Analysis.Real.exp_neg_pi_sq_mul_poly_bounded

namespace Commons.Analysis.Gaussian

/-! ### Helper lemmas -/

/-- For every `n : ℕ` and every `b > 0`, the map `t ↦ (1 + |t|)^n * exp(-b * t^2)` is bounded. -/
private theorem poly_abs_exp_neg_sq_bounded (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (1 + |t|) ^ n * Real.exp (-b * t ^ 2) ≤ C := by
  obtain ⟨C0, hC0pos, hC0⟩ := Commons.Analysis.Real.exp_neg_pi_sq_mul_poly_bounded n
  have hπ : 0 < Real.pi := Real.pi_pos
  have hbπ : 0 < b / Real.pi := div_pos hb hπ
  set ρ : ℝ := Real.sqrt (b / Real.pi) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact Real.sqrt_pos.mpr hbπ
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hρsq : ρ ^ 2 = b / Real.pi := by rw [hρdef]; exact Real.sq_sqrt hbπ.le
  set R : ℝ := max 1 ρ⁻¹ with hRdef
  have hR1 : (1:ℝ) ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRinv : ρ⁻¹ ≤ R := le_max_right _ _
  refine ⟨R ^ n * C0, by positivity, ?_⟩
  intro t
  set w : ℝ := ρ * |t| with hwdef
  have hw0 : 0 ≤ w := mul_nonneg hρpos.le (abs_nonneg t)
  have ht_eq : |t| = w / ρ := by
    rw [hwdef]; field_simp
  have hexp : Real.exp (-b * t ^ 2) = Real.exp (-Real.pi * w ^ 2) := by
    congr 1
    rw [hwdef, mul_pow, sq_abs]
    have hpi : Real.pi * ρ ^ 2 = b := by rw [hρsq]; field_simp
    nlinarith [hpi]
  rw [ht_eq, hexp]
  have hpow_le : (1 + w / ρ) ^ n ≤ (R * (1 + w)) ^ n := by
    apply pow_le_pow_left₀
    · positivity
    · have h1 : w / ρ ≤ R * w := by
        rw [div_eq_mul_inv, mul_comm w ρ⁻¹]
        exact mul_le_mul_of_nonneg_right hRinv hw0
      nlinarith
  rw [mul_pow] at hpow_le
  have hw1 : (1:ℝ) ≤ 1 + w := by linarith
  have hpow100 : (1 + w) ^ n ≤ (1 + w) ^ (100 * n) := by
    apply pow_le_pow_right₀ hw1
    exact Nat.le_mul_of_pos_left n (by norm_num)
  calc (1 + w / ρ) ^ n * Real.exp (-Real.pi * w ^ 2)
      ≤ (R ^ n * (1 + w) ^ n) * Real.exp (-Real.pi * w ^ 2) := by
        exact mul_le_mul_of_nonneg_right hpow_le (Real.exp_nonneg _)
    _ = R ^ n * ((1 + w) ^ n * Real.exp (-Real.pi * w ^ 2)) := by ring
    _ ≤ R ^ n * ((1 + w) ^ (100 * n) * Real.exp (-Real.pi * w ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hpow100 (Real.exp_nonneg _)
    _ = R ^ n * (Real.exp (-Real.pi * w ^ 2) * (1 + w) ^ (100 * n)) := by ring
    _ ≤ R ^ n * C0 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hC0 w hw0

/-- `(1 + |z|)^k ≤ (1 + |z|)^4` for `k ≤ 4`. -/
private lemma abs_pow_le_w (z : ℝ) (k : ℕ) (hk : k ≤ 4) : |z| ^ k ≤ (1 + |z|) ^ 4 := by
  have ha : (0:ℝ) ≤ |z| := abs_nonneg z
  have h1 : |z| ^ k ≤ (1 + |z|) ^ k := pow_le_pow_left₀ ha (by linarith) k
  have h2 : (1 + |z|) ^ k ≤ (1 + |z|) ^ 4 := pow_le_pow_right₀ (by linarith [abs_nonneg z]) hk
  linarith

private lemma one_le_w (z : ℝ) : (1:ℝ) ≤ (1 + |z|) ^ 4 :=
  one_le_pow₀ (by linarith [abs_nonneg z])

private lemma sq_le_w (z : ℝ) : z ^ 2 ≤ (1 + |z|) ^ 4 := by
  rw [← sq_abs z]; exact abs_pow_le_w z 2 (by norm_num)

private lemma pow4_le_w (z : ℝ) : z ^ 4 ≤ (1 + |z|) ^ 4 := by
  have h2 : |z| ^ 4 = z ^ 4 := by
    rw [show |z| ^ 4 = (|z| ^ 2) ^ 2 by ring, sq_abs z]; ring
  rw [← h2]; exact abs_pow_le_w z 4 le_rfl

private lemma abs_le_w (z : ℝ) : |z| ≤ (1 + |z|) ^ 4 := by
  have h : |z| ^ 1 ≤ (1 + |z|) ^ 4 := abs_pow_le_w z 1 (by norm_num)
  simpa using h

private lemma exp_mono_neg_pi (L u z : ℝ) (hL : 0 < L) (hLu : L ≤ u) :
    Real.exp (-Real.pi * u ^ 2 * z ^ 2) ≤ Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hLu2 : L ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hL.le hLu 2
  have hπL : Real.pi * L ^ 2 ≤ Real.pi * u ^ 2 := mul_le_mul_of_nonneg_left hLu2 Real.pi_pos.le
  have h := mul_le_mul_of_nonneg_right hπL (sq_nonneg z)
  nlinarith [h]

/-- For `0 < a < c/4`, a polynomial (in `|t-s|`) times `exp(-c*(t-s)^2)` with `|s| ≤ δ`
is dominated by a constant multiple of `exp(-a*t^2)`. -/
private theorem gauss_poly_decay_shift_le (c a δ : ℝ) (n : ℕ) (K : ℝ)
    (hc : 0 < c) (ha : 0 < a) (hac : a < c / 4) (hδ : 0 < δ) (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t s : ℝ, |s| ≤ δ →
      K * ((1 + |t - s|) ^ n * Real.exp (-c * (t - s) ^ 2))
        ≤ M * Real.exp (-a * t ^ 2) := by
  set b : ℝ := c / 4 - a with hbdef
  have hb : 0 < b := by rw [hbdef]; linarith
  obtain ⟨C0, hC0pos, hC0⟩ := poly_abs_exp_neg_sq_bounded n hb
  set P : ℝ := K * (1 + 3 * δ) ^ n with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  set M : ℝ := max (P * Real.exp (4 * a * δ ^ 2)) (K * (1 + δ) ^ n * C0) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact le_trans (by positivity : (0:ℝ) ≤ P * Real.exp (4 * a * δ ^ 2)) (le_max_left _ _)
  refine ⟨M, hMnn, ?_⟩
  intro t s hs
  by_cases ht : |t| ≤ 2 * δ
  · have hsq : t ^ 2 ≤ 4 * δ ^ 2 := by
      have h2 : t ^ 2 ≤ (2 * δ) ^ 2 := by
        rw [← sq_abs t]
        exact pow_le_pow_left₀ (abs_nonneg t) ht 2
      nlinarith [h2]
    have hbase : 1 + |t - s| ≤ 1 + 3 * δ := by
      have h2 : |t - s| ≤ |t| + |s| := by
        calc |t - s| = |t + (-s)| := by ring_nf
          _ ≤ |t| + |-s| := abs_add_le _ _
          _ = |t| + |s| := by rw [abs_neg]
      linarith
    have h1 : (1 + |t - s|) ^ n ≤ (1 + 3 * δ) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    have h2 : Real.exp (-c * (t - s) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg (t - s), hc]
    have hLHS : K * ((1 + |t - s|) ^ n * Real.exp (-c * (t - s) ^ 2)) ≤ P := by
      rw [hPdef]
      apply mul_le_mul_of_nonneg_left _ hK
      simpa using (mul_le_mul h1 h2 (Real.exp_nonneg _)
        (by positivity : (0:ℝ) ≤ (1 + 3 * δ) ^ n))
    have hexp_ge : Real.exp (-4 * a * δ ^ 2) ≤ Real.exp (-a * t ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hsq, ha]
    have hPge : P ≤ M * Real.exp (-a * t ^ 2) := by
      have hMP : P * Real.exp (4 * a * δ ^ 2) ≤ M := by
        rw [hMdef]; exact le_max_left _ _
      have hprod : Real.exp (4 * a * δ ^ 2) * Real.exp (-4 * a * δ ^ 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      have hPeq : P * Real.exp (4 * a * δ ^ 2) * Real.exp (-4 * a * δ ^ 2) = P := by
        rw [mul_assoc, hprod, mul_one]
      calc P = P * Real.exp (4 * a * δ ^ 2) * Real.exp (-4 * a * δ ^ 2) := hPeq.symm
        _ ≤ M * Real.exp (-4 * a * δ ^ 2) :=
              mul_le_mul_of_nonneg_right hMP (Real.exp_nonneg _)
        _ ≤ M * Real.exp (-a * t ^ 2) :=
              mul_le_mul_of_nonneg_left hexp_ge hMnn
    exact le_trans hLHS hPge
  · rw [not_le] at ht
    have hts_le : |t - s| ≤ |t| + δ := by
      have h2 : |t - s| ≤ |t| + |s| := by
        calc |t - s| = |t + (-s)| := by ring_nf
          _ ≤ |t| + |-s| := abs_add_le _ _
          _ = |t| + |s| := by rw [abs_neg]
      linarith
    have h1 : (1 + |t - s|) ^ n ≤ (1 + δ) ^ n * (1 + |t|) ^ n := by
      have hbase : 1 + |t - s| ≤ (1 + δ) * (1 + |t|) := by
        nlinarith [hts_le, abs_nonneg t, hδ]
      calc (1 + |t - s|) ^ n ≤ ((1 + δ) * (1 + |t|)) ^ n :=
            pow_le_pow_left₀ (by positivity) hbase n
        _ = (1 + δ) ^ n * (1 + |t|) ^ n := mul_pow _ _ _
    have htsq : t ^ 2 / 4 ≤ (t - s) ^ 2 := by
      have hgt : |t| / 2 ≤ |t - s| := by
        have h2 : |t| ≤ |t - s| + |s| := by
          calc |t| = |(t - s) + s| := by ring_nf
            _ ≤ |t - s| + |s| := abs_add_le _ _
        linarith [h2, hs, ht]
      have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ |t| / 2) hgt 2
      rw [div_pow, sq_abs, sq_abs] at hh
      norm_num at hh
      exact hh
    have hexp : Real.exp (-c * (t - s) ^ 2) ≤ Real.exp (-c * t ^ 2 / 4) := by
      apply Real.exp_le_exp.mpr
      nlinarith [htsq, hc]
    have hexp_split : Real.exp (-c * t ^ 2 / 4) = Real.exp (-b * t ^ 2) * Real.exp (-a * t ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      rw [hbdef]; ring
    calc K * ((1 + |t - s|) ^ n * Real.exp (-c * (t - s) ^ 2))
        ≤ K * ((1 + δ) ^ n * (1 + |t|) ^ n * Real.exp (-c * t ^ 2 / 4)) := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact mul_le_mul h1 hexp (Real.exp_nonneg _) (by positivity)
      _ = K * (1 + δ) ^ n * ((1 + |t|) ^ n * Real.exp (-b * t ^ 2)) * Real.exp (-a * t ^ 2) := by
          rw [hexp_split]; ring
      _ ≤ K * (1 + δ) ^ n * C0 * Real.exp (-a * t ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left (hC0 t) (by positivity)
      _ ≤ M * Real.exp (-a * t ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          rw [hMdef]; exact le_max_right _ _

private lemma E1_bound (L U : ℝ) (hL : 0 < L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u z : ℝ, L ≤ u → |u| ≤ U →
      |Real.exp (-Real.pi * u ^ 2 * z ^ 2) * (1 - 2 * Real.pi * u ^ 2 * z ^ 2)|
        ≤ K * (1 + |z|) ^ 4 * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by
  refine ⟨|1 + 2 * Real.pi * U ^ 2| + 1, by positivity, ?_⟩
  intro u z hLu huU
  have hU0 : 0 ≤ U := by linarith [hL, hLu, le_abs_self u, huU]
  have hu2U2 : u ^ 2 ≤ U ^ 2 := by
    rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg u) huU 2
  have hexpmono := exp_mono_neg_pi L u z hL hLu
  have hpoly : |1 - 2 * Real.pi * u ^ 2 * z ^ 2|
      ≤ (1 + 2 * Real.pi * U ^ 2) * (1 + |z|) ^ 4 := by
    have hy0 : 0 ≤ 2 * Real.pi * u ^ 2 * z ^ 2 := by positivity
    have e1 : |1 - 2 * Real.pi * u ^ 2 * z ^ 2| ≤ 1 + 2 * Real.pi * u ^ 2 * z ^ 2 := by
      have h := abs_sub_le 1 0 (2 * Real.pi * u ^ 2 * z ^ 2)
      simpa [abs_of_nonneg hy0] using h
    have e2 : 2 * Real.pi * u ^ 2 * z ^ 2 ≤ 2 * Real.pi * U ^ 2 * z ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hu2U2 (sq_nonneg z)
      nlinarith [h, Real.pi_pos]
    have e3 : 1 + 2 * Real.pi * U ^ 2 * z ^ 2 ≤ (1 + 2 * Real.pi * U ^ 2) * (1 + |z|) ^ 4 := by
      have hK0 : 0 ≤ 2 * Real.pi * U ^ 2 := by positivity
      rw [add_mul, one_mul]
      exact add_le_add (one_le_w z) (mul_le_mul_of_nonneg_left (sq_le_w z) hK0)
    linarith
  have hpoly' : |1 - 2 * Real.pi * u ^ 2 * z ^ 2|
      ≤ (|1 + 2 * Real.pi * U ^ 2| + 1) * (1 + |z|) ^ 4 :=
    le_trans hpoly (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (1 + 2 * Real.pi * U ^ 2)]) (by positivity))
  calc |Real.exp (-Real.pi * u ^ 2 * z ^ 2) * (1 - 2 * Real.pi * u ^ 2 * z ^ 2)|
      = Real.exp (-Real.pi * u ^ 2 * z ^ 2) * |1 - 2 * Real.pi * u ^ 2 * z ^ 2| := by
        rw [abs_mul, Real.abs_exp]
    _ ≤ Real.exp (-(Real.pi * L ^ 2) * z ^ 2) * ((|1 + 2 * Real.pi * U ^ 2| + 1) * (1 + |z|) ^ 4) :=
        mul_le_mul hexpmono hpoly' (abs_nonneg _) (Real.exp_nonneg _)
    _ = (|1 + 2 * Real.pi * U ^ 2| + 1) * (1 + |z|) ^ 4 * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by ring

private lemma E2_bound (L U : ℝ) (hL : 0 < L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u z : ℝ, L ≤ u → |u| ≤ U →
      |2 * Real.pi * u ^ 3 * z * Real.exp (-Real.pi * u ^ 2 * z ^ 2)|
        ≤ K * (1 + |z|) ^ 4 * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by
  refine ⟨|2 * Real.pi * U ^ 3| + 1, by positivity, ?_⟩
  intro u z hLu huU
  have hu0 : 0 < u := lt_of_lt_of_le hL hLu
  have hU0 : 0 ≤ U := by linarith [hL, hLu, le_abs_self u, huU]
  have huU' : u ≤ U := le_trans (le_abs_self u) huU
  have hu3U3 : u ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ hu0.le huU' 3
  have hexpmono := exp_mono_neg_pi L u z hL hLu
  have hpoly : 2 * Real.pi * u ^ 3 * |z| ≤ (2 * Real.pi * U ^ 3) * (1 + |z|) ^ 4 := by
    calc 2 * Real.pi * u ^ 3 * |z| = (2 * Real.pi * u ^ 3) * |z| := by ring
      _ ≤ (2 * Real.pi * U ^ 3) * |z| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu3U3 (by positivity)) (abs_nonneg z)
      _ ≤ (2 * Real.pi * U ^ 3) * (1 + |z|) ^ 4 :=
            mul_le_mul_of_nonneg_left (abs_le_w z) (by positivity)
  have hpoly' : 2 * Real.pi * u ^ 3 * |z| ≤ (|2 * Real.pi * U ^ 3| + 1) * (1 + |z|) ^ 4 :=
    le_trans hpoly (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (2 * Real.pi * U ^ 3)]) (by positivity))
  calc |2 * Real.pi * u ^ 3 * z * Real.exp (-Real.pi * u ^ 2 * z ^ 2)|
      = 2 * Real.pi * u ^ 3 * |z| * Real.exp (-Real.pi * u ^ 2 * z ^ 2) := by
        rw [abs_mul, abs_mul, abs_mul, Real.abs_exp, abs_pow, abs_mul,
            abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos, abs_of_pos hu0]
    _ ≤ (|2 * Real.pi * U ^ 3| + 1) * (1 + |z|) ^ 4 * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) :=
        mul_le_mul hpoly' hexpmono (Real.exp_nonneg _) (by positivity)

private lemma E3_bound (L U : ℝ) (hL : 0 < L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u z : ℝ, L ≤ u → |u| ≤ U →
      |Real.exp (-Real.pi * u ^ 2 * z ^ 2)
        * (4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 - 6 * Real.pi * u * z ^ 2)|
        ≤ K * (1 + |z|) ^ 4 * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by
  refine ⟨|4 * Real.pi ^ 2 * U ^ 3 + 6 * Real.pi * U| + 1, by positivity, ?_⟩
  intro u z hLu huU
  have hu0 : 0 < u := lt_of_lt_of_le hL hLu
  have hU0 : 0 ≤ U := by linarith [hL, hLu, le_abs_self u, huU]
  have huU' : u ≤ U := le_trans (le_abs_self u) huU
  have hu3U3 : u ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ hu0.le huU' 3
  have hexpmono := exp_mono_neg_pi L u z hL hLu
  have hpoly : |4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 - 6 * Real.pi * u * z ^ 2|
      ≤ (4 * Real.pi ^ 2 * U ^ 3 + 6 * Real.pi * U) * (1 + |z|) ^ 4 := by
    have hA0 : 0 ≤ 4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 := by positivity
    have hB0 : 0 ≤ 6 * Real.pi * u * z ^ 2 := by positivity
    have htri : |4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 - 6 * Real.pi * u * z ^ 2|
        ≤ 4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 + 6 * Real.pi * u * z ^ 2 := by
      rw [abs_sub_le_iff]; constructor <;> linarith
    have hA : 4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 ≤ 4 * Real.pi ^ 2 * U ^ 3 * (1 + |z|) ^ 4 := by
      have hAu : 4 * Real.pi ^ 2 * u ^ 3 ≤ 4 * Real.pi ^ 2 * U ^ 3 :=
        mul_le_mul_of_nonneg_left hu3U3 (by positivity)
      calc 4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 = (4 * Real.pi ^ 2 * u ^ 3) * z ^ 4 := by ring
        _ ≤ (4 * Real.pi ^ 2 * U ^ 3) * z ^ 4 := mul_le_mul_of_nonneg_right hAu (by positivity)
        _ = 4 * Real.pi ^ 2 * U ^ 3 * z ^ 4 := by ring
        _ ≤ 4 * Real.pi ^ 2 * U ^ 3 * (1 + |z|) ^ 4 :=
              mul_le_mul_of_nonneg_left (pow4_le_w z) (by positivity)
    have hB : 6 * Real.pi * u * z ^ 2 ≤ 6 * Real.pi * U * (1 + |z|) ^ 4 := by
      have hBu : 6 * Real.pi * u ≤ 6 * Real.pi * U :=
        mul_le_mul_of_nonneg_left huU' (by positivity)
      calc 6 * Real.pi * u * z ^ 2 = (6 * Real.pi * u) * z ^ 2 := by ring
        _ ≤ (6 * Real.pi * U) * z ^ 2 := mul_le_mul_of_nonneg_right hBu (by positivity)
        _ = 6 * Real.pi * U * z ^ 2 := by ring
        _ ≤ 6 * Real.pi * U * (1 + |z|) ^ 4 :=
              mul_le_mul_of_nonneg_left (sq_le_w z) (by positivity)
    calc |4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 - 6 * Real.pi * u * z ^ 2|
        ≤ 4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 + 6 * Real.pi * u * z ^ 2 := htri
      _ ≤ 4 * Real.pi ^ 2 * U ^ 3 * (1 + |z|) ^ 4 + 6 * Real.pi * U * (1 + |z|) ^ 4 := add_le_add hA hB
      _ = (4 * Real.pi ^ 2 * U ^ 3 + 6 * Real.pi * U) * (1 + |z|) ^ 4 := by ring
  have hpoly' : |4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 - 6 * Real.pi * u * z ^ 2|
      ≤ (|4 * Real.pi ^ 2 * U ^ 3 + 6 * Real.pi * U| + 1) * (1 + |z|) ^ 4 :=
    le_trans hpoly (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (4 * Real.pi ^ 2 * U ^ 3 + 6 * Real.pi * U)]) (by positivity))
  calc |Real.exp (-Real.pi * u ^ 2 * z ^ 2)
          * (4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 - 6 * Real.pi * u * z ^ 2)|
      = Real.exp (-Real.pi * u ^ 2 * z ^ 2)
          * |4 * Real.pi ^ 2 * u ^ 3 * z ^ 4 - 6 * Real.pi * u * z ^ 2| := by
        rw [abs_mul, Real.abs_exp]
    _ ≤ Real.exp (-(Real.pi * L ^ 2) * z ^ 2)
          * ((|4 * Real.pi ^ 2 * U ^ 3 + 6 * Real.pi * U| + 1) * (1 + |z|) ^ 4) :=
        mul_le_mul hexpmono hpoly' (abs_nonneg _) (Real.exp_nonneg _)
    _ = (|4 * Real.pi ^ 2 * U ^ 3 + 6 * Real.pi * U| + 1) * (1 + |z|) ^ 4
          * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by ring

private lemma E4_bound (L U : ℝ) (hL : 0 < L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u z : ℝ, L ≤ u → |u| ≤ U →
      |Real.exp (-Real.pi * u ^ 2 * z ^ 2)
        * (6 * Real.pi * u ^ 2 * z - 4 * Real.pi ^ 2 * u ^ 4 * z ^ 3)|
        ≤ K * (1 + |z|) ^ 4 * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by
  refine ⟨|6 * Real.pi * U ^ 2 + 4 * Real.pi ^ 2 * U ^ 4| + 1, by positivity, ?_⟩
  intro u z hLu huU
  have hu0 : 0 < u := lt_of_lt_of_le hL hLu
  have hU0 : 0 ≤ U := by linarith [hL, hLu, le_abs_self u, huU]
  have huU' : u ≤ U := le_trans (le_abs_self u) huU
  have hu2U2 : u ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hu0.le huU' 2
  have hu4U4 : u ^ 4 ≤ U ^ 4 := pow_le_pow_left₀ hu0.le huU' 4
  have hexpmono := exp_mono_neg_pi L u z hL hLu
  have hpoly : |6 * Real.pi * u ^ 2 * z - 4 * Real.pi ^ 2 * u ^ 4 * z ^ 3|
      ≤ (6 * Real.pi * U ^ 2 + 4 * Real.pi ^ 2 * U ^ 4) * (1 + |z|) ^ 4 := by
    have e1 : |6 * Real.pi * u ^ 2 * z - 0| = 6 * Real.pi * u ^ 2 * |z| := by
      rw [sub_zero, abs_mul, abs_mul, abs_pow, abs_mul,
          abs_of_pos (by norm_num : (0:ℝ) < 6), abs_of_pos Real.pi_pos, abs_of_pos hu0]
    have e2 : |0 - 4 * Real.pi ^ 2 * u ^ 4 * z ^ 3| = 4 * Real.pi ^ 2 * u ^ 4 * |z| ^ 3 := by
      rw [zero_sub, abs_neg, abs_mul, abs_mul, abs_pow, abs_pow, abs_mul, abs_pow,
          abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos Real.pi_pos, abs_of_pos hu0]
    have htri : |6 * Real.pi * u ^ 2 * z - 4 * Real.pi ^ 2 * u ^ 4 * z ^ 3|
        ≤ 6 * Real.pi * u ^ 2 * |z| + 4 * Real.pi ^ 2 * u ^ 4 * |z| ^ 3 := by
      have h := abs_sub_le (6 * Real.pi * u ^ 2 * z) 0 (4 * Real.pi ^ 2 * u ^ 4 * z ^ 3)
      rw [e1, e2] at h
      exact h
    have hA : 6 * Real.pi * u ^ 2 * |z| ≤ 6 * Real.pi * U ^ 2 * (1 + |z|) ^ 4 := by
      calc 6 * Real.pi * u ^ 2 * |z| = (6 * Real.pi * u ^ 2) * |z| := by ring
        _ ≤ (6 * Real.pi * U ^ 2) * |z| :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2U2 (by positivity)) (abs_nonneg z)
        _ ≤ (6 * Real.pi * U ^ 2) * (1 + |z|) ^ 4 :=
              mul_le_mul_of_nonneg_left (abs_le_w z) (by positivity)
    have hB : 4 * Real.pi ^ 2 * u ^ 4 * |z| ^ 3 ≤ 4 * Real.pi ^ 2 * U ^ 4 * (1 + |z|) ^ 4 := by
      calc 4 * Real.pi ^ 2 * u ^ 4 * |z| ^ 3 = (4 * Real.pi ^ 2 * u ^ 4) * |z| ^ 3 := by ring
        _ ≤ (4 * Real.pi ^ 2 * U ^ 4) * |z| ^ 3 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu4U4 (by positivity)) (by positivity)
        _ ≤ (4 * Real.pi ^ 2 * U ^ 4) * (1 + |z|) ^ 4 :=
              mul_le_mul_of_nonneg_left (abs_pow_le_w z 3 (by norm_num)) (by positivity)
    calc |6 * Real.pi * u ^ 2 * z - 4 * Real.pi ^ 2 * u ^ 4 * z ^ 3|
        ≤ 6 * Real.pi * u ^ 2 * |z| + 4 * Real.pi ^ 2 * u ^ 4 * |z| ^ 3 := htri
      _ ≤ 6 * Real.pi * U ^ 2 * (1 + |z|) ^ 4 + 4 * Real.pi ^ 2 * U ^ 4 * (1 + |z|) ^ 4 := add_le_add hA hB
      _ = (6 * Real.pi * U ^ 2 + 4 * Real.pi ^ 2 * U ^ 4) * (1 + |z|) ^ 4 := by ring
  have hpoly' : |6 * Real.pi * u ^ 2 * z - 4 * Real.pi ^ 2 * u ^ 4 * z ^ 3|
      ≤ (|6 * Real.pi * U ^ 2 + 4 * Real.pi ^ 2 * U ^ 4| + 1) * (1 + |z|) ^ 4 :=
    le_trans hpoly (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (6 * Real.pi * U ^ 2 + 4 * Real.pi ^ 2 * U ^ 4)]) (by positivity))
  calc |Real.exp (-Real.pi * u ^ 2 * z ^ 2)
          * (6 * Real.pi * u ^ 2 * z - 4 * Real.pi ^ 2 * u ^ 4 * z ^ 3)|
      = Real.exp (-Real.pi * u ^ 2 * z ^ 2)
          * |6 * Real.pi * u ^ 2 * z - 4 * Real.pi ^ 2 * u ^ 4 * z ^ 3| := by
        rw [abs_mul, Real.abs_exp]
    _ ≤ Real.exp (-(Real.pi * L ^ 2) * z ^ 2)
          * ((|6 * Real.pi * U ^ 2 + 4 * Real.pi ^ 2 * U ^ 4| + 1) * (1 + |z|) ^ 4) :=
        mul_le_mul hexpmono hpoly' (abs_nonneg _) (Real.exp_nonneg _)
    _ = (|6 * Real.pi * U ^ 2 + 4 * Real.pi ^ 2 * U ^ 4| + 1) * (1 + |z|) ^ 4
          * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by ring

private lemma E5_bound (L U : ℝ) (hL : 0 < L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u z : ℝ, L ≤ u → |u| ≤ U →
      |Real.exp (-Real.pi * u ^ 2 * z ^ 2)
        * (2 * Real.pi * u ^ 3 + 4 * Real.pi ^ 2 * u ^ 5 * z ^ 2)|
        ≤ K * (1 + |z|) ^ 4 * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by
  refine ⟨|2 * Real.pi * U ^ 3 + 4 * Real.pi ^ 2 * U ^ 5| + 1, by positivity, ?_⟩
  intro u z hLu huU
  have hu0 : 0 < u := lt_of_lt_of_le hL hLu
  have hU0 : 0 ≤ U := by linarith [hL, hLu, le_abs_self u, huU]
  have huU' : u ≤ U := le_trans (le_abs_self u) huU
  have hu3U3 : u ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ hu0.le huU' 3
  have hu5U5 : u ^ 5 ≤ U ^ 5 := pow_le_pow_left₀ hu0.le huU' 5
  have hexpmono := exp_mono_neg_pi L u z hL hLu
  have hpoly : |2 * Real.pi * u ^ 3 + 4 * Real.pi ^ 2 * u ^ 5 * z ^ 2|
      ≤ (2 * Real.pi * U ^ 3 + 4 * Real.pi ^ 2 * U ^ 5) * (1 + |z|) ^ 4 := by
    have habs : |2 * Real.pi * u ^ 3 + 4 * Real.pi ^ 2 * u ^ 5 * z ^ 2|
        = 2 * Real.pi * u ^ 3 + 4 * Real.pi ^ 2 * u ^ 5 * z ^ 2 :=
      abs_of_nonneg (by positivity)
    rw [habs, add_mul]
    have hA : 2 * Real.pi * u ^ 3 ≤ 2 * Real.pi * U ^ 3 * (1 + |z|) ^ 4 := by
      calc 2 * Real.pi * u ^ 3 ≤ 2 * Real.pi * U ^ 3 :=
            mul_le_mul_of_nonneg_left hu3U3 (by positivity)
        _ = 2 * Real.pi * U ^ 3 * 1 := by ring
        _ ≤ 2 * Real.pi * U ^ 3 * (1 + |z|) ^ 4 :=
              mul_le_mul_of_nonneg_left (one_le_w z) (by positivity)
    have hB : 4 * Real.pi ^ 2 * u ^ 5 * z ^ 2 ≤ 4 * Real.pi ^ 2 * U ^ 5 * (1 + |z|) ^ 4 := by
      calc 4 * Real.pi ^ 2 * u ^ 5 * z ^ 2 = (4 * Real.pi ^ 2 * u ^ 5) * z ^ 2 := by ring
        _ ≤ (4 * Real.pi ^ 2 * U ^ 5) * z ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu5U5 (by positivity)) (by positivity)
        _ ≤ (4 * Real.pi ^ 2 * U ^ 5) * (1 + |z|) ^ 4 :=
              mul_le_mul_of_nonneg_left (sq_le_w z) (by positivity)
    exact add_le_add hA hB
  have hpoly' : |2 * Real.pi * u ^ 3 + 4 * Real.pi ^ 2 * u ^ 5 * z ^ 2|
      ≤ (|2 * Real.pi * U ^ 3 + 4 * Real.pi ^ 2 * U ^ 5| + 1) * (1 + |z|) ^ 4 :=
    le_trans hpoly (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (2 * Real.pi * U ^ 3 + 4 * Real.pi ^ 2 * U ^ 5)]) (by positivity))
  calc |Real.exp (-Real.pi * u ^ 2 * z ^ 2)
          * (2 * Real.pi * u ^ 3 + 4 * Real.pi ^ 2 * u ^ 5 * z ^ 2)|
      = Real.exp (-Real.pi * u ^ 2 * z ^ 2)
          * |2 * Real.pi * u ^ 3 + 4 * Real.pi ^ 2 * u ^ 5 * z ^ 2| := by
        rw [abs_mul, Real.abs_exp]
    _ ≤ Real.exp (-(Real.pi * L ^ 2) * z ^ 2)
          * ((|2 * Real.pi * U ^ 3 + 4 * Real.pi ^ 2 * U ^ 5| + 1) * (1 + |z|) ^ 4) :=
        mul_le_mul hexpmono hpoly' (abs_nonneg _) (Real.exp_nonneg _)
    _ = (|2 * Real.pi * U ^ 3 + 4 * Real.pi ^ 2 * U ^ 5| + 1) * (1 + |z|) ^ 4
          * Real.exp (-(Real.pi * L ^ 2) * z ^ 2) := by ring

theorem gaussian_kernel_partial_bounds (u₀ x₀ : ℝ) (hu₀ : 0 < u₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u₀ ∧ ∃ B : ℝ → ℝ, MeasureTheory.Integrable B ∧
      (∀ u x y : ℝ, |u - u₀| < δ → |x - x₀| < δ →
        |Real.exp (-Real.pi * u^2 * (y - x)^2) * (1 - 2 * Real.pi * u^2 * (y - x)^2)| ≤ B y) ∧
      (∀ u x y : ℝ, |u - u₀| < δ → |x - x₀| < δ →
        |2 * Real.pi * u^3 * (y - x) * Real.exp (-Real.pi * u^2 * (y - x)^2)| ≤ B y) ∧
      (∀ u x y : ℝ, |u - u₀| < δ → |x - x₀| < δ →
        |Real.exp (-Real.pi * u^2 * (y - x)^2) * (4 * Real.pi^2 * u^3 * (y - x)^4 - 6 * Real.pi * u * (y - x)^2)| ≤ B y) ∧
      (∀ u x y : ℝ, |u - u₀| < δ → |x - x₀| < δ →
        |Real.exp (-Real.pi * u^2 * (y - x)^2) * (6 * Real.pi * u^2 * (y - x) - 4 * Real.pi^2 * u^4 * (y - x)^3)| ≤ B y) ∧
      (∀ u x y : ℝ, |u - u₀| < δ → |x - x₀| < δ →
        |Real.exp (-Real.pi * u^2 * (y - x)^2) * (2 * Real.pi * u^3 + 4 * Real.pi^2 * u^5 * (y - x)^2)| ≤ B y) := by
  set δ : ℝ := u₀ / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδle : δ ≤ u₀ := by rw [hδdef]; linarith
  have hu₀_eq : u₀ = 2 * δ := by rw [hδdef]; ring
  obtain ⟨K1, hK1, hb1⟩ := E1_bound δ (3 * δ) hδpos
  obtain ⟨K2, hK2, hb2⟩ := E2_bound δ (3 * δ) hδpos
  obtain ⟨K3, hK3, hb3⟩ := E3_bound δ (3 * δ) hδpos
  obtain ⟨K4, hK4, hb4⟩ := E4_bound δ (3 * δ) hδpos
  obtain ⟨K5, hK5, hb5⟩ := E5_bound δ (3 * δ) hδpos
  have hc : 0 < Real.pi * δ ^ 2 := by positivity
  have ha : 0 < Real.pi * δ ^ 2 / 8 := by positivity
  have hac : Real.pi * δ ^ 2 / 8 < Real.pi * δ ^ 2 / 4 := by
    have h := sq_pos_of_pos hδpos
    nlinarith [h, Real.pi_pos]
  obtain ⟨M1, hM1nn, hM1⟩ :=
    gauss_poly_decay_shift_le (Real.pi * δ ^ 2) (Real.pi * δ ^ 2 / 8) δ 4 K1 hc ha hac hδpos hK1
  obtain ⟨M2, hM2nn, hM2⟩ :=
    gauss_poly_decay_shift_le (Real.pi * δ ^ 2) (Real.pi * δ ^ 2 / 8) δ 4 K2 hc ha hac hδpos hK2
  obtain ⟨M3, hM3nn, hM3⟩ :=
    gauss_poly_decay_shift_le (Real.pi * δ ^ 2) (Real.pi * δ ^ 2 / 8) δ 4 K3 hc ha hac hδpos hK3
  obtain ⟨M4, hM4nn, hM4⟩ :=
    gauss_poly_decay_shift_le (Real.pi * δ ^ 2) (Real.pi * δ ^ 2 / 8) δ 4 K4 hc ha hac hδpos hK4
  obtain ⟨M5, hM5nn, hM5⟩ :=
    gauss_poly_decay_shift_le (Real.pi * δ ^ 2) (Real.pi * δ ^ 2 / 8) δ 4 K5 hc ha hac hδpos hK5
  set M : ℝ := max M1 (max M2 (max M3 (max M4 M5))) with hMdef
  have hM1le : M1 ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hM2le : M2 ≤ M := by rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM3le : M3 ≤ M := by
    rw [hMdef]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hM4le : M4 ≤ M := by
    rw [hMdef]
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hM5le : M5 ≤ M := by
    rw [hMdef]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hu_bounds : ∀ u : ℝ, |u - u₀| < δ → δ ≤ u ∧ |u| ≤ 3 * δ := by
    intro u hu
    have h1 : -δ < u - u₀ := (abs_lt.mp hu).1
    have h2 : u - u₀ < δ := (abs_lt.mp hu).2
    constructor
    · linarith [h1, hu₀_eq]
    · rw [abs_le]; constructor <;> linarith [h1, h2, hu₀_eq, hδpos]
  refine ⟨δ, hδpos, hδle, fun y => M * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hbase : MeasureTheory.Integrable
        (fun v : ℝ => M * Real.exp (-(Real.pi * δ ^ 2 / 8) * v ^ 2)) :=
      (integrable_exp_neg_mul_sq ha).const_mul M
    have h := hbase.comp_sub_right x₀
    simpa using h
  · intro u x y hu hx
    obtain ⟨huL, huU⟩ := hu_bounds u hu
    have hs : |x - x₀| ≤ δ := le_of_lt hx
    have hts : (y - x₀) - (x - x₀) = y - x := by ring
    have h1 : |Real.exp (-Real.pi * u ^ 2 * (y - x) ^ 2) * (1 - 2 * Real.pi * u ^ 2 * (y - x) ^ 2)|
        ≤ K1 * ((1 + |y - x|) ^ 4 * Real.exp (-(Real.pi * δ ^ 2) * (y - x) ^ 2)) := by
      simpa only [mul_assoc] using hb1 u (y - x) huL huU
    have h2 := hM1 (y - x₀) (x - x₀) hs
    rw [hts] at h2
    have hMle : M1 * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2)
        ≤ M * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2) :=
      mul_le_mul_of_nonneg_right hM1le (Real.exp_nonneg _)
    exact le_trans (le_trans h1 h2) hMle
  · intro u x y hu hx
    obtain ⟨huL, huU⟩ := hu_bounds u hu
    have hs : |x - x₀| ≤ δ := le_of_lt hx
    have hts : (y - x₀) - (x - x₀) = y - x := by ring
    have h1 : |2 * Real.pi * u ^ 3 * (y - x) * Real.exp (-Real.pi * u ^ 2 * (y - x) ^ 2)|
        ≤ K2 * ((1 + |y - x|) ^ 4 * Real.exp (-(Real.pi * δ ^ 2) * (y - x) ^ 2)) := by
      simpa only [mul_assoc] using hb2 u (y - x) huL huU
    have h2 := hM2 (y - x₀) (x - x₀) hs
    rw [hts] at h2
    have hMle : M2 * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2)
        ≤ M * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2) :=
      mul_le_mul_of_nonneg_right hM2le (Real.exp_nonneg _)
    exact le_trans (le_trans h1 h2) hMle
  · intro u x y hu hx
    obtain ⟨huL, huU⟩ := hu_bounds u hu
    have hs : |x - x₀| ≤ δ := le_of_lt hx
    have hts : (y - x₀) - (x - x₀) = y - x := by ring
    have h1 : |Real.exp (-Real.pi * u ^ 2 * (y - x) ^ 2)
          * (4 * Real.pi ^ 2 * u ^ 3 * (y - x) ^ 4 - 6 * Real.pi * u * (y - x) ^ 2)|
        ≤ K3 * ((1 + |y - x|) ^ 4 * Real.exp (-(Real.pi * δ ^ 2) * (y - x) ^ 2)) := by
      simpa only [mul_assoc] using hb3 u (y - x) huL huU
    have h2 := hM3 (y - x₀) (x - x₀) hs
    rw [hts] at h2
    have hMle : M3 * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2)
        ≤ M * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2) :=
      mul_le_mul_of_nonneg_right hM3le (Real.exp_nonneg _)
    exact le_trans (le_trans h1 h2) hMle
  · intro u x y hu hx
    obtain ⟨huL, huU⟩ := hu_bounds u hu
    have hs : |x - x₀| ≤ δ := le_of_lt hx
    have hts : (y - x₀) - (x - x₀) = y - x := by ring
    have h1 : |Real.exp (-Real.pi * u ^ 2 * (y - x) ^ 2)
          * (6 * Real.pi * u ^ 2 * (y - x) - 4 * Real.pi ^ 2 * u ^ 4 * (y - x) ^ 3)|
        ≤ K4 * ((1 + |y - x|) ^ 4 * Real.exp (-(Real.pi * δ ^ 2) * (y - x) ^ 2)) := by
      simpa only [mul_assoc] using hb4 u (y - x) huL huU
    have h2 := hM4 (y - x₀) (x - x₀) hs
    rw [hts] at h2
    have hMle : M4 * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2)
        ≤ M * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2) :=
      mul_le_mul_of_nonneg_right hM4le (Real.exp_nonneg _)
    exact le_trans (le_trans h1 h2) hMle
  · intro u x y hu hx
    obtain ⟨huL, huU⟩ := hu_bounds u hu
    have hs : |x - x₀| ≤ δ := le_of_lt hx
    have hts : (y - x₀) - (x - x₀) = y - x := by ring
    have h1 : |Real.exp (-Real.pi * u ^ 2 * (y - x) ^ 2)
          * (2 * Real.pi * u ^ 3 + 4 * Real.pi ^ 2 * u ^ 5 * (y - x) ^ 2)|
        ≤ K5 * ((1 + |y - x|) ^ 4 * Real.exp (-(Real.pi * δ ^ 2) * (y - x) ^ 2)) := by
      simpa only [mul_assoc] using hb5 u (y - x) huL huU
    have h2 := hM5 (y - x₀) (x - x₀) hs
    rw [hts] at h2
    have hMle : M5 * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2)
        ≤ M * Real.exp (-(Real.pi * δ ^ 2 / 8) * (y - x₀) ^ 2) :=
      mul_le_mul_of_nonneg_right hM5le (Real.exp_nonneg _)
    exact le_trans (le_trans h1 h2) hMle

end Commons.Analysis.Gaussian