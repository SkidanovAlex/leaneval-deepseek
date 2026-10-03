/-
# `Submission.Work.FIArea6Hecke.R.MGGrow.log_growth_arith`

**Polynomial–exponential growth bound for a three–term sum.**

For `k : ℕ` and positive constants `A Mf A₀` with `c₁, c₂ ≥ 1`, the function

`F(R) = log (A + Mf · c₁^R + A₀ · n^n · c₂^n)`,   `n = k/2 + R`,

is bounded for `R ≥ 1` by `C · R · (log (R+2) + K)` for suitable constants `C > 0`, `K ≥ 0`.

The proof is elementary bookkeeping, split into three pieces:

* `main_log_bound` turns the sum inside the logarithm into a product, using
  `s ≤ 3·P` with `P = (A+Mf+A₀)·c₁^R·n^n·c₂^n` (each summand is `≤ P` because the
  "exponential" factors `c₁^R, n^n, c₂^n` are all `≥ 1`), and then applies `log_mul`
  and `log_rpow`;
* `n_log_n_le` bounds `n·log n` by `(k/2+1)·R·(log(R+2) + log(k/2+2))`, using
  `n ≤ (k/2+1)·R` and `n ≤ (k/2+2)·(R+2)`;
* `const_bound_arith` is the final linear-in-`R` bookkeeping that absorbs the constants.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R.MGGrow

noncomputable section

/-- For `k : ℕ` and `R ≥ 1`, with `n = k/2 + R`, one has
`n · log n ≤ (k/2 + 1) · R · (log (R+2) + log (k/2 + 2))`. -/
lemma n_log_n_le (k : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    ((k : ℝ) / 2 + R) * Real.log ((k : ℝ) / 2 + R)
      ≤ ((k : ℝ) / 2 + 1) * R * (Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2)) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hhalf : (0 : ℝ) ≤ (k : ℝ) / 2 := by linarith
  have hR0 : 0 ≤ R := by linarith
  set n : ℝ := (k : ℝ) / 2 + R with hn
  have hn_pos : 0 < n := by rw [hn]; linarith
  have hn1 : 1 ≤ n := by rw [hn]; linarith
  -- step 1: `n ≤ (k/2+1)·R`
  have hstep1 : n ≤ ((k : ℝ) / 2 + 1) * R := by
    rw [hn]
    have h := mul_le_mul_of_nonneg_left hR hhalf
    nlinarith [h]
  -- step 2: `log n ≤ log (R+2) + log (k/2+2)`
  have hstep2 : Real.log n ≤ Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2) := by
    have hk2pos : 0 < (k : ℝ) / 2 + 2 := by linarith
    have hR2pos : 0 < R + 2 := by linarith
    have hle : n ≤ ((k : ℝ) / 2 + 2) * (R + 2) := by
      rw [hn]; nlinarith [mul_nonneg hhalf hR0]
    calc Real.log n ≤ Real.log (((k : ℝ) / 2 + 2) * (R + 2)) := Real.log_le_log hn_pos hle
      _ = Real.log ((k : ℝ) / 2 + 2) + Real.log (R + 2) :=
            Real.log_mul (ne_of_gt hk2pos) (ne_of_gt hR2pos)
      _ = Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2) := by ring
  have hlog_n_nn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hLnn : 0 ≤ Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2) := by
    have h1 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log ((k : ℝ) / 2 + 2) := Real.log_nonneg (by linarith)
    linarith
  have hpR : 0 ≤ ((k : ℝ) / 2 + 1) * R := mul_nonneg (by linarith) hR0
  calc n * Real.log n
      ≤ (((k : ℝ) / 2 + 1) * R) * (Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2)) :=
        mul_le_mul hstep1 hstep2 hlog_n_nn hpR
    _ = ((k : ℝ) / 2 + 1) * R * (Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2)) := by ring

/-- The core analytic bound: for `R ≥ 1` and `n = k/2 + R`,
`log (A + Mf·c₁^R + A₀·n^n·c₂^n)` is at most the sum of the logarithms of the
individual factors. -/
lemma main_log_bound (k : ℕ) {A Mf A₀ c₁ c₂ R : ℝ}
    (hA : 0 < A) (hMf : 0 < Mf) (hA₀ : 0 < A₀) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hR : 1 ≤ R) :
    Real.log (A + Mf * c₁ ^ R + A₀ * ((k : ℝ) / 2 + R) ^ ((k : ℝ) / 2 + R) *
        c₂ ^ ((k : ℝ) / 2 + R))
      ≤ Real.log 3 + Real.log (A + Mf + A₀) + R * Real.log c₁
        + ((k : ℝ) / 2 + 1) * R * (Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2) + Real.log c₂) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hhalf : (0 : ℝ) ≤ (k : ℝ) / 2 := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hc₁pos : 0 < c₁ := lt_of_lt_of_le zero_lt_one hc₁
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le zero_lt_one hc₂
  set n : ℝ := (k : ℝ) / 2 + R with hn
  have hn_pos : 0 < n := by rw [hn]; linarith
  have hn1 : 1 ≤ n := by rw [hn]; linarith
  have hnn_pos : 0 < n ^ n := Real.rpow_pos_of_pos hn_pos n
  have hc₁R_pos : 0 < c₁ ^ R := Real.rpow_pos_of_pos hc₁pos R
  have hc₂n_pos : 0 < c₂ ^ n := Real.rpow_pos_of_pos hc₂pos n
  have hAB : 0 < A + Mf + A₀ := by linarith
  set Q : ℝ := c₁ ^ R * n ^ n * c₂ ^ n with hQ
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hc₁ hR0) (Real.one_le_rpow hn1 hn_pos.le))
      (Real.one_le_rpow hc₂ hn_pos.le)
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  set P : ℝ := (A + Mf + A₀) * Q with hP
  have hPpos : 0 < P := mul_pos hAB hQpos
  -- each of the three summands is `≤ P`
  have hA_le : A ≤ P := by
    rw [hP]
    have h1 : A ≤ A + Mf + A₀ := by linarith
    have h2 : (A + Mf + A₀) * 1 ≤ (A + Mf + A₀) * Q := mul_le_mul_of_nonneg_left hQ1 hAB.le
    linarith
  have hM_le : Mf * c₁ ^ R ≤ P := by
    rw [hP]
    have h1 : Mf * c₁ ^ R ≤ (A + Mf + A₀) * c₁ ^ R :=
      mul_le_mul_of_nonneg_right (by linarith : Mf ≤ A + Mf + A₀) hc₁R_pos.le
    have h2 : c₁ ^ R ≤ Q := by
      rw [hQ]
      have hprod : 1 ≤ n ^ n * c₂ ^ n :=
        one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hn1 hn_pos.le) (Real.one_le_rpow hc₂ hn_pos.le)
      have h := le_mul_of_one_le_right hc₁R_pos.le hprod
      linarith [h]
    have h3 : (A + Mf + A₀) * c₁ ^ R ≤ (A + Mf + A₀) * Q :=
      mul_le_mul_of_nonneg_left h2 hAB.le
    linarith
  have hA₀_le : A₀ * n ^ n * c₂ ^ n ≤ P := by
    rw [hP]
    have h1 : A₀ * n ^ n * c₂ ^ n ≤ (A + Mf + A₀) * n ^ n * c₂ ^ n := by
      have h := mul_le_mul_of_nonneg_right (by linarith : A₀ ≤ A + Mf + A₀)
        (mul_nonneg hnn_pos.le hc₂n_pos.le)
      linarith [h]
    have h2 : n ^ n * c₂ ^ n ≤ Q := by
      rw [hQ]
      have hc₁R1 : 1 ≤ c₁ ^ R := Real.one_le_rpow hc₁ hR0
      have hnnc₂ : 0 ≤ n ^ n * c₂ ^ n := mul_nonneg hnn_pos.le hc₂n_pos.le
      have h := le_mul_of_one_le_left hnnc₂ hc₁R1
      linarith [h]
    have h3 : (A + Mf + A₀) * (n ^ n * c₂ ^ n) ≤ (A + Mf + A₀) * Q :=
      mul_le_mul_of_nonneg_left h2 hAB.le
    linarith [h1, h3]
  have hS_le : A + Mf * c₁ ^ R + A₀ * n ^ n * c₂ ^ n ≤ 3 * P := by linarith
  have hSpos : 0 < A + Mf * c₁ ^ R + A₀ * n ^ n * c₂ ^ n := by
    have h1 : 0 < Mf * c₁ ^ R := mul_pos hMf hc₁R_pos
    have h2 : 0 < A₀ * n ^ n * c₂ ^ n := mul_pos (mul_pos hA₀ hnn_pos) hc₂n_pos
    linarith
  have hlog_le : Real.log (A + Mf * c₁ ^ R + A₀ * n ^ n * c₂ ^ n) ≤ Real.log (3 * P) :=
    Real.log_le_log hSpos hS_le
  have hlogP : Real.log P
      = Real.log (A + Mf + A₀) + Real.log (c₁ ^ R) + Real.log (n ^ n) + Real.log (c₂ ^ n) := by
    rw [hP, Real.log_mul (ne_of_gt hAB) (ne_of_gt hQpos), hQ,
        Real.log_mul (ne_of_gt (mul_pos hc₁R_pos hnn_pos)) (ne_of_gt hc₂n_pos),
        Real.log_mul (ne_of_gt hc₁R_pos) (ne_of_gt hnn_pos)]
    ring
  have hlog3P : Real.log (3 * P) = Real.log 3 + Real.log P :=
    Real.log_mul (by norm_num) (ne_of_gt hPpos)
  have hlog_final : Real.log (A + Mf * c₁ ^ R + A₀ * n ^ n * c₂ ^ n)
      ≤ Real.log 3 + Real.log (A + Mf + A₀) + R * Real.log c₁ + n * Real.log n + n * Real.log c₂ := by
    calc Real.log (A + Mf * c₁ ^ R + A₀ * n ^ n * c₂ ^ n) ≤ Real.log (3 * P) := hlog_le
      _ = Real.log 3 + Real.log P := hlog3P
      _ = Real.log 3 + (Real.log (A + Mf + A₀) + Real.log (c₁ ^ R) + Real.log (n ^ n)
            + Real.log (c₂ ^ n)) := by rw [hlogP]
      _ = Real.log 3 + Real.log (A + Mf + A₀) + R * Real.log c₁ + n * Real.log n + n * Real.log c₂ := by
            rw [Real.log_rpow hc₁pos, Real.log_rpow hn_pos, Real.log_rpow hc₂pos]; ring
  have hnlogn' : n * Real.log n
      ≤ ((k : ℝ) / 2 + 1) * R * (Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2)) := by
    rw [hn]; exact n_log_n_le k hR
  have hnle : n ≤ ((k : ℝ) / 2 + 1) * R := by
    rw [hn]
    have h := mul_le_mul_of_nonneg_left hR hhalf
    nlinarith [h]
  have hnlogc₂ : n * Real.log c₂ ≤ ((k : ℝ) / 2 + 1) * R * Real.log c₂ := by
    have hlogc₂ : 0 ≤ Real.log c₂ := Real.log_nonneg hc₂
    have hpR : 0 ≤ ((k : ℝ) / 2 + 1) * R := mul_nonneg (by linarith) hR0
    exact mul_le_mul hnle le_rfl hlogc₂ hpR
  calc Real.log (A + Mf * c₁ ^ R + A₀ * n ^ n * c₂ ^ n)
      ≤ Real.log 3 + Real.log (A + Mf + A₀) + R * Real.log c₁ + n * Real.log n + n * Real.log c₂ := hlog_final
    _ ≤ Real.log 3 + Real.log (A + Mf + A₀) + R * Real.log c₁
          + ((k : ℝ) / 2 + 1) * R * (Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2))
          + ((k : ℝ) / 2 + 1) * R * Real.log c₂ := by linarith [hnlogn', hnlogc₂]
    _ = Real.log 3 + Real.log (A + Mf + A₀) + R * Real.log c₁
        + ((k : ℝ) / 2 + 1) * R * (Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2) + Real.log c₂) := by ring

/-- Abstract arithmetic bookkeeping: if `e, d, L ≥ 0`, `p > 0` and `R ≥ 1` then
`s + R·e + p·R·(L+d) ≤ (p+e+1)·R·(L + (e + p·d + max s 0 + 1))`. -/
lemma const_bound_arith {s e p d L R : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (hp : 0 < p) (hR : 1 ≤ R) :
    s + R * e + p * R * (L + d)
      ≤ (p + e + 1) * R * (L + (e + p * d + max s 0 + 1)) := by
  have hR0 : 0 ≤ R := by linarith
  have hp0 : 0 ≤ p := hp.le
  have hRL : 0 ≤ R * L := mul_nonneg hR0 hL
  have hC1 : 1 ≤ p + e + 1 := by linarith
  have hCp : p ≤ p + e + 1 := by linarith
  have hpd : 0 ≤ p * d := mul_nonneg hp0 hd
  have hMs0 : 0 ≤ max s 0 := le_max_right s 0
  have hMs_s : s ≤ max s 0 := le_max_left s 0
  have hRMs : max s 0 ≤ R * max s 0 := le_mul_of_one_le_left hMs0 hR
  have hs_bound : s ≤ R * max s 0 + R := by linarith
  have hK0 : 0 ≤ e + p * d + max s 0 + 1 := by linarith
  have h1 : p * R * L ≤ (p + e + 1) * R * L := by
    have h := mul_le_mul_of_nonneg_right hCp hRL
    nlinarith [h]
  have h2 : s + R * e + p * d * R ≤ R * (e + p * d + max s 0 + 1) := by
    have hexp : R * (e + p * d + max s 0 + 1) = R * e + R * (p * d) + R * max s 0 + R := by ring
    rw [hexp]
    have hpr : p * d * R = R * (p * d) := by ring
    linarith [hs_bound, hpr]
  have h3 : s + R * e + p * d * R ≤ (p + e + 1) * R * (e + p * d + max s 0 + 1) := by
    have hCRK : R * (e + p * d + max s 0 + 1) ≤ (p + e + 1) * (R * (e + p * d + max s 0 + 1)) :=
      le_mul_of_one_le_left (mul_nonneg hR0 hK0) hC1
    have hRK : s + R * e + p * d * R ≤ R * (e + p * d + max s 0 + 1) := by
      have hexp : R * (e + p * d + max s 0 + 1) = R * e + R * (p * d) + R * max s 0 + R := by ring
      rw [hexp]
      have hpr : p * d * R = R * (p * d) := by ring
      linarith [hs_bound, hpr]
    nlinarith [hRK, hCRK, mul_nonneg hR0 hK0]
  calc s + R * e + p * R * (L + d)
      = (s + R * e + p * d * R) + p * R * L := by ring
    _ ≤ (p + e + 1) * R * (e + p * d + max s 0 + 1) + (p + e + 1) * R * L := add_le_add h3 h1
    _ = (p + e + 1) * R * (L + (e + p * d + max s 0 + 1)) := by ring

theorem log_growth_arith (k : ℕ) {A Mf A₀ c₁ c₂ : ℝ}
    (hA : 0 < A) (hMf : 0 < Mf) (hA₀ : 0 < A₀) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
      Real.log (A + Mf * c₁ ^ R + A₀ * ((k : ℝ) / 2 + R) ^ ((k : ℝ) / 2 + R) *
          c₂ ^ ((k : ℝ) / 2 + R)) ≤ C * R * (Real.log (R + 2) + K) := by
  set s : ℝ := Real.log 3 + Real.log (A + Mf + A₀) with hs
  set e : ℝ := Real.log c₁ with he
  set p : ℝ := (k : ℝ) / 2 + 1 with hp
  set d : ℝ := Real.log ((k : ℝ) / 2 + 2) + Real.log c₂ with hd
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have he_nn : 0 ≤ e := by rw [he]; exact Real.log_nonneg hc₁
  have hd_nn : 0 ≤ d := by
    rw [hd]
    have h1 : 0 ≤ Real.log ((k : ℝ) / 2 + 2) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log c₂ := Real.log_nonneg hc₂
    linarith
  have hp_pos : 0 < p := by rw [hp]; linarith
  refine ⟨p + e + 1, e + p * d + max s 0 + 1, ?_, ?_, ?_⟩
  · linarith
  · have hpd : 0 ≤ p * d := mul_nonneg hp_pos.le hd_nn
    have := le_max_right s 0
    linarith
  · intro R hR
    have hL : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have hmain : Real.log (A + Mf * c₁ ^ R + A₀ * ((k : ℝ) / 2 + R) ^ ((k : ℝ) / 2 + R) *
          c₂ ^ ((k : ℝ) / 2 + R)) ≤ s + R * e + p * R * (Real.log (R + 2) + d) := by
      calc Real.log (A + Mf * c₁ ^ R + A₀ * ((k : ℝ) / 2 + R) ^ ((k : ℝ) / 2 + R) *
              c₂ ^ ((k : ℝ) / 2 + R))
          ≤ Real.log 3 + Real.log (A + Mf + A₀) + R * Real.log c₁
            + ((k : ℝ) / 2 + 1) * R * (Real.log (R + 2) + Real.log ((k : ℝ) / 2 + 2) + Real.log c₂) :=
              main_log_bound k hA hMf hA₀ hc₁ hc₂ hR
        _ = s + R * e + p * R * (Real.log (R + 2) + d) := by rw [hs, he, hp, hd]; ring
    have hcb := const_bound_arith (s := s) (e := e) (p := p) (d := d)
      (L := Real.log (R + 2)) (R := R) he_nn hd_nn hL hp_pos hR
    linarith [hmain, hcb]

end

end Work.FIArea6Hecke.R.MGGrow
