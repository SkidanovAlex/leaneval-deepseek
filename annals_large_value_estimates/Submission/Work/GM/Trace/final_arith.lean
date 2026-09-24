import Mathlib
import Submission.Work.GM.Trace.Spart_defs

/-!
# Final arithmetic for the `S₁`/`S₂` bookkeeping in GM Proposition 5.1

This file proves `Work.GM.Trace.final_arith`: the elementary real-arithmetic estimate that
turns a bound of the shape

`27 · X³ · (N³ w Az² Cd / N^j + 2 N³ w³ Az² Cz / (M N^ε)^j) + 24 · (…) / X^{j-1}`

(with `X = M N^(1+ε)/N`) into `≤ 1`, for `N` large, under `w ≤ M N + 1`, `j ≥ 4ε + 10` and
`ε j ≥ 20`.  Since `M N = N^{6/5}`, every term decays like a negative power of `N`, so the
result is an "eventually `≤ 1`" statement.

The proof bounds each of the three summands separately:

* `27 (M^{1+ε}/N)³ · N³ w Az² Cd / N^j  ≤ 54 Az² Cd · N^{-1}`,
* `27 (M^{1+ε}/N)³ · 2 N³ w³ Az² Cz / (M^ε)^j ≤ 432 Az² Cz · N^{-1}`,
* `24 (N³ w³ Az² Cd (1+M)^j / N^j) / (M^{1+ε}/N)^{j-1} ≤ 192 · 2^j Az² Cd · N^{-1}`,

and then chooses `N₀ > 54 Az² Cd + 432 Az² Cz + 192 · 2^j Az² Cd`.
-/

namespace Work.GM.Trace

open Submission.LargeValues

/-! ## Helper lemmas on real powers -/

/-- `(x^y)^k = x^(y k)` for `x ≥ 0`. -/
private lemma rpow_pow (x : ℝ) (hx : 0 ≤ x) (y : ℝ) (k : ℕ) :
    (x ^ y) ^ k = x ^ (y * k) := by
  rw [← Real.rpow_natCast (x ^ y) k, Real.rpow_mul hx]

/-- `x^a * x^k = x^(a + k)` for `x > 0` and a natural exponent `k`. -/
private lemma rpow_mul_pow (x : ℝ) (hx : 0 < x) (a : ℝ) (k : ℕ) :
    x ^ a * x ^ k = x ^ (a + k) := by
  rw [← Real.rpow_natCast x k, ← Real.rpow_add hx]

/-- For `x ≥ 1`, `x^a / x^k ≤ x^c` as soon as `a ≤ k + c`. -/
private lemma rpow_div_pow_le {x : ℝ} (hx : 1 ≤ x) {a c : ℝ} {k : ℕ}
    (h : a ≤ (k : ℝ) + c) : x ^ a / x ^ k ≤ x ^ c := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hk : 0 < x ^ k := pow_pos hx0 k
  have h1 : x ^ a ≤ x ^ ((k : ℝ) + c) := Real.rpow_le_rpow_of_exponent_le hx h
  rw [Real.rpow_add hx0, Real.rpow_natCast] at h1
  rw [div_le_iff₀ hk]
  calc x ^ a ≤ x ^ k * x ^ c := h1
    _ = x ^ c * x ^ k := by ring

/-- `(M N)^y = N^{(6/5) y}`. -/
private lemma Mrpow (N : ℕ) (y : ℝ) :
    M N ^ y = (N:ℝ) ^ ((6/5) * y) := by
  have hn0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  rw [M, ← Real.rpow_mul hn0]

/-! ## The three summand bounds -/

/-- The `Cd`-summand of the first group decays like `N^{-1}`. -/
private lemma term1 (ε : ℝ) (j : ℕ) (hj : 4*ε + 10 ≤ (j:ℝ)) (Az Cd : ℝ)
    (hAz : 0 ≤ Az) (hCd : 0 ≤ Cd)
    (N : ℕ) (hN : 2 ≤ N) (w : ℝ) (hw0 : 0 ≤ w) (hw : w ≤ M N + 1) :
    27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 * ((N : ℝ) ^ 3 * w * Az ^ 2 * Cd / (N : ℝ) ^ j)
      ≤ 54 * Az ^ 2 * Cd * (N : ℝ) ^ (-1 : ℝ) := by
  have hNpos : (0:ℕ) < N := by omega
  have hn0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hn1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hm0 : 0 < M N := M_pos (by omega : 1 ≤ N)
  have hm1 : 1 ≤ M N := M_ge_one (by omega : 1 ≤ N)
  have hw2 : w ≤ 2 * M N := by linarith
  have hjn : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  have hexp : (6/5) * (4 + 3*ε) ≤ (j:ℝ) + (-1) := by linarith
  have hkey : M N ^ (4 + 3*ε) / (N:ℝ)^j ≤ (N:ℝ)^(-1:ℝ) := by
    rw [Mrpow N (4+3*ε)]
    exact rpow_div_pow_le hn1 hexp
  have heq : 27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 * ((N : ℝ) ^ 3 * w * Az ^ 2 * Cd / (N : ℝ) ^ j)
      = 27 * M N ^ (3 + 3*ε) * w * Az^2 * Cd / (N:ℝ)^j := by
    have e1 : (M N ^ (1 + ε)) ^ 3 = M N ^ (3 + 3 * ε) := by
      rw [← Real.rpow_natCast (M N ^ (1 + ε)) 3, ← Real.rpow_mul hm0.le]
      congr 1
      ring
    rw [div_pow, e1]
    field_simp
  rw [heq]
  have hmul : M N ^ (3 + 3*ε) * M N = M N ^ (4 + 3*ε) := by
    have h := Real.rpow_add hm0 (3 + 3*ε) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  calc 27 * M N ^ (3 + 3 * ε) * w * Az ^ 2 * Cd / (N:ℝ)^j
      ≤ 27 * M N ^ (3 + 3 * ε) * (2 * M N) * Az ^ 2 * Cd / (N:ℝ)^j := by gcongr
    _ = 54 * Az ^ 2 * Cd * (M N ^ (4 + 3*ε) / (N:ℝ)^j) := by
        rw [← hmul]; ring
    _ ≤ 54 * Az ^ 2 * Cd * (N:ℝ)^(-1:ℝ) := by
        apply mul_le_mul_of_nonneg_left hkey
        positivity

/-- The `Cz`-summand of the first group decays like `N^{-1}`. -/
private lemma term2 (ε : ℝ) (hε : 0 < ε) (j : ℕ) (hj : 4*ε + 10 ≤ (j:ℝ)) (hεj : 20 ≤ ε * j)
    (Az Cz : ℝ) (hAz : 0 ≤ Az) (hCz : 0 ≤ Cz)
    (N : ℕ) (hN : 2 ≤ N) (w : ℝ) (hw0 : 0 ≤ w) (hw : w ≤ M N + 1) :
    27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 *
        (2 * (N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cz / (M N ^ ε) ^ j)
      ≤ 432 * Az ^ 2 * Cz * (N : ℝ) ^ (-1 : ℝ) := by
  have hNpos : (0:ℕ) < N := by omega
  have hn0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hn1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hm0 : 0 < M N := M_pos (by omega : 1 ≤ N)
  have hm1 : 1 ≤ M N := M_ge_one (by omega : 1 ≤ N)
  have hw2 : w ≤ 2 * M N := by linarith
  have hcase : (41:ℝ)/6 ≤ ε * ((j:ℝ) - 3) := by
    by_cases h1 : ε ≤ 1
    · have h2 : ε * ((j:ℝ) - 3) = ε*(j:ℝ) - 3*ε := by ring
      rw [h2]; linarith
    · push_neg at h1
      have h3 : (11:ℝ) ≤ (j:ℝ) - 3 := by linarith
      have h4 : (1:ℝ) ≤ ε := le_of_lt h1
      have h5 := mul_le_mul_of_nonneg_right h4 (by linarith : (0:ℝ) ≤ (j:ℝ) - 3)
      simp only [one_mul] at h5
      linarith
  have hexp2 : (6/5) * (6 + 3*ε - ε * (j:ℝ)) ≤ (-1:ℝ) := by
    have h : ε * ((j:ℝ) - 3) = ε*(j:ℝ) - 3*ε := by ring
    rw [h] at hcase
    linarith
  have hkey2 : M N ^ (6 + 3*ε - ε * (j:ℝ)) ≤ (N:ℝ)^(-1:ℝ) := by
    rw [Mrpow N (6 + 3*ε - ε*(j:ℝ))]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hexp2
  have heq : 27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 *
        (2 * (N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cz / (M N ^ ε) ^ j)
      = 54 * M N ^ (3 + 3*ε) * w ^ 3 * Az ^ 2 * Cz / (M N ^ ε) ^ j := by
    have e1 : (M N ^ (1 + ε)) ^ 3 = M N ^ (3 + 3 * ε) := by
      rw [← Real.rpow_natCast (M N ^ (1 + ε)) 3, ← Real.rpow_mul hm0.le]
      congr 1; ring
    rw [div_pow, e1]
    field_simp
    ring
  rw [heq, rpow_pow (M N) hm0.le ε j]
  have hmeq : 54 * M N ^ (3+3*ε) * (2*M N)^3 * Az^2 * Cz / M N ^ (ε*(j:ℝ))
      = 432 * Az^2 * Cz * M N ^ (6+3*ε - ε*(j:ℝ)) := by
    have key : M N ^ (3+3*ε) * M N^3 = M N ^ (6+3*ε) := by
      rw [← Real.rpow_natCast (M N) 3, ← Real.rpow_add hm0]
      congr 1; ring
    rw [Real.rpow_sub hm0]
    rw [show (2*M N)^3 = 8 * M N^3 by ring]
    rw [← key]
    ring
  calc 54 * M N ^ (3 + 3*ε) * w^3 * Az^2 * Cz / M N ^ (ε*(j:ℝ))
      ≤ 54 * M N ^ (3 + 3*ε) * (2*M N)^3 * Az^2 * Cz / M N ^ (ε*(j:ℝ)) := by
        gcongr
    _ = 432 * Az^2 * Cz * M N ^ (6 + 3*ε - ε*(j:ℝ)) := hmeq
    _ ≤ 432 * Az^2 * Cz * (N:ℝ)^(-1:ℝ) := by
        apply mul_le_mul_of_nonneg_left hkey2
        positivity

/-- The second group decays like `N^{-1}`. -/
private lemma term3 (ε : ℝ) (hε : 0 < ε) (j : ℕ) (hj : 4*ε + 10 ≤ (j:ℝ)) (hεj : 20 ≤ ε * j)
    (Az Cd : ℝ) (hAz : 0 ≤ Az) (hCd : 0 ≤ Cd)
    (N : ℕ) (hN : 2 ≤ N) (w : ℝ) (hw0 : 0 ≤ w) (hw : w ≤ M N + 1) :
    24 * ((N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cd * (1 + M N) ^ j / (N : ℝ) ^ j) /
        (M N ^ (1 + ε) / (N : ℝ)) ^ (j - 1)
      ≤ 192 * (2:ℝ)^j * Az ^ 2 * Cd * (N : ℝ) ^ (-1 : ℝ) := by
  have hNpos : (0:ℕ) < N := by omega
  have hn0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hn1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hm0 : 0 < M N := M_pos (by omega : 1 ≤ N)
  have hm1 : 1 ≤ M N := M_ge_one (by omega : 1 ≤ N)
  have hw2 : w ≤ 2 * M N := by linarith
  have hj1 : 1 ≤ j := by
    have : (1:ℝ) ≤ (j:ℝ) := by linarith
    exact_mod_cast this
  have hm21 : 1 + M N ≤ 2 * M N := by linarith
  have hcase : (13:ℝ)/2 ≤ ε * ((j:ℝ) - 1) := by
    by_cases h1 : ε ≤ 1
    · have h2 : ε * ((j:ℝ) - 1) = ε*(j:ℝ) - ε := by ring
      rw [h2]; linarith
    · push_neg at h1
      have h3 : (13:ℝ) ≤ (j:ℝ) - 1 := by linarith
      have h4 : (1:ℝ) ≤ ε := le_of_lt h1
      have h5 := mul_le_mul_of_nonneg_right h4 (by linarith : (0:ℝ) ≤ (j:ℝ) - 1)
      simp only [one_mul] at h5
      linarith
  have hexp3 : (2:ℝ) + (6/5) * (((3+j:ℕ):ℝ) - (1+ε)*((j:ℝ)-1)) ≤ -1 := by
    have hsplit : (1+ε)*((j:ℝ)-1) = ((j:ℝ)-1) + ε*((j:ℝ)-1) := by ring
    rw [hsplit]
    push_cast
    linarith
  have hstep : (N:ℝ)^2 * (M N ^ (3+j) / M N ^ ((1+ε)*((j:ℝ)-1))) ≤ (N:ℝ)^(-1:ℝ) := by
    have h1 : M N ^ (3+j) / M N ^ ((1+ε)*((j:ℝ)-1))
        = M N ^ (((3+j:ℕ):ℝ) - (1+ε)*((j:ℝ)-1)) := by
      rw [← Real.rpow_natCast (M N) (3+j), ← Real.rpow_sub hm0]
    rw [h1, Mrpow N (((3+j:ℕ):ℝ) - (1+ε)*((j:ℝ)-1))]
    rw [← Real.rpow_natCast (N:ℝ) 2, ← Real.rpow_add hn0]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hexp3
  have hpowj : (N:ℝ)^j = (N:ℝ)^(j-1) * (N:ℝ) := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos (show 0 < j by omega)]
    rw [pow_succ]
    simp only [Nat.pred_eq_sub_one]
  have heq : 24 * ((N:ℝ)^3 * w^3 * Az^2 * Cd * (1+M N)^j / (N:ℝ)^j) / (M N ^ (1+ε)/(N:ℝ))^(j-1)
      = 24 * (N:ℝ)^2 * w^3 * Az^2 * Cd * (1+M N)^j / M N ^ ((1+ε)*((j-1:ℕ):ℝ)) := by
    rw [div_pow, rpow_pow (M N) hm0.le (1+ε) (j-1), hpowj]
    field_simp
  rw [heq]
  have hcast : ((j-1:ℕ):ℝ) = (j:ℝ) - 1 := by
    rw [Nat.cast_sub hj1]; norm_num
  have hmeq : 24 * (N:ℝ)^2 * (2*M N)^3 * Az^2*Cd * (2*M N)^j / M N ^ ((1+ε)*((j-1:ℕ):ℝ))
      = 192 * (2:ℝ)^j * Az^2 * Cd * ((N:ℝ)^2 * (M N ^ (3+j) / M N ^ ((1+ε)*((j:ℝ)-1)))) := by
    rw [hcast, show (2*M N)^3 = 8 * M N^3 by ring, mul_pow]
    have h3j : M N ^ 3 * M N ^ j = M N ^ (3+j) := (pow_add (M N) 3 j).symm
    rw [show 24 * (N:ℝ)^2 * (8 * M N^3) * Az^2 * Cd * ((2:ℝ)^j * M N^j)
          / M N ^ ((1+ε)*((j:ℝ)-1))
        = 192 * (2:ℝ)^j * Az^2 * Cd *
            ((N:ℝ)^2 * ((M N^3 * M N^j) / M N ^ ((1+ε)*((j:ℝ)-1)))) by ring]
    rw [h3j]
  calc 24 * (N:ℝ)^2 * w^3 * Az^2*Cd*(1+M N)^j / M N ^ ((1+ε)*((j-1:ℕ):ℝ))
      ≤ 24 * (N:ℝ)^2 * (2*M N)^3 * Az^2*Cd*(2*M N)^j / M N ^ ((1+ε)*((j-1:ℕ):ℝ)) := by
        gcongr
    _ = 192 * (2:ℝ)^j * Az^2 * Cd * ((N:ℝ)^2 * (M N ^ (3+j) / M N ^ ((1+ε)*((j:ℝ)-1)))) := hmeq
    _ ≤ 192 * (2:ℝ)^j * Az^2 * Cd * (N:ℝ)^(-1:ℝ) := by
        apply mul_le_mul_of_nonneg_left hstep
        positivity

/-! ## The final statement -/

theorem final_arith (ε : ℝ) (hε : 0 < ε) (j : ℕ) (hj : 4 * ε + 10 ≤ (j : ℝ)) (hεj : 20 ≤ ε * j)
    (Az Cd Cz : ℝ) (hAz : 0 ≤ Az) (hCd : 0 ≤ Cd) (hCz : 0 ≤ Cz) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w : ℝ, 0 ≤ w → w ≤ Submission.LargeValues.M N + 1 →
      27 * (Submission.LargeValues.M N ^ (1 + ε) / (N : ℝ)) ^ 3 *
          ((N : ℝ) ^ 3 * w * Az ^ 2 * Cd / (N : ℝ) ^ j +
            2 * (N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cz / (Submission.LargeValues.M N ^ ε) ^ j) +
        24 * ((N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cd * (1 + Submission.LargeValues.M N) ^ j /
              (N : ℝ) ^ j) /
          (Submission.LargeValues.M N ^ (1 + ε) / (N : ℝ)) ^ (j - 1) ≤ 1 := by
  set K : ℝ := 54 * Az^2 * Cd + 432 * Az^2 * Cz + 192 * (2:ℝ)^j * Az^2 * Cd with hK
  obtain ⟨M0, hM0⟩ := exists_nat_gt (max 2 K)
  refine ⟨M0, ?_⟩
  intro N hN w hw0 hw
  have hNge : (M0:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hN2 : 2 ≤ N := by
    have h2 : (2:ℝ) ≤ max 2 K := le_max_left _ _
    have hlt : (2:ℝ) < (N:ℝ) := by linarith
    have : 2 < N := by exact_mod_cast hlt
    omega
  have hNK : K ≤ (N:ℝ) := by
    have h2 : K ≤ max 2 K := le_max_right _ _
    linarith
  have hn0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h1 := term1 ε j hj Az Cd hAz hCd N hN2 w hw0 hw
  have h2 := term2 ε hε j hj hεj Az Cz hAz hCz N hN2 w hw0 hw
  have h3 := term3 ε hε j hj hεj Az Cd hAz hCd N hN2 w hw0 hw
  have hE : 27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 *
          ((N : ℝ) ^ 3 * w * Az ^ 2 * Cd / (N : ℝ) ^ j +
            2 * (N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cz / (M N ^ ε) ^ j) +
        24 * ((N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cd * (1 + M N) ^ j /
              (N : ℝ) ^ j) /
          (M N ^ (1 + ε) / (N : ℝ)) ^ (j - 1)
      = 27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 * ((N : ℝ) ^ 3 * w * Az ^ 2 * Cd / (N : ℝ) ^ j)
        + 27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 *
            (2 * (N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cz / (M N ^ ε) ^ j)
        + 24 * ((N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cd * (1 + M N) ^ j / (N : ℝ) ^ j) /
            (M N ^ (1 + ε) / (N : ℝ)) ^ (j - 1) := by ring
  rw [hE]
  have hfin : K * (N:ℝ)^(-1:ℝ) ≤ 1 := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hn0]
    linarith
  have hcomb : 27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 * ((N : ℝ) ^ 3 * w * Az ^ 2 * Cd / (N : ℝ) ^ j)
        + 27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 *
            (2 * (N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cz / (M N ^ ε) ^ j)
        + 24 * ((N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cd * (1 + M N) ^ j / (N : ℝ) ^ j) /
            (M N ^ (1 + ε) / (N : ℝ)) ^ (j - 1) ≤ K * (N:ℝ)^(-1:ℝ) := by
    have hsum : 27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 * ((N : ℝ) ^ 3 * w * Az ^ 2 * Cd / (N : ℝ) ^ j)
          + 27 * (M N ^ (1 + ε) / (N : ℝ)) ^ 3 *
              (2 * (N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cz / (M N ^ ε) ^ j)
          + 24 * ((N : ℝ) ^ 3 * w ^ 3 * Az ^ 2 * Cd * (1 + M N) ^ j / (N : ℝ) ^ j) /
              (M N ^ (1 + ε) / (N : ℝ)) ^ (j - 1)
        ≤ 54 * Az ^ 2 * Cd * (N:ℝ)^(-1:ℝ) + 432 * Az ^ 2 * Cz * (N:ℝ)^(-1:ℝ)
          + 192 * (2:ℝ)^j * Az ^ 2 * Cd * (N:ℝ)^(-1:ℝ) := by linarith [h1, h2, h3]
    have he : 54 * Az ^ 2 * Cd * (N:ℝ)^(-1:ℝ) + 432 * Az ^ 2 * Cz * (N:ℝ)^(-1:ℝ)
          + 192 * (2:ℝ)^j * Az ^ 2 * Cd * (N:ℝ)^(-1:ℝ) = K * (N:ℝ)^(-1:ℝ) := by
      rw [hK]; ring
    linarith [hsum, he]
  linarith [hcomb, hfin]

end Work.GM.Trace
