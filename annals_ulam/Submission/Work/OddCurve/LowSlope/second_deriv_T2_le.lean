import Mathlib

/-!
# The numeric bound `T₂ ≤ 4/3` for the low-slope odd reconstruction

Let `k₁ = 2n+1`, `k₂ = 2n+2`, `E = R^(k₂) + r^(k₂) - 2`, `F = R^(k₁) - r^(k₁)`,
`p = 1 - 2|E|`, `q = 1 - 2|F|` and

`T₂ = (k₁ + k₂ r)(k₁ p + k₂ r q) / (k₂ k₁ R^(4n+1) (R+r)²)`.

Under the hypotheses `R^(k₂), r^(k₂) ∈ [3/8, 15/8]` (with `n ≥ 1`) we prove `T₂ ≤ 4/3`.

The proof never uses the two "closeness" hypotheses `|E| ≤ 1/2`, `|F| ≤ 1/2`; they are
carried only because the caller states the lemma in that form.

Write `k = 2n+1`, `W = k + (k+1) r`, `c = R^k (R+r)`.  Then

* `k p + (k+1) r q = W - 2 (k|E| + (k+1) r |F|)`, and `R^(4n+1) = R^(2k-1)`;
* `c² / R = R^(2k-1) (R+r)²`  (because `R^(2k) = R^(2k-1)·R`), so `c² ≤ R^(2k-1)(R+r)²`
  whenever `R ≤ 1`, and `R^(2k-1)(R+r)² ≥ 4` whenever `c ≥ 2` and `R ≤ 1`.

**Case `R ≥ 1`.**  `R^(2k-1) ≥ 1` and `R + r ≥ 1 + r`, so `(4/3)k(k+1)R^(2k-1)(R+r)² ≥
(4/3)k(k+1)(1+r)² ≥ W²` (`Bernoulli`-style algebra), and `kp + (k+1)rq ≤ W`.

**Case `R ≤ 1`.**
* If `c ≥ 2` then `R^(2k-1)(R+r)² ≥ c² ≥ 4 ≥ (k + (5/4)(k+1))²·3/16 …`, i.e.
  `(4/3)k(k+1)R^(2k-1)(R+r)² ≥ (16/3)k(k+1) ≥ W²` (as `r ≤ 5/4`).
* If `c ≤ 2` then `E + r F = c - 2` gives
  `k|E| + (k+1)r|F| ≥ k|c-2| + r|F| = k(2-c) + r|F|`, and `|F| ≥ k(r-1)` (for `r ≥ 1`
  because `R ≤ 1 ≤ r`; trivially for `r ≤ 1`).  Hence
  `W(kp+(k+1)rq) ≤ W² - 2kW((2-c) + r² - r) ≤ (4/3)k(k+1)c² ≤ (4/3)k(k+1)R^(2k-1)(R+r)²`,
  the middle inequality being a `Bernoulli`-free algebraic statement proved by completing
  the square in `c`.
-/

set_option linter.unusedVariables false

set_option maxHeartbeats 2000000

namespace Work.OddCurve.LowSlope

/-- `3/8 ≤ R^(K+1)` with `K ≥ 3` forces `R ≥ 3/4`. -/
private lemma pow_ge_three_quarters {K : ℕ} (hK : 3 ≤ K) {R : ℝ} (hR : 0 < R)
    (h1 : 3 / 8 ≤ R ^ (K + 1)) : 3 / 4 ≤ R := by
  have hK4 : (4 : ℕ) ≤ K + 1 := by omega
  have hle : (3 / 4 : ℝ) ^ (K + 1) ≤ (3 / 4 : ℝ) ^ 4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hK4
  have h4 : (3 / 4 : ℝ) ^ 4 = 81 / 256 := by norm_num
  have hbase : (3 / 4 : ℝ) ^ (K + 1) ≤ 3 / 8 := by rw [h4] at hle; linarith
  exact (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hR.le
    (by omega : K + 1 ≠ 0)).mp (le_trans hbase h1)

/-- `R^(K+1) ≤ 15/8` with `K ≥ 3` forces `R ≤ 5/4`. -/
private lemma pow_le_five_quarters {K : ℕ} (hK : 3 ≤ K) {R : ℝ} (hR : 0 < R)
    (h2 : R ^ (K + 1) ≤ 15 / 8) : R ≤ 5 / 4 := by
  have hK4 : (4 : ℕ) ≤ K + 1 := by omega
  have hle : (5 / 4 : ℝ) ^ 4 ≤ (5 / 4 : ℝ) ^ (K + 1) :=
    pow_le_pow_right₀ (by norm_num) hK4
  have h4 : (5 / 4 : ℝ) ^ 4 = 625 / 256 := by norm_num
  have hbase : (15 / 8 : ℝ) ≤ (5 / 4 : ℝ) ^ (K + 1) := by rw [h4] at hle; linarith
  exact (pow_le_pow_iff_left₀ hR.le (by norm_num : (0 : ℝ) ≤ 5 / 4)
    (by omega : K + 1 ≠ 0)).mp (le_trans h2 hbase)

/-- For `k ≥ 3` and `r ≥ 0`: `(k + (k+1)r)² ≤ (4/3) k (k+1) (1+r)²`. -/
private lemma sq_le_one_add {k r : ℝ} (hk : 3 ≤ k) (hr : 0 ≤ r) :
    (k + (k + 1) * r) ^ 2 ≤ (4 / 3) * k * (k + 1) * (1 + r) ^ 2 := by
  nlinarith [sq_nonneg ((k + 1) * r - k / 2), sq_nonneg (k - 3), sq_nonneg r]

/-- For `k ≥ 3`: `(k + (5/4)(k+1))² ≤ (16/3) k (k+1)`. -/
private lemma sq_upper {k : ℝ} (hk : 3 ≤ k) :
    (k + (5 / 4) * (k + 1)) ^ 2 ≤ (16 / 3) * k * (k + 1) := by
  nlinarith [sq_nonneg (k - 3), sq_nonneg (7 * k - 3)]

/-- The algebraic core of the case `R ≤ 1`, `c ≤ 2`:
`(k + (k+1)r)² - 2k(k+(k+1)r)(2 - c + r² - r) ≤ (4/3) k (k+1) c²`
for `k ≥ 3`, `3/4 ≤ r ≤ 5/4` and arbitrary `c` (no constraint on `c` is needed because the
left-hand side is concave in `c`). -/
private lemma core_ineq {k r c : ℝ} (hk : 3 ≤ k) (hr1 : 3 / 4 ≤ r) (hr2 : r ≤ 5 / 4) :
    (k + (k + 1) * r) ^ 2 - 2 * k * (k + (k + 1) * r) * (2 - c + r ^ 2 - r)
      ≤ (4 / 3) * k * (k + 1) * c ^ 2 := by
  have hkpos : (0 : ℝ) < k := by linarith
  have hkp1 : (0 : ℝ) < k + 1 := by linarith
  have hquad : 0 ≤ 8 * k * (k + 1) * r ^ 2 - (15 * k ^ 2 + 19 * k + 4) * r + 9 * k ^ 2 + 12 * k := by
    have h1 : (15 * k ^ 2 + 19 * k + 4) ^ 2 ≤ 32 * k * (k + 1) * (9 * k ^ 2 + 12 * k) := by
      nlinarith [sq_nonneg (k - 3), sq_nonneg (7 * k - 3), sq_nonneg (k * k - 9)]
    nlinarith [h1, sq_nonneg (16 * k * (k + 1) * r - (15 * k ^ 2 + 19 * k + 4)), sq_nonneg (k - 3)]
  have hWnonneg : 0 ≤ k + (k + 1) * r := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k + 1) (by linarith : (0 : ℝ) ≤ r)]
  have hfac : 8 * k * (k + 1) * (2 + r ^ 2 - r) - (k + (k + 1) * r) * (7 * k + 4)
      = 8 * k * (k + 1) * r ^ 2 - (15 * k ^ 2 + 19 * k + 4) * r + 9 * k ^ 2 + 12 * k := by
    ring
  have hkey : 0 ≤ (k + (k + 1) * r) * (8 * k * (k + 1) * (2 + r ^ 2 - r) - (k + (k + 1) * r) * (7 * k + 4)) := by
    rw [hfac]; exact mul_nonneg hWnonneg hquad
  have hbr : (k + (k + 1) * r) ^ 2 - 2 * k * (k + (k + 1) * r) * (2 + r ^ 2 - r)
      + 3 * k * (k + (k + 1) * r) ^ 2 / (4 * (k + 1)) ≤ 0 := by
    have h4 : (0 : ℝ) < 4 * (k + 1) := by linarith
    have hmul : (4 * (k + 1)) * ((k + (k + 1) * r) ^ 2
        - 2 * k * (k + (k + 1) * r) * (2 + r ^ 2 - r)
        + 3 * k * (k + (k + 1) * r) ^ 2 / (4 * (k + 1))) ≤ 0 := by
      field_simp
      nlinarith [hkey]
    nlinarith [hmul, h4]
  have hid : (k + (k + 1) * r) ^ 2 - 2 * k * (k + (k + 1) * r) * (2 - c + r ^ 2 - r)
      - (4 / 3) * k * (k + 1) * c ^ 2
      = ((k + (k + 1) * r) ^ 2 - 2 * k * (k + (k + 1) * r) * (2 + r ^ 2 - r)
          + 3 * k * (k + (k + 1) * r) ^ 2 / (4 * (k + 1)))
        - (4 / 3) * k * (k + 1) * (c - 3 * (k + (k + 1) * r) / (4 * (k + 1))) ^ 2 := by
    field_simp
    ring
  have hnn : 0 ≤ (4 / 3) * k * (k + 1) * (c - 3 * (k + (k + 1) * r) / (4 * (k + 1))) ^ 2 := by
    positivity
  linarith [hid, hbr, hnn]

/-- The main numeric estimate for a general exponent `K ≥ 3`. -/
private lemma key (K : ℕ) (hK : 3 ≤ K) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (ha1 : 3 / 8 ≤ R ^ (K + 1)) (ha2 : R ^ (K + 1) ≤ 15 / 8)
    (hb1 : 3 / 8 ≤ r ^ (K + 1)) (hb2 : r ^ (K + 1) ≤ 15 / 8) :
    ((K : ℝ) + ((K : ℝ) + 1) * r)
        * ((K : ℝ) * (1 - 2 * |R ^ (K + 1) + r ^ (K + 1) - 2|)
          + ((K : ℝ) + 1) * r * (1 - 2 * |R ^ K - r ^ K|))
      ≤ (4 / 3) * (K : ℝ) * ((K : ℝ) + 1) * (R ^ (2 * K - 1) * (R + r) ^ 2) := by
  set k : ℝ := (K : ℝ) with hkdef
  have hk3 : (3 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast hK
  have hkpos : (0 : ℝ) < k := by linarith
  have hR3 : 3 / 4 ≤ R := pow_ge_three_quarters hK hR ha1
  have hR5 : R ≤ 5 / 4 := pow_le_five_quarters hK hR ha2
  have hr3 : 3 / 4 ≤ r := pow_ge_three_quarters hK hr hb1
  have hr5 : r ≤ 5 / 4 := pow_le_five_quarters hK hr hb2
  set E : ℝ := R ^ (K + 1) + r ^ (K + 1) - 2 with hE
  set F : ℝ := R ^ K - r ^ K with hF
  set c : ℝ := R ^ K * (R + r) with hc
  set W : ℝ := k + (k + 1) * r with hW
  have hWnonneg : 0 ≤ W := by rw [hW]; nlinarith [hkpos, hr]
  have hWp : k * (1 - 2 * |E|) + (k + 1) * r * (1 - 2 * |F|)
      = W - 2 * (k * |E| + (k + 1) * r * |F|) := by rw [hW]; ring
  have hWq : k * (1 - 2 * |E|) + (k + 1) * r * (1 - 2 * |F|) ≤ W := by
    rw [hWp]
    have h1 : 0 ≤ k * |E| := by positivity
    have h2 : 0 ≤ (k + 1) * r * |F| := by positivity
    linarith
  have hK2 : (R ^ K) ^ 2 = R ^ (2 * K) := by rw [← pow_mul]; congr 1; omega
  have hc2 : c ^ 2 = R ^ (2 * K) * (R + r) ^ 2 := by rw [hc, mul_pow, hK2]
  have hpsucc : R ^ (2 * K) = R ^ (2 * K - 1) * R := by
    rw [← pow_succ]; congr 1; omega
  have hid : c ^ 2 = (R ^ (2 * K - 1) * (R + r) ^ 2) * R := by rw [hc2, hpsucc]; ring
  have hnn : 0 ≤ R ^ (2 * K - 1) * (R + r) ^ 2 := by positivity
  have hPhi_ge_c2 (hR1le : R ≤ 1) : c ^ 2 ≤ R ^ (2 * K - 1) * (R + r) ^ 2 := by
    rw [hid]
    exact mul_le_of_le_one_right hnn hR1le
  have hmain : W * (k * (1 - 2 * |E|) + (k + 1) * r * (1 - 2 * |F|))
      ≤ (4 / 3) * k * (k + 1) * (R ^ (2 * K - 1) * (R + r) ^ 2) := by
    rcases lt_or_ge R 1 with hRlt | hRge
    · -- `R < 1`, hence `R ≤ 1`
      have hR1le : R ≤ 1 := le_of_lt hRlt
      have hc2le : c ^ 2 ≤ R ^ (2 * K - 1) * (R + r) ^ 2 := hPhi_ge_c2 hR1le
      rcases lt_or_ge c 2 with hclt | hcge
      · -- `c < 2`
        have hcle : c ≤ 2 := le_of_lt hclt
        have hEid : E + r * F = c - 2 := by rw [hE, hF, hc]; ring
        have hFb : k * (r - 1) ≤ |F| := by
          rw [hkdef]
          rcases lt_or_ge r 1 with hrlt | hrge
          · have hneg : r - 1 ≤ 0 := by linarith
            have hcast : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
            have hle0 : ((K : ℝ)) * (r - 1) ≤ 0 := by nlinarith
            linarith [abs_nonneg F]
          · have hRK : R ^ K ≤ 1 := pow_le_one₀ hR.le hR1le
            have hrK : (1 : ℝ) ≤ r ^ K := one_le_pow₀ hrge
            have hFnonpos : R ^ K - r ^ K ≤ 0 := by linarith
            have hFval : |F| = r ^ K - R ^ K := by
              rw [hF, abs_of_nonpos hFnonpos]
              ring
            have hbern : 1 + ((K : ℝ)) * (r - 1) ≤ r ^ K := one_add_mul_sub_le_pow (by linarith) K
            linarith
        have hpen : k * (2 - c) + k * r * (r - 1) ≤ k * |E| + (k + 1) * r * |F| := by
          have h1 : |E + r * F| ≤ |E| + r * |F| := by
            calc |E + r * F| ≤ |E| + |r * F| := abs_add_le E (r * F)
              _ = |E| + r * |F| := by rw [abs_mul, abs_of_pos hr]
          have h2 : k * |E + r * F| = k * (2 - c) := by
            rw [hEid, abs_of_nonpos (by linarith : c - 2 ≤ 0)]
            ring
          have h3 : k * r * (r - 1) ≤ r * |F| := by
            have hh := mul_le_mul_of_nonneg_left hFb hr.le
            nlinarith [hh]
          have h4 : k * |E + r * F| ≤ k * (|E| + r * |F|) := mul_le_mul_of_nonneg_left h1 hkpos.le
          nlinarith [h2, h3, h4, hkpos, hr]
        have hcore := core_ineq hk3 hr3 hr5 (c := c)
        have hstep : W - 2 * (k * |E| + (k + 1) * r * |F|)
            ≤ W - 2 * (k * (2 - c) + k * r * (r - 1)) := by
          linarith [hpen]
        calc W * (k * (1 - 2 * |E|) + (k + 1) * r * (1 - 2 * |F|))
            = W * (W - 2 * (k * |E| + (k + 1) * r * |F|)) := by rw [hWp]
          _ ≤ W * (W - 2 * (k * (2 - c) + k * r * (r - 1))) :=
              mul_le_mul_of_nonneg_left hstep hWnonneg
          _ = (k + (k + 1) * r) ^ 2 - 2 * k * (k + (k + 1) * r) * (2 - c + r ^ 2 - r) := by
              rw [hW]; ring
          _ ≤ (4 / 3) * k * (k + 1) * c ^ 2 := hcore
          _ ≤ (4 / 3) * k * (k + 1) * (R ^ (2 * K - 1) * (R + r) ^ 2) :=
              mul_le_mul_of_nonneg_left hc2le (by positivity)
      · -- `2 ≤ c`
        have hPhi4 : 4 ≤ R ^ (2 * K - 1) * (R + r) ^ 2 :=
          le_trans (by nlinarith [hcge] : (4 : ℝ) ≤ c ^ 2) hc2le
        have hWsq : W ^ 2 ≤ (16 / 3) * k * (k + 1) := by
          have hWle : W ≤ k + (5 / 4) * (k + 1) := by rw [hW]; nlinarith [hr5]
          have hC := sq_upper hk3
          nlinarith [hWle, hWnonneg, hC]
        calc W * (k * (1 - 2 * |E|) + (k + 1) * r * (1 - 2 * |F|))
            ≤ W * W := mul_le_mul_of_nonneg_left hWq hWnonneg
          _ = W ^ 2 := by ring
          _ ≤ (16 / 3) * k * (k + 1) := hWsq
          _ = (4 / 3) * k * (k + 1) * 4 := by ring
          _ ≤ (4 / 3) * k * (k + 1) * (R ^ (2 * K - 1) * (R + r) ^ 2) :=
              mul_le_mul_of_nonneg_left hPhi4 (by positivity)
    · -- `1 ≤ R`
      have hsq := sq_le_one_add hk3 hr.le
      have hPhi : (1 + r) ^ 2 ≤ R ^ (2 * K - 1) * (R + r) ^ 2 := by
        have h1 : (1 : ℝ) ≤ R ^ (2 * K - 1) := one_le_pow₀ hRge
        have h2 : (1 + r) ^ 2 ≤ (R + r) ^ 2 := by nlinarith [hRge, hr]
        calc (1 + r) ^ 2 = 1 * (1 + r) ^ 2 := by ring
          _ ≤ R ^ (2 * K - 1) * (R + r) ^ 2 := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      calc W * (k * (1 - 2 * |E|) + (k + 1) * r * (1 - 2 * |F|))
          ≤ W * W := mul_le_mul_of_nonneg_left hWq hWnonneg
        _ = (k + (k + 1) * r) ^ 2 := by rw [hW]; ring
        _ ≤ (4 / 3) * k * (k + 1) * (1 + r) ^ 2 := hsq
        _ ≤ (4 / 3) * k * (k + 1) * (R ^ (2 * K - 1) * (R + r) ^ 2) :=
            mul_le_mul_of_nonneg_left hPhi (by positivity)
  exact hmain

theorem second_deriv_T2_le (n : ℕ) (hn : 1 ≤ n) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (ha1 : 3 / 8 ≤ R ^ (2 * n + 2)) (ha2 : R ^ (2 * n + 2) ≤ 15 / 8)
    (hb1 : 3 / 8 ≤ r ^ (2 * n + 2)) (hb2 : r ^ (2 * n + 2) ≤ 15 / 8)
    (hm : |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2| ≤ 1 / 2)
    (hv : |R ^ (2 * n + 1) - r ^ (2 * n + 1)| ≤ 1 / 2) :
    let k1 : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    let k2 : ℝ := ((2 * n + 2 : ℕ) : ℝ)
    let p : ℝ := 1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|
    let q : ℝ := 1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|
    (k1 + k2 * r) * (k1 * p + k2 * r * q) / (k2 * k1 * R ^ (4 * n + 1) * (R + r) ^ 2) ≤ 4 / 3 := by
  dsimp only
  have h2n : (2 * n + 1) + 1 = 2 * n + 2 := by omega
  have hKexp : 2 * (2 * n + 1) - 1 = 4 * n + 1 := by omega
  have hkcast : ((2 * n + 2 : ℕ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hkcast]
  have hden : 0 < (((2 * n + 1 : ℕ) : ℝ) + 1) * ((2 * n + 1 : ℕ) : ℝ) * R ^ (4 * n + 1) * (R + r) ^ 2 := by
    have h1 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
    positivity
  rw [div_le_iff₀ hden]
  have hkey := key (2 * n + 1) (by omega) hR hr (by rw [h2n]; exact ha1) (by rw [h2n]; exact ha2)
    (by rw [h2n]; exact hb1) (by rw [h2n]; exact hb2)
  rw [h2n] at hkey
  rw [hKexp] at hkey
  nlinarith [hkey]

end Work.OddCurve.LowSlope
