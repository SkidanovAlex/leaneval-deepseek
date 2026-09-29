import Mathlib
import Submission.Work.MainP.basic
import Submission.Work.MainP.divCeilMulGe

/-! Paper §5.1 parameter facts for `b = bpar n = clog 2 n` in the regime `2^61 ≤ b`.

With `c = ⌈4n/b⌉ = (4n + b - 1)/b`, `T = Tpar n = 2^(clog 2 c)`,
`kr = (kTpar n + D - 1)/D = ⌈kT/D⌉` and `r = rpar n = 2^kr`, `D = 1729`, this module proves all
the arithmetic conjuncts of `HvdH.MainParamsProp` that involve `T` and `r` (see `mainParams.lean`).

The key steps:

* `c` lies in `[2, 2^(b+2)]` and dominates `2^(b/2)` (from `n ≤ 2^b < 2n` and `b ≤ 2^(b/2)`);
* hence `c ≤ T` and, since `c > T/2` for a power of two `T`, `T ≤ 2c - 2`, so
  `2(4n) ≤ 2T·b` (below) and `T·b ≤ (2c-2)b ≤ 2(4n+b-1) - 2b = 8n - 2 < 8n` (above);
* `kT ≤ b + 2 < p` and `kT ≥ b/2 ≥ 2^60 ≥ 2D + 1 ≥ 1`;
* the exponent identities `kT ≤ D·kr ≤ kT + D - 1` for `kr = ⌈kT/D⌉` give
  `T ≤ r^D ≤ 2^(D-1)·T`, and `8 ≤ r`, `r ≤ T`. -/

namespace Work.MainP

/-- **The power-of-two trick.** If `c ≥ 2` and `T = 2^(Nat.clog 2 c)` is the least power of two
`≥ c`, then `c ≤ T` and `c > T/2`, i.e. `T ≤ 2c - 2`. -/
private theorem powClogLeTwoMulSub (c : ℕ) (hc : 2 ≤ c) : 2 ^ Nat.clog 2 c ≤ 2 * c - 2 := by
  have hlt : 1 < c := by omega
  have hk : 0 < Nat.clog 2 c := Nat.clog_pos (show 1 < 2 by norm_num) hlt
  have h := Nat.pow_pred_clog_lt_self (show 1 < 2 by norm_num) hlt
  have hthis : 2 ^ Nat.clog 2 c = 2 * 2 ^ (Nat.clog 2 c).pred := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hk, pow_succ]
    ring
  rw [hthis]
  omega

/-- Bounds on `c = ⌈4n/b⌉` with `b = bpar n` for `2^61 ≤ b`: `2 ≤ c`, `c ≤ 2^(b+2)` and
`2^(b/2) < c`. -/
private theorem cBounds (n : ℕ) (hb : 2 ^ 61 ≤ HvdH.bpar n) :
    2 ≤ (4 * n + HvdH.bpar n - 1) / HvdH.bpar n ∧
    (4 * n + HvdH.bpar n - 1) / HvdH.bpar n ≤ 2 ^ (HvdH.bpar n + 2) ∧
    2 ^ (HvdH.bpar n / 2) < (4 * n + HvdH.bpar n - 1) / HvdH.bpar n := by
  have hb1 : 1 ≤ HvdH.bpar n := by omega
  have hbpos : 0 < HvdH.bpar n := by omega
  have hb400 : 400 ≤ HvdH.bpar n := by omega
  have hn1 : 1 < n := one_lt_of_bpar_pos n hb1
  have hnle : n ≤ 2 ^ HvdH.bpar n := le_two_pow_bpar n
  have hpow : 2 ^ (HvdH.bpar n - 1) < n := pow_pred_lt_of_bpar n hn1
  -- `b ≤ 2^(b/2)` (from `b ≤ 2^(b/20)`)
  have hble : HvdH.bpar n ≤ 2 ^ (HvdH.bpar n / 2) := by
    have h := self_le_two_pow_div (HvdH.bpar n) hb400
    have h2 : 2 ^ (HvdH.bpar n / 20) ≤ 2 ^ (HvdH.bpar n / 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have htwob : 2 ^ (HvdH.bpar n) < 2 ^ (HvdH.bpar n + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- `2^(b+1) < 4n`
  have htwo : 2 ^ (HvdH.bpar n + 1) < 4 * n := by
    have h : 2 ^ (HvdH.bpar n - 1) * 4 = 2 ^ (HvdH.bpar n + 1) := by
      have h4 : (4:ℕ) = 2 ^ 2 := by norm_num
      rw [h4, ← pow_add]
      congr 1
      omega
    rw [← h]
    nlinarith [hpow]
  refine ⟨?_, ?_, ?_⟩
  · -- `2 ≤ c`
    rw [Nat.le_div_iff_mul_le hbpos]
    have h : HvdH.bpar n + 1 ≤ 4 * n := by
      have h1 : HvdH.bpar n + 1 ≤ 2 ^ HvdH.bpar n := by
        have := Nat.lt_two_pow_self (n := HvdH.bpar n); omega
      have h2 := Nat.one_le_two_pow (n := HvdH.bpar n)
      omega
    omega
  · -- `c ≤ 2^(b+2)`
    rw [Nat.div_le_iff_le_mul hbpos]
    have h1 : (2:ℕ) ^ (HvdH.bpar n + 2) = 4 * 2 ^ HvdH.bpar n := by
      rw [pow_add]; ring
    rw [h1]
    have h2 : 4 * n ≤ 4 * 2 ^ HvdH.bpar n := Nat.mul_le_mul_left 4 hnle
    have h3 : 4 * 2 ^ HvdH.bpar n ≤ 4 * 2 ^ HvdH.bpar n * HvdH.bpar n := by
      have hp : 1 ≤ 2 ^ HvdH.bpar n := Nat.one_le_two_pow
      nlinarith
    omega
  · -- `2^(b/2) < c`
    rw [Nat.lt_div_iff_mul_lt hbpos]
    have hsub : 4 * n + HvdH.bpar n - 1 - (HvdH.bpar n - 1) = 4 * n := by omega
    rw [hsub]
    have h1 : HvdH.bpar n * 2 ^ (HvdH.bpar n / 2) ≤ 2 ^ HvdH.bpar n := by
      have h2 : HvdH.bpar n * 2 ^ (HvdH.bpar n / 2)
          ≤ 2 ^ (HvdH.bpar n / 2) * 2 ^ (HvdH.bpar n / 2) :=
        Nat.mul_le_mul_right _ hble
      have h3 : (2:ℕ) ^ (HvdH.bpar n / 2) * 2 ^ (HvdH.bpar n / 2)
          = 2 ^ (2 * (HvdH.bpar n / 2)) := by
        rw [← pow_add]; ring
      have h4 : 2 * (HvdH.bpar n / 2) ≤ HvdH.bpar n := by omega
      rw [h3] at h2
      exact h2.trans (Nat.pow_le_pow_right (by norm_num) h4)
    have : HvdH.bpar n * 2 ^ (HvdH.bpar n / 2) < 4 * n :=
      lt_of_le_of_lt h1 (lt_trans htwob htwo)
    simpa [Nat.mul_comm] using this

/-- Facts about `Tpar n = 2^(kTpar n)` and `rpar n = 2^(krpar n)` for large `bpar n`.
`b = bpar n`, `c = (4n+b-1)/b`, `T = 2^(clog 2 c)`, `kr = (kT+d-1)/d`, `r = 2^kr`, `d = D = 1729`.
Trick for `T*b < 8n`: `clog 2 c` power of two `T` satisfies `c ≤ T` and `c > T/2`, hence
`T ≤ 2c-2`, so `T*b ≤ 2(4n+b-1)-2 < 8n`. -/
theorem TparFacts (n : ℕ) (hb : 2 ^ 61 ≤ HvdH.bpar n) :
    4 * n ≤ HvdH.Tpar n * HvdH.bpar n ∧
    HvdH.Tpar n * HvdH.bpar n < 8 * n ∧
    HvdH.Tpar n < 2 ^ (HvdH.bpar n + 3) ∧
    HvdH.rpar n ^ HvdH.D ≤ 2 ^ (HvdH.D - 1) * HvdH.Tpar n ∧
    HvdH.Tpar n ≤ HvdH.rpar n ^ HvdH.D ∧
    HvdH.kTpar n ≤ HvdH.bpar n + 2 ∧
    HvdH.rpar n ≤ HvdH.Tpar n ∧
    HvdH.kTpar n < HvdH.ppar n ∧
    HvdH.rpar n ^ HvdH.D ≤ 2 ^ (HvdH.D + 2) * n ∧
    1 ≤ HvdH.kTpar n ∧ 8 ≤ HvdH.rpar n := by
  obtain ⟨hc2, hcpow, hcbig⟩ := cBounds n hb
  have hb1 : 1 ≤ HvdH.bpar n := by omega
  have hbpos : 0 < HvdH.bpar n := by omega
  -- `c ≤ T` and `T ≤ 2c - 2`
  have hcleT : (4 * n + HvdH.bpar n - 1) / HvdH.bpar n ≤ HvdH.Tpar n := by
    have h := Nat.le_pow_clog (show 1 < 2 by norm_num) ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n)
    simpa [HvdH.Tpar, HvdH.kTpar] using h
  have hTle2c : HvdH.Tpar n ≤ 2 * ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) - 2 := by
    have h := powClogLeTwoMulSub ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) hc2
    simpa [HvdH.Tpar, HvdH.kTpar] using h
  have hcb : (4 * n + HvdH.bpar n - 1) / HvdH.bpar n * HvdH.bpar n ≤ 4 * n + HvdH.bpar n - 1 :=
    Nat.div_mul_le_self _ _
  -- 1. `4n ≤ T·b`
  have t1 : 4 * n ≤ HvdH.Tpar n * HvdH.bpar n := by
    calc 4 * n ≤ (4 * n + HvdH.bpar n - 1) / HvdH.bpar n * HvdH.bpar n :=
          divCeilMulGe _ _ hbpos
      _ ≤ HvdH.Tpar n * HvdH.bpar n := Nat.mul_le_mul_right _ hcleT
  -- 2. `T·b < 8n`
  have t2 : HvdH.Tpar n * HvdH.bpar n < 8 * n := by
    have h1 : HvdH.Tpar n + 2 ≤ 2 * ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) := by omega
    have h2 : (HvdH.Tpar n + 2) * HvdH.bpar n
        ≤ (2 * ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n)) * HvdH.bpar n :=
      Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul] at h2
    have h4 : (2 * ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n)) * HvdH.bpar n
        = 2 * (((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) * HvdH.bpar n) := by ring
    rw [h4] at h2
    have h5 : 2 * (((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) * HvdH.bpar n)
        ≤ 2 * (4 * n + HvdH.bpar n - 1) := Nat.mul_le_mul_left 2 hcb
    have h6 : 2 * (4 * n + HvdH.bpar n - 1) = 8 * n + 2 * HvdH.bpar n - 2 := by omega
    omega
  -- 6. `kT ≤ b + 2`
  have hkTle : HvdH.kTpar n ≤ HvdH.bpar n + 2 := by
    rw [HvdH.kTpar, Nat.clog_le_iff_le_pow (show 1 < 2 by norm_num)]
    exact hcpow
  -- 10. `1 ≤ kT`
  have hkT1 : 1 ≤ HvdH.kTpar n := by
    rw [HvdH.kTpar]
    exact Nat.clog_pos (show 1 < 2 by norm_num) (by omega)
  -- 3. `T < 2^(b+3)`
  have t3 : HvdH.Tpar n < 2 ^ (HvdH.bpar n + 3) := by
    have h1 : HvdH.Tpar n ≤ 2 ^ (HvdH.bpar n + 2) := Nat.pow_le_pow_right (by norm_num) hkTle
    have h2 : (2:ℕ) ^ (HvdH.bpar n + 2) < 2 ^ (HvdH.bpar n + 3) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact lt_of_le_of_lt h1 h2
  have hDpos : 0 < HvdH.D := by norm_num [HvdH.D]
  -- `⌈kT/D⌉ ≤ kT`
  have hkr_le : (HvdH.kTpar n + HvdH.D - 1) / HvdH.D ≤ HvdH.kTpar n := by
    have hD : HvdH.D = 1729 := rfl
    rw [hD, Nat.div_le_iff_le_mul (by norm_num : 0 < 1729)]
    omega
  -- 7. `r ≤ T`
  have t7 : HvdH.rpar n ≤ HvdH.Tpar n := by
    have h1 : (2:ℕ) ^ ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) ≤ 2 ^ HvdH.kTpar n :=
      Nat.pow_le_pow_right (by norm_num) hkr_le
    simpa [HvdH.rpar, HvdH.Tpar] using h1
  -- `⌈kT/D⌉·D ≤ kT + D - 1`
  have hkrD : ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) * HvdH.D ≤ HvdH.kTpar n + HvdH.D - 1 := by
    simpa [Nat.mul_comm] using
      Nat.div_mul_le_self (HvdH.kTpar n + HvdH.D - 1) HvdH.D
  -- 4. `r^D ≤ 2^(D-1)·T`
  have t4 : HvdH.rpar n ^ HvdH.D ≤ 2 ^ (HvdH.D - 1) * HvdH.Tpar n := by
    have h1 : HvdH.rpar n ^ HvdH.D = 2 ^ (((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) * HvdH.D) := by
      rw [HvdH.rpar, ← pow_mul]
    rw [h1]
    have h2 : (2:ℕ) ^ (((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) * HvdH.D)
        ≤ 2 ^ (HvdH.kTpar n + HvdH.D - 1) := Nat.pow_le_pow_right (by norm_num) hkrD
    have h3 : (2:ℕ) ^ (HvdH.kTpar n + HvdH.D - 1) = 2 ^ (HvdH.D - 1) * HvdH.Tpar n := by
      have he : HvdH.kTpar n + HvdH.D - 1 = (HvdH.D - 1) + HvdH.kTpar n := by omega
      rw [he, pow_add, HvdH.Tpar]
    exact h2.trans (le_of_eq h3)
  -- 5. `T ≤ r^D`
  have hkrD2 : HvdH.kTpar n ≤ ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) * HvdH.D :=
    divCeilMulGe _ _ hDpos
  have t5 : HvdH.Tpar n ≤ HvdH.rpar n ^ HvdH.D := by
    have h2 : (2:ℕ) ^ HvdH.kTpar n ≤ 2 ^ (((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) * HvdH.D) :=
      Nat.pow_le_pow_right (by norm_num) hkrD2
    have h3 : (2:ℕ) ^ (((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) * HvdH.D) = HvdH.rpar n ^ HvdH.D := by
      rw [HvdH.rpar, pow_mul]
    calc HvdH.Tpar n = 2 ^ HvdH.kTpar n := rfl
      _ ≤ _ := h2
      _ = HvdH.rpar n ^ HvdH.D := h3
  -- 8. `kT < p = 6b`
  have t8 : HvdH.kTpar n < HvdH.ppar n := by
    show HvdH.kTpar n < 6 * HvdH.bpar n
    omega
  -- `T ≤ 8n`
  have hTle8n : HvdH.Tpar n ≤ 8 * n := by
    calc HvdH.Tpar n = HvdH.Tpar n * 1 := (Nat.mul_one _).symm
      _ ≤ HvdH.Tpar n * HvdH.bpar n := Nat.mul_le_mul_left _ hb1
      _ ≤ 8 * n := le_of_lt t2
  -- 9. `r^D ≤ 2^(D+2)·n`
  have t9 : HvdH.rpar n ^ HvdH.D ≤ 2 ^ (HvdH.D + 2) * n := by
    have h2 : 2 ^ (HvdH.D - 1) * HvdH.Tpar n ≤ 2 ^ (HvdH.D - 1) * (8 * n) :=
      Nat.mul_le_mul_left _ hTle8n
    have h3 : (2:ℕ) ^ (HvdH.D - 1) * (8 * n) = 2 ^ (HvdH.D + 2) * n := by
      have h4 : (2:ℕ) ^ (HvdH.D - 1) * 8 = 2 ^ (HvdH.D + 2) := by
        rw [show HvdH.D + 2 = (HvdH.D - 1) + 3 by omega, pow_add]
        norm_num
      rw [← Nat.mul_assoc, h4]
    exact t4.trans (h2.trans (le_of_eq h3))
  -- `b/2 < kT`
  have hbhalf : HvdH.bpar n / 2 < HvdH.kTpar n := by
    have h1 : (2:ℕ) ^ (HvdH.bpar n / 2) < 2 ^ HvdH.kTpar n := lt_of_lt_of_le hcbig hcleT
    exact (Nat.pow_lt_pow_iff_right (show 1 < 2 by norm_num)).mp h1
  -- 11. `8 ≤ r`
  have t11 : 8 ≤ HvdH.rpar n := by
    have h1 : 2 * HvdH.D + 1 ≤ HvdH.kTpar n := by
      have h2 : 2 ^ 60 ≤ HvdH.bpar n / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        calc (2:ℕ) ^ 60 * 2 = 2 ^ 61 := by rw [← pow_succ]
          _ ≤ HvdH.bpar n := hb
      have h3 : 2 * HvdH.D + 1 ≤ 2 ^ 60 := by
        have hD : HvdH.D = 1729 := rfl
        rw [hD]; norm_num
      omega
    have hkr3 : 3 ≤ (HvdH.kTpar n + HvdH.D - 1) / HvdH.D := by
      rw [Nat.le_div_iff_mul_le hDpos]
      omega
    calc (8:ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) := Nat.pow_le_pow_right (by norm_num) hkr3
      _ = HvdH.rpar n := rfl
  exact ⟨t1, t2, t3, t4, t5, hkTle, t7, t8, t9, hkT1, t11⟩

end Work.MainP
