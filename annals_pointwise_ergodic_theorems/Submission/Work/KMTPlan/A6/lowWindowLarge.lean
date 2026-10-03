import Mathlib
import Submission.Work.KMTAreas.A7.goodRegime
import Submission.Work.KMTPlan.A6.le_two_rpow_self_of_ceil
import Submission.Work.KMTPlan.A6.lowSmallWindowConds

/-!
# The large-scale window condition of the low case of area A6

This module proves `Work.KMTPlan.A6.lowWindowLarge`: for `0 < ρ`, `8ρ ≤ 1`, `1 ≤ C₀` with
`ρC₀ ≤ 1/8` and any `Bw`, there is a threshold `Bc` such that every pair `(L,N)` with
`Bc ≤ L ≤ l_{(N)} = C₀ LogLog N` satisfies

  `Bw ≤ N`  and  `L + 3 · uScale ρ L ≤ Log N`,

where `uScale ρ L = ⌊2^{2ρL}⌋` (`Work.KMTAreas.A7.uScale`) and `Log N = ⌊log₂ N⌋`
(`Work.Analysis.EndVar.logN`).

The point is that the hypothesis `L ≤ C₀ LogLog N` forces `N` to be enormous as a function of `L`,
while `L` itself is bounded by the doubly-logarithmic scale and `uScale ρ L = ⌊2^{2ρL}⌋` is
controlled by the *quadruply* logarithmic estimate `2ρL ≤ LogLog N/4`, i.e.
`uScale ρ L ≤ 2^{LogLog N/4} ≤ 2^{(1/4) log₂ (Log N + 2)}`.

Concretely, writing `q = LogLog N` and `n = Log N`, so that `2^q ≤ n + 2`, and taking
`Q = max 8 (max C₀ (log₂ Bw + 3))`, `Bc = max 1 (C₀ * Q)`: from `Bc ≤ L ≤ C₀ q` we get `q ≥ Q`,
hence `n ≥ 2^Q - 2 ≥ log₂ Bw + 1`, hence `N ≥ 2^n ≥ 2^{2^Q-2} ≥ Bw`; and
`L ≤ C₀ q ≤ q²` and `u = uScale ρ L ≤ 2^{q/2}` (by `uScaleHalfPow`) give

  `L + 3u ≤ q² + 3·2^{q/2} ≤ 2^{q-1} - 2 + 3·2^{q}/8 = 7·2^q/8 - 2 ≤ 2^q - 2 ≤ n`,

using `q ≥ 8` (`mainRegimeArithThree`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open Work.Analysis.EndVar

/-! ## Elementary exponential-vs-quadratic arithmetic -/

/-- Linear beats exponential: `2q + 1 ≤ 2^{q-1}` for `q ≥ 8`. -/
private lemma two_mul_add_one_le_two_pow (q : ℕ) (hq : 8 ≤ q) : 2 * q + 1 ≤ 2 ^ (q - 1) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    rw [Nat.add_sub_cancel]
    calc 2 * (q + 1) + 1 ≤ 2 * (2 * q + 1) := by omega
      _ ≤ 2 * 2 ^ (q - 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ q := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]

/-- Quadratic beats exponential: `q^2 + 2 ≤ 2^{q-1}` for `q ≥ 8`. -/
private lemma sq_add_two_le_two_pow (q : ℕ) (hq : 8 ≤ q) : q ^ 2 + 2 ≤ 2 ^ (q - 1) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    rw [Nat.add_sub_cancel]
    have hA : 2 * q + 1 ≤ 2 ^ (q - 1) := two_mul_add_one_le_two_pow q hq
    have key : (q + 1) ^ 2 + 2 = (q ^ 2 + 2) + (2 * q + 1) := by ring
    rw [key]
    calc (q ^ 2 + 2) + (2 * q + 1) ≤ 2 ^ (q - 1) + 2 ^ (q - 1) := Nat.add_le_add ih hA
      _ = 2 ^ q := by rw [← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]

/-- **The main-regime arithmetic with a coefficient `3`.**  For `q ≥ 8`, `C₀ ≤ q`, `k ≤ C₀ q` and
`y ≤ 2^{q/2}`, one has `k + 3y ≤ 2^q - 2`.  (The version with coefficient `2` is
`Work.KMTPlan.A6.mainRegimeArith`.)  The room for the extra `y` comes from `k ≤ q² ≤ 2^q/4 - 1`
and `3y ≤ 3·2^{q-3} = 3·2^q/8`, whose sum `5·2^q/8 - 1` is still below `2^q - 2`. -/
private lemma mainRegimeArithThree (C₀ q k : ℕ) (y : ℝ) (hCq : C₀ ≤ q) (hq : 8 ≤ q)
    (hk : k ≤ C₀ * q) (hy : y ≤ (2 : ℝ) ^ ((q : ℝ) / 2)) :
    (k : ℝ) + 3 * y ≤ (2 : ℝ) ^ q - 2 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  set x : ℝ := (2 : ℝ) ^ q with hxdef
  -- `k ≤ q * q = q^2`
  have hkq : k ≤ q * q := le_trans hk (Nat.mul_le_mul_right q hCq)
  have hkR : (k : ℝ) ≤ (q : ℝ) ^ 2 := by
    have h : (k : ℝ) ≤ ((q * q : ℕ) : ℝ) := by exact_mod_cast hkq
    push_cast at h
    linarith
  -- `2^{q/2} ≤ 2^{q-3} = 2^q / 8`
  have hq3 : (q : ℝ) / 2 ≤ (q : ℝ) - 3 := by
    have : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hpow8 : (2 : ℝ) ^ ((q : ℝ) / 2) ≤ x / 8 := by
    have hmono : (2 : ℝ) ^ ((q : ℝ) / 2) ≤ (2 : ℝ) ^ ((q : ℝ) - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hq3
    have hsub : (2 : ℝ) ^ ((q : ℝ) - 3) = x / 8 := by
      rw [Real.rpow_sub h2pos, Real.rpow_natCast]
      rw [hxdef]
      norm_num
    linarith
  have hy3 : 3 * y ≤ 3 * x / 8 := by
    have h := mul_le_mul_of_nonneg_left (le_trans hy hpow8) (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  -- `q^2 + 2 ≤ 2^{q-1} = 2^q / 2`
  have hquad : (q : ℝ) ^ 2 + 2 ≤ x / 2 := by
    have h1 : q ^ 2 + 2 ≤ 2 ^ (q - 1) := sq_add_two_le_two_pow q hq
    have h2 : ((q ^ 2 + 2 : ℕ) : ℝ) ≤ ((2 ^ (q - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have hmul : 2 * (2 : ℝ) ^ (q - 1) = x := by
      rw [hxdef, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]
    have h3 : (2 : ℝ) ^ (q - 1) = x / 2 := by linarith
    linarith
  have hxnn : 0 ≤ x := by rw [hxdef]; positivity
  linarith

/-! ## The large-scale window condition -/

theorem lowWindowLarge (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : 8 * ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8) (Bw : ℕ) :
    ∃ Bc : ℕ, 1 ≤ Bc ∧ ∀ (L N : ℕ), Bc ≤ L → L ≤ Work.Analysis.EndVar.heightScale C₀ N →
      Bw ≤ N ∧ L + 3 * Work.KMTAreas.A7.uScale ρ L ≤ (Work.Analysis.EndVar.logN N).toNat := by
  set Q : ℕ := max 8 (max C₀ (Nat.log 2 Bw + 3)) with hQ
  refine ⟨max 1 (C₀ * Q), le_max_left _ _, ?_⟩
  intro L N hBc hLle
  have hC₀pos : 0 < C₀ := by omega
  set q : ℕ := Work.Analysis.EndVar.logLogN N with hqdef
  set n : ℕ := Nat.log 2 (max N 2) with hndef
  have hheight : Work.Analysis.EndVar.heightScale C₀ N = C₀ * q := by
    rw [Work.Analysis.EndVar.heightScale, hqdef]
  have hLq : L ≤ C₀ * q := by rw [hheight] at hLle; exact hLle
  have hCQle : C₀ * Q ≤ L := le_trans (le_max_right _ _) hBc
  have hQle : Q ≤ q := Nat.le_of_mul_le_mul_left (le_trans hCQle hLq) hC₀pos
  have hQ8 : 8 ≤ Q := le_max_left _ _
  have hCQ : C₀ ≤ Q := le_trans (le_max_left _ _) (le_max_right _ _)
  have hQlog : Nat.log 2 Bw + 3 ≤ Q := le_trans (le_max_right _ _) (le_max_right _ _)
  have hq8 : 8 ≤ q := le_trans hQ8 hQle
  have hCq : C₀ ≤ q := le_trans hCQ hQle
  -- `LogLog N = log₂ (Log N + 2)`, hence `2^q ≤ n + 2`
  have hq_eq : q = Nat.log 2 (n + 2) := by rw [hqdef, hndef]; rfl
  have hpow : 2 ^ q ≤ n + 2 := by
    rw [hq_eq]
    exact Nat.pow_log_le_self 2 (by omega)
  have h2Qle : 2 ^ Q ≤ 2 ^ q := Nat.pow_le_pow_right (n := 2) (by norm_num) hQle
  have hn2Q : 2 ^ Q - 2 ≤ n := by omega
  -- `n ≥ 2` and `N = max N 2`
  have hn2 : 2 ≤ n := by
    have h256 : 256 ≤ 2 ^ Q := by
      have h := Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) hQ8
      norm_num at h
      exact h
    omega
  have hn1 : 2 ^ n ≤ max N 2 := by
    rw [hndef]
    exact Nat.pow_log_le_self 2 (by omega)
  have hge2 : 2 ≤ N := by
    by_contra h
    have hN2 : max N 2 = 2 := Nat.max_eq_right (by omega : N ≤ 2)
    rw [hN2] at hn1
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) hn2
    norm_num at h4
    omega
  have hmaxN : max N 2 = N := Nat.max_eq_left hge2
  -- `Bw ≤ 2^{2^Q - 2} ≤ N`
  have hQpow : Nat.log 2 Bw + 1 ≤ 2 ^ Q - 2 := by
    have h1 : Nat.log 2 Bw + 3 ≤ 2 ^ Q := by
      have h2 := Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) hQlog
      have h3 : Nat.log 2 Bw + 3 < 2 ^ (Nat.log 2 Bw + 3) := Nat.lt_two_pow_self
      omega
    omega
  have hBwpow : Bw ≤ 2 ^ (2 ^ Q - 2) := by
    have h4 : Bw < 2 ^ (Nat.log 2 Bw + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) Bw
    have h5 : 2 ^ (Nat.log 2 Bw + 1) ≤ 2 ^ (2 ^ Q - 2) :=
      Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) hQpow
    exact le_trans (le_of_lt h4) h5
  have hNge : Bw ≤ N := by
    have h6 : 2 ^ (2 ^ Q - 2) ≤ 2 ^ n :=
      Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) hn2Q
    calc Bw ≤ 2 ^ (2 ^ Q - 2) := hBwpow
      _ ≤ 2 ^ n := h6
      _ ≤ max N 2 := hn1
      _ = N := hmaxN
  -- the scale inequality `L + 3 · uScale ρ L ≤ Log N`
  have hρC : ρ * (C₀ : ℝ) ≤ 1 / 4 := by linarith
  have hy : (Work.KMTAreas.A7.uScale ρ L : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) / 2) :=
    uScaleHalfPow ρ hρ C₀ q L L hρC le_rfl hLq
  have hmain : (L : ℝ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ) ≤ (2 : ℝ) ^ q - 2 :=
    mainRegimeArithThree C₀ q L _ hCq hq8 hLq hy
  have hscale : L + 3 * Work.KMTAreas.A7.uScale ρ L ≤ n := by
    have h2le : (2 : ℝ) ^ q - 2 ≤ (n : ℝ) := by
      have h3 : ((2 ^ q : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hpow
      push_cast at h3
      linarith
    have hreal : ((L + 3 * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hreal
  refine ⟨hNge, ?_⟩
  have hlog : (Work.Analysis.EndVar.logN N).toNat = n := by
    simp only [Work.Analysis.EndVar.logN, Int.toNat_natCast, hndef]
  rw [hlog]
  exact hscale

end Work.KMTPlan.A6
