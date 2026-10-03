import Mathlib
import Submission.Work.Peluse.UControl.petInitDefs

/-!
# The window bookkeeping of the PET chapter

See `NOTES_petChapter5_session16.md` §1ter.  The PET chain is run at its **maximal admissible
window** `petWindow γ D n`, and the conclusion's box (radius `⌊δ'M⌋`) is reached from the chain's
box (radius `⌊petWindow · M⌋`) by the box-average comparison.  The estimates needed are collected
here.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

/-- The closed form of the chain level: `petChainLevel γ k = γ^{2^k} / 2000^{2^k - 1}`. -/
lemma petChainLevel_eq (γ : ℝ) (k : ℕ) :
    petChainLevel γ k = γ ^ (2 ^ k) / 2000 ^ (2 ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [petChainLevel_succ, ih, div_pow, ← pow_mul, ← pow_mul, div_div]
    have hnum : 2 ^ k * 2 = 2 ^ (k + 1) := by rw [pow_succ]
    have hden : (2 ^ k - 1) * 2 + 1 = 2 ^ (k + 1) - 1 := by
      have := Nat.one_le_two_pow (n := k); omega
    rw [← pow_succ 2000 ((2 ^ k - 1) * 2), hden, hnum]

/-- The square of the chain level at `n - 1`, in closed form (`n ≥ 1`). -/
lemma petChainLevel_sq_pred (γ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    petChainLevel γ (n - 1) ^ 2 = γ ^ (2 ^ n) / 2000 ^ (2 ^ n - 2) := by
  rw [petChainLevel_eq, div_pow, ← pow_mul, ← pow_mul]
  have h1 : 2 ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ]; congr 1; omega
  have h2 : (2 ^ (n - 1) - 1) * 2 = 2 ^ n - 2 := by
    have := Nat.one_le_two_pow (n := n - 1); omega
  rw [h1, h2]

/-- **The window is not small.**  For `0 < γ ≤ 1`, `1 ≤ n`, `1 ≤ D`,

  `γ^{2^n+1} / (2000^{2^n} · 20000 · 2^n · D) ≤ petWindow γ D n`. -/
lemma petWindow_lower (γ : ℝ) (D n : ℕ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hn : 1 ≤ n)
    (hD : 1 ≤ D) :
    γ ^ (2 ^ n + 1) / (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ))
      ≤ petWindow γ D n := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2000 : (0 : ℝ) < 2000 := by norm_num
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos h2pos n
  have hpow2m : (0 : ℝ) < (2 : ℝ) ^ (n - 1) := pow_pos h2pos (n - 1)
  -- the factorial step
  have hfac : (2000 : ℝ) ^ (2 ^ n) = (2000 : ℝ) ^ (2 ^ n - 2) * (2000 : ℝ) ^ 2 := by
    have h2 : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    conv_lhs => rw [show 2 ^ n = (2 ^ n - 2) + 2 by omega]
    rw [pow_add]
  -- the core inequality
  have hle : (((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1 ≤ (2 : ℝ) ^ n * (D : ℝ) := by
    have hcast2 : (((2 ^ (n - 1) * D : ℕ) : ℝ)) = (2 : ℝ) ^ (n - 1) * (D : ℝ) := by
      push_cast; ring
    rw [hcast2]
    have h2n : (2 : ℝ) ^ (n - 1) * 2 = (2 : ℝ) ^ n := by
      rw [← pow_succ]; congr 1; omega
    have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (n - 1) * (D : ℝ) := by
      have h2n1 : (1 : ℝ) ≤ (2 : ℝ) ^ (n - 1) := one_le_pow₀ (n := n - 1) (by norm_num : (1:ℝ) ≤ 2)
      nlinarith [h2n1, hD1]
    nlinarith [h2n, hge1]
  have hkey : γ * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1)
      ≤ 2000 ^ 2 * ((2 : ℝ) ^ n * (D : ℝ)) := by
    have hnonneg : (0 : ℝ) ≤ (((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1 := by positivity
    have h1 : γ * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1)
        ≤ 1 * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1) :=
      mul_le_mul_of_nonneg_right hγ1 hnonneg
    have h2 : (1 : ℝ) ≤ 2000 ^ 2 := by norm_num
    have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ n * (D : ℝ) := by
      have h2n1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (n := n) (by norm_num : (1:ℝ) ≤ 2)
      nlinarith [h2n1, hD1]
    nlinarith [h1, hle, h2, h3]
  have hden1 : (0 : ℝ) < 2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ) := by positivity
  have hden2 : (0 : ℝ) < 2000 ^ (2 ^ n - 2)
      * (20000 * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1)) := by positivity
  have hmain : γ ^ (2 ^ n + 1) / (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ))
      ≤ γ ^ (2 ^ n) / (2000 ^ (2 ^ n - 2)
          * (20000 * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1))) := by
    rw [div_le_div_iff₀ hden1 hden2]
    have hb : (0 : ℝ) < 2000 ^ (2 ^ n - 2) := pow_pos h2000 _
    have hC : (0 : ℝ) ≤ γ ^ (2 ^ n) * (2000 ^ (2 ^ n - 2)) * 20000 := by
      have h1 : (0 : ℝ) ≤ γ ^ (2 ^ n) := pow_nonneg hγ0.le _
      have h2 : (0 : ℝ) ≤ γ ^ (2 ^ n) * (2000 ^ (2 ^ n - 2)) := mul_nonneg h1 hb.le
      exact mul_nonneg h2 (by norm_num)
    have h1 : γ ^ (2 ^ n) * (2000 ^ (2 ^ n - 2)) * 20000
          * (γ * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1))
        ≤ γ ^ (2 ^ n) * (2000 ^ (2 ^ n - 2)) * 20000
          * (2000 ^ 2 * ((2 : ℝ) ^ n * (D : ℝ))) :=
      mul_le_mul_of_nonneg_left hkey hC
    have hL : γ ^ (2 ^ n + 1)
          * (2000 ^ (2 ^ n - 2) * (20000 * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1)))
        = γ ^ (2 ^ n) * (2000 ^ (2 ^ n - 2)) * 20000
          * (γ * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1)) := by
      rw [pow_succ]; ring
    have hR : γ ^ (2 ^ n) * (2000 ^ (2 ^ n - 2)) * 20000
          * (2000 ^ 2 * ((2 : ℝ) ^ n * (D : ℝ)))
        = γ ^ (2 ^ n) * (2000 ^ (2 ^ n) * 20000 * ((2 : ℝ) ^ n * (D : ℝ))) := by
      have hfac' : (2000 : ℝ) ^ (2 ^ n - 2) * (2000 : ℝ) ^ 2 = (2000 : ℝ) ^ (2 ^ n) :=
        hfac.symm
      linear_combination (γ ^ (2 ^ n) * 20000 * ((2 : ℝ) ^ n * (D : ℝ))) * hfac'
    linarith [h1, hL, hR]
  have hX : γ ^ (2 ^ n + 1) / (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ))
      ≤ petChainLevel γ (n - 1) ^ 2
          / (20000 * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1)) := by
    rw [petChainLevel_sq_pred γ n hn, div_div]
    exact hmain
  have hT1 : γ ^ (2 ^ n + 1) / (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ)) ≤ 1 := by
    rw [div_le_one hden1]
    have hden1' : (1 : ℝ) ≤ 2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ) := by
      have h2000p : (1 : ℝ) ≤ 2000 ^ (2 ^ n) := one_le_pow₀ (n := 2 ^ n) (by norm_num : (1:ℝ) ≤ 2000)
      have h2n1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (n := n) (by norm_num : (1:ℝ) ≤ 2)
      nlinarith [h2000p, h2n1, hD1]
    calc γ ^ (2 ^ n + 1) ≤ 1 := pow_le_one₀ hγ0.le hγ1
      _ ≤ _ := hden1'
  calc γ ^ (2 ^ n + 1) / (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ))
      ≤ min 1 (petChainLevel γ (n - 1) ^ 2
          / (20000 * ((((2 ^ (n - 1) * D : ℕ) : ℝ)) + 1))) := le_min hT1 hX
    _ = petWindow γ D n := rfl

/-- The constant of the window bookkeeping: `petWinConst n W := 2000^{2^n} · 20000 · 2^n · 2 · W`
(the `2W` is the shift-bound factor: `D ≤ 2 W A / γ`). -/
abbrev petWinConst (n : ℕ) (W : ℝ) : ℝ := 2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * 2 * W

lemma petWinConst_pos (n : ℕ) {W : ℝ} (hW : 0 < W) : 0 < petWinConst n W := by
  rw [petWinConst]; positivity

/-- **The chain's window dominates the datum's.**  If the shift constant satisfies
`D ≤ 2 W A / γ` (with `W ≥ 1`) and the datum's window satisfies `δ' ≤ γ^K/A` with `K ≥ 2^n + 2`,
then `δ' / petWinConst n W ≤ petWindow γ D n`. -/
lemma petWindow_ratio_le (γ : ℝ) (D n : ℕ) (A W δ' : ℝ) (K : ℕ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hA : 1 ≤ A) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (hW : 1 ≤ W) (hDle : (D : ℝ) ≤ 2 * W * A / γ)
    (hδ' : 0 < δ') (hδle : δ' ≤ γ ^ K / A) (hK : 2 ^ n + 2 ≤ K) :
    δ' / petWinConst n W ≤ petWindow γ D n := by
  have hApos : (0 : ℝ) < A := by linarith
  have hWpos : (0 : ℝ) < W := by linarith
  have hCpos : (0 : ℝ) < petWinConst n W := petWinConst_pos n hWpos
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hlow : γ ^ (2 ^ n + 2) / (A * petWinConst n W) ≤ petWindow γ D n := by
    have hbase : γ ^ (2 ^ n + 1)
          / (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ)) ≤ petWindow γ D n :=
      petWindow_lower γ D n hγ0 hγ1 hn hD
    have hD' : (D : ℝ) * γ ≤ 2 * W * A := by
      have h2 : (D : ℝ) * γ ≤ (2 * W * A / γ) * γ := by
        exact mul_le_mul_of_nonneg_right hDle hγ0.le
      have hγne : γ ≠ 0 := ne_of_gt hγ0
      calc (D : ℝ) * γ ≤ (2 * W * A / γ) * γ := h2
        _ = 2 * W * A := by field_simp
    have hstep : γ ^ (2 ^ n + 2) / (A * petWinConst n W)
        ≤ γ ^ (2 ^ n + 1) / (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ)) := by
      have hden2 : (0 : ℝ) < 2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ) := by positivity
      have hden1 : (0 : ℝ) < A * petWinConst n W := by positivity
      rw [div_le_div_iff₀ hden1 hden2]
      have hp : γ ^ (2 ^ n + 2) = γ ^ (2 ^ n + 1) * γ := by
        rw [show 2 ^ n + 2 = (2 ^ n + 1) + 1 by omega, pow_succ]
      have hEq1 : γ ^ (2 ^ n + 2) * (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ))
          = γ ^ (2 ^ n + 1) * (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * ((D : ℝ) * γ)) := by
        rw [hp]; ring
      have hmono : 2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * ((D : ℝ) * γ)
          ≤ 2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (2 * W * A) :=
        mul_le_mul_of_nonneg_left hD' (by positivity)
      have hEq2 : A * petWinConst n W
          = 2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (2 * W * A) := by
        rw [petWinConst]; ring
      rw [hEq1, hEq2]
      have hγnn : (0 : ℝ) ≤ γ ^ (2 ^ n + 1) := pow_nonneg hγ0.le _
      exact mul_le_mul_of_nonneg_left hmono hγnn
    exact le_trans hstep hbase
  have hKle : γ ^ K ≤ γ ^ (2 ^ n + 2) := pow_le_pow_of_le_one hγ0.le hγ1 hK
  have hstep2 : δ' / petWinConst n W ≤ γ ^ (2 ^ n + 2) / (A * petWinConst n W) := by
    rw [div_le_div_iff₀ hCpos (by positivity)]
    have h1 : δ' * A ≤ γ ^ K := by
      rw [le_div_iff₀ hApos] at hδle; linarith
    nlinarith [h1, hKle, hCpos.le, hApos.le]
  exact le_trans hstep2 hlow

/-- **The corner bound.**  If the chain's window is too small to be nonempty (`petWindow · M < 1`)
then the datum's window forces the conclusion's box radius to be bounded. -/
lemma hist_le_of_small_window (γ : ℝ) (D n : ℕ) (A δ' M : ℝ) (W : ℝ) (K : ℕ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hA : 1 ≤ A) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (hW : 1 ≤ W) (hDle : (D : ℝ) ≤ 2 * W * A / γ)
    (hδ' : 0 < δ') (hδle : δ' ≤ γ ^ K / A) (hK : 2 ^ n + 2 ≤ K)
    (hM : 0 ≤ M) (hsmall : petWindow γ D n * M < 1) :
    δ' * M ≤ petWinConst n W := by
  have hApos : (0 : ℝ) < A := by linarith
  have hWpos : (0 : ℝ) < W := by linarith
  have hCpos : (0 : ℝ) < petWinConst n W := petWinConst_pos n hWpos
  have hpwpos : 0 < petWindow γ D n := by
    have hbase := petWindow_lower γ D n hγ0 hγ1 hn hD
    have h2 : (0 : ℝ) < γ ^ (2 ^ n + 1)
        / (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ)) := by positivity
    linarith
  have hMinv : M < 1 / petWindow γ D n := by
    rw [lt_div_iff₀ hpwpos]; linarith [hsmall]
  have hratio : δ' / petWinConst n W ≤ petWindow γ D n :=
    petWindow_ratio_le γ D n A W δ' K hγ0 hγ1 hA hn hD hW hDle hδ' hδle hK
  have hKM : δ' * M ≤ petWinConst n W := by
    have h1 : δ' * M ≤ δ' * (1 / petWindow γ D n) :=
      (mul_lt_mul_of_pos_left hMinv hδ').le
    have h2 : δ' * (1 / petWindow γ D n) ≤ petWinConst n W := by
      have hEq : δ' * (1 / petWindow γ D n) = δ' / petWindow γ D n := by ring
      rw [hEq, div_le_iff₀ hpwpos]
      have h3 := hratio
      rw [div_le_iff₀ hCpos] at h3
      linarith [h3]
    linarith [h1, h2]
  linarith [hKM]

/-- **The two-box comparison factor.** -/
lemma box_ratio_le (C pw dM : ℝ) (Hc Hδ : ℕ) (hC : 1 ≤ C) (hDδ : (Hδ : ℝ) ≤ dM)
    (hHc : pw - 1 ≤ (Hc : ℝ)) (h2 : 2 ≤ pw) (h1 : 1 ≤ dM)
    (hratio : 1 / C ≤ pw / dM) :
    1 / (3 * C) ≤ (2 * (Hc : ℝ) + 1) / (2 * (Hδ : ℝ) + 1) := by
  have hCpos : (0 : ℝ) < C := by linarith
  have hdMpos : (0 : ℝ) < dM := by linarith
  have hHcnn : (0 : ℝ) ≤ (Hc : ℝ) := Nat.cast_nonneg _
  have hHδnn : (0 : ℝ) ≤ (Hδ : ℝ) := Nat.cast_nonneg _
  have hnum : pw ≤ 2 * (Hc : ℝ) + 1 := by linarith
  have hden : 2 * (Hδ : ℝ) + 1 ≤ 3 * dM := by linarith
  have hdenpos : (0 : ℝ) < 2 * (Hδ : ℝ) + 1 := by linarith
  have hnumpos : (0 : ℝ) < 2 * (Hc : ℝ) + 1 := by linarith
  have hstep : pw / (3 * dM) ≤ (2 * (Hc : ℝ) + 1) / (2 * (Hδ : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) hdenpos]
    have hle1 : pw * (2 * (Hδ : ℝ) + 1) ≤ (2 * (Hc : ℝ) + 1) * (2 * (Hδ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hnum hdenpos.le
    have hle2 : (2 * (Hc : ℝ) + 1) * (2 * (Hδ : ℝ) + 1) ≤ (2 * (Hc : ℝ) + 1) * (3 * dM) :=
      mul_le_mul_of_nonneg_left hden hnumpos.le
    linarith [hle1, hle2]
  have hratio' : 1 / (3 * C) ≤ pw / (3 * dM) := by
    have hEq1 : (1 : ℝ) / (3 * C) = (1 / C) / 3 := by ring
    have hEq2 : pw / (3 * dM) = (pw / dM) / 3 := by ring
    rw [hEq1, hEq2]
    exact div_le_div_of_nonneg_right hratio (by norm_num)
  exact le_trans hratio' hstep

end

end Work.Peluse.UControl
