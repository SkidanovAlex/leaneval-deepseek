import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_defs
import Submission.Work.BMF.adi_lagrange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Helpers for the ADI descent (`Work.BMF.solve_adi`)

Definitions and elementary lemmas: the accumulated lattice denominators `Dfac`, the integers
`qj a b m = a^m - b^m`, the constants controlling the sup-norm growth, integrality lemmas, and
the arithmetic estimates on `qj`.
-/

namespace Work.BMF

open Polynomial Finset

/-- `∏_{i=m+1}^{k} i!`: the accumulated lattice denominator `D_m` of the descent
(`D_k = 1` and `D_{m-1} = D_m · m!`). -/
noncomputable def Dfac (k m : ℕ) : ℕ := ∏ i ∈ Finset.Icc (m + 1) k, i.factorial

/-- `q_m = a^m - b^m`. -/
def qj (a b m : ℕ) : ℕ := a ^ m - b ^ m

/-- The modulus product of the conclusion: `(k!)^{k+1} ∏_{m=1}^{k} q_m`. -/
noncomputable def bigq (k a b : ℕ) : ℕ :=
  (k.factorial) ^ (k + 1) * ∏ m ∈ Finset.Icc 1 k, qj a b m

/-- Constant controlling the growth of the sup-norm bound in one descent step:
`|T_j| (L/x)^{j+1} ≤ A_j · Dgrow`. -/
noncomputable def Dgrow (k : ℕ) (C₀ : ℝ) : ℝ :=
  (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * C₀ ^ 2 * (2 * (1 + 3 ^ (k + 1) * C₀ ^ (2 * k + 2)))

/-- The sup-norm bound at level `j` of the descent. -/
noncomputable def Alev (k : ℕ) (C₀ : ℝ) (j : ℕ) : ℝ :=
  (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1 - j) * ((k : ℝ) + 2 - j)

/-- Constant such that `|T_j| ≤ CT1 · A_j · C₀^j · N^{j+1}`. -/
noncomputable def CT1 (k : ℕ) (C₀ : ℝ) : ℝ :=
  2 * Real.pi * (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * C₀

/-- Constant such that `|T_j| ≤ CTc · N^{j+1}` at every level of the descent. -/
noncomputable def CTc (k : ℕ) (C₀ : ℝ) : ℝ := Alev k C₀ 0 * CT1 k C₀ * C₀ ^ k

section IntegralOn

theorem IntegralOn.const_mul {δ : ℝ} {γ : ℝ[X]} (h : IntegralOn δ γ) (m : ℤ) :
    IntegralOn δ (C (m : ℝ) * γ) := by
  intro n
  obtain ⟨z, hz⟩ := h n
  exact ⟨m * z, by rw [eval_C_mul, hz]; push_cast; ring⟩

theorem IntegralOn.add {δ : ℝ} {γ₁ γ₂ : ℝ[X]} (h₁ : IntegralOn δ γ₁) (h₂ : IntegralOn δ γ₂) :
    IntegralOn δ (γ₁ + γ₂) := by
  intro n
  obtain ⟨z₁, hz₁⟩ := h₁ n
  obtain ⟨z₂, hz₂⟩ := h₂ n
  exact ⟨z₁ + z₂, by rw [eval_add, hz₁, hz₂]; push_cast; ring⟩

theorem IntegralOn.sub {δ : ℝ} {γ₁ γ₂ : ℝ[X]} (h₁ : IntegralOn δ γ₁) (h₂ : IntegralOn δ γ₂) :
    IntegralOn δ (γ₁ - γ₂) := by
  intro n
  obtain ⟨z₁, hz₁⟩ := h₁ n
  obtain ⟨z₂, hz₂⟩ := h₂ n
  exact ⟨z₁ - z₂, by rw [eval_sub, hz₁, hz₂]; push_cast; ring⟩

theorem IntegralOn.const {δ : ℝ} (m : ℤ) : IntegralOn δ (C (m : ℝ)) := by
  intro n
  exact ⟨m, by rw [eval_C]⟩

private theorem IntegralOn.neg {δ : ℝ} {γ : ℝ[X]} (h : IntegralOn δ γ) : IntegralOn δ (-γ) := by
  have := h.const_mul (-1)
  simpa using this

/-- Enlarging the lattice by an integer factor preserves integrality. -/
theorem IntegralOn.mono {δ δ' : ℝ} {m : ℤ} (hm : δ' = δ * m) {γ : ℝ[X]}
    (h : IntegralOn δ γ) : IntegralOn δ' γ := by
  intro n
  obtain ⟨z, hz⟩ := h (m * n)
  refine ⟨z, ?_⟩
  rw [hm]
  convert hz using 2
  push_cast
  ring

end IntegralOn

section QjBounds

theorem qj_cast (a b m : ℕ) (hba : b ≤ a) : ((qj a b m : ℕ) : ℝ) = (a : ℝ) ^ m - (b : ℝ) ^ m := by
  unfold qj
  rw [Nat.cast_sub (Nat.pow_le_pow_left hba m), Nat.cast_pow, Nat.cast_pow]

theorem qj_pos (a b m : ℕ) (hba : b < a) (hm : 0 < m) : 0 < qj a b m := by
  unfold qj
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hba (Nat.pos_iff_ne_zero.mp hm))

theorem factorial_pos (m : ℕ) : 0 < m.factorial := Nat.factorial_pos m

theorem Dfac_pos (k m : ℕ) : 0 < Dfac k m := by
  unfold Dfac
  exact Finset.prod_pos fun i _ => Nat.factorial_pos i

theorem Dfac_step (k j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ k) :
    Dfac k (j - 1) = j.factorial * Dfac k j := by
  have hsub : j - 1 + 1 = j := by omega
  have hsplit : Finset.Icc j k = insert j (Finset.Icc (j + 1) k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : j ∉ Finset.Icc (j + 1) k := by
    simp only [Finset.mem_Icc]; omega
  unfold Dfac
  rw [hsub, hsplit, Finset.prod_insert hnot, mul_comm]

/-- If `|e| ≤ A` on an interval and `e` has degree `≤ j` while its `j`-th coefficient vanishes,
then the degree is `≤ j - 1`. -/
theorem natDegree_le_sub_one_of {e : ℝ[X]} {j : ℕ} (h1 : e.natDegree ≤ j) (h2 : e.coeff j = 0) :
    e.natDegree ≤ j - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rcases eq_or_lt_of_le (by omega : j ≤ N) with h | h
  · rw [← h]; exact h2
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h1 h)

/-- Lower bound for `q_m = a^m - b^m` from the comparability hypothesis `a ≤ C₀ N (a - b)`. -/
theorem qj_lower (a b m : ℕ) (hm : 1 ≤ m) {C₀ N : ℝ} (hC₀ : 1 ≤ C₀) (hN : 100 * C₀ ^ 4 ≤ N)
    (h1 : (a : ℝ) ≤ C₀ * N * ((a : ℝ) - (b : ℝ))) (hba : b < a) :
    (a : ℝ) ^ m / (C₀ * N) ≤ ((qj a b m : ℕ) : ℝ) := by
  have ha : 0 < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have hN0 : 0 < N := by
    have hC1 : (1 : ℝ) ≤ C₀ ^ 4 := one_le_pow₀ hC₀
    linarith
  have hCN : 0 < C₀ * N := by positivity
  have hle : (b : ℝ) ≤ (a : ℝ) := by
    have : b ≤ a := le_of_lt hba
    exact_mod_cast this
  have hdiff : (a : ℝ) / (C₀ * N) ≤ (a : ℝ) - (b : ℝ) := by
    rw [div_le_iff₀ hCN, mul_comm]
    linarith [h1]
  have hba' : (b : ℝ) ≤ (a : ℝ) - (a : ℝ) / (C₀ * N) := by linarith
  have hratio : (b : ℝ) / (a : ℝ) ≤ 1 - 1 / (C₀ * N) := by
    rw [div_le_iff₀ ha]
    have hEq : (1 - 1 / (C₀ * N)) * (a : ℝ) = (a : ℝ) - (a : ℝ) / (C₀ * N) := by
      rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
    rw [hEq]
    exact hba'
  have hratio0 : (0 : ℝ) ≤ (b : ℝ) / (a : ℝ) := by
    have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    positivity
  have hratio1 : (b : ℝ) / (a : ℝ) ≤ 1 := by
    rw [div_le_one ha]; exact hle
  have hpow : ((b : ℝ) / (a : ℝ)) ^ m ≤ (b : ℝ) / (a : ℝ) :=
    pow_le_of_le_one hratio0 hratio1 (by omega)
  have hbm : ((b : ℝ) / (a : ℝ)) ^ m * (a : ℝ) ^ m = (b : ℝ) ^ m := by
    rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt ha)]
  have key : (a : ℝ) ^ m - (b : ℝ) ^ m = (a : ℝ) ^ m * (1 - ((b : ℝ) / (a : ℝ)) ^ m) := by
    rw [mul_sub, mul_one, ← hbm]
    ring
  have h1r : 1 / (C₀ * N) ≤ 1 - ((b : ℝ) / (a : ℝ)) ^ m := by linarith
  have hfin : (qj a b m : ℝ) = (a : ℝ) ^ m - (b : ℝ) ^ m := qj_cast a b m (le_of_lt hba)
  rw [hfin, key]
  calc (a : ℝ) ^ m / (C₀ * N) = (a : ℝ) ^ m * (1 / (C₀ * N)) := by ring
    _ ≤ (a : ℝ) ^ m * (1 - ((b : ℝ) / (a : ℝ)) ^ m) :=
        mul_le_mul_of_nonneg_left h1r (pow_nonneg (le_of_lt ha) m)


/-- `Dgrow` is nonnegative. -/
theorem Dgrow_nonneg (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) : 0 ≤ Dgrow k C₀ := by
  unfold Dgrow
  have h1 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2 : (0 : ℝ) ≤ (k : ℝ) ^ k := pow_nonneg h1 k
  have h3 : (0 : ℝ) ≤ C₀ ^ 2 := sq_nonneg C₀
  have h4 : (0 : ℝ) ≤ C₀ ^ (2 * k + 2) := by
    have h : 2 * k + 2 = 2 * (k + 1) := by ring
    rw [h, pow_mul]
    exact pow_nonneg (sq_nonneg C₀) (k + 1)
  have h5 : (0 : ℝ) ≤ 3 ^ (k + 1) * C₀ ^ (2 * k + 2) := mul_nonneg (by positivity) h4
  have h6 : (0 : ℝ) ≤ 2 * (1 + 3 ^ (k + 1) * C₀ ^ (2 * k + 2)) :=
    mul_nonneg (by norm_num) (by linarith)
  have h7 : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := mul_nonneg h1 (by linarith)
  exact mul_nonneg (mul_nonneg (mul_nonneg h7 h2) h3) h6

/-- `Alev` is nonnegative at the levels attained by the descent. -/
theorem Alev_nonneg (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) {j : ℕ} (hj : j ≤ k) :
    0 ≤ Alev k C₀ j := by
  unfold Alev
  have hD : 0 ≤ Dgrow k C₀ := Dgrow_nonneg k C₀ hC₀
  have h1 : (0 : ℝ) ≤ C₀ + (k : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have h2 : (0 : ℝ) ≤ (1 + Dgrow k C₀) ^ (k + 1 - j) := pow_nonneg (by linarith) _
  have h3 : (0 : ℝ) ≤ (k : ℝ) + 2 - j := by
    have : (j : ℝ) ≤ k := by exact_mod_cast hj
    linarith [Nat.cast_nonneg (α := ℝ) k]
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-- `Alev` is decreasing in `j` on `j ≤ k`. -/
theorem Alev_le_zero (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) {j : ℕ} (hj : j ≤ k) :
    Alev k C₀ j ≤ Alev k C₀ 0 := by
  unfold Alev
  have hD : 0 ≤ Dgrow k C₀ := Dgrow_nonneg k C₀ hC₀
  have hD1 : 1 ≤ 1 + Dgrow k C₀ := by linarith
  have hexp : k + 1 - j ≤ k + 1 := Nat.sub_le _ _
  have hp1 : (1 + Dgrow k C₀) ^ (k + 1 - j) ≤ (1 + Dgrow k C₀) ^ (k + 1) :=
    pow_le_pow_right₀ hD1 hexp
  have hp2 : ((k : ℝ) + 2 - j) ≤ ((k : ℝ) + 2) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hp3 : 0 ≤ ((k : ℝ) + 2 - j) := by
    have : (j : ℝ) ≤ k := by exact_mod_cast hj
    linarith
  have hC : 0 ≤ (C₀ + (k : ℝ) + 2) := by positivity
  have hpow0 : 0 ≤ (1 + Dgrow k C₀) ^ (k + 1 - j) := pow_nonneg (by linarith) _
  have hpow1 : 0 ≤ (1 + Dgrow k C₀) ^ (k + 1) := pow_nonneg (by linarith) _
  have hstep : (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1 - j) * ((k : ℝ) + 2 - j)
      ≤ (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1) * ((k : ℝ) + 2) := by
    have hm1 : (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1 - j)
        ≤ (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left hp1 hC
    calc (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1 - j) * ((k : ℝ) + 2 - j)
        ≤ (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1) * ((k : ℝ) + 2 - j) :=
          mul_le_mul_of_nonneg_right hm1 hp3
      _ ≤ (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1) * ((k : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hp2 (mul_nonneg hC hpow1)
  simpa using hstep

end QjBounds

end Work.BMF
