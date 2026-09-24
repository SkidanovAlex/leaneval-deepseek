import Mathlib
import Submission.Work.GM.Trace.Spart_defs

/-!
# GM Lemma 4.5 / Proposition 5.1, the small `I_m`

For `m : ℤ³` with a **single** non-zero coordinate, GM §5 bound `I_m` by splitting the
triple sum `Σ_{t₁,t₂,t₃ ∈ W}` into the diagonal (`t₁ = t₂ = t₃`) and the rest.

* On the diagonal all three frequencies in `ĥ_{tᵢ-tⱼ}(mⱼN)` are `0`, so the single non-zero
  frequency contributes `≤ C_d/(|ρ(m)|^j N^j)` (by the decay hypothesis) and the other two
  factors contribute `≤ A₀ = ĥ_0(0)` each.  There are `|W|` such triples.
* Off the diagonal, `nzCount m = 1` means that two of the three factors are `ĥ_{tᵢ-tⱼ}(0)`;
  since `W` is `δ`-separated with `δ ≥ 1` and the triple is not constant, (at least) one of
  those two factors has a non-zero argument, hence is `≤ C_z/δ^j` by the zero-frequency
  decay hypothesis.  The other two factors are again `≤ A₀`, and there are `≤ |W|³` triples,
  giving `|W|³ A₀² C_z/δ^j` (with a factor `2` in the final statement since we take the union
  of the two conditions `t₁ ≠ t₂`, `t₂ ≠ t₃`).

Paper reference: `REFS/GuthMaynard_2405.20552.txt`, §5 (proof of Proposition 5.1).
-/

open Complex Finset
open scoped BigOperators
open Submission.GM Submission.LargeValues
set_option autoImplicit false

namespace Work.GM.Trace

/-- `p*q*r ≤ P*Q*R` from componentwise bounds, with the relevant non-negativities. -/
private theorem mul3_le_mul3 {p q r P Q R : ℝ} (h1 : p ≤ P) (h2 : q ≤ Q) (h3 : r ≤ R)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    p * q * r ≤ P * Q * R := by
  have hpq : p * q ≤ P * Q := mul_le_mul h1 h2 hq hP
  exact mul_le_mul hpq h3 hr (mul_nonneg hP hQ)

/-- If every term of a triple sum is bounded by `X` on the diagonal `a = b = c` and by `Y`
elsewhere (`X, Y ≥ 0`), then the sum is bounded by `|W| X + |W|³ Y`. -/
private theorem triple_sum_le_aux (W : Finset ℝ) (F : ℝ → ℝ → ℝ → ℂ) (X Y : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ‖F a b c‖ ≤ if a = b ∧ b = c then X else Y) :
    ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, F a b c‖ ≤ (W.card : ℝ) * X + (W.card : ℝ) ^ 3 * Y := by
  classical
  have h1 : ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, F a b c‖ ≤ ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ‖F a b c‖ := by
    calc ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, F a b c‖
        ≤ ∑ a ∈ W, ‖∑ b ∈ W, ∑ c ∈ W, F a b c‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ W, ∑ b ∈ W, ‖∑ c ∈ W, F a b c‖ := by
          apply sum_le_sum; intro a ha
          exact norm_sum_le _ _
      _ ≤ ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ‖F a b c‖ := by
          apply sum_le_sum; intro a ha
          apply sum_le_sum; intro b hb
          exact norm_sum_le _ _
  have h2 : (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ‖F a b c‖)
      ≤ ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then X else Y) := by
    apply sum_le_sum; intro a ha
    apply sum_le_sum; intro b hb
    apply sum_le_sum; intro c hc
    exact h a ha b hb c hc
  have hsplit : (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then X else Y))
      = (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then X else (0:ℝ)))
        + (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then (0:ℝ) else Y)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b hb
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro c hc
    by_cases hE : a = b ∧ b = c <;> simp [hE]
  have hdiag : (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then X else (0:ℝ)))
      = (W.card : ℝ) * X := by
    rw [show (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then X else (0:ℝ)))
        = (∑ a ∈ W, ∑ b ∈ W, (if a = b then X else 0)) from by
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro b hb
      rw [show (∑ c ∈ W, (if a = b ∧ b = c then X else (0:ℝ)))
          = (∑ c ∈ W, (if b = c then (if a = b then X else (0:ℝ)) else 0)) from by
        apply Finset.sum_congr rfl; intro c hc
        by_cases h : b = c <;> by_cases h' : a = b <;> simp [h, h']]
      rw [Finset.sum_ite_eq]; simp [hb]]
    rw [show (∑ a ∈ W, ∑ b ∈ W, (if a = b then X else 0)) = (∑ a ∈ W, X) from by
      apply Finset.sum_congr rfl; intro a ha
      rw [Finset.sum_ite_eq]; simp [ha]]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hoff : (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then (0:ℝ) else Y))
      ≤ (W.card : ℝ) ^ 3 * Y := by
    have hle : (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then (0:ℝ) else Y))
        ≤ ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, Y := by
      apply sum_le_sum; intro a ha
      apply sum_le_sum; intro b hb
      apply sum_le_sum; intro c hc
      by_cases hE : a = b ∧ b = c <;> simp [hE, hY]
    refine le_trans hle (le_of_eq ?_)
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  calc ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, F a b c‖
      ≤ ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ‖F a b c‖ := h1
    _ ≤ ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then X else Y) := h2
    _ = _ := hsplit
    _ ≤ (W.card : ℝ) * X + (W.card : ℝ) ^ 3 * Y := by
        rw [hdiag]
        exact add_le_add (le_refl _) hoff

/-- Decay of `ĥ_0` at the non-zero frequency `kN`, from the decay hypothesis
`‖ĥ_t(ξ)‖ ≤ C_d (1+|t|)^j/|ξ|^j` at `t = 0`. -/
private theorem hhat_zero_freq_le (N : ℕ) (hN : 1 ≤ N) (j : ℕ) (Cd : ℝ)
    (hdec : ∀ t ξ : ℝ, ξ ≠ 0 → ‖hhat t ξ‖ ≤ Cd * (1 + |t|) ^ j / |ξ| ^ j) :
    ∀ k : ℤ, k ≠ 0 → ‖hhat 0 ((k : ℝ) * N)‖ ≤ Cd / (|(k : ℝ)| ^ j * (N : ℝ) ^ j) := by
  intro k hk
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hξ : (k : ℝ) * (N : ℝ) ≠ 0 := mul_ne_zero hkR (ne_of_gt hNpos)
  have h := hdec 0 ((k : ℝ) * (N : ℝ)) hξ
  have h1 : (1 + |(0 : ℝ)|) ^ j = 1 := by rw [abs_zero, add_zero, one_pow]
  rw [h1, mul_one] at h
  rw [abs_mul, abs_of_nonneg (le_of_lt hNpos), mul_pow] at h
  exact h

/-- Decay of `ĥ_d(0)` for `|d| ≥ δ ≥ 1`, from the zero-frequency decay hypothesis. -/
private theorem hhat_zero_arg_le (δ : ℝ) (hδ : 1 ≤ δ) (j : ℕ) (Cz : ℝ) (hCz : 0 ≤ Cz)
    (hzero : ∀ t : ℝ, 1 ≤ |t| → ‖hhat t 0‖ ≤ Cz / |t| ^ j) :
    ∀ d : ℝ, δ ≤ |d| → ‖hhat d 0‖ ≤ Cz / δ ^ j := by
  intro d hd
  have hδpos : 0 < δ := lt_of_lt_of_le one_pos hδ
  have hd1 : 1 ≤ |d| := le_trans hδ hd
  calc ‖hhat d 0‖ ≤ Cz / |d| ^ j := hzero d hd1
    _ ≤ Cz / δ ^ j := div_le_div_of_nonneg_left hCz (pow_pos hδpos j)
        (pow_le_pow_left₀ (le_of_lt hδpos) hd j)

/-- The diagonal contribution: when `t₁ = t₂ = t₃` all three arguments vanish, so the triple
product is `ĥ_0(m₁N) ĥ_0(m₂N) ĥ_0(m₃N)`, of which exactly one factor is at a non-zero
frequency (namely `ρ(m) N`) and the two others are `≤ A₀`. -/
private theorem diag_bound_aux (N : ℕ) (j : ℕ) (Cd : ℝ) (hCd : 0 ≤ Cd)
    (hdec0 : ∀ k : ℤ, k ≠ 0 → ‖hhat 0 ((k : ℝ) * N)‖ ≤ Cd / (|(k : ℝ)| ^ j * (N : ℝ) ^ j))
    (hAz : ∀ t ξ : ℝ, ‖hhat t ξ‖ ≤ Azero)
    (m : ℤ × ℤ × ℤ) (hm : nzCount m = 1) :
    ‖hhat 0 ((m.1 : ℝ) * N) * hhat 0 ((m.2.1 : ℝ) * N) * hhat 0 ((m.2.2 : ℝ) * N)‖
      ≤ Azero ^ 2 * Cd / (|(rho m : ℝ)| ^ j * (N : ℝ) ^ j) := by
  have hAz0 : 0 ≤ Azero := Azero_nonneg
  have hDd : ∀ k : ℤ, (0 : ℝ) ≤ Cd / (|(k : ℝ)| ^ j * (N : ℝ) ^ j) := fun k =>
    div_nonneg hCd (mul_nonneg (pow_nonneg (abs_nonneg _) j)
      (pow_nonneg (Nat.cast_nonneg N) j))
  rcases nzCount_one_cases m hm with ⟨hm1, hm2, hm3⟩ | ⟨hm1, hm2, hm3⟩ | ⟨hm1, hm2, hm3⟩
  · have hr : rho m = m.1 := rho_of_ne_zero hm1
    have h1 : ‖hhat 0 ((m.1 : ℝ) * N)‖ ≤ Cd / (|(m.1 : ℝ)| ^ j * (N : ℝ) ^ j) := hdec0 m.1 hm1
    have h2 : ‖hhat 0 ((m.2.1 : ℝ) * N)‖ ≤ Azero := by
      rw [hm2, Int.cast_zero, zero_mul]; exact hAz 0 0
    have h3 : ‖hhat 0 ((m.2.2 : ℝ) * N)‖ ≤ Azero := by
      rw [hm3, Int.cast_zero, zero_mul]; exact hAz 0 0
    have hr' : |(m.1 : ℝ)| ^ j * (N : ℝ) ^ j = |(rho m : ℝ)| ^ j * (N : ℝ) ^ j := by rw [hr]
    calc ‖hhat 0 ((m.1 : ℝ) * N) * hhat 0 ((m.2.1 : ℝ) * N) * hhat 0 ((m.2.2 : ℝ) * N)‖
        = ‖hhat 0 ((m.1 : ℝ) * N)‖ * ‖hhat 0 ((m.2.1 : ℝ) * N)‖ *
            ‖hhat 0 ((m.2.2 : ℝ) * N)‖ := by rw [norm_mul, norm_mul]
      _ ≤ (Cd / (|(m.1 : ℝ)| ^ j * (N : ℝ) ^ j)) * Azero * Azero :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (hDd m.1)) h3 (norm_nonneg _)
            (mul_nonneg (hDd m.1) hAz0)
      _ = Azero ^ 2 * Cd / (|(rho m : ℝ)| ^ j * (N : ℝ) ^ j) := by rw [hr']; ring
  · have hr : rho m = m.2.1 := rho_of_fst_eq_zero hm1 hm2
    have h1 : ‖hhat 0 ((m.1 : ℝ) * N)‖ ≤ Azero := by
      rw [hm1, Int.cast_zero, zero_mul]; exact hAz 0 0
    have h2 : ‖hhat 0 ((m.2.1 : ℝ) * N)‖
        ≤ Cd / (|(m.2.1 : ℝ)| ^ j * (N : ℝ) ^ j) := hdec0 m.2.1 hm2
    have h3 : ‖hhat 0 ((m.2.2 : ℝ) * N)‖ ≤ Azero := by
      rw [hm3, Int.cast_zero, zero_mul]; exact hAz 0 0
    have hr' : |(m.2.1 : ℝ)| ^ j * (N : ℝ) ^ j = |(rho m : ℝ)| ^ j * (N : ℝ) ^ j := by rw [hr]
    calc ‖hhat 0 ((m.1 : ℝ) * N) * hhat 0 ((m.2.1 : ℝ) * N) * hhat 0 ((m.2.2 : ℝ) * N)‖
        = ‖hhat 0 ((m.1 : ℝ) * N)‖ * ‖hhat 0 ((m.2.1 : ℝ) * N)‖ *
            ‖hhat 0 ((m.2.2 : ℝ) * N)‖ := by rw [norm_mul, norm_mul]
      _ ≤ Azero * (Cd / (|(m.2.1 : ℝ)| ^ j * (N : ℝ) ^ j)) * Azero :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hAz0) h3 (norm_nonneg _)
            (mul_nonneg hAz0 (hDd m.2.1))
      _ = Azero ^ 2 * Cd / (|(rho m : ℝ)| ^ j * (N : ℝ) ^ j) := by rw [hr']; ring
  · have hr : rho m = m.2.2 := rho_of_fst_snd_eq_zero hm1 hm2
    have h1 : ‖hhat 0 ((m.1 : ℝ) * N)‖ ≤ Azero := by
      rw [hm1, Int.cast_zero, zero_mul]; exact hAz 0 0
    have h2 : ‖hhat 0 ((m.2.1 : ℝ) * N)‖ ≤ Azero := by
      rw [hm2, Int.cast_zero, zero_mul]; exact hAz 0 0
    have h3 : ‖hhat 0 ((m.2.2 : ℝ) * N)‖
        ≤ Cd / (|(m.2.2 : ℝ)| ^ j * (N : ℝ) ^ j) := hdec0 m.2.2 hm3
    have hr' : |(m.2.2 : ℝ)| ^ j * (N : ℝ) ^ j = |(rho m : ℝ)| ^ j * (N : ℝ) ^ j := by rw [hr]
    calc ‖hhat 0 ((m.1 : ℝ) * N) * hhat 0 ((m.2.1 : ℝ) * N) * hhat 0 ((m.2.2 : ℝ) * N)‖
        = ‖hhat 0 ((m.1 : ℝ) * N)‖ * ‖hhat 0 ((m.2.1 : ℝ) * N)‖ *
            ‖hhat 0 ((m.2.2 : ℝ) * N)‖ := by rw [norm_mul, norm_mul]
      _ ≤ Azero * Azero * (Cd / (|(m.2.2 : ℝ)| ^ j * (N : ℝ) ^ j)) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hAz0) h3 (norm_nonneg _)
            (mul_nonneg hAz0 hAz0)
      _ = Azero ^ 2 * Cd / (|(rho m : ℝ)| ^ j * (N : ℝ) ^ j) := by rw [hr']; ring

/-- The off-diagonal contribution: for a non-constant triple two of the three factors are at
zero frequency, and (since `W` is `δ`-separated) one of those has argument `≥ δ`, so that
factor is `≤ C_z/δ^j` while the other two are `≤ A₀`. -/
private theorem offdiag_bound_aux (N : ℕ) (W : Finset ℝ) (δ : ℝ) (hδ : 1 ≤ δ)
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → δ ≤ |t - s|)
    (j : ℕ) (Cz : ℝ) (hCz : 0 ≤ Cz)
    (hzero : ∀ t : ℝ, 1 ≤ |t| → ‖hhat t 0‖ ≤ Cz / |t| ^ j)
    (hAz : ∀ t ξ : ℝ, ‖hhat t ξ‖ ≤ Azero)
    (m : ℤ × ℤ × ℤ) (hm : nzCount m = 1)
    (a b c : ℝ) (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hne : ¬(a = b ∧ b = c)) :
    ‖hhat (a - b) ((m.1 : ℝ) * N) * hhat (b - c) ((m.2.1 : ℝ) * N) *
      hhat (c - a) ((m.2.2 : ℝ) * N)‖ ≤ Azero ^ 2 * Cz / δ ^ j := by
  have hAz0 : 0 ≤ Azero := Azero_nonneg
  have hδpos : 0 < δ := lt_of_lt_of_le one_pos hδ
  have hY : 0 ≤ Cz / δ ^ j := div_nonneg hCz (pow_nonneg (le_of_lt hδpos) j)
  have hh0 := hhat_zero_arg_le δ hδ j Cz hCz hzero
  rcases nzCount_one_cases m hm with ⟨hm1, hm2, hm3⟩ | ⟨hm1, hm2, hm3⟩ | ⟨hm1, hm2, hm3⟩
  · have e2 : (m.2.1 : ℝ) * N = 0 := by rw [hm2, Int.cast_zero, zero_mul]
    have e3 : (m.2.2 : ℝ) * N = 0 := by rw [hm3, Int.cast_zero, zero_mul]
    rw [e2, e3]
    by_cases hbc : b = c
    · have hab : a ≠ b := fun h => hne ⟨h, hbc⟩
      have hdc : δ ≤ |c - a| := by rw [← hbc]; exact hsep b hb a ha (fun h => hab h.symm)
      calc ‖hhat (a - b) ((m.1 : ℝ) * N) * hhat (b - c) 0 * hhat (c - a) 0‖
          = ‖hhat (a - b) ((m.1 : ℝ) * N)‖ * ‖hhat (b - c) 0‖ * ‖hhat (c - a) 0‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ Azero * Azero * (Cz / δ ^ j) :=
            mul3_le_mul3 (hAz _ _) (hAz _ _) (hh0 _ hdc) (norm_nonneg _) (norm_nonneg _) hAz0 hAz0
        _ = Azero ^ 2 * Cz / δ ^ j := by ring
    · have hdbc : δ ≤ |b - c| := hsep b hb c hc hbc
      calc ‖hhat (a - b) ((m.1 : ℝ) * N) * hhat (b - c) 0 * hhat (c - a) 0‖
          = ‖hhat (a - b) ((m.1 : ℝ) * N)‖ * ‖hhat (b - c) 0‖ * ‖hhat (c - a) 0‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ Azero * (Cz / δ ^ j) * Azero :=
            mul3_le_mul3 (hAz _ _) (hh0 _ hdbc) (hAz _ _) (norm_nonneg _) (norm_nonneg _) hAz0 hY
        _ = Azero ^ 2 * Cz / δ ^ j := by ring
  · have e1 : (m.1 : ℝ) * N = 0 := by rw [hm1, Int.cast_zero, zero_mul]
    have e3 : (m.2.2 : ℝ) * N = 0 := by rw [hm3, Int.cast_zero, zero_mul]
    rw [e1, e3]
    by_cases hca : c = a
    · have hab : a ≠ b := fun h => hne ⟨h, h.symm.trans hca.symm⟩
      have hdab : δ ≤ |a - b| := hsep a ha b hb hab
      calc ‖hhat (a - b) 0 * hhat (b - c) ((m.2.1 : ℝ) * N) * hhat (c - a) 0‖
          = ‖hhat (a - b) 0‖ * ‖hhat (b - c) ((m.2.1 : ℝ) * N)‖ * ‖hhat (c - a) 0‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (Cz / δ ^ j) * Azero * Azero :=
            mul3_le_mul3 (hh0 _ hdab) (hAz _ _) (hAz _ _) (norm_nonneg _) (norm_nonneg _) hY hAz0
        _ = Azero ^ 2 * Cz / δ ^ j := by ring
    · have hdca : δ ≤ |c - a| := hsep c hc a ha hca
      calc ‖hhat (a - b) 0 * hhat (b - c) ((m.2.1 : ℝ) * N) * hhat (c - a) 0‖
          = ‖hhat (a - b) 0‖ * ‖hhat (b - c) ((m.2.1 : ℝ) * N)‖ * ‖hhat (c - a) 0‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ Azero * Azero * (Cz / δ ^ j) :=
            mul3_le_mul3 (hAz _ _) (hAz _ _) (hh0 _ hdca) (norm_nonneg _) (norm_nonneg _) hAz0 hAz0
        _ = Azero ^ 2 * Cz / δ ^ j := by ring
  · have e1 : (m.1 : ℝ) * N = 0 := by rw [hm1, Int.cast_zero, zero_mul]
    have e2 : (m.2.1 : ℝ) * N = 0 := by rw [hm2, Int.cast_zero, zero_mul]
    rw [e1, e2]
    by_cases hab : a = b
    · have hbc : b ≠ c := fun h => hne ⟨hab, h⟩
      have hdbc : δ ≤ |b - c| := hsep b hb c hc hbc
      calc ‖hhat (a - b) 0 * hhat (b - c) 0 * hhat (c - a) ((m.2.2 : ℝ) * N)‖
          = ‖hhat (a - b) 0‖ * ‖hhat (b - c) 0‖ * ‖hhat (c - a) ((m.2.2 : ℝ) * N)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ Azero * (Cz / δ ^ j) * Azero :=
            mul3_le_mul3 (hAz _ _) (hh0 _ hdbc) (hAz _ _) (norm_nonneg _) (norm_nonneg _) hAz0 hY
        _ = Azero ^ 2 * Cz / δ ^ j := by ring
    · have hdab : δ ≤ |a - b| := hsep a ha b hb hab
      calc ‖hhat (a - b) 0 * hhat (b - c) 0 * hhat (c - a) ((m.2.2 : ℝ) * N)‖
          = ‖hhat (a - b) 0‖ * ‖hhat (b - c) 0‖ * ‖hhat (c - a) ((m.2.2 : ℝ) * N)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (Cz / δ ^ j) * Azero * Azero :=
            mul3_le_mul3 (hh0 _ hdab) (hAz _ _) (hAz _ _) (norm_nonneg _) (norm_nonneg _) hY hAz0
        _ = Azero ^ 2 * Cz / δ ^ j := by ring

theorem Iterm_bound_small (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) (δ : ℝ) (hδ : 1 ≤ δ)
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → δ ≤ |t - s|)
    (j : ℕ) (Cd Cz : ℝ) (hCd : 0 ≤ Cd) (hCz : 0 ≤ Cz)
    (hdec : ∀ t ξ : ℝ, ξ ≠ 0 → ‖Submission.GM.hhat t ξ‖ ≤ Cd * (1 + |t|) ^ j / |ξ| ^ j)
    (hzero : ∀ t : ℝ, 1 ≤ |t| → ‖Submission.GM.hhat t 0‖ ≤ Cz / |t| ^ j)
    (hAz : ∀ t ξ : ℝ, ‖Submission.GM.hhat t ξ‖ ≤ Work.GM.Trace.Azero)
    (m : ℤ × ℤ × ℤ) (hm : Submission.GM.nzCount m = 1) :
    ‖Submission.GM.Iterm N W m‖ ≤ (N : ℝ) ^ 3 *
      ((W.card : ℝ) * Work.GM.Trace.Azero ^ 2 * Cd / (|(Work.GM.Trace.rho m : ℝ)| ^ j * (N : ℝ) ^ j)
        + 2 * (W.card : ℝ) ^ 3 * Work.GM.Trace.Azero ^ 2 * Cz / δ ^ j) := by
  classical
  have hδpos : 0 < δ := lt_of_lt_of_le one_pos hδ
  have hAz0 : 0 ≤ Azero := Azero_nonneg
  set X : ℝ := Azero ^ 2 * Cd / (|(rho m : ℝ)| ^ j * (N : ℝ) ^ j) with hXdef
  set Y : ℝ := Azero ^ 2 * Cz / δ ^ j with hYdef
  have hXnn : 0 ≤ X := by
    rw [hXdef]
    exact div_nonneg (mul_nonneg (pow_nonneg hAz0 2) hCd)
      (mul_nonneg (pow_nonneg (abs_nonneg _) j) (pow_nonneg (Nat.cast_nonneg N) j))
  have hYnn : 0 ≤ Y := by
    rw [hYdef]
    exact div_nonneg (mul_nonneg (pow_nonneg hAz0 2) hCz) (pow_nonneg (le_of_lt hδpos) j)
  have hdec0 := hhat_zero_freq_le N hN j Cd hdec
  have hpoint : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W,
      ‖hhat (a - b) ((m.1 : ℝ) * N) * hhat (b - c) ((m.2.1 : ℝ) * N) *
        hhat (c - a) ((m.2.2 : ℝ) * N)‖ ≤ if a = b ∧ b = c then X else Y := by
    intro a ha b hb c hc
    by_cases hE : a = b ∧ b = c
    · rw [if_pos hE]
      have e1 : a - b = 0 := sub_eq_zero.mpr hE.1
      have e2 : b - c = 0 := sub_eq_zero.mpr hE.2
      have e3 : c - a = 0 := sub_eq_zero.mpr (by rw [← hE.2, ← hE.1])
      rw [e1, e2, e3, hXdef]
      exact diag_bound_aux N j Cd hCd hdec0 hAz m hm
    · rw [if_neg hE, hYdef]
      exact offdiag_bound_aux N W δ hδ hsep j Cz hCz hzero hAz m hm a b c ha hb hc hE
  have htriple := triple_sum_le_aux W (fun a b c => hhat (a - b) ((m.1 : ℝ) * N) *
    hhat (b - c) ((m.2.1 : ℝ) * N) * hhat (c - a) ((m.2.2 : ℝ) * N)) X Y hXnn hYnn hpoint
  have hI : Iterm N W m = (N : ℂ) ^ 3 *
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, hhat (a - b) ((m.1 : ℝ) * N) *
        hhat (b - c) ((m.2.1 : ℝ) * N) * hhat (c - a) ((m.2.2 : ℝ) * N)) := rfl
  rw [hI, norm_mul, norm_pow, Complex.norm_natCast]
  calc (N : ℝ) ^ 3 * ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, hhat (a - b) ((m.1 : ℝ) * N) *
        hhat (b - c) ((m.2.1 : ℝ) * N) * hhat (c - a) ((m.2.2 : ℝ) * N)‖
      ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) * X + (W.card : ℝ) ^ 3 * Y) :=
        mul_le_mul_of_nonneg_left htriple (by positivity)
    _ ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) * X + 2 * (W.card : ℝ) ^ 3 * Y) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg (pow_nonneg (Nat.cast_nonneg W.card) 3) hYnn]
    _ = (N : ℝ) ^ 3 * ((W.card : ℝ) * Azero ^ 2 * Cd /
          (|(rho m : ℝ)| ^ j * (N : ℝ) ^ j)
        + 2 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cz / δ ^ j) := by
        rw [hXdef, hYdef]; ring

end Work.GM.Trace
