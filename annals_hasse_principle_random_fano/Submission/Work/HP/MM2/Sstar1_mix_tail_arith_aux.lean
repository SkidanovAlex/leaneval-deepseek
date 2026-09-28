import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.card_Mon

/-!
# Auxiliary arithmetic for `Sstar1_mix_tail_arith`

Two elementary inputs used by the "large `B`" arithmetic of `Sstar1_mix_tail_arith`:

* `NN d n ≥ 2 * n + 2` for `2 ≤ d ≤ n` (via `card_Mon` and monotonicity of binomial
  coefficients), which is what makes the exponent `5(N-2)/6` available in the second
  estimate beat `n + 1/2`;
* `c (1 + log B)^e ≤ B^δ` eventually in `B`, for every `c > 0`, `δ > 0` and `e : ℕ`
  (a polylogarithmic-vs-power statement, proved from `Real.log_le_rpow_div`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MM2

open Work.HP

/-- For `2 ≤ d ≤ n` there are at least `2 n + 2` monomials of degree `d` in `n + 1`
variables: `NN d n = (n+d).choose d ≥ (n+2).choose 2 = (n+1)(n+2)/2 ≥ 2n+2`. -/
theorem two_mul_add_two_le_NN (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    2 * n + 2 ≤ NN d n := by
  rw [NN, Work.HP.Lat.card_Mon]
  have hn2 : 2 ≤ n := by omega
  have hsym1 : (n + d).choose d = (n + d).choose n := by
    have h := Nat.choose_symm (show d ≤ n + d by omega)
    rw [show n + d - d = n by omega] at h
    exact h.symm
  have hsym2 : (n + 2).choose n = (n + 2).choose 2 := by
    have h := Nat.choose_symm (show n ≤ n + 2 by omega)
    rw [show n + 2 - n = 2 by omega] at h
    exact h.symm
  have hmono : (n + 2).choose n ≤ (n + d).choose n :=
    Nat.choose_le_choose n (by omega)
  have hlow : 2 * n + 2 ≤ (n + 2).choose n := by
    rw [hsym2, Nat.choose_two_right, show n + 2 - 1 = n + 1 by omega]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    nlinarith [hn2]
  calc 2 * n + 2 ≤ (n + 2).choose n := hlow
    _ ≤ (n + d).choose n := hmono
    _ = (n + d).choose d := hsym1.symm

/-- For every `c > 0`, `δ > 0` and `e : ℕ` there is `B₀` with
`c (1 + log B)^e ≤ B^δ` for all `B ≥ B₀`, `B ≥ 1`. -/
theorem eventually_const_mul_one_add_log_pow_le_rpow (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (e : ℕ) :
    ∃ B₀ : ℝ, ∀ B : ℝ, 1 ≤ B → B₀ ≤ B → c * (1 + Real.log B) ^ e ≤ B ^ δ := by
  set η : ℝ := δ / (2 * ((e : ℝ) + 1)) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  set c' : ℝ := c * (1 + 1 / η) ^ e with hc'def
  have hc'pos : 0 < c' := by rw [hc'def]; positivity
  refine ⟨c' ^ (2 / δ), ?_⟩
  intro B hB1 hB0
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hlogBnn : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hlog : Real.log B ≤ B ^ η / η := Real.log_le_rpow_div hBpos.le hηpos
  have hBη1 : 1 ≤ B ^ η := Real.one_le_rpow hB1 hηpos.le
  have h1log : 1 + Real.log B ≤ (1 + 1 / η) * B ^ η := by
    have h2 : 1 + B ^ η / η ≤ (1 + 1 / η) * B ^ η := by
      have hrw : (1 + 1 / η) * B ^ η = B ^ η + B ^ η / η := by ring
      rw [hrw]
      linarith [hBη1]
    linarith [hlog, h2]
  have hηe : η * (e : ℝ) ≤ δ / 2 := by
    rw [hηdef, div_mul_eq_mul_div]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((e : ℝ) + 1))]
    have he : (e : ℝ) ≤ (e : ℝ) + 1 := by linarith
    nlinarith [hδ, (show (0 : ℝ) ≤ (e : ℝ) by positivity), he]
  have hfac_nn : 0 ≤ 1 + 1 / η := by positivity
  have hstep1 : (1 + Real.log B) ^ e ≤ (1 + 1 / η) ^ e * B ^ (δ / 2) := by
    have hpow : (1 + Real.log B) ^ e ≤ ((1 + 1 / η) * B ^ η) ^ e :=
      pow_le_pow_left₀ (by linarith) h1log e
    have hsplit : ((1 + 1 / η) * B ^ η) ^ e = (1 + 1 / η) ^ e * (B ^ η) ^ e := by
      rw [mul_pow]
    have hBηe : (B ^ η) ^ e = B ^ (η * (e : ℝ)) := by
      rw [← Real.rpow_natCast (B ^ η) e, ← Real.rpow_mul hBpos.le]
    have hle2 : (B ^ η) ^ e ≤ B ^ (δ / 2) := by
      rw [hBηe]
      exact Real.rpow_le_rpow_of_exponent_le hB1 hηe
    calc (1 + Real.log B) ^ e ≤ ((1 + 1 / η) * B ^ η) ^ e := hpow
      _ = (1 + 1 / η) ^ e * (B ^ η) ^ e := hsplit
      _ ≤ (1 + 1 / η) ^ e * B ^ (δ / 2) :=
          mul_le_mul_of_nonneg_left hle2 (pow_nonneg hfac_nn e)
  have hc'_le : c' ≤ B ^ (δ / 2) := by
    have h1 : (c' ^ (2 / δ)) ^ (δ / 2) ≤ B ^ (δ / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hc'pos.le _) hB0 (by linarith)
    have h2 : (c' ^ (2 / δ)) ^ (δ / 2) = c' := by
      rw [← Real.rpow_mul hc'pos.le]
      have hone : 2 / δ * (δ / 2) = 1 := by field_simp
      rw [hone, Real.rpow_one]
    rwa [h2] at h1
  calc c * (1 + Real.log B) ^ e ≤ c * ((1 + 1 / η) ^ e * B ^ (δ / 2)) :=
        mul_le_mul_of_nonneg_left hstep1 hc.le
    _ = c' * B ^ (δ / 2) := by rw [hc'def]; ring
    _ ≤ B ^ (δ / 2) * B ^ (δ / 2) :=
        mul_le_mul_of_nonneg_right hc'_le (Real.rpow_nonneg hBpos.le _)
    _ = B ^ δ := by
        rw [← Real.rpow_add hBpos]
        congr 1
        ring

end Work.HP.MM2
