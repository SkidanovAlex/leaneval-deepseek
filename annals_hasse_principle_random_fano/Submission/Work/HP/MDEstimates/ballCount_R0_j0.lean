import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDEstimates.ball_count_R0
import Submission.Work.HP.MDEstimates.R0j0.sum_high_le
import Submission.Work.HP.MDEstimates.R0j0.prod_lam_lower
import Submission.Work.HP.MDEstimates.R0j0.pow_le_pow_add_one

/-!
# `Work.HP.MDEstimates.ballCount_R0_j0`

The second part of Lemma R0 of Browning--Le Boudec--Sawin, *The Hasse principle for random Fano
hypersurfaces*, Annals of Math. 197 (2023): for an integral lattice `L` of rank `R` with successive
minima `lam L i`, with `M` and `J` such that `2M ≤ lam L 1`, `2J ≤ lam L (j0+1)`, and cut-offs
`1 ≤ T ≤ Y`, `lam L R ≤ Y`,

`#(L ∩ B(T)) ≤ K · ( T^{R-j} Y^j / det L + (T/M)^{j0} ((T/J)^{R-1-j0-j} + 1) )`.

The estimate is obtained from the Schmidt-type sum bound `ballCount_sum_bound`
(`#(L ∩ B(T)) ≤ K₁ Σ_{k ≤ R} T^k / (lam L 1 ⋯ lam L k)`) by splitting the sum at `R - j`:

* the *high* terms `k ≥ R - j` are bounded by `R · T^{R-j} Y^j / det L`
  (child lemma `R0j0.sum_high_le`);
* the *low* terms `k < R - j = j0 + 1 + (R-1-j0-j)` are split again at `j0 + 1`, using
  `lam L i ≥ 2M` for `i ≤ j0` and `lam L i ≥ 2J` for `i > j0` (child lemma `R0j0.prod_lam_lower`),
  and bounded by `R · (T/M)^{j0} ((T/J)^{R-1-j0-j} + 1)`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

open Work.HP

/-- Low-index part of the sum bound: the terms `k < R - j` of Schmidt's sum are bounded by
`R · (T/M)^{j0} ((T/J)^{R-1-j0-j} + 1)`.  Here `R - j = (j0+1) + n` with `n = R-1-j0-j`; the
first `j0+1` terms are controlled by `lam L i ≥ 2M` (`i ≤ j0`) and the remaining `n` terms by
`lam L i ≥ 2J` (`i > j0`), plus `T/M ≥ 1` and the elementary `x^{k} ≤ x^n + 1` for `0 ≤ x`,
`k ≤ n`. -/
private lemma sum_low_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (R j0 j : ℕ) (M J T : ℝ)
    (hrk : rk L = R) (hR : 1 ≤ R) (hj0 : j0 ≤ R - 1) (hj : j ≤ R - 1 - j0)
    (hT : 1 ≤ T) (hM : 0 < M) (hMT : M ≤ T) (hJ : 0 < J)
    (hM1 : 2 * M ≤ lam L 1) (hJ1 : 2 * J ≤ lam L (j0 + 1)) :
    (∑ k ∈ Finset.range (R - j), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1))
      ≤ (R : ℝ) * ((T / M) ^ j0 * ((T / J) ^ (R - 1 - j0 - j) + 1)) := by
  classical
  set f : ℕ → ℝ := fun k => T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) with hf
  set n : ℕ := R - 1 - j0 - j with hn
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hJ0 : (0 : ℝ) ≤ J := le_of_lt hJ
  have hTm : 1 ≤ T / M := (one_le_div hM).mpr hMT
  have hRj : R - j = (j0 + 1) + n := by omega
  have hsplit : ∑ k ∈ Finset.range (R - j), f k
      = (∑ k ∈ Finset.range (j0 + 1), f k)
        + ∑ k' ∈ Finset.range n, f ((j0 + 1) + k') := by
    rw [hRj, Finset.sum_range_add]
  rw [hsplit]
  have hfirst : ∑ k ∈ Finset.range (j0 + 1), f k ≤ ((j0 : ℝ) + 1) * (T / M) ^ j0 := by
    have hterm : ∀ k ∈ Finset.range (j0 + 1), f k ≤ (T / M) ^ j0 := by
      intro k hk
      have hkj : k ≤ j0 := by simp only [Finset.mem_range] at hk; omega
      have hkR : k ≤ R := by omega
      have hP := R0j0.prod_lam_lower L R j0 k M J hrk hM.le hJ0 (by omega) hkR hM1 hJ1
      rw [min_eq_left hkj] at hP
      simp only [Nat.sub_self, pow_zero, mul_one] at hP
      have hPpos : 0 < (2 * M) ^ k := pow_pos (by linarith) k
      have hle2 : T / (2 * M) ≤ T / M := div_le_div_of_nonneg_left hT0 hM (by linarith)
      calc f k = T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by simp only [hf]
        _ ≤ T ^ k / (2 * M) ^ k :=
            div_le_div_of_nonneg_left (pow_nonneg hT0 k) hPpos hP
        _ = (T / (2 * M)) ^ k := by rw [div_pow]
        _ ≤ (T / M) ^ k := pow_le_pow_left₀ (by positivity) hle2 k
        _ ≤ (T / M) ^ j0 := pow_le_pow_right₀ hTm hkj
    calc ∑ k ∈ Finset.range (j0 + 1), f k ≤ ∑ _k ∈ Finset.range (j0 + 1), (T / M) ^ j0 :=
          Finset.sum_le_sum hterm
      _ = ((j0 : ℝ) + 1) * (T / M) ^ j0 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hsecond : ∑ k' ∈ Finset.range n, f ((j0 + 1) + k')
      ≤ (n : ℝ) * ((T / M) ^ j0 * ((T / J) ^ n + 1)) := by
    have hterm : ∀ k' ∈ Finset.range n, f ((j0 + 1) + k')
        ≤ (T / M) ^ j0 * ((T / J) ^ n + 1) := by
      intro k' hk'
      have hk'n : k' < n := Finset.mem_range.mp hk'
      have hkR : (j0 + 1) + k' ≤ R := by omega
      have hmin : min ((j0 + 1) + k') j0 = j0 := min_eq_right (by omega)
      have hP := R0j0.prod_lam_lower L R j0 ((j0 + 1) + k') M J hrk hM.le hJ0
        (by omega) hkR hM1 hJ1
      rw [hmin] at hP
      rw [show (j0 + 1 + k') - j0 = 1 + k' by omega] at hP
      have hPpos : 0 < (2 * M) ^ j0 * (2 * J) ^ (1 + k') := by positivity
      have hle2M : T / (2 * M) ≤ T / M := div_le_div_of_nonneg_left hT0 hM (by linarith)
      have hle2J : T / (2 * J) ≤ T / J := div_le_div_of_nonneg_left hT0 hJ (by linarith)
      calc f ((j0 + 1) + k')
          = T ^ ((j0 + 1) + k') / ∏ i ∈ Finset.range ((j0 + 1) + k'), lam L (i + 1) := by
            simp only [hf]
        _ ≤ T ^ ((j0 + 1) + k') / ((2 * M) ^ j0 * (2 * J) ^ (1 + k')) :=
            div_le_div_of_nonneg_left (pow_nonneg hT0 _) hPpos hP
        _ = (T / (2 * M)) ^ j0 * (T / (2 * J)) ^ (1 + k') := by
            rw [div_pow, div_pow, div_mul_div_comm, ← pow_add,
              show j0 + (1 + k') = (j0 + 1) + k' by omega]
        _ ≤ (T / M) ^ j0 * ((T / J) ^ n + 1) := by
            refine mul_le_mul (pow_le_pow_left₀ (by positivity) hle2M j0) ?_
              (by positivity) (by positivity)
            refine le_trans (pow_le_pow_left₀ (by positivity) hle2J (1 + k')) ?_
            exact R0j0.pow_le_pow_add_one (by positivity) (by omega)
    calc ∑ k' ∈ Finset.range n, f ((j0 + 1) + k')
        ≤ ∑ _k' ∈ Finset.range n, ((T / M) ^ j0 * ((T / J) ^ n + 1)) := Finset.sum_le_sum hterm
      _ = (n : ℝ) * ((T / M) ^ j0 * ((T / J) ^ n + 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_trans (add_le_add hfirst hsecond) ?_
  have hA0 : 0 ≤ (T / M) ^ j0 := by positivity
  have hB0 : 0 ≤ (T / J) ^ n + 1 := by positivity
  have hB1 : 1 ≤ (T / J) ^ n + 1 := by
    have : 0 ≤ (T / J) ^ n := by positivity
    linarith
  have hle : ((j0 : ℝ) + 1) + (n : ℝ) ≤ (R : ℝ) := by
    have h1 : ((j0 + 1 + n : ℕ) : ℝ) ≤ (R : ℝ) := by
      have h2 : j0 + 1 + n ≤ R := by omega
      exact_mod_cast h2
    simpa using h1
  have h1 : ((j0 : ℝ) + 1) * (T / M) ^ j0
      ≤ ((j0 : ℝ) + 1) * (T / M) ^ j0 * ((T / J) ^ n + 1) := by
    have h3 := mul_le_mul_of_nonneg_left hB1
      (show (0 : ℝ) ≤ ((j0 : ℝ) + 1) * (T / M) ^ j0 by positivity)
    linarith
  calc ((j0 : ℝ) + 1) * (T / M) ^ j0 + (n : ℝ) * ((T / M) ^ j0 * ((T / J) ^ n + 1))
      ≤ ((j0 : ℝ) + 1) * (T / M) ^ j0 * ((T / J) ^ n + 1)
        + (n : ℝ) * ((T / M) ^ j0 * ((T / J) ^ n + 1)) := by linarith
    _ = (((j0 : ℝ) + 1) + (n : ℝ)) * ((T / M) ^ j0 * ((T / J) ^ n + 1)) := by ring
    _ ≤ (R : ℝ) * ((T / M) ^ j0 * ((T / J) ^ n + 1)) :=
        mul_le_mul_of_nonneg_right hle (by positivity)

/-- **Lemma R0, second part** (Browning--Le Boudec--Sawin, Annals 2023). -/
theorem ballCount_R0_j0 {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (R j0 j : ℕ) (M J Y T : ℝ),
      rk L = R → 2 ≤ R → j0 ≤ R - 1 → j ≤ R - 1 - j0 → 1 ≤ T → M ≤ T → T ≤ Y →
      lam L R ≤ Y → 0 < detL L → detL L ≤ ∏ i ∈ Finset.range R, lam L (i + 1) →
      0 < M → 2 * M ≤ lam L 1 → 0 < J → 2 * J ≤ lam L (j0 + 1) →
      (ballCount L T : ℝ) ≤ K * (T ^ (R - j) * Y ^ j / detL L
          + (T / M) ^ j0 * ((T / J) ^ (R - 1 - j0 - j) + 1)) := by
  classical
  obtain ⟨K1, hK1pos, hK1⟩ := ballCount_sum_bound (ι := ι) (Fintype.card ι)
  refine ⟨K1 * ((Fintype.card ι : ℝ) + 1), mul_pos hK1pos (by positivity), ?_⟩
  intro L R j0 j M J Y T hrk hR2 hj0 hj hT hMT hTY hlam hdet hdetle hM hM1 hJ hJ1
  have hR1 : 1 ≤ R := by omega
  set X : ℝ := T ^ (R - j) * Y ^ j / detL L with hX
  set Z : ℝ := (T / M) ^ j0 * ((T / J) ^ (R - 1 - j0 - j) + 1) with hZ
  have hB1 : (1 : ℝ) ≤ T := hT
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hsum := hK1 L (rk_le_card L) T hT
  rw [hrk] at hsum
  have hlow := sum_low_le L R j0 j M J T hrk hR1 hj0 hj hT hM hMT hJ hM1 hJ1
  have hhigh := R0j0.sum_high_le L R j Y T hrk hR1 (by omega) hT hTY hlam hdet hdetle
  rw [← hX] at hhigh
  rw [← hZ] at hlow
  have hsplit : (∑ k ∈ Finset.range (R + 1), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1))
      = (∑ k ∈ Finset.range (R - j), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1))
        + ∑ k ∈ Finset.range (j + 1),
            T ^ (R - j + k) / ∏ i ∈ Finset.range (R - j + k), lam L (i + 1) := by
    have h : R + 1 = (R - j) + (j + 1) := by omega
    rw [h, Finset.sum_range_add]
  have hRle : (R : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have := rk_le_card L
    rw [hrk] at this
    exact_mod_cast this
  have hAB : (∑ k ∈ Finset.range (R - j), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1))
        + ∑ k ∈ Finset.range (j + 1),
            T ^ (R - j + k) / ∏ i ∈ Finset.range (R - j + k), lam L (i + 1)
      ≤ ((Fintype.card ι : ℝ) + 1) * (X + Z) := by
    have h3 : (R : ℝ) * (X + Z) ≤ ((Fintype.card ι : ℝ) + 1) * (X + Z) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    calc (∑ k ∈ Finset.range (R - j), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1))
          + ∑ k ∈ Finset.range (j + 1),
              T ^ (R - j + k) / ∏ i ∈ Finset.range (R - j + k), lam L (i + 1)
        ≤ (R : ℝ) * Z + (R : ℝ) * X := add_le_add hlow hhigh
      _ = (R : ℝ) * (X + Z) := by ring
      _ ≤ ((Fintype.card ι : ℝ) + 1) * (X + Z) := h3
  calc (ballCount L T : ℝ)
      ≤ K1 * ∑ k ∈ Finset.range (R + 1), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := hsum
    _ = K1 * ((∑ k ∈ Finset.range (R - j), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1))
        + ∑ k ∈ Finset.range (j + 1),
            T ^ (R - j + k) / ∏ i ∈ Finset.range (R - j + k), lam L (i + 1)) := by rw [hsplit]
    _ ≤ K1 * (((Fintype.card ι : ℝ) + 1) * (X + Z)) := mul_le_mul_of_nonneg_left hAB hK1pos.le
    _ = K1 * ((Fintype.card ι : ℝ) + 1) * (X + Z) := by ring

end Work.HP.MDEstimates
