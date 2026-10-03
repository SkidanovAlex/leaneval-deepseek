import Mathlib

/-!
# An abstract `ℓ¹` estimate on `ℤ`

This file proves `Work.KMTAreas.A7.TsumIntLeOfBounds`: a nonnegative sequence on `ℤ` which is
bounded by `A` everywhere and by `B/j²` off the origin has total mass at most
`C · (K·A + B/K)`, with an absolute constant `C`.

The proof splits `ℤ` into the origin, the two half lines starting at `±1`
(`tsum_of_add_one_of_neg_add_one`) and each half line into its first `K` terms and its tail
(`Summable.sum_add_tsum_nat_add`).  The head contributes at most `K·A` per half line (there are
only `K` terms of size `≤ A`), the origin at most `A`, and each tail at most `B/K`: there the
index satisfies `|j| ≥ K+1`, so the `1/j²` bound applies and

`∑_{n ∈ ℕ} B/(n+K+1)² ≤ B · (1/K)`,

which is proved by telescoping, `B/(n+K+1)² ≤ B·(1/(n+K) - 1/(n+K+1))`, the partial sums of the
right-hand side being `B·(1/K - 1/(n+K))`.  The constant `C = 6` then absorbs
`(2K+1)A + 2B/K ≤ 3K·A + 2B/K ≤ 6(K·A + B/K)`.
-/

set_option autoImplicit false

namespace Work.KMTAreas.A7

open scoped BigOperators

/-- **The shifted `ζ(2)` tail.**  For `K ≥ 1` the series `∑_{n ∈ ℕ} 1/(n+K+1)²` is summable and
its sum is at most `1/K`.

Telescoping: for `n : ℕ` one has `1/(n+K+1)² ≤ 1/(n+K) - 1/(n+K+1)`, because
`(n+K)(n+K+1) ≤ (n+K+1)²`; the partial sums of the right-hand side are
`1/K - 1/(N+K)`, which tend to `1/K`. -/
private lemma summable_tsum_shift_inv_sq (K : ℕ) (hK : 1 ≤ K) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + (K : ℝ) + 1) ^ 2) ∧
      ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + (K : ℝ) + 1) ^ 2 ≤ 1 / (K : ℝ) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n : ℝ) + (K : ℝ)) - 1 / ((n : ℝ) + (K : ℝ) + 1) := by
    intro n
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + (K : ℝ))
    linarith
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      ((1 : ℝ) / ((n : ℝ) + (K : ℝ)) - 1 / ((n : ℝ) + (K : ℝ) + 1))
      = 1 / (K : ℝ) - 1 / ((N : ℝ) + (K : ℝ)) := by
    intro N
    rw [show (∑ n ∈ Finset.range N,
          ((1 : ℝ) / ((n : ℝ) + (K : ℝ)) - 1 / ((n : ℝ) + (K : ℝ) + 1)))
        = ∑ n ∈ Finset.range N,
          ((1 : ℝ) / ((n : ℝ) + (K : ℝ)) - (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + (K : ℝ))) from
      Finset.sum_congr rfl (fun n _ => by
        have hcast : (((n + 1 : ℕ) : ℝ) + (K : ℝ)) = (n : ℝ) + (K : ℝ) + 1 := by
          push_cast; ring
        rw [hcast])]
    rw [Finset.sum_range_sub']
    norm_num
  have ht : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + (K : ℝ))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (((n + K : ℕ) : ℝ))) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (Filter.tendsto_add_atTop_nat K)
    refine h1.congr' (Filter.Eventually.of_forall (fun n => ?_))
    push_cast
    ring
  have hhas : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + (K : ℝ)) - 1 / ((n : ℝ) + (K : ℝ) + 1))
      (1 / (K : ℝ)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
    have hgoal : (fun N : ℕ => ∑ n ∈ Finset.range N,
          ((1 : ℝ) / ((n : ℝ) + (K : ℝ)) - 1 / ((n : ℝ) + (K : ℝ) + 1)))
        = fun N : ℕ => (1 : ℝ) / (K : ℝ) - 1 / ((N : ℝ) + (K : ℝ)) := funext hpart
    rw [hgoal]
    simpa using (tendsto_const_nhds.sub ht)
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + (K : ℝ)) - 1 / ((n : ℝ) + (K : ℝ) + 1)) :=
    hhas.summable
  have hle : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + (K : ℝ) + 1) ^ 2
      ≤ (1 : ℝ) / ((n : ℝ) + (K : ℝ)) - 1 / ((n : ℝ) + (K : ℝ) + 1) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + (K : ℝ) := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + (K : ℝ) + 1 := by positivity
    have hkey : (1 : ℝ) / ((n : ℝ) + (K : ℝ) + 1) ^ 2
        ≤ 1 / (((n : ℝ) + (K : ℝ)) * ((n : ℝ) + (K : ℝ) + 1)) := by
      apply one_div_le_one_div_of_le (mul_pos h1 h2)
      nlinarith
    have heq : (1 : ℝ) / (((n : ℝ) + (K : ℝ)) * ((n : ℝ) + (K : ℝ) + 1))
        = (1 : ℝ) / ((n : ℝ) + (K : ℝ)) - 1 / ((n : ℝ) + (K : ℝ) + 1) := by
      field_simp
      ring
    rwa [heq] at hkey
  have hsum2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + (K : ℝ) + 1) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hsum
  exact ⟨hsum2, le_trans (Summable.tsum_le_tsum hle hsum2 hsum) hhas.tsum_eq.le⟩

/-- The series `∑_{n ∈ ℕ} 1/(n+1)²` is summable (the `ζ(2)` series with its vanishing `n = 0`
term removed). -/
private lemma summable_inv_succ_sq : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have h3 : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2) :=
    (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h2
  simpa using h3

/-- For any `c : ℝ` and `m : ℕ` the series `∑_{n ∈ ℕ} c/(n+m+1)²` is summable: comparison with
the `ζ(2)`-series `∑ 1/(n+1)²`. -/
private lemma summable_div_add_sq_succ (c : ℝ) (m : ℕ) :
    Summable (fun n : ℕ => c / ((n : ℝ) + (m : ℝ) + 1) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + (m : ℝ) + 1) ^ 2) := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2)
      (g := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + (m : ℝ) + 1) ^ 2)
      (fun n => by positivity) (fun n => ?_) summable_inv_succ_sq
    apply one_div_le_one_div_of_le (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) 2)
    have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [h1, h2]
  simpa [div_eq_mul_inv] using hbase.mul_left c

/-- An abstract `ℓ¹` estimate on `ℤ`: a nonnegative sequence bounded by `A` everywhere and by
`B/j²` off the origin has total mass at most `C·(K·A + B/K)`, the constant `C` being absolute.
(Proof: split `ℤ` into `{|j| ≤ K}` and the two tails via
`tsum_of_add_one_of_neg_add_one`; the head has `2K+1 ≤ 3K` terms of size `≤ A`, and each tail is
comparable with `∑_{n} 1/(n+K)² ≤ 2/K`.) -/
theorem TsumIntLeOfBounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℤ → ℝ) (A B : ℝ) (K : ℕ),
      0 ≤ A → 0 ≤ B → 1 ≤ K →
      (∀ j : ℤ, 0 ≤ f j) →
      (∀ j : ℤ, f j ≤ A) →
      (∀ j : ℤ, j ≠ 0 → f j ≤ B / (j : ℝ) ^ 2) →
      ∑' j : ℤ, f j ≤ C * ((K : ℝ) * A + B / K) := by
  have hdiv : ∀ (c : ℝ) (m : ℕ), Summable (fun n : ℕ => c / ((n : ℝ) + (m : ℝ) + 1) ^ 2) :=
    summable_div_add_sq_succ
  refine ⟨6, by norm_num, ?_⟩
  intro f A B K hA hB hK hf0 hfA hfB
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have hsumB0 : Summable (fun n : ℕ => B / ((n : ℝ) + 1) ^ 2) := by simpa using hdiv B 0
  have hsumB : Summable (fun n : ℕ => B / ((n : ℝ) + (K : ℝ) + 1) ^ 2) := hdiv B K
  -- the two half series are summable, by comparison with `B/(n+1)²`
  have hgs : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => B / ((n : ℝ) + 1) ^ 2)
      (g := fun n : ℕ => f ((n : ℤ) + 1)) (fun n => hf0 _) (fun n => ?_) hsumB0
    have hj : ((n : ℤ) + 1) ≠ 0 := by omega
    have h := hfB ((n : ℤ) + 1) hj
    simpa using h
  have hhs : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => B / ((n : ℝ) + 1) ^ 2)
      (g := fun n : ℕ => f (-((n : ℤ) + 1))) (fun n => hf0 _) (fun n => ?_) hsumB0
    have hj : -((n : ℤ) + 1) ≠ 0 := by omega
    have h := hfB (-((n : ℤ) + 1)) hj
    have hcast : (((-((n : ℤ) + 1)) : ℤ) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
    have hsq : (-((n : ℝ) + 1)) ^ 2 = ((n : ℝ) + 1) ^ 2 := by ring
    calc f (-((n : ℤ) + 1)) ≤ B / (((-((n : ℤ) + 1)) : ℤ) : ℝ) ^ 2 := h
      _ = B / ((n : ℝ) + 1) ^ 2 := by rw [hcast, hsq]
  -- split each half line at `K`
  have hpos := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => f ((n : ℤ) + 1)) K hgs
  have hneg := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => f (-((n : ℤ) + 1))) K hhs
  have hposhead : ∑ i ∈ Finset.range K, f ((i : ℤ) + 1) ≤ (K : ℝ) * A := by
    calc ∑ i ∈ Finset.range K, f ((i : ℤ) + 1) ≤ ∑ i ∈ Finset.range K, A :=
          Finset.sum_le_sum (fun i _ => hfA _)
      _ = (K : ℝ) * A := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hpostail : ∑' i : ℕ, f (((i + K : ℕ) : ℤ) + 1) ≤ B / (K : ℝ) := by
    have hle : ∀ i : ℕ, f (((i + K : ℕ) : ℤ) + 1) ≤ B / ((i : ℝ) + (K : ℝ) + 1) ^ 2 := by
      intro i
      have hj : (((i + K : ℕ) : ℤ) + 1) ≠ 0 := by omega
      have h := hfB (((i + K : ℕ) : ℤ) + 1) hj
      have hcast : (((((i + K : ℕ) : ℤ) + 1 : ℤ)) : ℝ) = (i : ℝ) + (K : ℝ) + 1 := by
        push_cast; ring
      calc f (((i + K : ℕ) : ℤ) + 1)
          ≤ B / (((((i + K : ℕ) : ℤ) + 1 : ℤ)) : ℝ) ^ 2 := h
        _ = B / ((i : ℝ) + (K : ℝ) + 1) ^ 2 := by rw [hcast]
    have hsumf : Summable (fun i : ℕ => f (((i + K : ℕ) : ℤ) + 1)) :=
      (summable_nat_add_iff K).mpr hgs
    calc ∑' i : ℕ, f (((i + K : ℕ) : ℤ) + 1)
        ≤ ∑' i : ℕ, B / ((i : ℝ) + (K : ℝ) + 1) ^ 2 := Summable.tsum_le_tsum hle hsumf hsumB
      _ = B * ∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + (K : ℝ) + 1) ^ 2 := by
            rw [← tsum_mul_left]
            exact tsum_congr (fun i => by ring)
      _ ≤ B * (1 / (K : ℝ)) := mul_le_mul_of_nonneg_left (summable_tsum_shift_inv_sq K hK).2 hB
      _ = B / (K : ℝ) := by rw [mul_one_div]
  have hneghead : ∑ i ∈ Finset.range K, f (-((i : ℤ) + 1)) ≤ (K : ℝ) * A := by
    calc ∑ i ∈ Finset.range K, f (-((i : ℤ) + 1)) ≤ ∑ i ∈ Finset.range K, A :=
          Finset.sum_le_sum (fun i _ => hfA _)
      _ = (K : ℝ) * A := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnegtail : ∑' i : ℕ, f (-(((i + K : ℕ) : ℤ) + 1)) ≤ B / (K : ℝ) := by
    have hle : ∀ i : ℕ, f (-(((i + K : ℕ) : ℤ) + 1)) ≤ B / ((i : ℝ) + (K : ℝ) + 1) ^ 2 := by
      intro i
      have hj : -(((i + K : ℕ) : ℤ) + 1) ≠ 0 := by omega
      have h := hfB (-(((i + K : ℕ) : ℤ) + 1)) hj
      have hcast : ((((-(((i + K : ℕ) : ℤ) + 1)) : ℤ)) : ℝ) = -((i : ℝ) + (K : ℝ) + 1) := by
        push_cast; ring
      have hsq : (-((i : ℝ) + (K : ℝ) + 1)) ^ 2 = ((i : ℝ) + (K : ℝ) + 1) ^ 2 := by ring
      calc f (-(((i + K : ℕ) : ℤ) + 1))
          ≤ B / ((((-(((i + K : ℕ) : ℤ) + 1)) : ℤ)) : ℝ) ^ 2 := h
        _ = B / ((i : ℝ) + (K : ℝ) + 1) ^ 2 := by rw [hcast, hsq]
    have hsumf : Summable (fun i : ℕ => f (-(((i + K : ℕ) : ℤ) + 1))) :=
      (summable_nat_add_iff K).mpr hhs
    calc ∑' i : ℕ, f (-(((i + K : ℕ) : ℤ) + 1))
        ≤ ∑' i : ℕ, B / ((i : ℝ) + (K : ℝ) + 1) ^ 2 := Summable.tsum_le_tsum hle hsumf hsumB
      _ = B * ∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + (K : ℝ) + 1) ^ 2 := by
            rw [← tsum_mul_left]
            exact tsum_congr (fun i => by ring)
      _ ≤ B * (1 / (K : ℝ)) := mul_le_mul_of_nonneg_left (summable_tsum_shift_inv_sq K hK).2 hB
      _ = B / (K : ℝ) := by rw [mul_one_div]
  have hp : ∑' n : ℕ, f ((n : ℤ) + 1) ≤ (K : ℝ) * A + B / (K : ℝ) := by
    rw [← hpos]; linarith [hposhead, hpostail]
  have hn : ∑' n : ℕ, f (-((n : ℤ) + 1)) ≤ (K : ℝ) * A + B / (K : ℝ) := by
    rw [← hneg]; linarith [hneghead, hnegtail]
  rw [tsum_of_add_one_of_neg_add_one hgs hhs]
  have hKA : A ≤ (K : ℝ) * A := by
    calc A = (1 : ℝ) * A := (one_mul A).symm
      _ ≤ (K : ℝ) * A := mul_le_mul_of_nonneg_right hK1 hA
  have hA0 : (0 : ℝ) ≤ (K : ℝ) * A := mul_nonneg hKpos.le hA
  have hBK0 : (0 : ℝ) ≤ B / (K : ℝ) := div_nonneg hB hKpos.le
  have hf00 := hfA 0
  linarith [hp, hn, hKA, hA0, hBK0, hf00]

end Work.KMTAreas.A7
