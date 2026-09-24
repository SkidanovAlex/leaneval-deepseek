import Mathlib
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.tail_part_bound

namespace Work.GM.Affine

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

/-!
# The lattice sum of the shifted decay function of `\hat\psi_1`

GM §9 needs the bound

`∑_{ℓ ∈ ℤ} ‖psi1hat K (M₃ (ℓ - y))‖ ≤ C ((1/β)^N + 4·2^N/M₃^N)`

for `|y| ≤ 1/2`, `M₃ ≥ 1`, `β > 0`, `β ≤ M₃|y|` and a decay hypothesis
`‖psi1hat K z‖ ≤ C/(1+|z|)^N` with `N ≥ 2`.

The term `ℓ = 0` is bounded by `C/β^N` (since `M₃|y| ≥ β`).  For `ℓ ≠ 0` one has
`|ℓ - y| ≥ |ℓ|/2` (as `|y| ≤ 1/2` and `|ℓ| ≥ 1`), hence
`‖psi1hat K (M₃(ℓ-y))‖ ≤ C·2^N/(M₃^N |ℓ|^N)`; the resulting lattice `p`-series is
`∑_{ℓ ≠ 0} 1/|ℓ|^N = 2 ∑_{n} 1/(n+1)^N ≤ 4`, the last bound following from a telescoping
estimate for partial sums.
-/

/-- Telescoping identity `∑_{n<K} (1/(n+c) - 1/(n+c+1)) = 1/c - 1/(K+c)`. -/
lemma sum_range_telescope_inv (K : ℕ) (c : ℝ) :
    ∑ n ∈ Finset.range K, ((1:ℝ)/((n:ℝ)+c) - 1/((n:ℝ)+c+1)) = 1/c - 1/((K:ℝ)+c) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- `∑_{n : ℕ} 1/(n+1)^N ≤ 2` for `N ≥ 2`. -/
lemma tsum_nat_one_add_inv_pow_le {N : ℕ} (hN : 2 ≤ N) :
    (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^N) ≤ 2 := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun K => ?_)
  have hterm : ∀ n : ℕ,
      (1:ℝ)/((n:ℝ)+1+1)^N ≤ 1/((n:ℝ)+1) - 1/((n:ℝ)+1+1) := by
    intro n
    have hbase : (1:ℝ) ≤ (n:ℝ)+1+1 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hpow : ((n:ℝ)+1)*((n:ℝ)+1+1) ≤ ((n:ℝ)+1+1)^N := by
      have h2 : ((n:ℝ)+1+1)^2 ≤ ((n:ℝ)+1+1)^N := pow_le_pow_right₀ hbase hN
      have h01 : (0:ℝ) ≤ (n:ℝ)+1+1 := by positivity
      have hle1 : ((n:ℝ)+1) ≤ ((n:ℝ)+1+1) := by linarith
      have h3 : ((n:ℝ)+1)*((n:ℝ)+1+1) ≤ ((n:ℝ)+1+1)*((n:ℝ)+1+1) :=
        mul_le_mul_of_nonneg_right hle1 h01
      calc ((n:ℝ)+1)*((n:ℝ)+1+1) ≤ ((n:ℝ)+1+1)*((n:ℝ)+1+1) := h3
        _ = ((n:ℝ)+1+1)^2 := by ring
        _ ≤ ((n:ℝ)+1+1)^N := h2
    have hle : (1:ℝ)/((n:ℝ)+1+1)^N ≤ 1/(((n:ℝ)+1)*((n:ℝ)+1+1)) :=
      one_div_le_one_div_of_le (show (0:ℝ) < ((n:ℝ)+1)*((n:ℝ)+1+1) by positivity) hpow
    have hid : (1:ℝ)/(((n:ℝ)+1)*((n:ℝ)+1+1)) = 1/((n:ℝ)+1) - 1/((n:ℝ)+1+1) := by
      have h1 : ((n:ℝ)+1) ≠ 0 := by positivity
      have h2 : ((n:ℝ)+1+1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hid] at hle
    exact hle
  rcases K with _ | K'
  · simp
  rw [Finset.sum_range_succ']
  have hsum : ∑ n ∈ Finset.range K', (1:ℝ)/((((n+1:ℕ)):ℝ)+1)^N ≤ 1 := by
    calc ∑ n ∈ Finset.range K', (1:ℝ)/((((n+1:ℕ)):ℝ)+1)^N
        = ∑ n ∈ Finset.range K', (1:ℝ)/((n:ℝ)+1+1)^N := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [show ((((n+1:ℕ)):ℝ)+1) = (n:ℝ)+1+1 by push_cast; ring]
      _ ≤ ∑ n ∈ Finset.range K', (1/((n:ℝ)+1) - 1/((n:ℝ)+1+1)) :=
          Finset.sum_le_sum (fun n _ => hterm n)
      _ = 1 - 1/((K':ℝ)+1) := by
          rw [sum_range_telescope_inv K' 1]
          norm_num
      _ ≤ 1 := by
          have : (0:ℝ) ≤ 1/((K':ℝ)+1) := by positivity
          linarith
  have hzero : (1:ℝ)/((((0:ℕ)):ℝ)+1)^N = 1 := by norm_num
  rw [hzero]
  linarith

/-- `ℓ ↦ 1/|ℓ|^N` is summable on `ℤ` for `N ≥ 2`. -/
lemma summable_int_inv_abs_pow {N : ℕ} (hN : 2 ≤ N) :
    Summable (fun ℓ : ℤ => (1:ℝ)/|(ℓ:ℝ)|^N) := by
  have hbase := (summable_int_inv_one_add_abs_pow N (by omega : 1 < N)).mul_left ((2:ℝ)^N)
  refine Summable.of_nonneg_of_le (fun ℓ => by positivity) (fun ℓ => ?_) hbase
  rcases eq_or_ne ℓ 0 with h0 | h0
  · subst h0
    rw [show |(((0:ℤ)):ℝ)| = 0 by simp, zero_pow (by omega : N ≠ 0), div_zero]
    positivity
  · have hℓ1 : (1:ℝ) ≤ |(ℓ:ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h0
    have hlt : (0:ℝ) < |(ℓ:ℝ)| := by linarith
    have h3 : ((1:ℝ) + |(ℓ:ℝ)|)^N ≤ ((2:ℝ) * |(ℓ:ℝ)|)^N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    rw [mul_pow] at h3
    rw [div_le_iff₀ (pow_pos hlt N)]
    calc (1:ℝ) ≤ ((2:ℝ)^N * |(ℓ:ℝ)|^N) / ((1 + |(ℓ:ℝ)|)^N) := by
          rw [le_div_iff₀ (by positivity)]
          simpa using h3
      _ = (2:ℝ)^N * (1/(1+|(ℓ:ℝ)|)^N) * |(ℓ:ℝ)|^N := by ring

/-- `∑_{ℓ : ℤ} 1/|ℓ|^N ≤ 4` for `N ≥ 2`. -/
lemma tsum_int_inv_abs_pow_le {N : ℕ} (hN : 2 ≤ N) :
    (∑' ℓ : ℤ, (1:ℝ)/|(ℓ:ℝ)|^N) ≤ 4 := by
  have hsumm := summable_int_inv_abs_pow hN
  have hsP : Summable (fun n : ℕ => (1:ℝ)/|(((n:ℤ)+1:ℤ):ℝ)|^N) :=
    hsumm.comp_injective (i := fun n : ℕ => (n:ℤ)+1) (by intro a b hab; simp only [] at hab; omega)
  have hsN : Summable (fun n : ℕ => (1:ℝ)/|((-((n:ℤ)+1):ℤ):ℝ)|^N) :=
    hsumm.comp_injective (i := fun n : ℕ => -((n:ℤ)+1)) (by intro a b hab; simp only [] at hab; omega)
  have hsplit := tsum_of_add_one_of_neg_add_one
    (f := fun ℓ : ℤ => (1:ℝ)/|(ℓ:ℝ)|^N) hsP hsN
  have hf0 : (1:ℝ)/|(((0:ℤ)):ℝ)|^N = 0 := by
    rw [show |(((0:ℤ)):ℝ)| = 0 by simp, zero_pow (by omega : N ≠ 0), div_zero]
  have hP : (∑' n : ℕ, (1:ℝ)/|(((n:ℤ)+1:ℤ):ℝ)|^N)
      = ∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^N := by
    apply tsum_congr; intro n
    have hx : |(((n:ℤ)+1:ℤ):ℝ)| = (n:ℝ)+1 := by
      push_cast
      exact abs_of_nonneg (by positivity)
    rw [hx]
  have hQ : (∑' n : ℕ, (1:ℝ)/|((-((n:ℤ)+1):ℤ):ℝ)|^N)
      = ∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^N := by
    apply tsum_congr; intro n
    have hx : |((-((n:ℤ)+1):ℤ):ℝ)| = (n:ℝ)+1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [hx]
  calc (∑' ℓ : ℤ, (1:ℝ)/|(ℓ:ℝ)|^N)
      = (∑' n : ℕ, (1:ℝ)/|(((n:ℤ)+1:ℤ):ℝ)|^N) + (1:ℝ)/|(((0:ℤ)):ℝ)|^N
          + (∑' n : ℕ, (1:ℝ)/|((-((n:ℤ)+1):ℤ):ℝ)|^N) := hsplit
    _ = (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^N) + 0 + (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^N) := by
          rw [hP, hQ, hf0]
    _ ≤ 2 + 0 + 2 := by
          have h := tsum_nat_one_add_inv_pow_le hN
          linarith
    _ = 4 := by norm_num

/-- Pointwise lattice bound: each term of the shift-sum is dominated by an `ℓ = 0` term
`C(1/β)^N` plus the decay term `(C 2^N/M₃^N)·(1/|ℓ|^N)`. -/
lemma norm_psi1hat_shift_le {K : ℝ} {N : ℕ} (hN : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ z : ℝ, ‖psi1hat K z‖ ≤ C / (1 + |z|) ^ N)
    {M₃ y β : ℝ} (hM₃ : 1 ≤ M₃) (hy : |y| ≤ 1 / 2) (hβ : 0 < β) (hyβ : β ≤ M₃ * |y|)
    (ℓ : ℤ) :
    ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖ ≤
      (if ℓ = 0 then C * (1 / β) ^ N else 0)
        + (C * 2 ^ N / M₃ ^ N) * (1 / |(ℓ:ℝ)| ^ N) := by
  have hM₃nn : (0:ℝ) ≤ M₃ := by linarith
  have hM₃pos : (0:ℝ) < M₃ := by linarith
  rcases eq_or_ne ℓ 0 with h0 | h0
  · subst h0
    rw [if_pos rfl]
    have habs : |M₃ * ((((0:ℤ)):ℝ) - y)| = M₃ * |y| := by
      rw [abs_mul, abs_of_nonneg hM₃nn]
      congr 1
      simp
    have hd := hdec (M₃ * ((((0:ℤ)):ℝ) - y))
    rw [habs] at hd
    have hβle : β ≤ 1 + M₃ * |y| := by linarith [abs_nonneg y]
    have hden : β^N ≤ (1 + M₃*|y|)^N := pow_le_pow_left₀ hβ.le hβle N
    have h1 : C / (1 + M₃*|y|)^N ≤ C / β^N :=
      div_le_div_of_nonneg_left hC (pow_pos hβ N) hden
    have h2 : C / β^N = C * (1/β)^N := by rw [one_div_pow]; ring
    have h3 : (C * 2^N / M₃^N) * (1 / |((((0:ℤ)):ℝ))|^N) = 0 := by
      have hz : ((((0:ℤ)):ℝ)) = 0 := Int.cast_zero
      rw [hz, abs_zero, zero_pow (by omega : N ≠ 0), div_zero, mul_zero]
    rw [h3, add_zero]
    linarith [hd, h1, h2]
  · rw [if_neg h0, zero_add]
    have hℓ1 : (1:ℝ) ≤ |(ℓ:ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h0
    have hly : |(ℓ:ℝ)| / 2 ≤ |(ℓ:ℝ) - y| := by
      have h1 : |(ℓ:ℝ)| - |y| ≤ |(ℓ:ℝ) - y| := abs_sub_abs_le_abs_sub _ _
      have h2 : |(ℓ:ℝ)| / 2 ≤ |(ℓ:ℝ)| - |y| := by linarith
      linarith
    have habs : |M₃ * ((ℓ:ℝ) - y)| = M₃ * |(ℓ:ℝ) - y| := by
      rw [abs_mul, abs_of_nonneg hM₃nn]
    have hd := hdec (M₃ * ((ℓ:ℝ) - y))
    rw [habs] at hd
    have hchain : M₃ * (|(ℓ:ℝ)|/2) ≤ 1 + M₃ * |(ℓ:ℝ) - y| := by
      have h3 : M₃ * (|(ℓ:ℝ)|/2) ≤ M₃ * |(ℓ:ℝ) - y| :=
        mul_le_mul_of_nonneg_left hly hM₃nn
      have h4 : (0:ℝ) ≤ M₃ * |(ℓ:ℝ) - y| := mul_nonneg hM₃nn (abs_nonneg _)
      linarith
    have hpos : (0:ℝ) < M₃ * (|(ℓ:ℝ)|/2) := by
      have hlt : (0:ℝ) < |(ℓ:ℝ)| := by linarith
      positivity
    have hpow : (M₃ * (|(ℓ:ℝ)|/2))^N ≤ (1 + M₃ * |(ℓ:ℝ) - y|)^N :=
      pow_le_pow_left₀ hpos.le hchain N
    have h1 : C / (1 + M₃ * |(ℓ:ℝ) - y|)^N ≤ C / (M₃*(|(ℓ:ℝ)|/2))^N :=
      div_le_div_of_nonneg_left hC (pow_pos hpos N) hpow
    have h2 : C / (M₃*(|(ℓ:ℝ)|/2))^N = (C*2^N/M₃^N) * (1/|(ℓ:ℝ)|^N) := by
      have h1 : M₃*(|(ℓ:ℝ)|/2) = M₃*|(ℓ:ℝ)|/2 := by ring
      have hM₃ne : M₃ ≠ 0 := ne_of_gt hM₃pos
      have hxne : |(ℓ:ℝ)| ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < |(ℓ:ℝ)|)
      rw [h1, div_pow, mul_pow]
      field_simp
    linarith [hd, h1, h2]

theorem tsum_norm_psi1hat_shift_pow_le {K : ℝ} {N : ℕ} (hN : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ z : ℝ, ‖psi1hat K z‖ ≤ C / (1 + |z|) ^ N)
    {M₃ y β : ℝ} (hM₃ : 1 ≤ M₃) (hy : |y| ≤ 1 / 2) (hβ : 0 < β) (hyβ : β ≤ M₃ * |y|) :
    (∑' ℓ : ℤ, ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖) ≤ C * ((1 / β) ^ N + 4 * 2 ^ N / M₃ ^ N) := by
  set F : ℤ → ℝ := fun ℓ => ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖ with hF
  set G : ℤ → ℝ := fun ℓ =>
      (if ℓ = 0 then C * (1 / β) ^ N else 0)
        + (C * 2 ^ N / M₃ ^ N) * (1 / |(ℓ:ℝ)| ^ N) with hG
  have hpt : ∀ ℓ : ℤ, F ℓ ≤ G ℓ := by
    intro ℓ
    rw [hF, hG]
    exact norm_psi1hat_shift_le hN hC hdec hM₃ hy hβ hyβ ℓ
  have hs1 : Summable (fun ℓ : ℤ => (if ℓ = 0 then C * (1/β)^N else 0)) :=
    summable_of_ne_finset_zero (s := {(0:ℤ)}) (by
      intro b hb
      simp only [Finset.mem_singleton] at hb
      rw [if_neg hb])
  have hs2 : Summable (fun ℓ : ℤ => (C * 2^N / M₃^N) * (1 / |(ℓ:ℝ)|^N)) :=
    (summable_int_inv_abs_pow hN).mul_left _
  have hGsumm : Summable G := by rw [hG]; exact hs1.add hs2
  have hFsumm : Summable F := Summable.of_nonneg_of_le (fun ℓ => norm_nonneg _) hpt hGsumm
  refine le_trans (Summable.tsum_le_tsum hpt hFsumm hGsumm) ?_
  have hval : (∑' ℓ : ℤ, G ℓ)
      = C * (1/β)^N + (C * 2^N / M₃^N) * (∑' ℓ : ℤ, (1 / |(ℓ:ℝ)|^N)) := by
    have hsplit : (∑' ℓ : ℤ, G ℓ)
        = (∑' ℓ : ℤ, (if ℓ = 0 then C * (1/β)^N else 0))
          + (∑' ℓ : ℤ, (C * 2^N / M₃^N) * (1 / |(ℓ:ℝ)|^N)) := by
      rw [hG]
      exact Summable.tsum_add hs1 hs2
    rw [hsplit, tsum_eq_single (0:ℤ) (by intro b hb; rw [if_neg hb]), tsum_mul_left,
      if_pos (rfl : (0:ℤ) = 0)]
  rw [hval]
  have hbig := tsum_int_inv_abs_pow_le hN
  have hcoef : (0:ℝ) ≤ C * 2^N / M₃^N := by
    have hM₃N : (0:ℝ) < M₃^N := pow_pos (by linarith) N
    positivity
  have h1 : (C * 2^N / M₃^N) * (∑' ℓ : ℤ, (1 / |(ℓ:ℝ)|^N))
      ≤ (C * 2^N / M₃^N) * 4 := mul_le_mul_of_nonneg_left hbig hcoef
  calc C * (1/β)^N + (C * 2^N / M₃^N) * (∑' ℓ : ℤ, (1 / |(ℓ:ℝ)|^N))
      ≤ C * (1/β)^N + (C * 2^N / M₃^N) * 4 := by linarith
    _ = C * ((1 / β) ^ N + 4 * 2 ^ N / M₃ ^ N) := by ring

end

end Work.GM.Affine
