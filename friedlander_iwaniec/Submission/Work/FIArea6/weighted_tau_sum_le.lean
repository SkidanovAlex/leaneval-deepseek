import Mathlib
import Submission.Work.FIArea6.prime_recip_sum_le

/-!
# `Work.FIArea6.weighted_tau_sum_le`

The elementary average bound

`∑_{d ∈ s} 2^{7 ω(d)} / d ≤ (log Y + 1) · exp (4000 (log log Y + 1))`

for any finite set `s` of naturals with `d ≤ Y`.  The true size of the sum is
`≍ (log Y)^{2^7}`; the (deliberately) enormous constant `4000` leaves ample room.

The proof is the classical Euler-product bound: `2^{7ω(·)}/·` is multiplicative on coprime
arguments and its Euler product is

`∏_{p ≤ Y} (1 + 128/(p-1))`,

whose logarithm is at most `256 · log log Y + O(1)` by the first Mertens theorem
(`Work.FIArea6.primeRecips_upper`, imported here).
-/

namespace Work.FIArea6

open Nat Finset
open scoped BigOperators

noncomputable section

/-- The multiplicative weight `wτ(n) = 2^{7 ω(n)}/n`. -/
private def wtau (n : ℕ) : ℝ := (2 : ℝ) ^ (7 * n.primeFactors.card) / (n : ℝ)

private lemma wtau_zero : wtau 0 = 0 := by simp [wtau]

private lemma wtau_one : wtau 1 = 1 := by simp [wtau]

private lemma wtau_nonneg (n : ℕ) : 0 ≤ wtau n :=
  div_nonneg (by positivity) (Nat.cast_nonneg n)

private lemma wtau_mul {m n : ℕ} (h : Nat.Coprime m n) : wtau (m * n) = wtau m * wtau n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [wtau]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [wtau]
  have hcard : (m * n).primeFactors.card = m.primeFactors.card + n.primeFactors.card := by
    rw [Nat.primeFactors_mul hm hn, Finset.card_union_of_disjoint h.disjoint_primeFactors]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [wtau, hcard, Nat.cast_mul]
  rw [show (7 : ℕ) * (m.primeFactors.card + n.primeFactors.card)
      = 7 * m.primeFactors.card + 7 * n.primeFactors.card by ring, pow_add]
  field_simp

/-- The local factor `∑_e wτ(p^e)` is summable for every prime `p`. -/
private lemma wtau_local_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun n : ℕ => ‖wtau (p ^ n)‖) := by
  have hg : Summable (fun n : ℕ => 128 * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left 128
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hb : ∀ n : ℕ, ‖wtau (p ^ n)‖ ≤ 128 * (1 / 2 : ℝ) ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [wtau]
    · have hpf : (p ^ n).primeFactors = {p} := Nat.primeFactors_prime_pow (by omega) hp
      have hval : wtau (p ^ n) = 128 * (1 / (p : ℝ)) ^ n := by
        rw [wtau, hpf, Finset.card_singleton, Nat.cast_pow]
        rw [show (2 : ℝ) ^ (7 * 1) = 128 by norm_num, div_eq_mul_inv, one_div, inv_pow]
      have hnn : 0 ≤ 128 * (1 / (p : ℝ)) ^ n := by positivity
      rw [hval, Real.norm_of_nonneg hnn]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact pow_le_pow_left₀ (by positivity)
        ((one_div_le_one_div hp0 (by norm_num : (0:ℝ) < 2)).mpr hp2) n
  exact (Summable.of_norm_bounded hg hb).norm

/-- The value of the local Euler factor: `∑_e wτ(p^e) = 1 + 128/(p-1)`. -/
private lemma wtau_tsum_prime {p : ℕ} (hp : p.Prime) :
    (∑' n : ℕ, wtau (p ^ n)) = 1 + 128 / ((p : ℝ) - 1) := by
  have hsumm : Summable (fun n : ℕ => wtau (p ^ n)) := (wtau_local_summable hp).of_norm
  rw [hsumm.tsum_eq_zero_add]
  have h0 : wtau (p ^ 0) = 1 := by rw [pow_zero]; exact wtau_one
  rw [h0]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hterm : ∀ b : ℕ, wtau (p ^ (b + 1)) = 128 * (1 / (p : ℝ)) * (1 / (p : ℝ)) ^ b := by
    intro b
    have hpf : (p ^ (b + 1)).primeFactors = {p} := Nat.primeFactors_prime_pow (by omega) hp
    have hnn : 0 ≤ 128 * (1 / (p : ℝ)) * (1 / (p : ℝ)) ^ b := by positivity
    rw [wtau, hpf, Finset.card_singleton, Nat.cast_pow]
    rw [show (2 : ℝ) ^ (7 * 1) = 128 by norm_num, div_eq_mul_inv, one_div, inv_pow]
    rw [pow_succ]
    ring
  have hgeom : (∑' b : ℕ, (1 / (p : ℝ)) ^ b) = (1 - 1 / (p : ℝ))⁻¹ :=
    tsum_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_lt_one hp0]
      exact_mod_cast hp.one_lt)
  rw [show (∑' b : ℕ, wtau (p ^ (b + 1)))
        = ∑' b : ℕ, 128 * (1 / (p : ℝ)) * (1 / (p : ℝ)) ^ b from tsum_congr hterm,
      tsum_mul_left, hgeom]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  field_simp

/-- A finite initial segment of a nonnegative sequence is at most its sum over the smooth
numbers. -/
private lemma sum_range_le_tsum_smooth (N : ℕ) (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hfnn : ∀ n, 0 ≤ f n) (hsumm : Summable (fun m : N.smoothNumbers => f m)) :
    ∑ n ∈ Finset.range N, f n ≤ ∑' m : N.smoothNumbers, f m := by
  have hgs : Summable (N.smoothNumbers.indicator f) := by
    rw [← summable_subtype_iff_indicator]
    exact hsumm
  have heq : (∑ n ∈ Finset.range N, N.smoothNumbers.indicator f n)
      = ∑ n ∈ Finset.range N, f n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    rw [Set.indicator_apply]
    by_cases hns : n ∈ N.smoothNumbers
    · rw [if_pos hns]
    · rw [if_neg hns]
      have hn0 : n = 0 := by
        by_contra h
        exact hns (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero h) hn)
      rw [hn0, hf0]
  have hle : ∑ n ∈ Finset.range N, N.smoothNumbers.indicator f n
      ≤ ∑' n, N.smoothNumbers.indicator f n :=
    hgs.sum_le_tsum (Finset.range N) (fun i _ => Set.indicator_nonneg (fun a _ => hfnn a) i)
  rw [heq, ← tsum_subtype N.smoothNumbers f] at hle
  exact hle

/-- Numeric input: `log log x ≥ -1/2` for `x ≥ 2`. -/
private lemma log_log_ge_neg_half {x : ℝ} (hx : 2 ≤ x) :
    -(1 / 2 : ℝ) ≤ Real.log (Real.log x) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hpos2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hposx : 0 < Real.log x := Real.log_pos hx1
  have hmono : Real.log (Real.log 2) ≤ Real.log (Real.log x) := Real.log_le_log hpos2 hlogx
  have hlog23 : Real.log (2 / 3 : ℝ) ≤ Real.log (Real.log 2) :=
    Real.log_le_log (by norm_num) hlog2
  have h3 : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2) := by
    rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  have hexp : Real.log (3 / 2 : ℝ) ≤ 1 / 2 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 3 / 2)
      (show (3 / 2 : ℝ) ≤ Real.exp (1 / 2) by
        have := Real.add_one_le_exp (1 / 2 : ℝ); linarith)
    rwa [Real.log_exp] at h
  linarith

/-- The Euler product of the weight, bounded by `exp (256 (log log Y + O(1)))`. -/
private lemma prod_primesLE_le (Y : ℕ) (hY : 2 ≤ Y) :
    (∏ p ∈ Nat.primesLE Y, (1 + 128 / ((p : ℝ) - 1)))
      ≤ Real.exp (256 * (Real.log (Real.log Y) + (1 - Real.log (Real.log 2)))) := by
  have hY2 : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hrec : Commons.NumberTheory.Mertens.primeRecips (Y : ℝ)
      = ∑ p ∈ Nat.primesLE Y, (1 : ℝ) / (p : ℝ) := by
    simp only [Commons.NumberTheory.Mertens.primeRecips, Nat.floor_natCast]
  calc (∏ p ∈ Nat.primesLE Y, (1 + 128 / ((p : ℝ) - 1)))
      ≤ ∏ p ∈ Nat.primesLE Y, Real.exp (128 / ((p : ℝ) - 1)) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
          have : 0 ≤ 128 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
          linarith
        · intro p hp
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
          have hx : 0 ≤ 128 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
          linarith [Real.add_one_le_exp (128 / ((p : ℝ) - 1))]
    _ = Real.exp (∑ p ∈ Nat.primesLE Y, 128 / ((p : ℝ) - 1)) := by rw [Real.exp_sum]
    _ ≤ Real.exp (∑ p ∈ Nat.primesLE Y, 256 / (p : ℝ)) := by
        apply Real.exp_le_exp.mpr
        apply Finset.sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < (p:ℝ) - 1) (by linarith : (0:ℝ) < (p:ℝ))]
        nlinarith
    _ = Real.exp (256 * ∑ p ∈ Nat.primesLE Y, (1 : ℝ) / (p : ℝ)) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [one_div, div_eq_mul_inv]
    _ ≤ Real.exp (256 * (Real.log (Real.log Y) + (1 - Real.log (Real.log 2)))) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [← hrec]
        exact primeRecips_upper hY2

theorem weighted_tau_sum_le (Y : ℕ) (hY : 2 ≤ Y) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ≤ Y) :
    (∑ d ∈ s, (2 : ℝ) ^ (7 * d.primeFactors.card) / (d : ℝ))
      ≤ (Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1)) := by
  have hY2 : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by linarith
  obtain ⟨hSmmNorm, hHasSum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (R := ℝ) (f := wtau) wtau_one (fun {m n} h => wtau_mul h)
      (fun {p} hp => wtau_local_summable hp) (Y + 1)
  have hSmm : Summable (fun m : (Y + 1).smoothNumbers => wtau m) := hSmmNorm.of_norm
  have htsum : (∑' m : (Y + 1).smoothNumbers, wtau m)
      = ∏ p ∈ Nat.primesLE Y, (1 + 128 / ((p : ℝ) - 1)) := by
    rw [hHasSum.tsum_eq]
    apply Finset.prod_congr rfl
    intro p hp
    exact wtau_tsum_prime (Nat.mem_primesBelow.mp hp).2
  have hsub : s.filter (fun d => 0 < d) ⊆ Finset.range (Y + 1) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_range]
    have := hs d hd.1
    omega
  have hsplit : (∑ d ∈ s.filter (fun d => 0 < d), wtau d) = ∑ d ∈ s, wtau d := by
    apply Finset.sum_subset
    · intro d hd; rw [Finset.mem_filter] at hd; exact hd.1
    · intro d hd hnot
      have hle : ¬ (0 < d) := by
        intro h
        exact hnot (by rw [Finset.mem_filter]; exact ⟨hd, h⟩)
      have hd0 : d = 0 := by omega
      rw [hd0, wtau_zero]
  calc (∑ d ∈ s, (2 : ℝ) ^ (7 * d.primeFactors.card) / (d : ℝ))
      = ∑ d ∈ s, wtau d := by simp only [wtau]
    _ = ∑ d ∈ s.filter (fun d => 0 < d), wtau d := hsplit.symm
    _ ≤ ∑ d ∈ Finset.range (Y + 1), wtau d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => wtau_nonneg i)
    _ ≤ ∑' m : (Y + 1).smoothNumbers, wtau m :=
        sum_range_le_tsum_smooth (Y + 1) wtau wtau_zero wtau_nonneg hSmm
    _ = ∏ p ∈ Nat.primesLE Y, (1 + 128 / ((p : ℝ) - 1)) := htsum
    _ ≤ Real.exp (256 * (Real.log (Real.log Y) + (1 - Real.log (Real.log 2)))) :=
        prod_primesLE_le Y hY
    _ ≤ (Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1)) := by
        have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg hY1
        have hone : (1 : ℝ) ≤ Real.log (Y : ℝ) + 1 := by linarith
        have hL := log_log_ge_neg_half hY2
        have hL2 := log_log_ge_neg_half (show (2 : ℝ) ≤ 2 by norm_num)
        have hAB : 256 * (Real.log (Real.log (Y : ℝ)) + (1 - Real.log (Real.log 2)))
            ≤ 4000 * (Real.log (Real.log (Y : ℝ)) + 1) := by nlinarith [hL, hL2]
        have hexp : Real.exp (256 * (Real.log (Real.log (Y : ℝ)) + (1 - Real.log (Real.log 2))))
            ≤ Real.exp (4000 * (Real.log (Real.log (Y : ℝ)) + 1)) := Real.exp_le_exp.mpr hAB
        have hBnn : 0 ≤ Real.exp (4000 * (Real.log (Real.log (Y : ℝ)) + 1)) := Real.exp_nonneg _
        nlinarith [hexp, hone, hBnn, hlogY]

end

end Work.FIArea6
