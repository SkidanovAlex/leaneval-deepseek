import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.NumberTheory.Moebius.sum_moebius_primeFactors_ge

namespace Commons.NumberTheory.Sieve

open Finset

/-- The multiples of `n` in `[1, N]` number `N / n`. -/
private lemma card_multiples_Icc (N n : ℕ) :
    ((Finset.Icc 1 N).filter (fun k => n ∣ k)).card = N / n := by
  have hset : (Finset.Icc 1 N).filter (fun k => n ∣ k)
      = (Finset.range N.succ).filter (fun k => k ≠ 0 ∧ n ∣ k) := by
    apply Finset.ext
    intro k
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by omega, by omega, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, by omega⟩, h3⟩
  rw [hset, Nat.card_multiples']

/-- Möbius sums over `z`-rough numbers: for `2 ≤ z` and `2 ≤ w`,
`|∑ μ(n)/n| ≤ 2` where `n` runs over the integers `1 ≤ n ≤ ⌊w⌋` all of whose prime
factors are `≥ z`.

The proof doubles-counts `w·S = Σ_{n rough} μ(n)·⌊w/n⌋ + (error)`: the first term
equals the number of `z`-smooth integers `≤ ⌊w⌋` (via
`sum_moebius_primeFactors_ge`), which is `≤ ⌊w⌋`, while the error is a sum of
fractional parts, bounded by the number of rough integers `≤ ⌊w⌋ ≤ ⌊w⌋`.  Hence
`|w·S| ≤ 2⌊w⌋ ≤ 2w`. -/
theorem moebius_rough_recip_abs_le_two :
    ∀ z w : ℝ, 2 ≤ z → 2 ≤ w →
      |∑ n ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ)),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 2 := by
  intro z w hz hw
  classical
  set N : ℕ := ⌊w⌋₊ with hN
  have hwpos : (0:ℝ) < w := by linarith
  have hN2 : 2 ≤ N := by rw [hN]; exact Nat.le_floor hw
  set RF : Finset ℕ :=
    (Finset.Icc 1 N).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ)) with hRF
  set SmF : Finset ℕ :=
    (Finset.Icc 1 N).filter (fun m => ∀ p : ℕ, p ∈ m.primeFactors → (p : ℝ) < z) with hSmF
  have hRF_sub : RF ⊆ Finset.Icc 1 N := by rw [hRF]; exact Finset.filter_subset _ _
  have hSmF_sub : SmF ⊆ Finset.Icc 1 N := by rw [hSmF]; exact Finset.filter_subset _ _
  have hmemRF : ∀ n ∈ RF, 1 ≤ n ∧ n ≤ N := by
    intro n hn
    have h := hRF_sub hn
    rw [Finset.mem_Icc] at h
    exact h
  -- Double-count the `⌊w/n⌋`'s: the Möbius-weighted count of rough divisors of `k`
  -- is `1` exactly when `k` is `z`-smooth.
  have hStepD :
      (∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) * ((N / n : ℕ) : ℝ)) = (SmF.card : ℝ) := by
    have key : ∀ n ∈ RF, ((N / n : ℕ) : ℝ)
        = ∑ k ∈ (Finset.Icc 1 N).filter (fun k => n ∣ k), (1:ℝ) := by
      intro n hn
      rw [Finset.sum_const, card_multiples_Icc]; simp
    calc (∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) * ((N / n : ℕ) : ℝ))
        = ∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ)
            * ∑ k ∈ (Finset.Icc 1 N).filter (fun k => n ∣ k), (1:ℝ) := by
          apply Finset.sum_congr rfl; intro n hn; rw [key n hn]
      _ = ∑ n ∈ RF, ∑ k ∈ (Finset.Icc 1 N).filter (fun k => n ∣ k),
            (ArithmeticFunction.moebius n : ℝ) := by
          apply Finset.sum_congr rfl; intro n hn
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk; ring
      _ = ∑ n ∈ RF, ∑ k ∈ Finset.Icc 1 N,
            (if n ∣ k then (ArithmeticFunction.moebius n : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro n hn; rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ RF,
            (if n ∣ k then (ArithmeticFunction.moebius n : ℝ) else 0) :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.Icc 1 N,
            (if (∀ p : ℕ, p ∈ k.primeFactors → (p:ℝ) < z) then (1:ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro k hk
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
          have hk0 : k ≠ 0 := by omega
          have hfilter : RF.filter (fun n => n ∣ k)
              = k.divisors.filter (fun d => ∀ p : ℕ, p ∈ d.primeFactors → z ≤ (p : ℝ)) := by
            apply Finset.ext
            intro n
            rw [Finset.mem_filter, hRF, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter,
              Nat.mem_divisors]
            constructor
            · rintro ⟨⟨⟨hn1, hnN⟩, hr⟩, hdvd⟩
              exact ⟨⟨hdvd, hk0⟩, hr⟩
            · rintro ⟨⟨hdvd, _⟩, hr⟩
              have hn1 : 1 ≤ n := by
                rcases Nat.eq_zero_or_pos n with h0 | h0
                · subst h0; obtain ⟨c, hc⟩ := hdvd; omega
                · exact h0
              have hnN : n ≤ N := le_trans (Nat.le_of_dvd (by omega) hdvd) hkN
              exact ⟨⟨⟨hn1, hnN⟩, hr⟩, hdvd⟩
          rw [← Finset.sum_filter, hfilter]
          exact Commons.NumberTheory.Moebius.sum_moebius_primeFactors_ge z k hk0
      _ = (SmF.card : ℝ) := by
          rw [hSmF, Finset.sum_boole]
  -- `w·S = Σ μ(n)·w/n`
  have h1 : w * (∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))
      = ∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) * (w / (n : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, _⟩ := hmemRF n hn
    have hn0 : (n:ℝ) ≠ 0 := by positivity
    field_simp
  have h2 : (∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) * (w / (n : ℝ)))
      = (∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) * ((N / n : ℕ) : ℝ))
        + (∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ)
            * (w / (n:ℝ) - ((N / n : ℕ) : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  -- the fractional parts are in `[0,1)`
  have hfrac : ∀ n ∈ RF, (0:ℝ) ≤ w / (n:ℝ) - ((N / n : ℕ) : ℝ)
      ∧ w / (n:ℝ) - ((N / n : ℕ) : ℝ) < 1 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := hmemRF n hn
    have hfl : ⌊w / (n:ℝ)⌋₊ = N / n := by rw [hN]; exact Nat.floor_div_natCast w n
    have hcast : ((N / n : ℕ) : ℝ) = ⌊w / (n:ℝ)⌋₊ := by rw [hfl]
    have hnonneg : 0 ≤ w / (n:ℝ) := by positivity
    constructor
    · rw [hcast]; exact sub_nonneg.mpr (Nat.floor_le hnonneg)
    · rw [hcast]; have := Nat.lt_floor_add_one (w / (n:ℝ)); linarith
  have hT2 : |∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ)
      * (w / (n:ℝ) - ((N / n : ℕ) : ℝ))| ≤ (N:ℝ) := by
    calc |∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ)
            * (w / (n:ℝ) - ((N / n : ℕ) : ℝ))|
        ≤ ∑ n ∈ RF, |(ArithmeticFunction.moebius n : ℝ)
            * (w / (n:ℝ) - ((N / n : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ RF, (w / (n:ℝ) - ((N / n : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [abs_mul]
          obtain ⟨hf0, hf1⟩ := hfrac n hn
          have hmu := ArithmeticFunction.abs_moebius_le_one (n := n)
          have hmuR : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
            rw [← Int.cast_abs]; exact_mod_cast hmu
          rw [abs_of_nonneg hf0]
          exact mul_le_mul_of_nonneg_right hmuR hf0 |>.trans_eq (one_mul _)
      _ ≤ ∑ n ∈ RF, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          exact le_of_lt (hfrac n hn).2
      _ = (RF.card : ℝ) := by simp
      _ ≤ (N:ℝ) := by
          have hc : RF.card ≤ N := by
            have h := Finset.card_le_card hRF_sub
            rw [Nat.card_Icc] at h; omega
          exact_mod_cast hc
  have hwS : w * (∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))
      = (SmF.card : ℝ)
        + ∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ)
            * (w / (n:ℝ) - ((N / n : ℕ) : ℝ)) := by
    rw [h1, h2, hStepD]
  have hSmFle : (SmF.card : ℝ) ≤ (N:ℝ) := by
    have hc : SmF.card ≤ N := by
      have h := Finset.card_le_card hSmF_sub
      rw [Nat.card_Icc] at h; omega
    exact_mod_cast hc
  have hkey : |w * (∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))| ≤ 2 * w := by
    rw [hwS]
    have hfirst : |(SmF.card:ℝ) + ∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ)
            * (w / (n:ℝ) - ((N / n : ℕ) : ℝ))|
        ≤ (SmF.card:ℝ) + |∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ)
            * (w / (n:ℝ) - ((N / n : ℕ) : ℝ))| := by
      have h := abs_add_le (SmF.card:ℝ)
        (∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) * (w / (n:ℝ) - ((N / n : ℕ) : ℝ)))
      rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ (SmF.card:ℝ))] at h
    calc |(SmF.card:ℝ) + ∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ)
            * (w / (n:ℝ) - ((N / n : ℕ) : ℝ))|
        ≤ (SmF.card:ℝ) + |∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ)
            * (w / (n:ℝ) - ((N / n : ℕ) : ℝ))| := hfirst
      _ ≤ (N:ℝ) + (N:ℝ) := add_le_add hSmFle hT2
      _ = 2*(N:ℝ) := by ring
      _ ≤ 2*w := by
          have : (N:ℝ) ≤ w := by rw [hN]; exact Nat.floor_le (le_of_lt hwpos)
          linarith
  have hS : |∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 2 := by
    rw [abs_mul, abs_of_pos hwpos] at hkey
    have h2w : w * |∑ n ∈ RF, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ w * 2 := by
      linarith
    exact le_of_mul_le_mul_left h2w hwpos
  exact hS

end Commons.NumberTheory.Sieve