import Mathlib
import Submission.Work.BMF.KfDefs
import Submission.Work.BMF.KfPrimeSum.sum_Icc_sigma_eq_sum_divisors
import Submission.Work.BMF.liouville.primesLE_sum_log_div_mul_pred_le_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Step A of `Work.BMF.halasz_Kbound`: the prime-sum reduction of `Kf`

`Kf f x = Σ_{n ≤ x} f n log n` is compared with `Σ_{p ≤ x} log p · f p · Mf f (x/p)` at the cost
of an absolute multiple of `x`, uniformly in the multiplicative `1`-bounded `f`.

The proof has four steps:

* `ArithmeticFunction.vonMangoldt_sum`, `log n = Σ_{d ∣ n} Λ d`, turns the sum over `n` into a sum
  over divisor pairs `n = d · m` (`Kf_eq_sum_vonMangoldt_Tf`, using the hyperbola reindexing
  `Work.BMF.KfPrimeSum.sum_Icc_sigma_eq_sum_divisors`);
* `Λ` vanishes off prime powers, so the `d`-sum is regrouped by prime powers
  (`Kf_vonMangoldt_regroup`);
* for each prime `p ≤ N` the sum `Σ_k Tf f N (p ^ k)` is compared with `f p · Σ_{m ≤ N/p} f m`
  with error `≤ 3N/(p(p-1))` (`Kf_primeSum_diff_le`);
* `Σ_{p ≤ N} log p/(p(p-1)) ≤ 2` sums the errors (`primeSum_const_le`).
-/

namespace Work.BMF

open Finset

/-- The number of multiples of `p` in `[1, Y]` is at most `Y / p`. -/
private lemma card_filter_dvd_Icc_le (p Y : ℕ) (hp : 0 < p) :
    ((Finset.Icc 1 Y).filter (fun m => p ∣ m)).card ≤ Y / p := by
  have hsub : Set.MapsTo (fun m : ℕ => m / p)
      ↑((Finset.Icc 1 Y).filter (fun m => p ∣ m)) ↑(Finset.Icc 1 (Y / p)) := by
    intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hm2⟩, hpd⟩ := hm
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hpd) hp, Nat.div_le_div_right hm2⟩
  have hinj : Set.InjOn (fun m : ℕ => m / p)
      ↑((Finset.Icc 1 Y).filter (fun m => p ∣ m)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have hab' : a / p = b / p := hab
    rw [← Nat.mul_div_cancel' ha.2, ← Nat.mul_div_cancel' hb.2, hab']
  calc ((Finset.Icc 1 Y).filter (fun m => p ∣ m)).card
      ≤ (Finset.Icc 1 (Y / p)).card := Finset.card_le_card_of_injOn _ hsub hinj
    _ = Y / p := by simp

/-- `Σ_{2 ≤ k ≤ K} p^{-k} ≤ 1/(p(p-1))` for `p ≥ 2`. -/
private lemma geom_Icc_two_inv_pow_le (p K : ℕ) (hp : 2 ≤ p) :
    (∑ k ∈ Finset.Icc 2 K, ((p : ℝ))⁻¹ ^ k) ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hx0 : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := by positivity
  have hx1 : ((p : ℝ))⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    linarith
  have hgeo := geom_sum_Ico_le_of_lt_one (x := ((p : ℝ))⁻¹) (m := 2) (n := K + 1) hx0 hx1
  refine hgeo.trans_eq ?_
  have h0 : ((p : ℝ)) ≠ 0 := by positivity
  have h1 : ((p : ℝ)) - 1 ≠ 0 := by linarith
  field_simp

/-- Per-prime comparison: for a prime `p ≤ N`,
`Σ_{k ≥ 1, p^k ≤ N} Tf f N (p^k)` differs from `f p · Σ_{m ≤ N/p} f m` by at most
`3N/(p(p-1))`.  Only multiplicativity on coprime arguments and `‖f‖ ≤ 1` are used. -/
private lemma Kf_primeSum_diff_le (f : ℕ → ℂ)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) (hb : ∀ n, ‖f n‖ ≤ 1)
    (N p : ℕ) (hp : p.Prime) (hpN : p ≤ N) :
    ‖(∑ k ∈ Finset.Icc 1 (Nat.log p N), Tf f N (p ^ k))
        - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m)‖
      ≤ 3 * (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  set K := Nat.log p N with hK
  have hp2 : 2 ≤ p := hp.two_le
  have hK1 : 1 ≤ K := by
    rw [hK]; exact Nat.log_pos hp.one_lt hpN
  have hsplit : (∑ k ∈ Finset.Icc 1 K, Tf f N (p ^ k))
      = Tf f N p + ∑ k ∈ Finset.Icc 2 K, Tf f N (p ^ k) := by
    rw [show Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp [Finset.mem_Icc])]
    simp
  have hT1 : Tf f N p - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m)
      = ∑ m ∈ Finset.Icc 1 (N / p), (f (p * m) - f p * f m) := by
    rw [Tf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hzero : ∀ m ∈ Finset.Icc 1 (N / p), ¬ p ∣ m → f (p * m) - f p * f m = 0 := by
    intro m hm hpm
    rw [hmul p m ((hp.coprime_iff_not_dvd).mpr hpm), sub_self]
  have h1 : ‖Tf f N p - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m)‖
      ≤ 2 * ((N : ℝ) / (p : ℝ) ^ 2) := by
    rw [hT1]
    have hcard := card_filter_dvd_Icc_le p (N / p) hp.pos
    calc ‖∑ m ∈ Finset.Icc 1 (N / p), (f (p * m) - f p * f m)‖
        ≤ ∑ m ∈ Finset.Icc 1 (N / p), ‖f (p * m) - f p * f m‖ := norm_sum_le _ _
      _ = ∑ m ∈ (Finset.Icc 1 (N / p)).filter (fun m => p ∣ m),
            ‖f (p * m) - f p * f m‖ := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro m hm hmnot
          have hpnm : ¬ p ∣ m := by
            intro hpd
            exact hmnot (Finset.mem_filter.mpr ⟨hm, hpd⟩)
          rw [hzero m hm hpnm]
          simp
      _ ≤ ∑ m ∈ (Finset.Icc 1 (N / p)).filter (fun m => p ∣ m), (2 : ℝ) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          have ha : ‖f (p * m) - f p * f m‖ ≤ ‖f (p * m)‖ + ‖f p * f m‖ := norm_sub_le _ _
          have hb1 : ‖f p * f m‖ ≤ 1 := by
            rw [norm_mul]
            nlinarith [hb p, hb m, norm_nonneg (f p), norm_nonneg (f m)]
          linarith [hb (p * m)]
      _ = 2 * (((Finset.Icc 1 (N / p)).filter (fun m => p ∣ m)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 2 * ((N / p / p : ℕ) : ℝ) := by
          have hc : ((((Finset.Icc 1 (N / p)).filter (fun m => p ∣ m)).card : ℕ) : ℝ)
              ≤ ((N / p / p : ℕ) : ℝ) := by
            exact_mod_cast hcard
          linarith
      _ ≤ 2 * ((N : ℝ) / (p : ℝ) ^ 2) := by
          have h2 : ((N / p / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 := by
            calc ((N / p / p : ℕ) : ℝ) ≤ ((N / p : ℕ) : ℝ) / (p : ℝ) := Nat.cast_div_le
              _ ≤ ((N : ℝ) / (p : ℝ)) / (p : ℝ) :=
                    div_le_div_of_nonneg_right Nat.cast_div_le (by positivity)
              _ = (N : ℝ) / (p : ℝ) ^ 2 := by ring
          linarith
  have htail : ‖∑ k ∈ Finset.Icc 2 K, Tf f N (p ^ k)‖
      ≤ (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    calc ‖∑ k ∈ Finset.Icc 2 K, Tf f N (p ^ k)‖
        ≤ ∑ k ∈ Finset.Icc 2 K, ‖Tf f N (p ^ k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Icc 2 K, ((N / p ^ k : ℕ) : ℝ) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [Tf]
          calc ‖∑ m ∈ Finset.Icc 1 (N / p ^ k), f (p ^ k * m)‖
              ≤ ∑ m ∈ Finset.Icc 1 (N / p ^ k), ‖f (p ^ k * m)‖ := norm_sum_le _ _
            _ ≤ ∑ m ∈ Finset.Icc 1 (N / p ^ k), (1 : ℝ) :=
                Finset.sum_le_sum (fun m hm => hb (p ^ k * m))
            _ = ((Finset.Icc 1 (N / p ^ k)).card : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ = ((N / p ^ k : ℕ) : ℝ) := by simp
      _ ≤ ∑ k ∈ Finset.Icc 2 K, (N : ℝ) * (((p : ℝ))⁻¹) ^ k := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hc := Nat.cast_div_le (α := ℝ) (m := N) (n := p ^ k)
          simp only [Nat.cast_pow] at hc
          rw [div_eq_mul_inv, ← inv_pow] at hc
          exact hc
      _ = (N : ℝ) * ∑ k ∈ Finset.Icc 2 K, (((p : ℝ))⁻¹) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ k ∈ Finset.Icc 2 K, (((p : ℝ))⁻¹) ^ k
              ≤ ∑ k ∈ Finset.Ico 2 (K + 1), (((p : ℝ))⁻¹) ^ k := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
                · intro x hx
                  simp only [Finset.mem_Icc] at hx
                  simp only [Finset.mem_Ico]
                  omega
                · intro x hx hxs
                  positivity
            _ ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := geom_Icc_two_inv_pow_le p K hp2
      _ = (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by ring
  have hfinal : 2 * ((N : ℝ) / (p : ℝ) ^ 2) + (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ 3 * (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    have hpR : (0 : ℝ) < (p : ℝ) := by positivity
    have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    have hle : (N : ℝ) / (p : ℝ) ^ 2 ≤ (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [div_le_div_iff₀ (show (0 : ℝ) < (p : ℝ) ^ 2 by positivity)
        (show (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) by positivity)]
      nlinarith [(show (0 : ℝ) ≤ (N : ℝ) by positivity), hpR, hpm1]
    have heq : 3 * (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        = 3 * ((N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by ring
    rw [heq]
    linarith
  rw [hsplit]
  calc ‖Tf f N p + (∑ k ∈ Finset.Icc 2 K, Tf f N (p ^ k))
          - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m)‖
      = ‖(Tf f N p - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m))
          + (∑ k ∈ Finset.Icc 2 K, Tf f N (p ^ k))‖ := by
        congr 1; ring
    _ ≤ ‖Tf f N p - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m)‖
          + ‖∑ k ∈ Finset.Icc 2 K, Tf f N (p ^ k)‖ := norm_add_le _ _
    _ ≤ 3 * (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        linarith [h1, htail, hfinal]

/-- Regrouping the von-Mangoldt weighted sum by prime powers: `Λ` vanishes off prime powers,
and `Λ (p^k) = log p`. -/
private lemma Kf_vonMangoldt_regroup (f : ℕ → ℂ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * Tf f N d)
      = ∑ p ∈ N.primesLE, (Real.log (p : ℝ) : ℂ) *
          ∑ k ∈ Finset.Icc 1 (Nat.log p N), Tf f N (p ^ k) := by
  have h1 : (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * Tf f N d)
      = ∑ d ∈ ((Finset.Icc 1 N).filter IsPrimePow),
          ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * Tf f N d := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x hx hxn
    have hΛ : ArithmeticFunction.vonMangoldt x = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
      exact fun hpp => hxn (Finset.mem_filter.mpr ⟨hx, hpp⟩)
    simp [hΛ]
  have heq : (Finset.Icc 1 N).filter IsPrimePow
      = ((Finset.Icc 1 N).filter Nat.Prime).biUnion
          (fun p => (Finset.Icc 1 (Nat.log p N)).image (p ^ ·)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd1, hd2⟩, hpp⟩
      obtain ⟨p, k, hpprime, hkpos, rfl⟩ := (isPrimePow_nat_iff d).mp hpp
      refine ⟨p, ⟨⟨hpprime.one_le, ?_⟩, hpprime⟩, k, ⟨hkpos, ?_⟩, rfl⟩
      · exact (Nat.le_self_pow hkpos.ne' p).trans hd2
      · exact Nat.le_log_of_pow_le hpprime.one_lt hd2
    · rintro ⟨p, ⟨⟨hp1, hpN⟩, hpprime⟩, k, ⟨hk1, hklog⟩, rfl⟩
      refine ⟨⟨one_le_pow₀ hpprime.one_le, ?_⟩, ?_⟩
      · exact Nat.pow_le_of_le_log (by omega) hklog
      · exact (isPrimePow_nat_iff (p ^ k)).mpr ⟨p, k, hpprime, hk1, rfl⟩
  have hdisj : (((Finset.Icc 1 N).filter Nat.Prime : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun p => (Finset.Icc 1 (Nat.log p N)).image (p ^ ·)) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro p hp q hq hne
    obtain ⟨x, hx⟩ := hne
    rw [Finset.mem_inter, Finset.mem_image, Finset.mem_image] at hx
    obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hxb⟩⟩ := hx
    rw [Finset.mem_Icc] at ha hb
    exact (Nat.Prime.pow_inj' (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
      (by omega) (by omega) hxb.symm).1
  rw [h1, heq, Finset.sum_biUnion hdisj, Nat.primesLE_eq_filter_Icc_one N]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hinj : Set.InjOn (fun k => p ^ k) ↑(Finset.Icc 1 (Nat.log p N)) := by
    intro a _ b _ hab
    exact Nat.pow_right_injective (Finset.mem_filter.mp hp).2.two_le hab
  rw [Finset.sum_image hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkne : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  rw [ArithmeticFunction.vonMangoldt_apply_pow hkne,
    ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]

/-- `log n = Σ_{d ∣ n} Λ d` turns `Σ_{n ≤ N} f n log n` into a double sum over divisor pairs
`n = d * m`; the inner reindexing is `KfPrimeSum.sum_Icc_sigma_eq_sum_divisors`. -/
lemma Kf_eq_sum_vonMangoldt_Tf (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n * (Real.log n : ℂ))
      = ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * Tf f N d := by
  have hA := KfPrimeSum.sum_Icc_sigma_eq_sum_divisors
    (fun d m => ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * f (d * m)) N
  have hR : (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * Tf f N d)
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
          ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * f (d * m) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Tf, Finset.mul_sum]
  rw [hR, hA]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hlog : (Real.log n : ℂ)
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) := by
    rw [← ArithmeticFunction.vonMangoldt_sum (n := n)]
    push_cast
    rfl
  rw [hlog, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  rw [Nat.mul_div_cancel' hdvd]
  ring

/-- The total error accumulated over all primes: `Σ_{p ≤ N} log p · 3N/(p(p-1)) ≤ 6N`
(using `Σ_p log p/(p(p-1)) ≤ 2`). -/
lemma primeSum_const_le (N : ℕ) :
    (∑ p ∈ N.primesLE, Real.log (p : ℝ) * (3 * (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))))
      ≤ 6 * (N : ℝ) := by
  have hb := Work.BMF.liouville.primesLE_sum_log_div_mul_pred_le_two N
  have h1 : (∑ p ∈ N.primesLE, Real.log (p : ℝ) * (3 * (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))))
      = 3 * (N : ℝ) * ∑ p ∈ N.primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    ring
  rw [h1]
  have h2 : 3 * (N : ℝ) * ∑ p ∈ N.primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ 3 * (N : ℝ) * 2 := mul_le_mul_of_nonneg_left hb (by positivity)
  linarith

/-- STEP A of the proof of `Work.BMF.halasz_Kbound`, with the constant quantified first
(so that it is uniform in `f`): for `f` multiplicative with `f 1 = 1` and `‖f n‖ ≤ 1`, the sum
`Work.BMF.Kf f x = Σ_{n ≤ x} f n * log n` agrees with `Σ_{p ≤ x} log p * f p * Mf f (x/p)`
up to an absolute multiple of `x`.
Route: `log n = Σ_p v_p(n) log p`, swap the sums, and for each prime `p` telescope
`T_k := Σ_{m ≤ x/p^k} f (m p^k)` using `T_k - T_{k+1} = f(p^k) * Σ_{m ≤ x/p^k, p ∤ m} f m`
(multiplicativity, `p^k` coprime to `m`); the `p ∤ m` restriction is then removed at the cost
of `O(x/p^{k+1})`, the prime powers `k ≥ 2` cost `O(x log p/p^k)` and `Σ_p log p/(p(p-1)) < ∞`,
so the constant is `≤ 5` uniformly in `f` (only `‖f n‖ ≤ 1` is used). -/
theorem Kf_primeSum_reduction_abs :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x : ℝ, 2 ≤ x →
        ‖Work.BMF.Kf f x - ∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Work.BMF.Mf f (x / p)‖
          ≤ C * x := by
  refine ⟨10, by norm_num, ?_⟩
  intro f hf1 hmul hb x hx
  set N := ⌊x⌋₊ with hN
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hxN : (N : ℝ) ≤ x := by
    rw [hN]; exact Nat.floor_le hx0
  have hp1 : ∀ p ∈ N.primesLE, (1 : ℝ) ≤ p := by
    intro p hp
    exact_mod_cast Nat.Prime.one_le (Nat.prime_of_mem_primesLE hp)
  have hKf : Kf f x = ∑ p ∈ N.primesLE, (Real.log (p : ℝ) : ℂ) *
      ∑ k ∈ Finset.Icc 1 (Nat.log p N), Tf f N (p ^ k) := by
    have h1 : Kf f x = ∑ n ∈ Finset.Icc 1 N, f n * (Real.log n : ℂ) := by
      rw [Kf, ← hN]
    rw [h1, Kf_eq_sum_vonMangoldt_Tf f N]
    exact Kf_vonMangoldt_regroup f N
  have hMf : ∀ p : ℕ, Mf f (x / p) = ∑ m ∈ Finset.Icc 1 (N / p), f m := by
    intro p
    rw [Mf, Nat.floor_div_natCast, ← hN]
  have key : Kf f x - ∑ p ∈ N.primesLE, (Real.log (p : ℝ) : ℂ) * f p * Mf f (x / p)
      = ∑ p ∈ N.primesLE, (Real.log (p : ℝ) : ℂ) *
          ((∑ k ∈ Finset.Icc 1 (Nat.log p N), Tf f N (p ^ k))
            - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m)) := by
    rw [hKf]
    simp only [hMf]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun p hp => by ring)
  rw [key]
  calc ‖∑ p ∈ N.primesLE, (Real.log (p : ℝ) : ℂ) *
          ((∑ k ∈ Finset.Icc 1 (Nat.log p N), Tf f N (p ^ k))
            - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m))‖
      ≤ ∑ p ∈ N.primesLE, ‖(Real.log (p : ℝ) : ℂ) *
          ((∑ k ∈ Finset.Icc 1 (Nat.log p N), Tf f N (p ^ k))
            - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m))‖ := norm_sum_le _ _
    _ = ∑ p ∈ N.primesLE, Real.log (p : ℝ) * ‖(∑ k ∈ Finset.Icc 1 (Nat.log p N), Tf f N (p ^ k))
            - f p * (∑ m ∈ Finset.Icc 1 (N / p), f m)‖ := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [norm_mul, Complex.norm_of_nonneg (Real.log_nonneg (hp1 p hp))]
    _ ≤ ∑ p ∈ N.primesLE, Real.log (p : ℝ) * (3 * (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        exact mul_le_mul_of_nonneg_left
          (Kf_primeSum_diff_le f hmul hb N p (Nat.prime_of_mem_primesLE hp)
            (Nat.le_of_mem_primesLE hp))
          (Real.log_nonneg (hp1 p hp))
    _ ≤ 6 * (N : ℝ) := primeSum_const_le N
    _ ≤ 10 * x := by linarith

end Work.BMF
