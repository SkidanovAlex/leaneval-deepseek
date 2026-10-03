/-
  Companion paper, §9: the `(R′₃)` step for the Friedlander–Iwaniec sequence.

  The companion derives `(R′₃)` from `(R₃)` by Cauchy–Schwarz with the `τ^{10}`-weighted `(1.7)`
  bound.  For X² + Y⁴ the paper's `(1.6)` (hence its `τ^{10}`-bound) is FALSE — the local density
  at `p⁴` beats `d^{−1}τ(d)^8` — so we use the trivial split instead:

      `τ(d)|r_d| ≤ |r_d| + τ(d)·(A_d(t) + g(d)A(t))`,

  whose three pieces are exactly `(R₃)`, the `τ^8`-reduction into the cube range
  (`(2τ)^{40}`-weighted aggregate of `S25`), and the crude `τ`-count.
-/
import Mathlib
import Submission.ASP.S33
import Submission.ASP.S25
import Submission.ASP.S32
import Submission.ASP.S9b
import Submission.Commons.NumberTheory.DivisorSum.sum_mul_tau_pow_eight_le_cube
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_ncard_prime_pow_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_ncard_prime_pow_sqrt
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_prime_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Commons.NumberTheory.FriedlanderIwaniec.gdens_le_one
import Submission.Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 3200000

namespace Submission.ASP

open Finset

noncomputable section

/-- The pointwise bound `|FIr d t| ≤ A_d(t) + g(d)·A(t)`. -/
lemma FIr_abs_le_Ad (d t : ℕ) :
    |FIr d t| ≤ Ad FIa d t + FIg d * Acount FIa t :=
  abs_r_le FIa FIg FIr t FIa_nonneg (fun n => FIg_nonneg n) (FI_approx (t : ℝ)) d

/-- `FIg d ≤ 1`. -/
lemma FIg_le_one (d : ℕ) : FIg d ≤ 1 := by
  rw [FIg]
  have := Commons.NumberTheory.FriedlanderIwaniec.gdens_le_one d
  exact_mod_cast this

/-- The `τ`-weighted sum of the congruence sums `A_d(t)`: exchange the `d`- and `n`-sums and
apply `∑_{d ∣ n} τ(d) ≤ τ(n)^2`. -/
lemma sum_tau_Ad_le (t Y : ℕ) :
    (∑ k ∈ Finset.Icc 1 Y, (k.divisors.card : ℝ) * Ad FIa k t)
      ≤ ∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (2 : ℕ) := by
  have h1 : ∀ k : ℕ, Ad FIa k t
      = ∑ n ∈ (Finset.Icc 1 t).filter (fun n => k ∣ n), FIa n := by
    intro k; rw [Ad, Nat.floor_natCast]
  have hA : (∑ k ∈ Finset.Icc 1 Y, (k.divisors.card : ℝ) * Ad FIa k t)
      = ∑ n ∈ Finset.Icc 1 t, FIa n * (∑ k ∈ (Finset.Icc 1 Y).filter (fun k => k ∣ n),
          (k.divisors.card : ℝ)) := by
    calc (∑ k ∈ Finset.Icc 1 Y, (k.divisors.card : ℝ) * Ad FIa k t)
        = ∑ k ∈ Finset.Icc 1 Y, ∑ n ∈ (Finset.Icc 1 t).filter (fun n => k ∣ n),
            (k.divisors.card : ℝ) * FIa n := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [h1 k, Finset.mul_sum]
      _ = ∑ k ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 t,
            (if k ∣ n then (k.divisors.card : ℝ) * FIa n else 0) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_filter]
      _ = ∑ n ∈ Finset.Icc 1 t, ∑ k ∈ Finset.Icc 1 Y,
            (if k ∣ n then (k.divisors.card : ℝ) * FIa n else 0) := Finset.sum_comm
      _ = ∑ n ∈ Finset.Icc 1 t, FIa n * (∑ k ∈ (Finset.Icc 1 Y).filter (fun k => k ∣ n),
            (k.divisors.card : ℝ)) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          by_cases hkn : k ∣ n
          · simp only [hkn, if_true]; ring
          · simp only [hkn, if_false, mul_zero]
  rw [hA]
  refine Finset.sum_le_sum (fun n hn => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (FIa_nonneg n)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hsub : (Finset.Icc 1 Y).filter (fun k => k ∣ n) ⊆ n.divisors := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact Nat.mem_divisors.mpr ⟨hk.2, by omega⟩
  have h3 : (∑ k ∈ n.divisors, (k.divisors.card : ℕ) ^ (1 : ℕ))
      ≤ (n.divisors.card) ^ (1 + 1) := sum_divisors_card_pow_le 1 n
  have h2' : (∑ k ∈ n.divisors, (k.divisors.card : ℕ))
      ≤ (n.divisors.card) ^ (2 : ℕ) := by simpa using h3
  have h2'' : (∑ k ∈ n.divisors, (k.divisors.card : ℝ))
      ≤ ((n.divisors.card : ℝ)) ^ (2 : ℕ) := by exact_mod_cast h2'
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)) h2''

/-- The `τ^8`-weighted sum of `FIa` reduces to the `(2τ)^{40}`-weighted cube-range aggregate. -/
lemma sum_FIa_tau_pow_eight_le (t : ℕ) :
    (∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (8 : ℕ))
      ≤ ∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
          (2 * (d.divisors.card : ℝ)) ^ (40 : ℕ) * (Submission.Ad d t : ℝ) := by
  have h := Commons.NumberTheory.DivisorSum.sum_mul_tau_pow_eight_le_cube
    (fun n => FIa n) (fun n => FIa_nonneg n) t
  simp only [Real.rpow_natCast] at h
  refine le_trans h ?_
  refine Finset.sum_le_sum (fun d _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcast : (∑ n ∈ (Finset.Icc 1 t).filter (fun n => d ∣ n), FIa n) = Ad FIa d (t : ℝ) := by
    rw [Ad, Nat.floor_natCast]
  rw [hcast, FI_Ad_eq]
  linarith

/-- **Part 1** — the `τ`-weighted cubefree sum of `|FIr|` is bounded by `(R₃)` plus the two
elementary aggregates. -/
lemma sum_cubefree_tau_abs_FIr_le (t Y : ℕ) :
    (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * |FIr k t|)
      ≤ (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, |FIr k t|)
        + (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
            (2 * (d.divisors.card : ℝ)) ^ (40 : ℕ) * (Submission.Ad d t : ℝ))
        + Acount FIa (t : ℝ) * (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN,
            (k.divisors.card : ℝ) * FIg k) := by
  have hsub : (Finset.Icc 1 Y).filter CubefreeN ⊆ Finset.Icc 1 Y := Finset.filter_subset _ _
  have hA0 : (0 : ℝ) ≤ Acount FIa (t : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
  have hpt : ∀ k : ℕ,
      (k.divisors.card : ℝ) * |FIr k t|
        ≤ |FIr k t| + (k.divisors.card : ℝ) * Ad FIa k t
          + Acount FIa (t : ℝ) * ((k.divisors.card : ℝ) * FIg k) := by
    intro k
    have h1 := FIr_abs_le_Ad k t
    have hτ : (0 : ℝ) ≤ (k.divisors.card : ℝ) := by positivity
    have hAk : (0 : ℝ) ≤ Ad FIa k t := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
    have habs : (0 : ℝ) ≤ |FIr k t| := abs_nonneg _
    have h2 : ((k.divisors.card : ℝ)) * |FIr k t|
        ≤ ((k.divisors.card : ℝ)) * (Ad FIa k t + FIg k * Acount FIa t) :=
      mul_le_mul_of_nonneg_left h1 hτ
    have h3 : ((k.divisors.card : ℝ)) * (Ad FIa k t + FIg k * Acount FIa t)
        = ((k.divisors.card : ℝ)) * Ad FIa k t
          + Acount FIa (t : ℝ) * ((k.divisors.card : ℝ) * FIg k) := by ring
    linarith [h2, h3]
  have hstep : (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * |FIr k t|)
      ≤ ∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN,
          (|FIr k t| + (k.divisors.card : ℝ) * Ad FIa k t
            + Acount FIa (t : ℝ) * ((k.divisors.card : ℝ) * FIg k)) :=
    Finset.sum_le_sum (fun k _ => hpt k)
  have hsplit : (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN,
        (|FIr k t| + (k.divisors.card : ℝ) * Ad FIa k t
          + Acount FIa (t : ℝ) * ((k.divisors.card : ℝ) * FIg k)))
      = (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, |FIr k t|)
        + (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * Ad FIa k t)
        + Acount FIa (t : ℝ) * (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN,
            (k.divisors.card : ℝ) * FIg k) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hAd1 : (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * Ad FIa k t)
      ≤ ∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (8 : ℕ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => mul_nonneg (by positivity) (Finset.sum_nonneg (fun n _ => FIa_nonneg n)))) ?_
    refine le_trans (sum_tau_Ad_le t Y) ?_
    refine Finset.sum_le_sum (fun n hn => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (FIa_nonneg n)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hcard1 : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
      have : 1 ≤ n.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      exact_mod_cast this
    exact pow_le_pow_right₀ hcard1 (by norm_num)
  have hstep' : (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * |FIr k t|)
      ≤ (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, |FIr k t|)
        + (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * Ad FIa k t)
        + Acount FIa (t : ℝ) * (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN,
            (k.divisors.card : ℝ) * FIg k) := by
    rw [hsplit] at hstep
    exact hstep
  refine le_trans hstep' ?_
  have h1 : (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, |FIr k t|)
        + (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * Ad FIa k t)
      ≤ (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, |FIr k t|)
        + ∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (8 : ℕ) :=
    add_le_add le_rfl hAd1
  refine le_trans (add_le_add h1 le_rfl) ?_
  have h2 : (∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (8 : ℕ))
      ≤ ∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
          (2 * (d.divisors.card : ℝ)) ^ (40 : ℕ) * (Submission.Ad d t : ℝ) :=
    sum_FIa_tau_pow_eight_le t
  exact add_le_add (add_le_add le_rfl h2) le_rfl

lemma FIg_prime_pow_le_half (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    FIg (p ^ e) ≤ 2 / (p : ℝ) ^ (e / 2) := by
  have hb := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_ncard_prime_pow_le
    (p := p) (e := e) hp he
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hval : FIg (p ^ e)
      = (({x : ZMod (p ^ e) × ZMod (p ^ e) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ)
          / ((p : ℝ) ^ e) ^ 2 := by
    rw [FIg, Submission.gdens, Submission.N]
    push_cast
    ring
  rw [hval]
  have hcast : ((({x : ZMod (p ^ e) × ZMod (p ^ e) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℕ) : ℝ)
      ≤ ((2 * p ^ (e + e / 2) : ℕ) : ℝ) := by exact_mod_cast hb
  push_cast at hcast
  have hposq : (0 : ℝ) < ((p : ℝ) ^ e) ^ 2 := by positivity
  refine le_trans (div_le_div_of_nonneg_right hcast hposq.le) ?_
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : ((p : ℝ) ^ e) ^ 2 = (p : ℝ) ^ (2 * e) := by rw [← pow_mul]; ring_nf
  rw [h2]
  have key : (p : ℝ) ^ (e + e / 2) * (p : ℝ) ^ (e / 2) ≤ (p : ℝ) ^ (2 * e) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hp1 (by omega)
  nlinarith [key]

lemma FIg_prime_pow_le (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    FIg (p ^ e) ≤ 3 / (p : ℝ) := by
  rcases eq_or_lt_of_le he with h1 | h2
  · rw [← h1, pow_one]
    have h := (Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_prime_le p hp).1
    have hgoal : FIg p
        = (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 2 := by
      rw [FIg, Submission.gdens, Submission.N]
      push_cast
      ring
    rw [hgoal]
    exact h
  · have h := FIg_prime_pow_le_half p e hp he
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    have h2' : (p : ℝ) ≤ (p : ℝ) ^ (e / 2) := by
      have : 1 ≤ e / 2 := by omega
      calc (p : ℝ) = (p : ℝ) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (p : ℝ) ^ (e / 2) := pow_le_pow_right₀ hp1 this
    have h3 : 2 / (p : ℝ) ^ (e / 2) ≤ 2 / (p : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h2'
    have h4 : 2 / (p : ℝ) ≤ 3 / (p : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hp0.le
    linarith

/-- `∑_{a ∈ s} a ^ e a`-form multiplicativity. -/
private lemma FIg_prod_eq (s : Finset ℕ) (e : ℕ → ℕ)
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime (a ^ e a) (b ^ e b)) :
    FIg (∏ a ∈ s, a ^ e a) = ∏ a ∈ s, FIg (a ^ e a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FI_gdens_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, FI_gdens_mul]
      · rw [ih (fun a' ha' b' hb' hne =>
          hcop a' (Finset.mem_insert_of_mem ha') b' (Finset.mem_insert_of_mem hb') hne)]
      · exact Nat.Coprime.prod_right (fun b hb =>
          hcop a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
            (fun h => ha (h ▸ hb)))

/-- `FIg (p^e) ≤ 3/p²` for `e ≥ 2`... -/
lemma FIg_prime_sq_le (p : ℕ) (hp : p.Prime) : FIg (p ^ 2) ≤ 3 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hval : FIg (p ^ 2)
      = (({x : ZMod (p ^ 2) × ZMod (p ^ 2) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ)
          / ((p : ℝ) ^ 2) ^ 2 := by
    rw [FIg, Submission.gdens, Submission.N]
    push_cast
    ring
  rw [hval]
  have hb := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_ncard_prime_pow_sqrt
    (p := p) (e := 2) hp (by norm_num)
  rw [show ((p : ℝ) ^ 2) ^ 2 = (p : ℝ) ^ 4 by ring] at hval ⊢
  have hs : Real.sqrt ((p : ℝ) ^ 2) = (p : ℝ) := Real.sqrt_sq hp0.le
  have hcast : ((({x : ZMod (p ^ 2) × ZMod (p ^ 2) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℕ) : ℝ)
      ≤ 3 * (p : ℝ) ^ (2 - 1) * Real.sqrt ((p : ℝ) ^ 2) := hb
  rw [hs] at hcast
  refine le_trans (div_le_div_of_nonneg_right hcast (by positivity)) (le_of_eq ?_)
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

lemma FIg_four_le : FIg 4 ≤ 3 / 4 := by
  have h := FIg_prime_sq_le 2 (by norm_num)
  norm_num at h ⊢
  exact h

/-- `FIg d = ∏_{p ∣ d} FIg (p ^ d.factorization p)`. -/
lemma FIg_eq_prod_primeFactors_pow (d : ℕ) (hd : 0 < d) :
    FIg d = ∏ p ∈ d.primeFactors, FIg (p ^ d.factorization p) := by
  have hcop : ∀ a ∈ d.primeFactors, ∀ b ∈ d.primeFactors, a ≠ b →
      Nat.Coprime (a ^ d.factorization a) (b ^ d.factorization b) := by
    intro a ha b hb hne
    have hap : a.Prime := Nat.prime_of_mem_primeFactors ha
    have hbp : b.Prime := Nat.prime_of_mem_primeFactors hb
    exact (Nat.coprime_primes hap hbp).mpr hne |>.pow _ _
  have h := FIg_prod_eq d.primeFactors (fun p => d.factorization p) hcop
  have key : (∏ p ∈ d.primeFactors, p ^ d.factorization p) = d :=
    (Nat.prod_primeFactors_pow_factorization hd.ne').symm
  rw [key] at h
  exact h

/-- For a cubefree `d`, `FIg d ≤ 3^{ω(d)}/d`. -/
lemma FIg_le_three_pow_omega_div (d : ℕ) (hd : 0 < d) (hcf : CubefreeN d) :
    FIg d ≤ (3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) := by
  rw [FIg_eq_prod_primeFactors_pow d hd]
  have hpt : ∀ p ∈ d.primeFactors, FIg (p ^ d.factorization p)
      ≤ (3 : ℝ) / (p : ℝ) ^ (d.factorization p) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hle2 : d.factorization p ≤ 2 := hcf p hp
    have hne0 : d.factorization p ≠ 0 := Finsupp.mem_support_iff.mp (by
      rwa [← Nat.support_factorization] at hp)
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    interval_cases d.factorization p
    · exact absurd rfl hne0
    · simpa using FIg_prime_pow_le p 1 hpp le_rfl
    · simpa using FIg_prime_sq_le p hpp
  refine le_trans (Finset.prod_le_prod₀ (fun p _ => FIg_nonneg _) hpt) ?_
  have hnum : (∏ p ∈ d.primeFactors, (3 : ℝ)) = (3 : ℝ) ^ (d.primeFactors.card) :=
    Finset.prod_const _
  have hden : (∏ p ∈ d.primeFactors, (p : ℝ) ^ (d.factorization p)) = (d : ℝ) := by
    have h1 : (∏ p ∈ d.primeFactors, (p : ℝ) ^ (d.factorization p))
        = (∏ p ∈ d.primeFactors, (((p ^ d.factorization p : ℕ)) : ℝ)) :=
      Finset.prod_congr rfl (fun p _ => (Nat.cast_pow p _).symm)
    rw [h1, ← Nat.cast_prod, (Nat.prod_primeFactors_pow_factorization hd.ne').symm]
  rw [Finset.prod_div_distrib, hnum, hden]

/-- A bound for the `τ`-weighted cubefree density sum. -/
lemma sum_cubefree_tau_mul_FIg_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 2 ≤ Y →
      (∑ d ∈ (Finset.Icc 1 Y).filter CubefreeN, (d.divisors.card : ℝ) * FIg d)
        ≤ C * (Real.log ((Y : ℝ) + 2)) ^ (16 : ℕ) := by
  obtain ⟨C4, hC4, h4⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 4
  refine ⟨C4, hC4, fun Y hY => ?_⟩
  have hbase : (1 : ℝ) ≤ Real.log ((Y : ℝ) + 2) := by
    have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have he4 : Real.exp 1 ≤ (Y : ℝ) + 2 := by
      linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he4
    rwa [Real.log_exp] at h
  have hpt : ∀ d ∈ (Finset.Icc 1 Y).filter CubefreeN,
      (d.divisors.card : ℝ) * FIg d ≤ ((d.divisors.card : ℝ)) ^ (4 : ℕ) / (d : ℝ) := by
    intro d hd
    obtain ⟨hdI, hdcf⟩ := Finset.mem_filter.mp hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
    have hd0 : 0 < d := hd1
    have hcard1 : (1 : ℝ) ≤ (d.divisors.card : ℝ) := by
      have : 1 ≤ d.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hd0.ne'⟩
      exact_mod_cast this
    have hbound := FIg_le_three_pow_omega_div d hd0 hdcf
    have h2pow : (2 : ℝ) ^ (d.primeFactors.card) ≤ (d.divisors.card : ℝ) := by
      have := Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors hd0
      exact_mod_cast this
    have h3 : (3 : ℝ) ^ (d.primeFactors.card) ≤ ((d.divisors.card : ℝ)) ^ (3 : ℕ) := by
      have h8 : (3 : ℝ) ≤ 8 := by norm_num
      calc (3 : ℝ) ^ (d.primeFactors.card) ≤ (8 : ℝ) ^ (d.primeFactors.card) :=
            pow_le_pow_left₀ (by norm_num) h8 _
        _ = ((2 : ℝ) ^ (d.primeFactors.card)) ^ (3 : ℕ) := by
            rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← pow_mul, ← pow_mul]
            ring_nf
        _ ≤ ((d.divisors.card : ℝ)) ^ (3 : ℕ) := pow_le_pow_left₀ (by positivity) h2pow 3
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    calc (d.divisors.card : ℝ) * FIg d
        ≤ (d.divisors.card : ℝ) * ((3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ ≤ (d.divisors.card : ℝ) * (((d.divisors.card : ℝ)) ^ (3 : ℕ) / (d : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right h3 hdpos.le
      _ = ((d.divisors.card : ℝ)) ^ (4 : ℕ) / (d : ℝ) := by ring
  refine le_trans (Finset.sum_le_sum hpt) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun d _ _ => by positivity)) ?_
  simpa using h4 Y (by omega)


/-- `Aseq` is monotone. -/
lemma Aseq_mono {m n : ℕ} (h : m ≤ n) : Submission.Aseq m ≤ Submission.Aseq n := by
  rw [Submission.Aseq, Submission.Aseq]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun k hk => by rw [Finset.mem_range] at hk ⊢; omega) (fun i _ _ => Nat.zero_le _)

/-- **(R′₃) for the Friedlander–Iwaniec sequence**: the `τ`-weighted cubefree sum over
`k ≤ R3cut x` is bounded by `(R₃)` (the same sum without the `τ`-weight) plus `A(x)(log x)^W`.
This replaces the companion's Cauchy–Schwarz step, which relies on the (false for X² + Y⁴)
hypothesis `(1.6)`. -/
theorem FIr_Rprime3_le :
    ∃ C W : ℝ, 0 < C ∧ 0 ≤ W ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x → ∀ Y : ℕ,
      Y ≤ Submission.X2Y4R3.R3cut x →
      (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * |FIr k t|)
        ≤ (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, |FIr k t|)
          + C * (Submission.Aseq x : ℝ) * (Real.log x) ^ W := by
  obtain ⟨C2, B2, X2, hC2, hcube⟩ := cube_range_Ad_le
  obtain ⟨C3, hC3, hrho⟩ := sum_cubefree_tau_mul_FIg_le
  obtain ⟨cA, hcA, XA, hAlow⟩ := Submission.X2Y4R.exists_const_mul_rpow_le_Aseq
  obtain ⟨X7, hX7'⟩ := Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
    (K := 1) (by norm_num) (n := 2 ^ 25) (r := (1 : ℝ) / 10) (by norm_num)
  set C3' : ℝ := max C3 1 with hC3'def
  have hC3'pos : (0 : ℝ) < C3' := by rw [hC3'def]; exact lt_max_of_lt_right one_pos
  have hC3'1 : (1 : ℝ) ≤ C3' := le_max_right _ _
  have hC3le : C3 ≤ C3' := le_max_left _ _
  refine ⟨2 * (C2 + C3'), max (max B2 0) 16, by positivity,
    le_trans (le_max_right B2 0) (le_max_left _ _),
    max (max ⌈X2⌉₊ XA) (max X7 64), fun x hx t ht2 htx Y hY => ?_⟩
  have hxX2 : X2 ≤ (x : ℝ) := by
    refine le_trans (Nat.le_ceil X2) ?_
    exact_mod_cast (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx))
  have hxXA : XA ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hxX7 : X7 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hx64 : 64 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hx4 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 4 ≤ x by omega)
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 3 ≤ x by omega)
    linarith [Real.exp_one_lt_three]
  have hlog0 : (0 : ℝ) ≤ Real.log x := le_trans zero_le_one hlog1
  have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := by positivity
  have hagg : (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
        (2 * (d.divisors.card : ℝ)) ^ (40 : ℕ) * (Submission.Ad d t : ℝ))
      ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2 := by
    have h := hcube x hxX2 t ht2 htx
    have heq : (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
          (2 * (d.divisors.card : ℝ)) ^ (40 : ℕ) * (Submission.Ad d t : ℝ))
        = (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
          (2 * (d.divisors.card : ℝ)) ^ (40 : ℝ) * (Submission.Ad d t : ℝ)) := by
      refine Finset.sum_congr rfl (fun d _ => ?_)
      congr 1
      rw [show (40 : ℝ) = ((40 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rw [heq]; exact h
  have hexp : (((2 ^ 25 : ℕ) : ℝ)) = ((2 : ℝ) ^ 25) := by norm_num
  have hY4 : (Y : ℝ) ≤ (x : ℝ) ^ ((4 : ℝ) / 5) := by
    have h1 : (Y : ℝ) ≤ ((Submission.X2Y4R3.R3cut x : ℕ) : ℝ) := by exact_mod_cast hY
    have h2 : ((Submission.X2Y4R3.R3cut x : ℕ) : ℝ)
        ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
      rw [Submission.X2Y4R3.R3cut]; exact Nat.floor_le (by positivity)
    have hlogle : (Real.log x) ^ (2 ^ 25 : ℕ) ≤ (Real.log ((x : ℝ) + 2)) ^ (2 ^ 25 : ℕ) :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith))
        (Real.log_le_log (by linarith) (by linarith)) _
    have h3 : (Real.log ((x : ℝ) + 2)) ^ (2 ^ 25 : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
      have h := hX7'.2 x hxX7
      rw [one_mul] at h
      exact h
    have hstep : (Real.log x) ^ ((2 : ℝ) ^ 25) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
      rw [← hexp, Real.rpow_natCast]
      exact le_trans hlogle h3
    have h4 : (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)
        ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (x : ℝ) ^ ((1 : ℝ) / 10) :=
      mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hx0.le _)
    have h5 : (x : ℝ) ^ ((7 : ℝ) / 10) * (x : ℝ) ^ ((1 : ℝ) / 10)
        = (x : ℝ) ^ ((4 : ℝ) / 5) := by
      rw [← Real.rpow_add hx0]; norm_num
    linarith [h1, h2, h4, h5.le, h5.ge]
  have hYx : (Y : ℝ) + 2 ≤ (x : ℝ) := by
    have h6 : (x : ℝ) ^ ((4 : ℝ) / 5) ≤ (x : ℝ) / 2 := by
      have h7 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 5) := by
        have h8 : (x : ℝ) ^ ((1 : ℝ) / 5) ≥ (32 : ℝ) ^ ((1 : ℝ) / 5) := by
          refine Real.rpow_le_rpow (by norm_num) ?_ (by norm_num)
          have : (32 : ℕ) ≤ x := by omega
          exact_mod_cast this
        have h9 : (32 : ℝ) ^ ((1 : ℝ) / 5) = 2 := by
          rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 5,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        linarith [h8, h9.le, h9.ge]
      have h10 : (x : ℝ) = (x : ℝ) ^ ((4 : ℝ) / 5) * (x : ℝ) ^ ((1 : ℝ) / 5) := by
        rw [← Real.rpow_add hx0]; norm_num
      nlinarith [h7, hx0, Real.rpow_nonneg hx0.le ((4 : ℝ) / 5)]
    linarith [h6, hY4, hx4]
  have hlogY : Real.log ((Y : ℝ) + 2) ≤ Real.log x :=
    Real.log_le_log (by positivity) hYx
  have hlogY0 : (0 : ℝ) ≤ Real.log ((Y : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hdensity : (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * FIg k)
      ≤ C3' * (Real.log x) ^ (16 : ℕ) := by
    rcases Nat.lt_or_ge Y 2 with hY2 | hY2
    · have hle : (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * FIg k)
          ≤ 1 := by
        interval_cases Y
        · simp
        · rw [Finset.Icc_self]
          have hcf1 : CubefreeN 1 := by intro p hp; simp at hp
          rw [Finset.filter_singleton, if_pos hcf1, Finset.sum_singleton]
          simp [FI_gdens_one]
      have h2 : (1 : ℝ) ≤ (Real.log x) ^ (16 : ℕ) := one_le_pow₀ hlog1
      calc (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, (k.divisors.card : ℝ) * FIg k)
          ≤ 1 := hle
        _ = 1 * 1 := by ring
        _ ≤ C3' * (Real.log x) ^ (16 : ℕ) := mul_le_mul hC3'1 h2 (by norm_num) hC3'pos.le
    · refine le_trans (hrho Y hY2) ?_
      refine le_trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlogY0 hlogY 16) hC3.le) ?_
      exact mul_le_mul_of_nonneg_right hC3le (pow_nonneg hlog0 16)
  have hAcount : Acount FIa (t : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    rw [FI_Acount_eq]
    have h1 : ((Submission.Aseq t : ℕ) : ℝ) ≤ (Submission.Aseq x : ℝ) := by
      exact_mod_cast Aseq_mono htx
    linarith
  have hcrude : Acount FIa (t : ℝ) * (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN,
        (k.divisors.card : ℝ) * FIg k)
      ≤ (Submission.Aseq x : ℝ) * (C3' * (Real.log x) ^ (16 : ℕ)) := by
    refine le_trans (mul_le_mul hAcount hdensity
      (Finset.sum_nonneg (fun k _ => mul_nonneg (by positivity) (FIg_nonneg k))) hA0) ?_
    exact le_of_eq (by ring)
  have hW : (0 : ℝ) ≤ max (max B2 0) 16 := le_trans (le_max_right B2 0) (le_max_left _ _)
  have hlogB2 : (Real.log x) ^ B2 ≤ (Real.log x) ^ (max (max B2 0) 16) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (le_trans (le_max_left B2 0) (le_max_left _ _))
  have hlog16 : (Real.log x) ^ (16 : ℕ) ≤ (Real.log x) ^ (max (max B2 0) 16) := by
    have h := Real.rpow_le_rpow_of_exponent_le hlog1
      (show (((16 : ℕ) : ℝ)) ≤ max (max B2 0) 16 by exact le_max_right (max B2 0) 16)
    simpa only [Real.rpow_natCast] using h
  have hlogW0 : (0 : ℝ) ≤ (Real.log x) ^ (max (max B2 0) 16) := Real.rpow_nonneg hlog0 _
  have h1 : C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2
      ≤ (C2 + C3') * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max (max B2 0) 16) := by
    calc C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2
        ≤ (C2 + C3') * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2 := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hlog0 _)
          exact mul_le_mul_of_nonneg_right (by linarith) hA0
      _ ≤ (C2 + C3') * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max (max B2 0) 16) := by
          refine mul_le_mul_of_nonneg_left hlogB2 ?_
          exact mul_nonneg (by linarith) hA0
  have h3 : (Submission.Aseq x : ℝ) * (C3' * (Real.log x) ^ (16 : ℕ))
      ≤ (C2 + C3') * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max (max B2 0) 16) := by
    calc (Submission.Aseq x : ℝ) * (C3' * (Real.log x) ^ (16 : ℕ))
        = C3' * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (16 : ℕ)) := by ring
      _ ≤ C3' * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (max (max B2 0) 16)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog16 hA0) hC3'pos.le
      _ ≤ (C2 + C3') * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (max (max B2 0) 16)) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hA0 hlogW0)
      _ = (C2 + C3') * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max (max B2 0) 16) := by ring
  have hsum : (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
        (2 * (d.divisors.card : ℝ)) ^ (40 : ℕ) * (Submission.Ad d t : ℝ))
        + Acount FIa (t : ℝ) * (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN,
            (k.divisors.card : ℝ) * FIg k)
      ≤ 2 * (C2 + C3') * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max (max B2 0) 16) := by
    have h4 := add_le_add (le_trans hagg h1) (le_trans hcrude h3)
    linarith [h4]
  have hfin : (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, |FIr k t|)
        + (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
            (2 * (d.divisors.card : ℝ)) ^ (40 : ℕ) * (Submission.Ad d t : ℝ))
        + Acount FIa (t : ℝ) * (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN,
            (k.divisors.card : ℝ) * FIg k)
      ≤ (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, |FIr k t|)
        + 2 * (C2 + C3') * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max (max B2 0) 16) := by
    linarith [hsum]
  exact le_trans (sum_cubefree_tau_abs_FIr_le t Y) hfin

/-- **(R′₃)-assembly**: `E₁` (the `ν ≤ L` part of the §9 error term) is bounded by the
`(R₃)`-sum over the cubefree moduli plus `A(x)(log x)^W`. -/
theorem Eone_FIr_le : ∃ C W : ℝ, 0 < C ∧ 0 ≤ W ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
    ∀ t : ℕ, 2 ≤ t → t ≤ x → ∀ D L : ℕ, D * L ^ 2 ≤ Submission.X2Y4R3.R3cut x →
      Eone FIr t D L
        ≤ (∑ k ∈ (Finset.Icc 1 (D * L ^ 2)).filter CubefreeN, |FIr k t|)
          + C * (Submission.Aseq x : ℝ) * (Real.log x) ^ W := by
  obtain ⟨C, W, hC, hW, X0, h0⟩ := FIr_Rprime3_le
  exact ⟨C, W, hC, hW, X0, fun x hx t ht2 htx D L hDL =>
    E1_le FIr t D L (le_trans (h0 x hx t ht2 htx (D * L ^ 2) hDL) le_rfl)⟩

/-- **(R′₃)-assembly at an arbitrary `(R₃)`-exponent**: `E₁` (the `ν ≤ L` part of the §9 error
term) is bounded by the paper's `(R₃)`-input `4·A(x)·(log x)^{−λ}` plus `A(x)(log x)^W`.  This is
the exact form in which `S32.Rtilde_sum_le_signed_of_inputs` consumes it. -/
theorem Eone_FIr_le_R3 (lamm : ℝ) :
    ∃ C W : ℝ, 0 < C ∧ 0 ≤ W ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ t : ℕ, 2 ≤ t → t ≤ x → ∀ D L : ℕ, D * L ^ 2 + 1 ≤ Submission.X2Y4R3.R3cut x →
        Eone FIr t D L
          ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)
            + C * (Submission.Aseq x : ℝ) * (Real.log x) ^ W := by
  obtain ⟨C, W, hC, hW, X0, h0⟩ := Eone_FIr_le
  obtain ⟨X1, h1⟩ := FIr_cubefree_sum_le_generic lamm
  refine ⟨C, W, hC, hW, max X0 X1, fun x hx t ht2 htx D L hDL => ?_⟩
  have hx0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : X1 ≤ x := le_trans (le_max_right _ _) hx
  have hsub : (Finset.Icc 1 (D * L ^ 2)).filter CubefreeN
      ⊆ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk.2⟩
  have h3 : (∑ k ∈ (Finset.Icc 1 (D * L ^ 2)).filter CubefreeN, |FIr k t|)
      ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg _))
      (h1 x hx1 t ht2 htx)
  refine le_trans (h0 x hx0 t ht2 htx D L (le_trans (Nat.le_succ _) hDL)) ?_
  linarith [h3]

/-- The `S₂`-input of (9.12) for the Friedlander–Iwaniec sequence:
`∑_{n ≤ t} a_n τ(n)³ ≪ A(x)(log x)^B` (via the `τ^8`-reduction into the cube range). -/
lemma sum_FIa_tau_cube_le :
    ∃ C B X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (3 : ℕ))
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x) ^ B := by
  obtain ⟨C2, B2, X2, hC2, hcube⟩ := cube_range_Ad_le
  refine ⟨C2, B2, X2, hC2, fun x hx t ht2 htx => ?_⟩
  calc (∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (3 : ℕ))
      ≤ ∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (8 : ℕ) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (FIa_nonneg n)
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hcard1 : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
          have : 1 ≤ n.divisors.card :=
            Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
          exact_mod_cast this
        exact pow_le_pow_right₀ hcard1 (by norm_num)
    _ ≤ ∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
          (2 * (d.divisors.card : ℝ)) ^ (40 : ℕ) * (Submission.Ad d t : ℝ) :=
        sum_FIa_tau_pow_eight_le t
    _ ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2 := by
        have h := hcube x hx t ht2 htx
        have heq : (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
              (2 * (d.divisors.card : ℝ)) ^ (40 : ℕ) * (Submission.Ad d t : ℝ))
            = (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
              (2 * (d.divisors.card : ℝ)) ^ (40 : ℝ) * (Submission.Ad d t : ℝ)) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          congr 1
          rw [show (40 : ℝ) = ((40 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
        rw [heq]; exact h

/-- The `E₂₁`-counting input of (9.12) in the form required by `S9d.Etwo_le`. -/
lemma sum_tau_cube_sqdvCount_le : ∃ C : ℝ, 0 < C ∧ ∀ x t Y : ℕ, 1 ≤ Y → 1 ≤ t → t ≤ x →
    (∑ n ∈ Finset.Icc 1 t, ((n.divisors.card : ℝ)) ^ (3 : ℕ) * (sqdvCount n (Y + 1) t : ℝ))
      ≤ C * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ (71 : ℕ) / (Y : ℝ) := by
  obtain ⟨C, hC, hCb⟩ := sum_tau_cube_sqr_dvd_gt_le
  refine ⟨C, hC, fun x t Y hY ht htx => ?_⟩
  calc (∑ n ∈ Finset.Icc 1 t, ((n.divisors.card : ℝ)) ^ (3 : ℕ) * (sqdvCount n (Y + 1) t : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 t, ((n.divisors.card : ℝ)) ^ (3 : ℕ)
          * (((Finset.Icc 1 x).filter (fun ν => Y < ν ∧ ν ^ 2 ∣ n)).card : ℝ) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hsub : sqdvCount n (Y + 1) t
            ≤ ((Finset.Icc 1 x).filter (fun ν => Y < ν ∧ ν ^ 2 ∣ n)).card := by
          rw [sqdvCount]
          refine Finset.card_le_card ?_
          intro ν hν
          rw [Finset.mem_filter] at hν
          obtain ⟨hν1, hν2⟩ := hν
          rw [Finset.mem_filter] at hν1
          obtain ⟨hν1a, _⟩ := hν1
          rw [Finset.mem_Icc] at hν1a
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hν1a.2 htx⟩,
            by omega, hν2⟩
        exact_mod_cast hsub
    _ ≤ ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ (3 : ℕ)
          * (((Finset.Icc 1 x).filter (fun ν => Y < ν ∧ ν ^ 2 ∣ n)).card : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (by
          intro n hn
          rw [Finset.mem_Icc] at hn ⊢
          exact ⟨hn.1, le_trans hn.2 htx⟩) (fun n _ _ => by positivity)
    _ ≤ C * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ (71 : ℕ) / (Y : ℝ) := hCb x Y hY (by omega)

end

end Submission.ASP
