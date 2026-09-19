import Mathlib
import Submission.BoundedGaps
import Submission.Commons.NumberTheory.CongruenceWindows.exists_residue_class_prod
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Rescale

open Finset Filter
open scoped BigOperators Topology

set_option maxHeartbeats 1000000

/-!
# The modulus/residue setup of the Maynard sieve

For an admissible tuple `H : Fin k → ℕ` (Polymath8a (2): `H` is injective and misses
at least one residue class modulo every prime) the sieve needs a squarefree modulus
`W = ∏_{p ≤ w} p` and a residue class `b (mod W)` with

  `(b + H i, W) = 1` for all `i`

(Polymath8a §3): the moduli `W` must be divisible by every prime `≤ w`, and the
residue `b` has to avoid the finitely many bad classes `-H i` modulo the primes
dividing `W`.

This module builds the elementary part of that setup:

* `smoothModulus w = ∏_{p ≤ w} p` and its basic arithmetic (nonzero, prime
  divisors, complete coprimality criterion);
* `exists_sieve_residue`: for every admissible `H` and every `w` there is
  `b < ∏_{p ≤ w} p` with `(b + H i, ∏_{p ≤ w} p) = 1` for all `i`.

The residue is produced by the Chinese remainder theorem
(`Commons.NumberTheory.CongruenceWindows.exists_residue_class_prod`) applied to the
system `b ≡ -r_p (mod p)`, where `r_p` is a residue class missed by all the `H i`
(existing by admissibility).
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The squarefree smooth modulus `∏_{p ≤ w} p` of the Maynard sieve. -/
noncomputable def smoothModulus (w : ℕ) : ℕ := ∏ p ∈ Nat.primesLE w, p

theorem smoothModulus_pos (w : ℕ) : 0 < smoothModulus w :=
  Finset.prod_pos fun p hp => (Nat.mem_primesLE.mp hp).2.pos

theorem smoothModulus_ne_zero (w : ℕ) : smoothModulus w ≠ 0 :=
  (smoothModulus_pos w).ne'

/-- Every prime `≤ w` divides `smoothModulus w`. -/
theorem prime_dvd_smoothModulus {p w : ℕ} (hp : p.Prime) (hpw : p ≤ w) :
    p ∣ smoothModulus w :=
  Finset.dvd_prod_of_mem _ (Nat.mem_primesLE.mpr ⟨hpw, hp⟩)

/-- A prime dividing `smoothModulus w` is `≤ w`. -/
theorem prime_le_of_prime_dvd_smoothModulus {p w : ℕ} (hp : p.Prime)
    (hdiv : p ∣ smoothModulus w) : p ≤ w := by
  rw [smoothModulus] at hdiv
  rcases (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hdiv with ⟨q, hq, hpq⟩
  have hqprime : q.Prime := (Nat.mem_primesLE.mp hq).2
  have hqp_eq : q = p := ((Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq).symm
  rw [hqp_eq] at hq
  exact (Nat.mem_primesLE.mp hq).1

/-- `n` is coprime to `smoothModulus w` iff no prime `≤ w` divides `n`. -/
theorem coprime_smoothModulus_iff (n w : ℕ) :
    n.Coprime (smoothModulus w) ↔ ∀ p : ℕ, p.Prime → p ≤ w → ¬ p ∣ n := by
  constructor
  · intro h p hp hpw hdiv
    have hdvd : p ∣ n.gcd (smoothModulus w) :=
      Nat.dvd_gcd hdiv (prime_dvd_smoothModulus hp hpw)
    rw [h] at hdvd
    exact hp.ne_one (Nat.dvd_one.mp hdvd)
  · intro h
    refine Nat.Coprime.prod_right fun p hp => ?_
    have hp' : p.Prime := (Nat.mem_primesLE.mp hp).2
    exact Nat.Coprime.symm
      (hp'.coprime_iff_not_dvd.mpr (h p hp' (Nat.mem_primesLE.mp hp).1))

/-- **The sieve residue.**  For an admissible tuple `H` and any cutoff `w` there is a
residue class `b (mod ∏_{p ≤ w} p)` such that `b + H i` is coprime to `∏_{p ≤ w} p` for
every `i`. -/
theorem exists_sieve_residue {k : ℕ} (H : Fin k → ℕ)
    (hH : Submission.BoundedGaps.IsAdmissible k H) (w : ℕ) :
    ∃ b : ℕ, b < smoothModulus w ∧ ∀ i : Fin k, (b + H i).Coprime (smoothModulus w) := by
  classical
  -- a residue class missed by all the `H i`, for every prime `≤ w`
  have hmiss : ∀ p ∈ (Nat.primesLE w : Finset ℕ),
      ∃ r : ℕ, r < p ∧ ∀ i : Fin k, H i % p ≠ r :=
    fun p hp => hH.2 p (Nat.mem_primesLE.mp hp).2
  choose r hr_lt hr_ne using hmiss
  -- the CRT system `b ≡ -r p (mod p)` over the primes `p ≤ w`
  haveI : Fintype {p // p ∈ (Nat.primesLE w : Finset ℕ)} :=
    Finset.fintypeCoeSort (Nat.primesLE w)
  have hprod : (∏ p : {p // p ∈ (Nat.primesLE w : Finset ℕ)}, (p : ℕ)) = smoothModulus w := by
    rw [smoothModulus, Finset.prod_subtype (Nat.primesLE w) (fun x => Iff.rfl) (fun p => p)]
  have hs : ∀ p : {p // p ∈ (Nat.primesLE w : Finset ℕ)}, (p : ℕ) ≠ 0 :=
    fun p => ((Nat.mem_primesLE.mp p.2).2).ne_zero
  have hcop : Pairwise (fun p q : {p // p ∈ (Nat.primesLE w : Finset ℕ)} =>
      ((p : ℕ).Coprime (q : ℕ))) := by
    intro p q hpq
    have hpp : (p : ℕ).Prime := (Nat.mem_primesLE.mp p.2).2
    have hqp : (q : ℕ).Prime := (Nat.mem_primesLE.mp q.2).2
    rw [hpp.coprime_iff_not_dvd]
    intro hdiv
    exact hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp hdiv))
  obtain ⟨b, hb_lt, hb⟩ :=
    Commons.NumberTheory.CongruenceWindows.exists_residue_class_prod
      (fun p : {p // p ∈ (Nat.primesLE w : Finset ℕ)} => (p : ℕ))
      (fun p : {p // p ∈ (Nat.primesLE w : Finset ℕ)} => ((p : ℕ) - r p p.2)) hs hcop
  have hblt : b < smoothModulus w := by rwa [hprod] at hb_lt
  refine ⟨b, hblt, ?_⟩
  intro i
  rw [coprime_smoothModulus_iff]
  intro p hp hpw hdiv
  have hpι : p ∈ (Nat.primesLE w : Finset ℕ) := Nat.mem_primesLE.mpr ⟨hpw, hp⟩
  have hpr : r p hpι < p := hr_lt p hpι
  -- the CRT congruence `b ≡ -r p (mod p)`, read in `ZMod p`
  have hbmod : (b : ZMod p) = ((p - r p hpι : ℕ) : ZMod p) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact (hb b).mpr (Nat.mod_eq_of_lt hb_lt) ⟨p, hpι⟩
  have hpr_neg : ((p - r p hpι : ℕ) : ZMod p) = -(r p hpι : ZMod p) := by
    rw [Nat.cast_sub (le_of_lt hpr)]
    simp
  have hzero : ((b + H i : ℕ) : ZMod p) = 0 := by
    have h0 : ((b + H i : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff' (b + H i) 0 p]
      simpa using Nat.dvd_iff_mod_eq_zero.mp hdiv
    simpa using h0
  have hHi : (((H i : ℕ)) : ZMod p) = (r p hpι : ZMod p) := by
    have hsum : (b : ZMod p) + ((H i : ℕ) : ZMod p) = 0 := by
      rw [← Nat.cast_add]; exact hzero
    rw [hbmod, hpr_neg] at hsum
    have := eq_neg_of_add_eq_zero_left hsum
    simpa using this.symm
  have := (ZMod.natCast_eq_natCast_iff' (H i) (r p hpι) p).mp hHi
  rw [Nat.mod_eq_of_lt hpr] at this
  exact hr_ne p hpι i this


/-! ## The analytic side conditions -/

/-- The slowly growing cutoff `w x = ⌊log log x⌋`. -/
noncomputable def slowCutoff (x : ℕ) : ℕ := ⌊Real.log (Real.log (x : ℝ))⌋₊

theorem tendsto_slowCutoff : Tendsto slowCutoff atTop atTop := by
  have h : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun x : ℕ => ⌊Real.log (Real.log (x : ℝ))⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp h
  change Tendsto (fun x : ℕ => ⌊Real.log (Real.log (x : ℝ))⌋₊) atTop atTop
  exact h2

/-- `θ(w) = log (∏_{p ≤ w} p)`. -/
theorem log_smoothModulus_eq_theta (w : ℕ) :
    Real.log (smoothModulus w : ℝ) = Chebyshev.theta (w : ℝ) := by
  have hprod : (smoothModulus w : ℝ) = ∏ p ∈ Nat.primesLE w, (p : ℝ) := by
    rw [smoothModulus]; push_cast; rfl
  rw [hprod, Real.log_prod (fun p hp => by
    have := (Nat.mem_primesLE.mp hp).2
    exact_mod_cast this.ne_zero)]
  rw [show Chebyshev.theta (w : ℝ) =
      ∑ m ∈ Finset.Ioc 0 w, (if m.Prime then Real.log (m : ℝ) else 0) from by
    unfold Chebyshev.theta
    rw [Nat.floor_natCast, ← Finset.sum_filter]]
  have hset : Nat.primesLE w = (Finset.Ioc 0 w).filter (fun m => Nat.Prime m) := by
    ext m
    rw [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  rw [hset, Finset.sum_filter]

/-- `log log x / √(log x) → 0`. -/
theorem tendsto_loglog_div_sqrtlog :
    Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0) := by
  have h1 : (fun x : ℕ => Real.log (Real.log (x : ℝ)) / (Real.log (x : ℝ)) ^ ((1:ℝ)/2))
      =ᶠ[atTop] fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.sqrt (Real.log (x : ℝ)) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    rw [Real.sqrt_eq_rpow]
  have h2 : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ)) / (Real.log (x : ℝ)) ^ ((1:ℝ)/2))
      atTop (𝓝 0) := by
    have ho := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
    have hcomp := ho.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa [Function.comp_def] using hcomp
  exact h2.congr' h1


/-- The sieve modulus `W x = ∏_{p ≤ ⌊log log x⌋} p` is at most a fixed power of `log x`. -/
theorem smoothModulus_slowCutoff_le :
    ∀ᶠ x : ℕ in atTop, (smoothModulus (slowCutoff x) : ℝ) ≤ (Real.log (x : ℝ)) ^ (2 : ℕ) := by
  have hlog1_ev : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    rw [Real.le_log_iff_exp_le (by positivity)]
    calc Real.exp 1 ≤ (3 : ℝ) := by
          have := Real.exp_one_lt_d9; linarith
      _ ≤ (x : ℝ) := by exact_mod_cast hx
  filter_upwards [hlog1_ev] with x hlog1
  have hlogpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hθ : Real.log (smoothModulus (slowCutoff x) : ℝ) ≤
      Real.log 3 * Real.log (Real.log (x : ℝ)) := by
    rw [log_smoothModulus_eq_theta]
    refine le_trans (Commons.NumberTheory.Chebyshev.theta_le_log3_mul (slowCutoff x)) ?_
    have hfloor : (slowCutoff x : ℝ) ≤ Real.log (Real.log (x : ℝ)) :=
      Nat.floor_le (Real.log_nonneg hlog1)
    exact mul_le_mul_of_nonneg_left hfloor (Real.log_nonneg (by norm_num))
  calc (smoothModulus (slowCutoff x) : ℝ)
      = Real.exp (Real.log (smoothModulus (slowCutoff x) : ℝ)) :=
        (Real.exp_log (by exact_mod_cast smoothModulus_pos (slowCutoff x))).symm
    _ ≤ Real.exp (Real.log 3 * Real.log (Real.log (x : ℝ))) := Real.exp_le_exp.mpr hθ
    _ = (Real.log (x : ℝ)) ^ (Real.log 3) := by
          rw [Real.rpow_def_of_pos hlogpos]; ring_nf
    _ ≤ (Real.log (x : ℝ)) ^ (2 : ℕ) := by
          rw [← Real.rpow_natCast (Real.log (x : ℝ)) 2]
          exact Real.rpow_le_rpow_of_exponent_le hlog1 (by
            have h3 := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num)
            have h3' : Real.log 3 < (2 : ℝ) := by linarith
            exact h3'.le)

/-- `log W x / √(log x) → 0` for `W x = ∏_{p ≤ ⌊log log x⌋} p`. -/
theorem tendsto_log_smoothModulus_slowCutoff_div_sqrtlog :
    Tendsto (fun x : ℕ =>
      Real.log (smoothModulus (slowCutoff x) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0) := by
  refine squeeze_zero' (g := fun x : ℕ => Real.log 3 *
    (Real.log (Real.log (x : ℝ)) / Real.sqrt (Real.log (x : ℝ)))) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with x hx
    have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      calc Real.exp 1 ≤ (3 : ℝ) := by
            have := Real.exp_one_lt_d9; linarith
        _ ≤ (x : ℝ) := by exact_mod_cast hx
    have hlogW : 0 ≤ Real.log (smoothModulus (slowCutoff x) : ℝ) := by
      rw [log_smoothModulus_eq_theta]
      exact Chebyshev.theta_nonneg _
    exact div_nonneg hlogW (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 3] with x hx
    have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      calc Real.exp 1 ≤ (3 : ℝ) := by
            have := Real.exp_one_lt_d9; linarith
        _ ≤ (x : ℝ) := by exact_mod_cast hx
    have hlogpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
    have hsqrtpos : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.mpr hlogpos
    have hθ : Real.log (smoothModulus (slowCutoff x) : ℝ) ≤
        Real.log 3 * Real.log (Real.log (x : ℝ)) := by
      rw [log_smoothModulus_eq_theta]
      refine le_trans (Commons.NumberTheory.Chebyshev.theta_le_log3_mul (slowCutoff x)) ?_
      have hfloor : (slowCutoff x : ℝ) ≤ Real.log (Real.log (x : ℝ)) :=
        Nat.floor_le (Real.log_nonneg hlog1)
      exact mul_le_mul_of_nonneg_left hfloor (Real.log_nonneg (by norm_num))
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hθ hsqrtpos.le
  · have h := tendsto_loglog_div_sqrtlog.const_mul (Real.log 3)
    simpa using h


/-- The cutoff `⌊log log x⌋` eventually exceeds all the differences `H j - H i`. -/
theorem eventually_slowCutoff_gt {k : ℕ} (H : Fin k → ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ i j : Fin k, i ≠ j → H j - H i < slowCutoff x := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ i : Fin k, H i ≤ N := ⟨Finset.univ.sup H, fun i =>
    Finset.le_sup (Finset.mem_univ i)⟩
  filter_upwards [tendsto_slowCutoff.eventually (eventually_gt_atTop (N + 1))] with x hx
  intro i j _
  have : H j - H i ≤ N := by
    have := hN j
    omega
  omega

/-- A sieve level `D` dominating `x^σ`. -/
theorem exists_sieve_level (σ : ℝ) :
    ∃ D : ℕ → ℕ, ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ σ ≤ (D x : ℝ) :=
  ⟨fun x => ⌈((x : ℝ) ^ σ)⌉₊, Filter.Eventually.of_forall fun x => Nat.le_ceil _⟩

end Commons.NumberTheory.MaynardSieve
