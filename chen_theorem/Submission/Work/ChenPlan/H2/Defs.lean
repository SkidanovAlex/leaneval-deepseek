import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.H1.Defs

/-!
# h2 at `M = x^{1/10}`: the per-`q` sieve problem and its vocabulary

This module sets up the objects used to deduce Chen's `h2`

  `Σ_{q ∈ winPrimes M Y} apMass x M q ≤ (39/25) · x · VsieveOdd M`     (`M = ⌊x^{1/10}⌋+1`)

from the upper linear sieve `LinearSieveUpper` (`Submission/ChenPlan/Interfaces.lean`).

For each window prime `q` we sieve the subsequence `{p ≤ x : p prime, q ∣ p + 2}` of the
shifted primes by the odd primes `< M`, with density `ν(d) = 1/φ(d)`, total mass
`X = x/φ(q)` and level `Λ = D/q` (`D = √x/(log x)^B`).  The sifted sum is exactly
`apMass x M q`; the remainder is the Bombieri–Vinogradov quantity `remSumQ`, and the main
term involves the sieve product `VsieveOdd M` and the linear-sieve envelope `Utab`.

* `apSupport`, `apSieve` : the `BoundingSieve` attached to the residue class `q`
  (the density `ν`, the weight `log (n-2)` and the squarefreeness of `oddPrimLt M`
  are taken from `Work.ChenPlan.H1.Defs`).
* `shiftRem`, `remSumQ` : the (weighted) Bombieri–Vinogradov remainder of that sieve.
-/

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.ChenPlan.H2

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight
open Work.ChenPlan.H1 (chenSupport chenWeight chenWeight_nonneg chenWeight_add_two
  invTotient invTotient_apply invTotient_mult oddPrimLt_squarefree)

/-! ## The sieve problem attached to a residue class `q` -/

/-- The support of the per-`q` sieve: the shifted primes `p + 2`, `p ≤ x` prime, with
`q ∣ p + 2`. -/
def apSupport (x q : ℕ) : Finset ℕ := (chenSupport x).filter (fun n => q ∣ n)

/-- **The sieve problem of the residue class `q`**: shifted primes divisible by `q`,
sifting the odd primes below `M`, density `ν = 1/φ`, total mass `x/φ(q)`. -/
def apSieve (x M q : ℕ) : BoundingSieve where
  support := apSupport x q
  prodPrimes := oddPrimLt M
  prodPrimes_squarefree := oddPrimLt_squarefree M
  weights := chenWeight
  weights_nonneg := chenWeight_nonneg
  totalMass := (x : ℝ) / (q.totient : ℝ)
  nu := invTotient
  nu_mult := invTotient_mult
  nu_pos_of_prime := by
    intro p hp _
    rw [invTotient_apply]
    exact inv_pos.mpr (by exact_mod_cast (Nat.totient_pos.mpr hp.pos))
  nu_lt_one_of_prime := by
    intro p hp hpd
    rw [invTotient_apply]
    have hpne2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpd
      have h0 : oddPrimLt M % 2 = 0 := Nat.mod_eq_zero_of_dvd hpd
      have h1 := oddPrimLt_odd M
      omega
    have hp3 : 3 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hpne2
      · omega
    rw [Nat.totient_prime hp, Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    exact inv_lt_one_of_one_lt₀ (by linarith)

@[simp] lemma apSieve_support (x M q : ℕ) : (apSieve x M q).support = apSupport x q := rfl
@[simp] lemma apSieve_prodPrimes (x M q : ℕ) : (apSieve x M q).prodPrimes = oddPrimLt M := rfl
@[simp] lemma apSieve_weights (x M q : ℕ) : (apSieve x M q).weights = chenWeight := rfl
@[simp] lemma apSieve_nu (x M q : ℕ) : (apSieve x M q).nu = invTotient := rfl
@[simp] lemma apSieve_totalMass (x M q : ℕ) :
    (apSieve x M q).totalMass = (x : ℝ) / (q.totient : ℝ) := rfl

/-! ## The remainder of the sieve -/

/-- `|θ_m(x) - x/φ(m)|`, the Bombieri–Vinogradov error at the modulus `m`. -/
def shiftRem (x m : ℕ) : ℝ := |thetaD x m - (x : ℝ) / (m.totient : ℝ)|

/-- The `3^{ω(d)}`-weighted remainder attached to the residue class `q` at level `Λ`:
the remainders of the sieve `apSieve x M q` with `d ∣ oddPrimLt M`, `d < Λ`. -/
def remSumQ (x M q : ℕ) (Λ : ℝ) : ℝ :=
  ((oddPrimLt M).divisors.filter (fun d : ℕ => (d : ℝ) < Λ)).sum
    (fun d => (3 : ℝ) ^ d.primeFactors.card * shiftRem x (q * d))

lemma remSumQ_nonneg (x M q : ℕ) (Λ : ℝ) : 0 ≤ remSumQ x M q Λ :=
  Finset.sum_nonneg fun d _ => mul_nonneg (by positivity) (abs_nonneg _)

/-! ## Elementary identification lemmas -/

/-- A prime `p` with `p ∣ oddPrimLt M` is an odd prime `< M`. -/
lemma prime_of_dvd_oddPrimLt {p M : ℕ} (hp : p.Prime) (hpd : p ∣ oddPrimLt M) :
    p ∈ oddLt M := by
  have hprod : p ∣ ∏ q ∈ oddLt M, q := by
    rwa [← oddPrimLt_eq_prod_oddLt]
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q : ℕ => q)).mp hprod
  have hqp : q.Prime := (Submission.mem_oddLt.mp hq).1
  rcases (Nat.dvd_prime hqp).mp hpq with h | h
  · exact absurd h hp.ne_one
  · rwa [h]

/-- Every prime factor of a divisor of `oddPrimLt M` is `< M`. -/
lemma primeFactor_lt_of_dvd_oddPrimLt {p d M : ℕ} (hd : d ∣ oddPrimLt M)
    (hp : p.Prime) (hpd : p ∣ d) : p < M :=
  (Submission.mem_oddLt.mp (prime_of_dvd_oddPrimLt hp (dvd_trans hpd hd))).2.2

/-- A window prime is coprime to every divisor of `oddPrimLt M`. -/
lemma coprime_winPrime_divisor {M q d : ℕ} (hq : q.Prime) (hqM : M ≤ q) (hd : d ∣ oddPrimLt M) :
    Nat.Coprime q d := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  have h1 : Nat.gcd q d ≠ 1 := h
  have h2 : Nat.gcd q d ∣ q := Nat.gcd_dvd_left q d
  have h3 : Nat.gcd q d ∣ d := Nat.gcd_dvd_right q d
  obtain ⟨r, hrp, hrg⟩ := Nat.exists_prime_and_dvd h1
  have hrq : r = q := by
    rcases (Nat.dvd_prime hq).mp (dvd_trans hrg h2) with hh | hh
    · exact absurd hh hrp.ne_one
    · exact hh
  have hrM : r < M := primeFactor_lt_of_dvd_oddPrimLt hd hrp (dvd_trans hrg h3)
  omega

/-- The pointwise weight identity behind `apSieve_multSum`. -/
lemma apWt_ite (q d p : ℕ) (hcd : Nat.Coprime q d) :
    (if q ∣ p + 2 then (if d ∣ p + 2 then chenWeight (p + 2) else 0) else 0)
      = Real.log (p : ℝ) * (if q * d ∣ p + 2 then 1 else 0) := by
  by_cases hq : q ∣ p + 2
  · by_cases hd : d ∣ p + 2
    · rw [if_pos hq, if_pos hd, if_pos (hcd.mul_dvd_of_dvd_of_dvd hq hd), chenWeight_add_two p]
      ring
    · rw [if_pos hq, if_neg hd, if_neg (fun h => hd (dvd_trans (dvd_mul_left d q) h))]
      ring
  · rw [if_neg hq, if_neg (fun h => hq (dvd_trans (dvd_mul_right q d) h))]
    ring

/-- The `multSum` of the sieve at `d` is `θ x (q*d)`, for a window prime `q` and a divisor
`d` of `oddPrimLt M`. -/
lemma apSieve_multSum {x M q d : ℕ} (hqp : q.Prime) (hqM : M ≤ q) (hd : d ∣ oddPrimLt M) :
    (apSieve x M q).multSum d = thetaD x (q * d) := by
  have hcd : Nat.Coprime q d := coprime_winPrime_divisor hqp hqM hd
  rw [BoundingSieve.multSum]
  rw [show (apSieve x M q).support = apSupport x q from rfl,
    show (apSieve x M q).weights = chenWeight from rfl]
  rw [apSupport, Finset.sum_filter, chenSupport, Finset.sum_image]
  · rw [thetaD_eq]
    exact Finset.sum_congr rfl (fun p _ => apWt_ite q d p hcd)
  · intro a _ b _ hab
    exact Nat.add_right_cancel hab

/-- The remainder of the sieve at `d` is `θ x (q*d) - x/φ(q*d)`. -/
lemma apSieve_rem {x M q d : ℕ} (hqp : q.Prime) (hqM : M ≤ q) (hd : d ∣ oddPrimLt M) :
    (apSieve x M q).rem d = thetaD x (q * d) - (x : ℝ) / ((q * d).totient : ℝ) := by
  have hcd : Nat.Coprime q d := coprime_winPrime_divisor hqp hqM hd
  rw [BoundingSieve.rem, apSieve_multSum hqp hqM hd]
  rw [show (apSieve x M q).nu d = invTotient d from rfl,
    show (apSieve x M q).totalMass = (x : ℝ) / (q.totient : ℝ) from rfl,
    invTotient_apply]
  rw [Nat.totient_mul hcd, Nat.cast_mul]
  field_simp

/-- `ν d = 1/φ(d)` for divisors of `oddPrimLt M`. -/
lemma invTotient_eq (M d : ℕ) (_hd : d ∣ oddPrimLt M) :
    invTotient d = 1 / (d.totient : ℝ) := by
  rw [invTotient_apply, one_div]

/-- `apMass` as a sum over `range (x+1)` of an indicator. -/
lemma apMass_eq_range (x M q : ℕ) :
    Submission.apMass x M q =
      (Finset.range (x + 1)).sum (fun p => if p.Prime ∧ (oddPrimLt M).Coprime (p + 2) ∧ q ∣ p + 2
        then Real.log (p : ℝ) else 0) := by
  rw [Submission.apMass, Submission.s0Set, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp : p.Prime <;> by_cases hc : (p + 2).Coprime (oddPrimLt M) <;>
    by_cases hq : q ∣ p + 2 <;>
    simp [Commons.NumberTheory.Chen.ChenEight.Id, hp, hc, hq, Nat.coprime_comm]

/-- The support as an image of the prime range. -/
lemma apSupport_eq_image (x q : ℕ) :
    apSupport x q
      = ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ q ∣ p + 2)).image (fun p => p + 2) := by
  ext n
  simp only [apSupport, chenSupport, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨p, hp, hpn⟩, hqn⟩
    refine ⟨p, ⟨hp.1, hp.2, ?_⟩, hpn⟩
    rwa [hpn]
  · rintro ⟨p, ⟨hp1, hp2, hq⟩, hpn⟩
    exact ⟨⟨p, ⟨hp1, hp2⟩, hpn⟩, hpn ▸ hq⟩

/-- Sums over the support can be taken over the prime range. -/
lemma sum_apSupport (x q : ℕ) (g : ℕ → ℝ) :
    (apSupport x q).sum g
      = ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ q ∣ p + 2)).sum
          (fun p => g (p + 2)) := by
  rw [apSupport_eq_image]
  exact Finset.sum_image (fun a _ b _ hab => Nat.add_right_cancel hab)

/-- The `siftedSum` of the sieve as a sum over `range (x+1)` of the same indicator. -/
lemma siftedSum_eq_range (x M q : ℕ) :
    (apSieve x M q).siftedSum =
      (Finset.range (x + 1)).sum (fun p => if p.Prime ∧ (oddPrimLt M).Coprime (p + 2) ∧ q ∣ p + 2
        then Real.log (p : ℝ) else 0) := by
  rw [BoundingSieve.siftedSum,
    show (apSieve x M q).support = apSupport x q from rfl,
    show (apSieve x M q).prodPrimes = oddPrimLt M from rfl,
    show (apSieve x M q).weights = chenWeight from rfl]
  rw [sum_apSupport]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp : p.Prime <;> by_cases hq : q ∣ p + 2 <;>
    by_cases hc : (p + 2).Coprime (oddPrimLt M) <;>
    simp [hp, hq, hc, chenWeight_add_two p, Nat.coprime_comm]

/-- The `siftedSum` of the sieve is Chen's `apMass`. -/
lemma apSieve_siftedSum (x M q : ℕ) : (apSieve x M q).siftedSum = Submission.apMass x M q := by
  rw [siftedSum_eq_range, apMass_eq_range]

/-- `sieveV` of the sieve is the odd Euler product `VsieveOdd`. -/
lemma apSieve_sieveV (x M q : ℕ) : Submission.ChenPlan.sieveV (apSieve x M q) = VsieveOdd M := by
  rw [Submission.ChenPlan.sieveV]
  rw [show (apSieve x M q).prodPrimes = oddPrimLt M from rfl,
    show (apSieve x M q).nu = invTotient from rfl]
  have hpf : (oddPrimLt M).primeFactors = oddLt M := by
    rw [oddPrimLt_eq_prod_oddLt]
    exact Nat.primeFactors_prod (fun p hp => (Submission.mem_oddLt.mp hp).1)
  rw [hpf]
  unfold VsieveOdd
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [invTotient_apply]
  have hp3 : 3 ≤ p := (Submission.mem_oddLt.mp hp).2.1
  rw [Nat.totient_prime (Submission.mem_oddLt.mp hp).1, Nat.cast_sub (by omega : 1 ≤ p)]
  push_cast
  ring

/-- `remSum` of the sieve is the `3^{ω(d)}`-weighted Bombieri–Vinogradov remainder
`remSumQ`. -/
lemma apSieve_remSum {x M q : ℕ} (hqp : q.Prime) (hqM : M ≤ q) (Λ : ℝ) :
    Submission.ChenPlan.remSum (apSieve x M q) Λ = remSumQ x M q Λ := by
  rw [Submission.ChenPlan.remSum, remSumQ]
  rw [show (apSieve x M q).prodPrimes = oddPrimLt M from rfl]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ oddPrimLt M := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  rw [apSieve_rem hqp hqM hdvd]
  rfl

end

end Work.ChenPlan.H2
