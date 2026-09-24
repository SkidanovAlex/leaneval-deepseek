import Mathlib
import Submission.Chen.SwitchDefs
import Submission.ChenPlan.Interfaces
import Submission.Work.NumberTheory.Chen.BTermCount.Defs
import Submission.Work.NumberTheory.Chen.BTermCount.CorrectionDefs
import Submission.Work.NumberTheory.Chen.BTermCount.SelbergWeightsSpec

/-!
# Chen's `h3`: the sieve problem

The sieve problem of Chen's `h3` (the switched `B`-term) at sift limit `M` and window top `Y`
(the end application uses `M = Submission.chenSiftLimitTenth x`, `Y = Submission.chenWindowTop x`):

* support: the shifted products `n - 2` for `n ∈ B̄ = bProdSet x M Y`,
* weights: `1`,
* sifting primes: the odd primes below `Y` (`ChenEight.oddPrimLt Y`),
* `X = totalMass = #B̄`, density `ν d = 1/φ(d)`.

The sifted sum is then exactly the number of *survivors*
`survivorSet x M Y = {n ∈ B̄ : no odd prime < Y divides n - 2}`, the remainder is
`bRem x M Y d = # {n ∈ B̄ : d ∣ n - 2} - #B̄/φ(d)`, and `sieveV` is the odd Mertens product
`VsieveOdd Y = ∏_{3 ≤ p < Y} (1 - 1/(p-1))`.

This module builds the `BoundingSieve` instance and identifies these four quantities.
It is modelled on the `h1` analogue `Submission.Work.ChenPlan.H1.Defs`.
-/

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.ChenPlan.H3

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight
open Work.NumberTheory.Chen.BTermCount

/-! ## The arithmetic function `d ↦ 1/φ(d)` -/

/-- `d ↦ 1/φ(d)` as an arithmetic function; multiplicative, with value `1/(p-1)` at an odd prime. -/
def invTotient : ArithmeticFunction ℝ :=
  ⟨fun n => ((Nat.totient n : ℕ) : ℝ)⁻¹, by simp⟩

lemma invTotient_apply (n : ℕ) : invTotient n = ((Nat.totient n : ℕ) : ℝ)⁻¹ := rfl

lemma invTotient_mult : ArithmeticFunction.IsMultiplicative invTotient := by
  constructor
  · rw [invTotient_apply, Nat.totient_one]; norm_num
  · intro m n hmn
    rw [invTotient_apply, invTotient_apply, invTotient_apply, Nat.totient_mul hmn,
      Nat.cast_mul, mul_inv]

/-! ## Coprimality with the odd primorial -/

/-- `oddPrimLt Y` is the product of the odd primes below `Y`. -/
lemma oddPrimLt_eq_prodOddLt (Y : ℕ) : oddPrimLt Y = ∏ p ∈ oddLt Y, p := by
  rw [oddPrimLt_eq_prod_oddLt]

/-- An integer `a` is coprime to the odd primorial below `Y` exactly when no odd prime
below `Y` divides it. -/
lemma coprime_oddPrimLt_iff {Y a : ℕ} :
    Nat.Coprime (oddPrimLt Y) a ↔ ∀ q ∈ oddLt Y, ¬ q ∣ a := by
  rw [oddPrimLt_eq_prodOddLt, Nat.coprime_comm, Nat.coprime_prod_right_iff]
  refine ⟨fun h q hq => ?_, fun h q hq => ?_⟩
  · have hp : q.Prime := (Submission.mem_oddLt.mp hq).1
    exact hp.coprime_iff_not_dvd.mp (Nat.coprime_comm.mp (h q hq))
  · have hp : q.Prime := (Submission.mem_oddLt.mp hq).1
    exact Nat.coprime_comm.mpr (hp.coprime_iff_not_dvd.mpr (h q hq))

/-! ## The support, the weights and the sieve -/

/-- The support of the sieve: the shifted products `n - 2` for `n ∈ B̄`. -/
def bSupport (x M Y : ℕ) : Finset ℕ := (bProdSet x M Y).image (fun n => n - 2)

/-- `n - 2` determines `n` for `n ≥ 2`. -/
lemma injOn_sub_two {s : Finset ℕ} (hs : ∀ n ∈ s, 2 ≤ n) :
    ∀ a ∈ s, ∀ b ∈ s, a - 2 = b - 2 → a = b := by
  intro a ha b hb h
  have ha2 := hs a ha
  have hb2 := hs b hb
  omega

/-- Every element of `B̄` is `≥ 2`. -/
lemma two_le_of_mem_bProdSet {x M Y n : ℕ} (hn : n ∈ bProdSet x M Y) : 2 ≤ n := by
  have h := bProdSet_subset_Icc x M Y hn
  simp only [Finset.mem_Icc] at h
  exact h.1

/-- **Chen's `h3` sieve problem**: weights `1` on the shifted products `{n - 2 : n ∈ B̄}`,
sifting the odd primes below `Y`, approximation `X = #B̄`, density `ν d = 1/φ(d)`. -/
def bSieve (x M Y : ℕ) : BoundingSieve where
  support := bSupport x M Y
  prodPrimes := oddPrimLt Y
  prodPrimes_squarefree := squarefree_oddPrimLt Y
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := ((bProdSet x M Y).card : ℝ)
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
      have h0 : oddPrimLt Y % 2 = 0 := Nat.mod_eq_zero_of_dvd hpd
      have h1 := oddPrimLt_odd Y
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

/-! ## The identification of the sieve quantities -/

/-- The weight of the multiples of `d` in the sieve is `#{n ∈ B̄ : d ∣ n - 2}`. -/
lemma bSieve_multSum (x M Y d : ℕ) :
    (bSieve x M Y).multSum d
      = (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ) := by
  rw [BoundingSieve.multSum]
  rw [show (bSieve x M Y).support = bSupport x M Y from rfl,
    show (bSieve x M Y).weights = fun _ : ℕ => (1 : ℝ) from rfl]
  rw [bSupport, Finset.sum_image (injOn_sub_two (fun n hn => two_le_of_mem_bProdSet hn))]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : d ∣ n - 2 <;> simp [h]

/-- The remainder of the sieve is the `B`-term remainder `bRem`. -/
lemma bSieve_rem (x M Y d : ℕ) : (bSieve x M Y).rem d = bRem x M Y d := by
  rw [BoundingSieve.rem, bSieve_multSum]
  rw [show (bSieve x M Y).nu d = invTotient d from rfl,
    show (bSieve x M Y).totalMass = ((bProdSet x M Y).card : ℝ) from rfl,
    invTotient_apply, bRem]
  rw [div_eq_inv_mul]

/-- The sifted sum of the sieve is the number of survivors. -/
lemma bSieve_siftedSum (x M Y : ℕ) :
    (bSieve x M Y).siftedSum = (survivorCount x M Y : ℝ) := by
  rw [BoundingSieve.siftedSum]
  rw [show (bSieve x M Y).support = bSupport x M Y from rfl,
    show (bSieve x M Y).prodPrimes = oddPrimLt Y from rfl,
    show (bSieve x M Y).weights = fun _ : ℕ => (1 : ℝ) from rfl]
  rw [survivorCount_eq_card, survivorSet]
  rw [bSupport, Finset.sum_image (injOn_sub_two (fun n hn => two_le_of_mem_bProdSet hn))]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : Nat.Coprime (oddPrimLt Y) (n - 2)
  · rw [if_pos h, if_pos ((coprime_oddPrimLt_iff).mp h)]; norm_num
  · rw [if_neg h, if_neg (fun hc => h ((coprime_oddPrimLt_iff).mpr hc))]; norm_num

/-- `sieveV` of the sieve is the odd Euler product `VsieveOdd`. -/
lemma bSieve_sieveV (x M Y : ℕ) : Submission.ChenPlan.sieveV (bSieve x M Y) = VsieveOdd Y := by
  rw [Submission.ChenPlan.sieveV]
  rw [show (bSieve x M Y).prodPrimes = oddPrimLt Y from rfl,
    show (bSieve x M Y).nu = invTotient from rfl]
  rw [primeFactors_oddPrimLt]
  unfold VsieveOdd
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp3 : 3 ≤ p := (Submission.mem_oddLt.mp hp).2.1
  rw [invTotient_apply, Nat.totient_prime (Submission.mem_oddLt.mp hp).1,
    Nat.cast_sub (by omega : 1 ≤ p)]
  push_cast
  ring

/-- `remSum` of the sieve is the `3^{ω(d)}`-weighted sum of `|bRem|` over the divisors of the
odd primorial below the level `D`. -/
lemma bSieve_remSum (x M Y : ℕ) (D : ℝ) :
    Submission.ChenPlan.remSum (bSieve x M Y) D
      = ∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < D),
          (3 : ℝ) ^ d.primeFactors.card * |bRem x M Y d| := by
  rw [Submission.ChenPlan.remSum]
  rw [show (bSieve x M Y).prodPrimes = oddPrimLt Y from rfl]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [bSieve_rem]

end

end Work.ChenPlan.H3
