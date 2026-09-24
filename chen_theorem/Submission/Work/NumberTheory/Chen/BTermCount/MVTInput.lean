import Submission.Work.NumberTheory.Chen.BTermCount.Basic

open Finset Filter
open scoped BigOperators Topology

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The missing input: a level of distribution for the ternary sequence

The `B`-term sieve is the upper-bound sieve for the sequence

    𝒜 = { n - 2 : n = q q₂ q₃ ∈ B̄ } ,   sieved by the odd primes `< Y` .

For a modulus `d | P(Y)` the relevant quantity is

    r_d = #{n ∈ B̄ : d ∣ n - 2} - #B̄ / φ(d) ,

and the sieve's error term is `Σ_{d ≤ D} 3 ^ (ω d) |r_d|`.  This module isolates the exact
statement needed, in the same shape as the *proved* level-of-distribution theorem for shifted
primes (`Commons.NumberTheory.BombieriVinogradov.level_of_distribution_shift_vonMangoldt`).

Since `n = q q₂ q₃` and all prime factors of `d | P(Y)` are `< Y ≤ q₂, q₃`, the congruence
`q q₂ q₃ ≡ 2 (mod d)` is a congruence for `q` alone (the cofactor `q₂q₃` is invertible mod `d`),
so `r_d` is a *bilinear* remainder: it involves `#{q₂q₃ ≡ a (mod d)}` for the semiprime
cofactor.  Controlling `Σ_{d ≤ D} |r_d|` at level `D ≈ √x` is therefore the Bombieri–Vinogradov
mean value theorem for bilinear forms (BJS Lemma `lemma:bf`, Pan's theorem) — the piece which is
*not* available in this workspace; the linear analogue is proved here, and the bilinear mean
value theorem is work in progress elsewhere in the repository
(`Submission/Work/NumberTheory/BombieriVinogradov/mvt_wip.lean`).

Everything in this file is unconditional; the hypothesis below is only *used* in
`SelbergSieve.lean` / `MainMVT.lean`.
-/

/-- The remainder `#{n ∈ B̄ : d ∣ n-2} − #B̄/φ(d)` of the ternary sieve sequence. -/
noncomputable def bRem (x M Y d : ℕ) : ℝ :=
  (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ)
    - ((bProdSet x M Y).card : ℝ) / (Nat.totient d : ℝ)

/-- **The level of distribution for the ternary sequence.**  For every `A > 0` there is `B > 0`
such that, eventually in `x`, the divisor-weighted remainders over odd moduli
`d ≤ √x / (log x)^B` are at most `x / (log x)^A`. -/
def BTernaryLevelOfDistribution : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
    ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
        (fun d : ℕ => d % 2 = 1)).sum
      (fun d => (3 : ℝ) ^ (d.primeFactors.card) * |bRem x (Submission.chenSiftLimit x)
        (Submission.chenWindowTop x) d|)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A

/-- The same input, only over moduli dividing the odd primorial below the window top `Y`
(which is the only case the sieve uses; for `D ≤ Y` the two formulations agree since any
`d ≤ D` has all its prime factors `< Y`). -/
def BTernaryLevelOfDistribution' : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
    ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
        (fun d : ℕ => d % 2 = 1 ∧ d ∣ oddPrimLt (Submission.chenWindowTop x))).sum
      (fun d => (3 : ℝ) ^ (d.primeFactors.card) * |bRem x (Submission.chenSiftLimit x)
        (Submission.chenWindowTop x) d|)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A

/-- The unweighted version (this is the form in which the linear analogue is available in the
commons for shifted primes). -/
def BTernaryLevelOfDistribution0 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
    ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
        (fun d : ℕ => d % 2 = 1)).sum
      (fun d => |bRem x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) d|)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A

end Work.NumberTheory.Chen.BTermCount
