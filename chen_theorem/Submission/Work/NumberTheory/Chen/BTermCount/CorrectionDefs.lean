import Submission.Work.NumberTheory.Chen.BTermCount.MVTInput

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The bilinear level of distribution for the ternary sequence: the corrected remainder

`Submission.Work.NumberTheory.Chen.BTermCount.MVTInput` defines the remainder

  `bRem x M Y d = #{n ∈ B̄ : d ∣ n - 2} - #B̄ / φ(d)`

of the ternary sieve sequence `n ↦ n - 2`, `n = q q₂ q₃ ∈ B̄`.  The main term `#B̄ / φ(d)`
is the *naive* one.  It ignores that the elements of `B̄` sharing a prime factor with `d` can
never satisfy `d ∣ n - 2`: indeed, if `d` is odd and `p ∣ d`, `p ∣ n` then `p ∣ n - 2` forces
`p ∣ 2 ∤ d`, a contradiction.  Concretely, for a window prime `q ∈ [M, Y)` the whole branch
`q ∣ n` of `B̄` (of size `N_q = #{n ∈ B̄ : q ∣ n}`, for `x = 10⁷`, `q = 5`: `N_5 = 40665`
against `#B̄ = 168512`) is excluded, so that

  `r_d = -Σ_{q ∣ d} N_q / φ(d) + (equidistribution error)`.

The first term is *systematic* and, summed over `d ≤ D` with the weights `3 ^ (ω d)`, equals
`409901` (resp. `5327822`) at `x = 10⁷` (resp. `10⁸`), i.e. `10.6` (resp. `18.1`) times
`x / log² x` — it dominates the whole discrepancy sum at these values of `x`.

The *correct* sieve main term (the one produced by the orthogonality relations, and the one in
the bilinear Bombieri–Vinogradov lemma of Bombieri–Johnston–Starichkova / Pan) restricts the
elements of `B̄` to those coprime to `d`.  This module introduces that corrected remainder
`bRemCorr` together with

  `bShared x M Y d = #{n ∈ B̄ : ∃ p prime, p ∣ d ∧ p ∣ n}`  (`= #B̄ - #{n ∈ B̄ : (n,d) = 1}`)

and records the elementary identity `bRem = bRemCorr - bShared / φ(d)`.  The level of
distribution for `bRem` therefore splits into the (deep) level of distribution for `bRemCorr`
plus the (elementary) bound on the mass `bShared`.
-/

/-- The number of elements of `B̄` sharing a prime factor with `d`. -/
noncomputable def bShared (x M Y d : ℕ) : ℕ :=
  ((bProdSet x M Y).filter (fun n => ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p ∣ n)).card

theorem bShared_le_card (x M Y d : ℕ) : bShared x M Y d ≤ (bProdSet x M Y).card :=
  Finset.card_filter_le _ _

/-- The remainder of the ternary sieve sequence with the **corrected** (multiplicative-density)
main term: only the elements of `B̄` that are coprime to `d` are allowed to contribute to the
main term.  Equivalently `bRemCorr x M Y d = #{n ∈ B̄ : d ∣ n - 2} - #{n ∈ B̄ : (n,d) = 1} / φ(d)`. -/
noncomputable def bRemCorr (x M Y d : ℕ) : ℝ :=
  (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ)
    - (((bProdSet x M Y).card : ℝ) - (bShared x M Y d : ℝ)) / (Nat.totient d : ℝ)

/-- **The elementary decomposition.**  The naive remainder differs from the corrected one by the
mass of the elements of `B̄` sharing a prime factor with `d`, divided by `φ(d)`. -/
theorem bRem_eq_bRemCorr_sub (x M Y d : ℕ) :
    bRem x M Y d = bRemCorr x M Y d - (bShared x M Y d : ℝ) / (Nat.totient d : ℝ) := by
  unfold bRem bRemCorr
  ring

end Work.NumberTheory.Chen.BTermCount
