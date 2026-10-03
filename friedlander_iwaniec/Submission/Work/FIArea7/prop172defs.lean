/-
# `Submission.Work.FIArea7.prop172defs` — shared vocabulary of the *FI* §25 reduction

Definitions used by `Submission/Work/FIArea7/prop172classical.lean` (the reduction of *FI*
Proposition 17.2 / (17.18) to Props. 23.1, 23.2 and Theorem 2ψ, following *FI* §25) and by the
lemmas delegated for it.  Every declaration here is proved; the file contains no `sorry`.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.SepDiv
import Submission.Work.FIArea7.sepIdx_partition

set_option autoImplicit false

namespace Work.FIArea7

open Finset

/-- **The *FI* §24 separation condition with the total number of prime factors fixed.**  For a
given total `k`, a decreasing list `p : Fin k → ℕ` of primes with product `d·m·n` whose
`dIdx`-positions multiply to `d`, its `mIdx`-positions to `m` and its `nIdx`-positions to `n`. -/
def IsSepPairK (r k : ℕ) (d m n : ℕ) : Prop :=
  ∃ p : Fin k → ℕ, IsPrimeList (d * m * n) k p ∧ d = ∏ i ∈ dIdx r k, p i ∧
    m = ∏ i ∈ mIdx r k, p i ∧ n = ∏ i ∈ nIdx r k, p i

/-- `IsSepPair` is `IsSepPairK` for some `k`, by definition of the two predicates. -/
theorem isSepPair_iff_exists_isSepPairK (r d m n : ℕ) :
    IsSepPair r d m n ↔ ∃ k, IsSepPairK r k d m n := Iff.rfl

/-- The prime-avoidance condition *FI* (5.8) on the **norm**: `(n, Π) = 1` for
`Π = ∏_{q ≤ Pz} q`. -/
def NoSmallPrimesNat (Pa : Work.FITop.Params) (n : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ Pa.Pz → ¬ q ∣ n

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The indicator of the prime-avoidance condition, as a `ℂ`-valued weight: `nspInd Pa n = 1` if
`(n, Π) = 1` and `0` otherwise.  (`NoSmallPrimesNat Pa` is not a decidable proposition, so the
indicator is bundled here once and for all, to keep the statements of the delegated estimates
free of `if`s over undecidable propositions.) -/
def nspInd (Pa : Work.FITop.Params) (n : ℕ) : ℂ := if NoSmallPrimesNat Pa n then 1 else 0

lemma norm_nspInd_le_one (Pa : Work.FITop.Params) (n : ℕ) : ‖nspInd Pa n‖ ≤ 1 := by
  unfold nspInd
  split <;> simp

/-- `nspInd` is multiplicative on coprime arguments. -/
lemma nspInd_mul (Pa : Work.FITop.Params) {m n : ℕ} (h : Nat.Coprime m n) :
    nspInd Pa (m * n) = nspInd Pa m * nspInd Pa n := by
  unfold nspInd
  by_cases hmn : NoSmallPrimesNat Pa (m * n)
  · have hm : NoSmallPrimesNat Pa m := fun q hq hqPz hdvd =>
      hmn q hq hqPz (Dvd.dvd.mul_right hdvd n)
    have hn : NoSmallPrimesNat Pa n := fun q hq hqPz hdvd =>
      hmn q hq hqPz (Dvd.dvd.mul_left hdvd m)
    rw [if_pos hmn, if_pos hm, if_pos hn, mul_one]
  · rw [if_neg hmn]
    have hkey : ¬ (NoSmallPrimesNat Pa m ∧ NoSmallPrimesNat Pa n) := by
      rintro ⟨hm, hn⟩
      exact hmn (fun q hq hqPz hdvd => by
        rcases (Nat.Prime.dvd_mul hq).mp hdvd with h1 | h1
        · exact hm q hq hqPz h1
        · exact hn q hq hqPz h1)
    rcases not_and_or.mp hkey with h | h
    · rw [if_neg h, zero_mul]
    · rw [if_neg h, mul_zero]

end

end Work.FIArea7
