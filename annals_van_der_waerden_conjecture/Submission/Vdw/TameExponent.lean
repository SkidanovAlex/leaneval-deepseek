import Mathlib
import Submission.Vdw.TamePrep
import Submission.Commons.NumberTheory.NumberField.tame_different_not_pow_dvd

open Classical
open scoped NumberField
open UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Tame different, count form (Dedekind's theorem for tame primes)

Completes the **tame-different theorem** in the count form used by the
discriminant-index (Lemma 24) programme.  The upper bound
`¬ P^e | 𝔡` for tame primes (`p ∤ e`) was proved by the shared commons
(`Commons.NumberTheory.NumberField.tame_different`, a global
trace-witness argument); `Submission/Vdw/TamePrep.lean` supplies the free
lower bound `m_P ≥ e_P − 1`, the equivalence between the count and
divisibility forms, and the *tameness input* (`e_P ≤ [K : ℚ]`, so that
`p > [K : ℚ]` makes every prime over `p` tame).

Assembled here:

* `tame_count_eq` : `p ∤ e_P` ⟹ `m_P = e_P − 1` (count form of Dedekind's
  different theorem for tame primes);
* `tame_count_of_gt_degree` : `p > [K : ℚ]` prime ⟹ `m_P = e_P − 1` for
  every prime `P` over `p`;
* `discr_val_tame_of_gt_degree` : `p > [K : ℚ]` prime ⟹
  `v_p(|discr K|) = Σ_{P | p} f_P·(e_P − 1)` — the exact tame shape of the
  discriminant valuation that the residue-side comparison of Bhargava's
  Lemma 24 consumes (together with the decomposition L58–L60 and the
  finiteness input `ramIdx_mul_inertiaDeg_le_finrank`).
-/

namespace Submission.Vdw

noncomputable section

open Ideal

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- **Tame different, count form**: for a tame prime (`p ∤ e_P`) the exponent
`m_P` of `P` in the different ideal is exactly `e_P − 1`. -/
theorem tame_count_eq (p : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (htame : ¬ p ∣ P.ramificationIdx ℤ) :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P = P.ramificationIdx ℤ - 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hupper : (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤ P.ramificationIdx ℤ - 1 :=
    (different_count_le_iff_not_pow_dvd (K := K) p hp P).mpr
      (Commons.NumberTheory.NumberField.tame_different_not_pow_dvd (K := K) p P htame)
  exact different_count_eq_sub_one_of_le (K := K) p hp P hupper

/-- For `p > [K : ℚ]` prime, every prime ideal of `𝒪_K` over `p` has
different-ideal exponent exactly `e_P − 1` (tame, by
`tame_of_prime_gt_finrank`). -/
theorem tame_count_of_gt_degree (p : ℕ) (hp : Nat.Prime p)
    (hgt : Module.finrank ℚ K < p) (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P = P.ramificationIdx ℤ - 1 := by
  exact tame_count_eq (K := K) p hp P (tame_of_prime_gt_finrank (K := K) p hp hgt P)

/-- **Tame shape of the discriminant valuation**: for `p > [K : ℚ]` prime,
`v_p(|discr K|) = Σ_{P | p} f_P·(e_P − 1)` (sum over the prime ideals
dividing the different that lie over `p`; unramified primes contribute
`f_P·0 = 0` and so are absent).  This is the exact input of the residue-side
comparison of Lemma 24. -/
theorem discr_val_tame_of_gt_degree (p : ℕ) [Fact (Nat.Prime p)]
    (hgt : Module.finrank ℚ K < p) :
    padicValNat p (NumberField.discr K).natAbs =
      (((normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
        (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))).sum
        fun P : Ideal (𝓞 K) => P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)) := by
  exact discr_val_eq_sum_f_mul_sub_one (K := K) (p := p) (by
    intro P hPmem hPover
    have hPmem' : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) :=
      (Multiset.mem_toFinset.mp hPmem)
    have hδ : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
    have hmax : P.IsMaximal :=
      Commons.NumberTheory.NumberField.isMaximal_of_mem_normalizedFactors hδ hPmem'
    haveI : P.IsMaximal := hmax
    haveI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hPover
    exact tame_count_of_gt_degree (K := K) p (Fact.out (p := Nat.Prime p)) hgt P)

end
end Submission.Vdw
