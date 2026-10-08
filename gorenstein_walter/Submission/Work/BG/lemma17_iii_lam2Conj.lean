import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda
import Submission.Work.BG.H0Conj
import Submission.Work.BG.lemma17_ii_aux
import Submission.Work.BG.lemma17_iii_aux

/-!
# BG: `λ₂` is fixed by the conjugation action `ν ↦ ν^s` (Lemma 1.7(iii), ingredient)

In the Hypothesis-1.2 setting with `|H₀ : U| = 2`, the group `Λ` of linear characters of
`H₀/U` has exactly two elements and its non-trivial element `λ₂` (here an arbitrary
`lam2 : H₀/U →* ℂˣ` with `lam2 ≠ 1`) is **invariant** under the conjugation action
`ν ↦ ν^s` of any `s ∈ H` on `CF(H₀)`
(`Work.BG.conjByH P s (Work.BG.lambdaInf P lam2) = Work.BG.lambdaInf P lam2`).

The reason is that `H` normalises `U` (`Work.BG.mem_U_conj_iff`), so conjugation by `s`
preserves the coset `H₀ ∖ U = T`; equivalently, for `h ∈ H₀` the quotient elements
`quotMk P h` and `quotMk P (conjMulEquiv P s h)` are simultaneously trivial.  As
`quotGroup P` has order two, `lam2` is injective (its kernel is a proper subgroup of a
group of prime order), hence its value is `1` exactly on the identity and `-1` on every
other element; together with the simultaneous triviality this gives equality of values.

The helper `Work.BG.lam2_apply_eq_neg_one` below is the second half of
`Work.BG.lemma17_iii_dualC2` (`Submission/Work/BG/lemma17_iii_dualC2.lean`), restricted
to what this file needs.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- **`λ₂` takes the value `-1` off the identity.**  If the quotient `H₀/U` has order two
and `lam2 : H₀/U →* ℂˣ` is non-trivial, then for every `x ≠ 1` the complex value of
`lam2 x` is `-1`.

`lam2` is injective because its kernel is a subgroup of the group `quotGroup P` of prime
order `2` and is not everything (`lam2 ≠ 1`); every `x` satisfies `x ^ 2 = 1` because
`orderOf x ∣ Nat.card (quotGroup P) = 2` and `x ≠ 1`; so `(lam2 x) ^ 2 = 1` in `ℂˣ`,
whence the complex number `lam2 x` is a root of `X ^ 2 - 1`, i.e. `±1`, and it is
`≠ 1`. -/
theorem lam2_apply_eq_neg_one (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    (h2 : Nat.card (quotGroup P) = 2) {lam2 : quotGroup P →* ℂˣ} (hlam2 : lam2 ≠ 1)
    {x : quotGroup P} (hx : x ≠ 1) : ((lam2 x : ℂˣ) : ℂ) = -1 := by
  haveI : Fact (Nat.card (quotGroup P)).Prime := ⟨h2 ▸ Nat.prime_two⟩
  have hker : MonoidHom.ker lam2 = ⊥ := by
    rcases (MonoidHom.ker lam2).eq_bot_or_eq_top_of_prime_card with h | h
    · exact h
    · exact absurd (MonoidHom.ker_eq_top_iff.mp h) hlam2
  have hinj : Function.Injective lam2 := (MonoidHom.ker_eq_bot_iff lam2).mp hker
  have hx1 : lam2 x ≠ 1 := fun hh => hx (hinj (by rw [hh, map_one]))
  have hx2 : x ^ 2 = 1 := by
    have hdvd : orderOf x ∣ 2 := by rw [← h2]; exact orderOf_dvd_natCard x
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf x) hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx
    · rw [← h1]; exact pow_orderOf_eq_one x
  have hsq : ((lam2 x : ℂˣ) : ℂ) ^ 2 = 1 := by
    have hp : (lam2 x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
    rw [← Units.val_pow_eq_pow_val, hp, Units.val_one]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact absurd (Units.ext h) hx1
  · exact h

/-- **`λ₂` is fixed by conjugation by any `s ∈ H`.**  Since `H` normalises `U`, the
elements `h` and `s h s⁻¹` of `H₀` are trivial in `H₀/U` simultaneously, and `lam2`
being trivial exactly on the identity (see `lam2_apply_eq_neg_one`) forces the two values
to agree. -/
theorem lemma17_iii_lam2Conj {G : Type} [Group G] [Finite G] (P : Work.BG.Hyp12 G)
    [(P.U.subgroupOf P.H0).Normal]
    (h2 : Nat.card (Work.BG.quotGroup P) = 2) {lam2 : Work.BG.quotGroup P →* ℂˣ}
    (hlam2 : lam2 ≠ 1) (s : ↥P.H) :
    Work.BG.conjByH P s (Work.BG.lambdaInf P lam2) = Work.BG.lambdaInf P lam2 := by
  ext h
  rw [conjByH_apply, lambdaInf_apply, lambdaInf_apply]
  -- `s h s⁻¹ ∈ U ↔ h ∈ U`, so `quotMk P (s h s⁻¹)` and `quotMk P h` are trivial together
  have hiff : quotMk P (conjMulEquiv P s h) = 1 ↔ quotMk P h = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]
    simp only [Subgroup.mem_subgroupOf]
    rw [conjMulEquiv_apply]
    exact mem_U_conj_iff P s (h : G)
  rcases eq_or_ne (quotMk P h) 1 with h1 | h1
  · -- both trivial: both values are `1`
    rw [h1, hiff.mpr h1, map_one]
  · -- both non-trivial: both values are `-1`
    rw [lam2_apply_eq_neg_one P h2 hlam2 h1,
      lam2_apply_eq_neg_one P h2 hlam2 (fun hh => h1 (hiff.mp hh))]

end Work.BG
