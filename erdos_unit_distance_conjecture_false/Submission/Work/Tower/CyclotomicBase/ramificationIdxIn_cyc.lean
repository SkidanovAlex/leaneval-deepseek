import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs

/-!
# The ramification index of `r i` in `ℚ(ζ_D)`

For a family `r : Fin ℓ → ℕ` of pairwise distinct primes with `D = ∏ i, r i`, the rational prime
`r i` has ramification index `r i - 1` in the cyclotomic field `ℚ(ζ_D)`.

Since `D` is squarefree, `D = r i ^ (0 + 1) * (D / r i)` with `r i ∤ D / r i`, so Mathlib's
formula `IsCyclotomicExtension.Rat.ramificationIdxIn_eq` -- which computes the ramification index
of `p` in `ℚ(ζ_n)` as `p ^ k * (p - 1)` where `n = p ^ (k + 1) * m` and `p ∤ m` -- applies with
`k = 0` and `p = r i`.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Work.Tower.CyclotomicBase

variable {ℓ : ℕ}

/-- `D r = r i * (D r / r i)`: the prime `r i` divides the product `D r` once. -/
lemma D_eq_mul_div (r : Fin ℓ → ℕ) (i : Fin ℓ) : D r = r i * (D r / r i) :=
  (Nat.mul_div_cancel' (r_dvd_D r i)).symm

/-- For a family of pairwise distinct primes, `r i` does not divide `D r / r i`. -/
lemma not_dvd_div_D (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hrinj : Function.Injective r) (i : Fin ℓ) : ¬ r i ∣ D r / r i := by
  have hprod : D r = r i * ∏ j ∈ Finset.univ.erase i, r j :=
    (Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i)).symm
  rw [hprod, Nat.mul_div_cancel_left _ (hr i).pos]
  intro hdiv
  obtain ⟨j, hj, hij⟩ := ((hr i).prime.dvd_finsetProd_iff r).mp hdiv
  rw [Finset.mem_erase] at hj
  exact hj.1 (hrinj (Nat.prime_dvd_prime_iff_eq (hr i) (hr j) |>.mp hij)).symm

theorem ramificationIdxIn_cyc {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hrinj : Function.Injective r) [NeZero (D r)] (i : Fin ℓ) :
    (Ideal.span {(r i : ℤ)}).ramificationIdxIn (NumberField.RingOfIntegers (Cyc r)) =
      r i - 1 := by
  haveI : Fact (Nat.Prime (r i)) := ⟨hr i⟩
  haveI : IsCyclotomicExtension {D r} ℚ (Cyc r) := isCyclotomicExtension_cyc r
  have hn : D r = r i ^ (0 + 1) * (D r / r i) := by
    rw [zero_add, pow_one]
    exact D_eq_mul_div r i
  have hm : ¬ r i ∣ D r / r i := not_dvd_div_D r hr hrinj i
  have h := IsCyclotomicExtension.Rat.ramificationIdxIn_eq (D r) (Cyc r)
    (m := D r / r i) (p := r i) (k := 0) hn hm
  rwa [pow_zero, one_mul] at h

end Work.Tower.CyclotomicBase
