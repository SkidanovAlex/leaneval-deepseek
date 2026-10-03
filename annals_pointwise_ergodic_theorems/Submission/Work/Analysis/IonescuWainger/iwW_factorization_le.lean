import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset

/-!
# Prime-exponent bound for elements of `W_{≤l}`

If `w` belongs to the Ionescu–Wainger set `W_{≤l}` (products of at most `D_ρ` distinct
primes from `(N_0^{(l)}, 2^l]`, each to a power `≤ D_ρ`), then every prime exponent
of `w` is at most `D_ρ`, and moreover it can only be nonzero for primes in the range
`(N_0^{(l)}, 2^l]`:

* `Work.Analysis.IonescuWainger.iwW_factorization_le`

The proof: `w ∈ W_{≤l}` divides `iwProd ρ l = ∏_{p ∈ (N_0, 2^l]} p^{D_ρ}`, factorization
is monotone under divisibility, and the factorization of that product is `D_ρ` at each
prime of the range and `0` elsewhere.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

/-- The factorization of a product of primes raised to given powers: it is `e q` at
each `q ∈ S` and `0` off `S`. -/
private theorem prod_prime_pow_factorization {S : Finset ℕ} {e : ℕ → ℕ}
    (hp : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (S.prod (fun p => p ^ e p)).factorization q = if q ∈ S then e q else 0 := by
  classical
  rw [Nat.factorization_prod_apply (fun x hx => pow_ne_zero _ (hp x hx).ne_zero)]
  have key : ∀ p ∈ S, ((p ^ e p).factorization q) = if p = q then e p else 0 := by
    intro p hp'
    rw [(hp p hp').factorization_pow, Finsupp.single_apply]
  rw [Finset.sum_congr rfl key]
  simp

theorem iwW_factorization_le {ρ : ℝ} {l w q : ℕ} (hw : w ∈ Work.Analysis.IonescuWainger.iwW ρ l) :
    w.factorization q ≤ if q ∈ Work.Analysis.IonescuWainger.iwPrimeRange ρ l
      then Work.Analysis.IonescuWainger.iwD ρ else 0 := by
  obtain ⟨hdvd, -⟩ := mem_iwW.mp hw
  classical
  have hle : w.factorization q ≤ (iwProd ρ l).factorization q :=
    Nat.factorization_le_factorization_of_dvd_right hdvd
      (pos_of_mem_iwW hw).ne' (iwProd_ne_zero ρ l)
  have hprod : (iwProd ρ l).factorization q
      = if q ∈ iwPrimeRange ρ l then iwD ρ else 0 :=
    prod_prime_pow_factorization (fun p hp => (Finset.mem_filter.mp hp).2) q
  rw [hprod] at hle; exact hle

end Work.Analysis.IonescuWainger
