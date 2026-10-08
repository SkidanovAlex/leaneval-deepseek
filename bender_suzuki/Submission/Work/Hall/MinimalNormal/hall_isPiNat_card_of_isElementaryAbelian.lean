import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The order of an elementary abelian `p`-group is a `p`-number

If `A` is elementary abelian of exponent `p` with `p` prime (`A` abelian and `a ^ p = 1` for all
`a ∈ A`), then every prime divisor of `|A|` equals `p`. Indeed, if a prime `q` divides `|A|`, then by
Cauchy's theorem `A` contains an element of order `q`; as every element has order dividing `p`, we
get `q ∣ p`, hence `q = p`.

(Commutativity is not needed for this; the argument only uses that the exponent divides `p`.)
-/

namespace Work.Hall.MinimalNormal

theorem hall_isPiNat_card_of_isElementaryAbelian {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : Work.Hall.IsElementaryAbelian p A) (hp : p.Prime) :
    Work.Hall.IsPiNat (fun q => q = p) (Nat.card A) := by
  intro q hq hd
  -- Cauchy's theorem: a prime `q` dividing `|A|` gives an element of order `q`.
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hq⟩) hd
  -- Every element of `A` has order dividing `p`.
  have hpa : a ^ p = 1 := h.2 a
  have hdvd : orderOf a ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpa
  rw [ha] at hdvd
  -- Two primes dividing one another are equal.
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd

end Work.Hall.MinimalNormal
