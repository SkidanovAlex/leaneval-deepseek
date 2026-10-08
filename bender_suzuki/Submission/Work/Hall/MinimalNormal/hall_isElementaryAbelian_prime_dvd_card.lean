import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Prime divisors of the order of an elementary abelian group

If `A` is elementary abelian of exponent `p` with `p` prime, then `A` is a `p`-group:
every element `a : A` satisfies `a ^ p = 1`, hence `A` has exponent dividing `p`.
A finite group whose exponent divides `p` has order a power of `p`, so every prime divisor of
`Nat.card A` must equal `p`.
-/

namespace Work.Hall.MinimalNormal

theorem hall_isElementaryAbelian_prime_dvd_card {G : Type*} [Group G] [Finite G] {p q : ℕ} {A : Subgroup G}
    (h : Work.Hall.IsElementaryAbelian p A) (hp : p.Prime) (hq : q.Prime) (hd : q ∣ Nat.card A) :
    q = p := by
  -- `A` is a `p`-group: every element satisfies `a ^ p = 1`.
  have hpg : IsPGroup p A := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    exact ⟨1, by simpa using h.2 g⟩
  -- hence its card divides some power of `p`
  obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow (G := A)).mp hpg
  have hqp : q ∣ p ^ n := hd.trans hn
  -- a prime dividing `p ^ n` divides `p`, and `p` is prime, so `q = p`
  have hdd : q ∣ p := hq.dvd_of_dvd_pow hqp
  rcases (Nat.dvd_prime hp).mp hdd with h1 | hp'
  · exact absurd h1 hq.ne_one
  · exact hp'

end Work.Hall.MinimalNormal
