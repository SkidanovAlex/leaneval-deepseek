import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_prime_sq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- **(9.1) of the companion paper "Asymptotic sieve for primes"** for the
Friedlander–Iwaniec density `g(d) = N(d)/d²`, `N(d) = #{(x₁,x₂) ∈ (ℤ/d)² : x₁² + x₂⁴ ≡ 0}`:
for every prime `p`, `g(p²) ≤ g(p)` and `g(p²) ≤ 4/p²`, where `g(d) = N(d)/d²`.

(The local counts are `N(p) = 1`, `N(p²) = p²` for `p ≡ 3 (mod 4)`;
`N(p) = 2p−1`, `N(p²) = 3p²−2p` for `p ≡ 1 (mod 4)`; and `N(2) = 2`, `N(4) = 4`.) -/
theorem local_density_prime_sq_le (p : ℕ) (hp : p.Prime) :
    (({x : ZMod (p ^ 2) × ZMod (p ^ 2) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 4
        ≤ (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 2
      ∧ (({x : ZMod (p ^ 2) × ZMod (p ^ 2) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 4
        ≤ 4 / (p : ℝ) ^ 2 := by
  obtain ⟨-, h1, h2, -⟩ := X2Y4_gdens_prime_sq_le p hp
  simp only [] at h1 h2
  have hd : ((p ^ 2 : ℕ) : ℝ) ^ 2 = (p : ℝ) ^ 4 := by push_cast; ring
  rw [hd] at h1 h2
  exact ⟨h1, h2⟩

end Commons.NumberTheory.FriedlanderIwaniec
