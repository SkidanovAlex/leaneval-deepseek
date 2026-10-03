import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound

namespace Work.FIArea5.S16Hecke

/-- **Power bound for the Hecke eigenvalues.**  For `‖χ‖ ≤ 1` and a prime `p`, the Hecke eigenvalue
of a prime power satisfies `‖λ(p^ν)‖ ≤ 4(ν+1)`.  Indeed `λ(n)` is bounded by `4 τ(n)` and
`τ(p^ν) = ν + 1`.  This is the degree-`2` shape of the Euler factor used in (16.30)–(16.31). -/
theorem heckeLam_pow_bound {chi : GaussianInt → ℂ} {k : ℤ} {p : ℕ} (hp : p.Prime)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (ν : ℕ) :
    ‖heckeLam chi k (p ^ ν)‖ ≤ 4 * ((ν : ℝ) + 1) := by
  have h1 : 1 ≤ p ^ ν := Nat.one_le_pow ν p hp.pos
  have hbnd := heckeLam_bound chi k hb h1
  have hcard : (p ^ ν).divisors.card = ν + 1 := by
    rw [Nat.divisors_prime_pow hp ν]
    simp
  rw [hcard] at hbnd
  push_cast at hbnd
  linarith

end Work.FIArea5.S16Hecke
