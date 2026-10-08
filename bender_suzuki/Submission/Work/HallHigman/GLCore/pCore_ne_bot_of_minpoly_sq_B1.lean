import Mathlib
import Submission.Work.HallHigman.HallHigmanB
import Submission.Work.HallHigman.FT71

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

universe v

open Polynomial in
/-- The engine of Feit--Thompson's Lemma 7.1 with the order-`p` form of Theorem B:  if `x` has
minimal polynomial `(X - 1) ^ 2` on a faithful `F_p`-module of a `p`-solvable group of odd order,
then `O_p(H) ≠ 1`.

Proof: `(W.ρ x - 1) ^ 2 = 0` (`minpoly.aeval`); since `p ≠ 2` and `p` is prime, `p - 1 ≥ 2`, so
`(W.ρ x - 1) ^ (p - 1) = ((W.ρ x - 1) ^ 2) ^ ((p - 1) / 2) * (W.ρ x - 1) ^ ((p - 1) % 2) = 0`; and
`x ≠ 1` because `orderOf x = p ^ n` with `n > 0`.  `HallHigmanB1` with `O_p(H) = ⊥` then gives the
contradiction. -/
theorem pCore_ne_bot_of_minpoly_sq_B1 {p : ℕ} [Fact p.Prime]
    (hB : Work.HallHigman.HallHigmanB1.{0, v} (ZMod p) p) (hp : p ≠ 2) {H : Type v} [Group H]
    [Finite H] (hsol : Work.HallHigman.IsPSolvable p H) (hodd : Odd (Nat.card H))
    (W : FDRep (ZMod p) H) (hfaith : Function.Injective W.ρ) {x : H} {n : ℕ} (hn : 0 < n)
    (hx : orderOf x = p ^ n) (hmin : minpoly (ZMod p) (W.ρ x) = (X - 1) ^ 2) :
    Work.HallHigman.pCore p H ≠ ⊥ := by
  intro hbot
  -- `x ≠ 1`, since `orderOf x = p ^ n` with `n > 0` and `p ≥ 2`.
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have : 1 < p ^ n := one_lt_pow₀ (by omega : 1 < p) hn.ne'
    omega
  -- `(W.ρ x - 1) ^ 2 = 0` from the minimal polynomial.
  have hsq : (W.ρ x - 1) ^ 2 = 0 := by
    have h := minpoly.aeval (ZMod p) (W.ρ x)
    rw [hmin, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_one] at h
    simpa using h
  -- hence `(W.ρ x - 1) ^ (p - 1) = 0`, because `p - 1 ≥ 2`.
  have hp1 : 2 ≤ p - 1 := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hpred : (W.ρ x - 1) ^ (p - 1) = 0 := by
    rw [show p - 1 = 2 + (p - 1 - 2) from (Nat.add_sub_of_le hp1).symm, pow_add, hsq, zero_mul]
  exact (hB H hsol hodd W hfaith hbot x hxne) hpred

end Work.HallHigman.GLCore
