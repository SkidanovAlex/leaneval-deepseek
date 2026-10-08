/-
Arithmetic for the *quadratic* non-abelian case of the p-stability GL-core
(`Work.PStable.Quad.nonabelian_case_quad`).

Setting.  `Q ≤ GL(V)` is a non-abelian finite `q`-group of order prime to `p`, normalised by an
element `X` of order `p` (prime, `p ≠ 2`) which does not commute with `Q`, `V` is irreducible for
`Q ∪ {X}`, and every proper `X`-invariant subgroup of `Q` commutes with `X` (minimality).
Assume the *quadratic* hypothesis `(X - 1) ^ 2 = 0`.  Writing

* `n = |Q / Z(Q)|`,
* `b = dim End_Q(V)`,
* `c = dim C_{End V}(X)`,
* `D = dim V`,

the proof of the non-abelian case gives three numerical facts:

* (Fourier, `Work.HallHigman.GLCore.fourier_finrank`)   `D ^ 2 = n * b`;
* (orbit count, `Work.HallHigman.GLCore.p_mul_finrank_commutant_le`)
      `p * c ≤ (p + n - 1) * b`;
* (commutant lower bound with `r = 2`, `Work.HallHigman.GLCore.sq_finrank_le_mul_finrank_commutant`)
      `D ^ 2 ≤ 2 * c`, i.e. `n * b ≤ 2 * c`;
* (fixed-point congruence, `Work.HallHigman.GLCore.dvd_centerQuotient_sub_one`) `p ∣ n - 1`.

For odd `|Q|` the classical Hall–Higman proof replaces `r = 2` by `r = p - 1` and uses the oddness
of `n` to contradict `p ≤ n - 1`; quadratically the sharper `r = 2` already makes
`(p - 2) * (n - 2) ≤ 2` untenable: from `p ≥ 5` and `n ≥ 2` one gets `n ≤ 3`, and then
`p ∣ n - 1` forces `p ≤ 2`.  That is the content of `quad_arith_p5` below.  It covers in
particular the case `q = 2` (where `|Q|` is even and `n` need not be odd).
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PStable.Quad

/-- Arithmetic core of the quadratic non-abelian case for `p ≥ 5`: with `b > 0` and
`p * c ≤ (p + n) * b`, `n * b ≤ 2 * c`, `n ≥ 2`, `p ∣ n - 1` and `5 ≤ p`, we get a
contradiction. -/
lemma quad_arith_p5 {p n b c : ℕ} (hp : 5 ≤ p) (hn : 2 ≤ n) (hb : 0 < b)
    (h1 : p * c ≤ (p + n) * b) (h2 : n * b ≤ 2 * c) (hdvd : p ∣ n - 1) : False := by
  have hA : p * (n * b) ≤ 2 * ((p + n) * b) := by
    calc p * (n * b) ≤ p * (2 * c) := Nat.mul_le_mul_left p h2
      _ = 2 * (p * c) := by ring
      _ ≤ 2 * ((p + n) * b) := Nat.mul_le_mul_left 2 h1
  have hB : (p * n) * b ≤ (2 * (p + n)) * b := by
    calc (p * n) * b = p * (n * b) := by ring
      _ ≤ 2 * ((p + n) * b) := hA
      _ = (2 * (p + n)) * b := by ring
  have hpn : p * n ≤ 2 * (p + n) := Nat.le_of_mul_le_mul_right hB hb
  have hpn' : p * n ≤ 2 * p + 2 * n := by linarith [hpn]
  have hnle : n ≤ 3 := by nlinarith
  have hn1 : 0 < n - 1 := by omega
  have hp_le : p ≤ n - 1 := Nat.le_of_dvd hn1 hdvd
  omega

end Work.PStable.Quad
