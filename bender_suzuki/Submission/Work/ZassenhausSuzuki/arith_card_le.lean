import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

theorem arith_card_le {N d q : ℕ} (hN : 0 < N) (hd : 1 ≤ d) (hq : q = d + 1)
    (h : 2 * (q + 1) * N * N + (q + 1) * N * (N + 1) * (d - 1) + N * (N + 1) * d * q ≤
      2 * (q + 1) * (N * (N + 1) * d)) :
    N ≤ q := by
  subst hq
  -- Move the whole inequality to `ℤ`, where `nlinarith` can do the algebra.
  have h' : (2 * (d + 1 + 1) * N * N + (d + 1 + 1) * N * (N + 1) * (d - 1)
        + N * (N + 1) * d * (d + 1) : ℤ) ≤
      (2 * (d + 1 + 1) * (N * (N + 1) * d) : ℤ) := by exact_mod_cast h
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  nlinarith [h']

end Work.ZassenhausSuzuki
