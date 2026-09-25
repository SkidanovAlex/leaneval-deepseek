import Mathlib

namespace Work.ShafarevichKoch

/-- Parity lemma for the Shafarevich--Koch presentation of the pro-2 group attached to
`ℚ(√-30030)`: from `4 ∣ u² + u'² - 30030 (v² + v'²)` and `2 ∣ uv + u'v'` one concludes that
`u` and `u'` are even and that `v` and `v'` have the same parity.

Arithmetic content: `30030 = 2 · 3 · 5 · 7 · 11 · 13 ≡ 2 (mod 4)`, and squares modulo `4`
are `0` or `1`. Reducing the first hypothesis mod `4` shows `u` and `u'` must both be even;
then `v² + v'²` is even, i.e. `v ≡ v' (mod 2)`. The second hypothesis rules out the only
remaining alternative, namely `u, u'` odd and `v, v'` of opposite parity. -/
theorem parity_of_four_dvd_sq_add {u v u' v' : ℤ}
    (h1 : (4 : ℤ) ∣ u ^ 2 + u' ^ 2 - 30030 * (v ^ 2 + v' ^ 2))
    (h2 : (2 : ℤ) ∣ u * v + u' * v') :
    Even u ∧ Even u' ∧ (2 : ℤ) ∣ v + v' ∧ (2 : ℤ) ∣ v - v' := by
  -- Turn the two `Even` goals into divisibility by `2`.
  rw [even_iff_two_dvd, even_iff_two_dvd]
  -- Unfold the two divisibility hypotheses into equations.
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  -- Split into the sixteen parity cases.  In each case the goal and the hypotheses become
  -- polynomial (linear in the atoms `a, b, c, d, a^2, …`) statements after `ring_nf`, and
  -- `omega` either exhibits the witnesses or derives a contradiction.
  rcases Int.even_or_odd u with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
  rcases Int.even_or_odd u' with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
  rcases Int.even_or_odd v with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;>
  rcases Int.even_or_odd v' with ⟨d, rfl⟩ | ⟨d, rfl⟩ <;>
  ring_nf at hk hl ⊢ <;>
  omega

end Work.ShafarevichKoch
