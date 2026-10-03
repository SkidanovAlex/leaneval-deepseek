import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- `N(d) = #{(α, γ) ∈ (ZMod d)² : α² + γ⁴ = 0}` is at most the total number of
pairs `d²`.  (For `d = 0` the ambient type `ZMod 0 × ZMod 0` is not finite and
`gdens 0 = 0` is handled separately below.) -/
private lemma N_le_sq {d : ℕ} (hd : 0 < d) : Submission.N d ≤ d ^ 2 := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have h1 : Submission.N d ≤ Nat.card (ZMod d × ZMod d) := by
    show ({x : ZMod d × ZMod d | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard ≤ Nat.card (ZMod d × ZMod d)
    exact Set.ncard_le_card _
  rw [Nat.card_prod, Nat.card_zmod] at h1
  simpa [pow_two] using h1

/-- **The local density is at most one**: `g(d) = N(d)/d² ≤ 1` for every `d ≥ 0`.
Indeed `N(d)` counts solutions of a congruence in `(ZMod d)²`, a set of size
`d²`; for `d = 0` the density is `0` because `N(0)/0² = 0`. -/
theorem gdens_le_one (d : ℕ) : Submission.gdens d ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    rw [Submission.gdens]
    simp
  · have hN : Submission.N d ≤ d ^ 2 := N_le_sq hd
    rw [Submission.gdens, div_le_one (by positivity)]
    exact_mod_cast hN

end Commons.NumberTheory.FriedlanderIwaniec
