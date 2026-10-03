import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_prime_pow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_rho_div_polylog
import Submission.Commons.Data.Nat.padicValNat_factorization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- Fibre bound for the map `y ↦ #{x : x ^ 2 + y ^ 4 = 0}` modulo `p ^ e`: when
`y ≠ 0` and `4 v_p(y) < e`, the number of `x` with `x ^ 2 + y ^ 4 = 0` is at most
`2 * p ^ (2 v_p(y))`. -/
theorem X2Y4_fiber_ncard_le_prime_pow {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    {y : ZMod (p ^ e)} (hy : y ≠ 0) (h4 : 4 * padicValNat p y.val < e) :
    ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0}.ncard)
      ≤ 2 * p ^ (2 * padicValNat p y.val) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hyval : y.val ≠ 0 := fun h => hy ((ZMod.val_eq_zero y).mp h)
  obtain ⟨hfac, hunit⟩ :=
    Commons.Data.Nat.padicValNat_factorization (p := p) (d := y.val) hyval
  set v : ℕ := padicValNat p y.val with hv
  set u : ℕ := y.val / p ^ v with hu
  -- hfac : y.val = p ^ v * u, hunit : ¬ p ∣ u
  have hu2 : ¬ p ∣ u ^ 2 := fun h => hunit (hp.dvd_of_dvd_pow h)
  have h2c : 2 * (2 * v) < e := by omega
  -- express `y ^ 2` as the cast of a natural number
  have hy2 : y ^ 2 = ((p ^ (2 * v) * u ^ 2 : ℕ) : ZMod (p ^ e)) := by
    rw [show y = ((y.val : ℕ) : ZMod (p ^ e)) from (ZMod.natCast_zmod_val y).symm]
    rw [← Nat.cast_pow, hfac]
    have hn : (p ^ v * u) ^ 2 = p ^ (2 * v) * u ^ 2 := by
      rw [mul_pow, ← pow_mul, show v * 2 = 2 * v by ring]
    rw [hn]
  have hy4 : y ^ 4 = ((p ^ (2 * v) * u ^ 2 : ℕ) : ZMod (p ^ e)) ^ 2 := by
    rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, hy2]
  have hset : ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0} : Set (ZMod (p ^ e)))
      = {x : ZMod (p ^ e) | x ^ 2 + ((p ^ (2 * v) * u ^ 2 : ℕ) : ZMod (p ^ e)) ^ 2 = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← hy4]
  rw [hset]
  rw [ncard_sq_add_sq_prime_pow_reduction (p := p) (e := e) (c := 2 * v) (u := u ^ 2)
        hp he hu2 h2c]
  have hroot : ({γ : ZMod (p ^ (e - 2 * (2 * v))) | γ ^ 2 = -1}.ncard) ≤ 2 :=
    ncard_sq_roots_neg_one_prime_pow_le_two hp (by omega)
  calc p ^ (2 * v) * ({γ : ZMod (p ^ (e - 2 * (2 * v))) | γ ^ 2 = -1}.ncard)
      ≤ p ^ (2 * v) * 2 := Nat.mul_le_mul_left _ hroot
    _ = 2 * p ^ (2 * v) := by ring

end Commons.NumberTheory.FriedlanderIwaniec
