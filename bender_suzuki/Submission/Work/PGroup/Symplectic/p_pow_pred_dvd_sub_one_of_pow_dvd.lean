import Mathlib
import Submission.Work.PGroup.Symplectic.dvd_sub_one_of_dvd_pow_sub_one
import Submission.Work.PGroup.Symplectic.prime_pow_dvd_pow_pred_one_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup.Symplectic

/-- Lifting the exponent, in divisibility form: if an odd prime `p` satisfies
`p ^ n ∣ a ^ p - 1` with `n ≥ 2`, then `p ^ (n - 1) ∣ a - 1`.

Indeed `a ^ p ≡ 1 (mod p)` forces `p ∣ a - 1` (Fermat), so `a = 1 + k * p`; then
`v_p (a ^ p - 1) = v_p (a - 1) + 1`, giving the result. -/
theorem p_pow_pred_dvd_sub_one_of_pow_dvd {p n a : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hn : 2 ≤ n) (h : p ^ n ∣ a ^ p - 1) : p ^ (n - 1) ∣ a - 1 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  -- `p ∣ a ^ p - 1`, hence `p ∣ a - 1` by Fermat's little theorem
  have hp_dvd : p ∣ a ^ p - 1 :=
    dvd_trans (dvd_pow_self p (by omega : n ≠ 0)) h
  have hpa : p ∣ a - 1 := dvd_sub_one_of_dvd_pow_sub_one hp hp_dvd
  rcases hpa with ⟨k, hk⟩
  -- write `a = 1 + k * p` so that the lifting-the-exponent lemma applies
  have ha_eq : a = 1 + k * p := by rw [mul_comm k p]; omega
  have h' : p ^ n ∣ (1 + k * p) ^ p - 1 := by rw [← ha_eq]; exact h
  have hk' : p ^ (n - 2) ∣ k := (prime_pow_dvd_pow_pred_one_iff hp hodd hn).mp h'
  rcases hk' with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  rw [hk, hj]
  have hn1 : n - 1 = n - 2 + 1 := by omega
  rw [hn1, pow_succ']
  ring

end Work.PGroup.Symplectic
