import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.PiNat

/-- A `π`-number and a `π'`-number are coprime: any common prime divisor `p` would have to
lie both in `π` and in its complement. -/
theorem hall_coprime_of_isPiNat {π : ℕ → Prop} {m n : ℕ} (hm : Work.Hall.IsPiNat π m)
    (hn : Work.Hall.IsPiNat (fun p => ¬ π p) n) (hm0 : m ≠ 0) (hn0 : n ≠ 0) : m.Coprime n := by
  rw [Nat.Coprime]
  by_contra h
  have hne : Nat.gcd m n ≠ 0 := by
    intro h0
    exact hm0 (Nat.gcd_eq_zero_iff.mp h0).1
  have hgt1 : 1 < Nat.gcd m n := by omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgt1.ne'
  exact (hn p hp (hpdvd.trans (Nat.gcd_dvd_right m n)))
    (hm p hp (hpdvd.trans (Nat.gcd_dvd_left m n)))

end Work.Hall.PiNat
