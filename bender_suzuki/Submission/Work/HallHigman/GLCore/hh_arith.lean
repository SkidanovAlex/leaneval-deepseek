import Mathlib
import Submission.Work.HallHigman.GLCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- **L11 of the GL-core design** (Step 4f of the proof of Hall--Higman B, see
`NOTES_LEAD_ft_hallhigman.md` §2.2): the final arithmetic contradiction.  Here `s = dim W` is odd
and `> 1`, `D = dim V`, `b = dim End_𝒬(V)`, `c = dim C(X)`, and the two inequalities are the
upper bound from the `Ad X`-orbit count and the lower bound from the commutant/PID argument. -/
lemma hh_arith {p s b D c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs : Odd s) (hs1 : 1 < s)
    (hdvd : p ∣ s ^ 2 - 1) (hb : 0 < b) (hF : D ^ 2 = s ^ 2 * b)
    (hU : p * c ≤ (p + s ^ 2 - 1) * b) (hL : D ^ 2 ≤ (p - 1) * c) : False := by
  -- `p` is an odd prime, `s` is odd and `1 < s`.
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hs3 : 3 ≤ s := by rcases hs with ⟨k, hk⟩; omega
  have hp1 : 1 ≤ p := by omega
  -- Cross-multiplying the two inequalities (through `D² = s² b`) eliminates `c`:
  -- `p s² b ≤ (p-1)(p+s²-1) b`, and `b > 0`, so `p s² ≤ (p-1)(p+s²-1)`.
  have hsq : s ^ 2 ≤ (p - 1) ^ 2 := by
    have hchain : p * s ^ 2 * b ≤ (p - 1) * (p + s ^ 2 - 1) * b := by
      calc p * s ^ 2 * b = p * D ^ 2 := by rw [hF]; ring
        _ ≤ p * ((p - 1) * c) := Nat.mul_le_mul_left p hL
        _ = (p - 1) * (p * c) := by ring
        _ ≤ (p - 1) * ((p + s ^ 2 - 1) * b) := Nat.mul_le_mul_left (p - 1) hU
        _ = (p - 1) * (p + s ^ 2 - 1) * b := by ring
    have hkey : p * s ^ 2 ≤ (p - 1) * (p + s ^ 2 - 1) := Nat.le_of_mul_le_mul_right hchain hb
    have h1 : p + s ^ 2 - 1 = (p - 1) + s ^ 2 := by omega
    rw [h1] at hkey
    have h2 : p = (p - 1) + 1 := by omega
    nlinarith [hkey, h2]
  -- Hence `s ≤ p - 1`, so `s + 1 ≤ p`; parity (`s` odd, `p` odd) upgrades this to `s + 1 < p`.
  have hsle : s ≤ p - 1 := (Nat.pow_le_pow_iff_left (n := 2) (by norm_num)).mp hsq
  have hsp : s + 1 ≤ p := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hlt : s + 1 < p := by
    rcases Nat.lt_or_eq_of_le hsp with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hpodd
      obtain ⟨m, hm⟩ := hs
      omega
  -- Now `s² - 1 = (s+1)(s-1)` with both factors positive and `< p`, contradicting `p ∣ s² - 1`.
  have hfac : s ^ 2 - 1 = (s + 1) * (s - 1) := by simpa using sq_tsub_sq s 1
  rw [hfac] at hdvd
  rcases (hp.dvd_mul).1 hdvd with h | h
  · have := Nat.le_of_dvd (by omega : 0 < s + 1) h
    omega
  · have := Nat.le_of_dvd (by omega : 0 < s - 1) h
    omega

end Work.HallHigman.GLCore
