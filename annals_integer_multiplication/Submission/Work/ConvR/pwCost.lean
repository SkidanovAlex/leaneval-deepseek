import Mathlib
import Submission.Work.ConvR.pwdefs

namespace Work.ConvR

/-!
# The cost accounting for the ConvR pointwise map

`pwCost` is the elementary (purely arithmetic) bookkeeping step of Proposition 3.4:
given that the three vectors handled in one pointwise step have encoding size at most
`13 * (M*r + 1) * p^2`, and that the size bookkeeping integers `iszp`, `iszr` are at
most `p + 3` resp. `p + 1`, the cost expression of the step is dominated by

`4*M*x + C * (M*r + 1) * p^2 + C`,  `C = 8*Kq + 13*kK + 33*K3 + 20*K4 + kK + 1`.

The proof splits the bound into the pieces coming from the two program fragments
(K3 part, K4 part) and the two `self`-products (`Kq` part, `kK` part), each estimated
separately with `Nat.mul_le_mul`-style arguments, and finishes by linear arithmetic.
-/

set_option maxHeartbeats 2000000 in
theorem pwCost (Kq kK K3 K4 M r p x : ℕ) (hr : 1 ≤ r) (hp : 1 ≤ p)
    (vszA vszB vszZ iszp iszr : ℕ)
    (hA : vszA ≤ 13 * (M * r + 1) * p ^ 2) (hB : vszB ≤ 13 * (M * r + 1) * p ^ 2)
    (hZ : vszZ ≤ 13 * (M * r + 1) * p ^ 2)
    (hpz : iszp ≤ p + 3) (hrz : iszr ≤ p + 1) :
    K3 * (vszA + vszB + iszp + iszr + 1)
      + (M * (4 * x + Kq * (r + 1) * (p + 1) ^ 2 + kK * (2 * r * p + 9 * r + 2)) + kK)
      + K4 * (vszZ + iszp + iszr + 1)
    ≤ 4 * M * x + (8 * Kq + 13 * kK + 33 * K3 + 20 * K4 + kK + 1) * (M * r + 1) * p ^ 2
      + (8 * Kq + 13 * kK + 33 * K3 + 20 * K4 + kK + 1) := by
  -- The size hypotheses give the two `K3`/`K4` sums.
  have hAB : vszA + vszB + iszp + iszr + 1 ≤ 26 * ((M * r + 1) * p ^ 2) + (2 * p + 5) := by
    nlinarith [hA, hB, hpz, hrz]
  have hZZ : vszZ + iszp + iszr + 1 ≤ 13 * ((M * r + 1) * p ^ 2) + (2 * p + 5) := by
    nlinarith [hZ, hpz, hrz]
  have h3 : K3 * (vszA + vszB + iszp + iszr + 1)
      ≤ K3 * (26 * ((M * r + 1) * p ^ 2) + (2 * p + 5)) := Nat.mul_le_mul_left K3 hAB
  have h4 : K4 * (vszZ + iszp + iszr + 1)
      ≤ K4 * (13 * ((M * r + 1) * p ^ 2) + (2 * p + 5)) := Nat.mul_le_mul_left K4 hZZ
  -- `p^2` is the unit scale: it is bounded by `(M*r+1)*p^2`.
  have hT1 : 1 ≤ M * r + 1 := by nlinarith
  have hsq : p ^ 2 ≤ (M * r + 1) * p ^ 2 := by
    calc p ^ 2 = p ^ 2 * 1 := by ring
      _ ≤ p ^ 2 * (M * r + 1) := Nat.mul_le_mul_left _ hT1
      _ = (M * r + 1) * p ^ 2 := by ring
  have hsqK (c : ℕ) : c * p ^ 2 ≤ c * ((M * r + 1) * p ^ 2) := by
    have := Nat.mul_le_mul_left c hsq
    simpa using this
  -- The `Kq` part: `M*(r+1)*(p+1)^2 ≤ 8*(M*r+1)*p^2`, using `(p+1)^2 ≤ 4*p^2`.
  have hKq : M * (Kq * (r + 1) * (p + 1) ^ 2) ≤ 8 * Kq * ((M * r + 1) * p ^ 2) := by
    have h1 : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by nlinarith
    have h2 : M * (r + 1) ≤ 2 * (M * r + 1) := by nlinarith
    have h3 : M * (r + 1) * (p + 1) ^ 2 ≤ 8 * ((M * r + 1) * p ^ 2) := by
      calc M * (r + 1) * (p + 1) ^ 2 ≤ (2 * (M * r + 1)) * (4 * p ^ 2) := Nat.mul_le_mul h2 h1
        _ = 8 * ((M * r + 1) * p ^ 2) := by ring
    calc M * (Kq * (r + 1) * (p + 1) ^ 2)
        = Kq * (M * (r + 1) * (p + 1) ^ 2) := by ring
      _ ≤ Kq * (8 * ((M * r + 1) * p ^ 2)) := Nat.mul_le_mul_left Kq h3
      _ = 8 * Kq * ((M * r + 1) * p ^ 2) := by ring
  -- The `kK` part: `M*(2rp + 9r + 2) ≤ 13*(M*r+1)*p^2`.
  have hkK : M * (kK * (2 * r * p + 9 * r + 2)) ≤ 13 * kK * ((M * r + 1) * p ^ 2) := by
    have hc : 2 * r * p + 9 * r + 2 ≤ (11 * r + 2) * p ^ 2 := by
      have h : p ≤ p ^ 2 := by nlinarith
      nlinarith [h]
    have hm : M * (11 * r + 2) ≤ 13 * (M * r + 1) := by nlinarith
    have h3 : M * (2 * r * p + 9 * r + 2) ≤ 13 * ((M * r + 1) * p ^ 2) := by
      calc M * (2 * r * p + 9 * r + 2) ≤ M * ((11 * r + 2) * p ^ 2) := Nat.mul_le_mul_left M hc
        _ = (M * (11 * r + 2)) * p ^ 2 := by ring
        _ ≤ (13 * (M * r + 1)) * p ^ 2 := Nat.mul_le_mul_right _ hm
        _ = 13 * ((M * r + 1) * p ^ 2) := by ring
    calc M * (kK * (2 * r * p + 9 * r + 2)) = kK * (M * (2 * r * p + 9 * r + 2)) := by ring
      _ ≤ kK * (13 * ((M * r + 1) * p ^ 2)) := Nat.mul_le_mul_left kK h3
      _ = 13 * kK * ((M * r + 1) * p ^ 2) := by ring
  -- The lower order `K3` / `K4` contributions: `2p + 5 ≤ 7*(M*r+1)*p^2 + const`.
  have hK3low : K3 * (2 * p + 5) ≤ 7 * K3 * ((M * r + 1) * p ^ 2) + 33 * K3 := by
    have h1 : 2 * p + 5 ≤ 7 * p ^ 2 + 33 := by nlinarith
    have h2 : 7 * p ^ 2 + 33 ≤ 7 * ((M * r + 1) * p ^ 2) + 33 := by
      have h := hsqK 7; omega
    calc K3 * (2 * p + 5) ≤ K3 * (7 * ((M * r + 1) * p ^ 2) + 33) :=
          Nat.mul_le_mul_left K3 (le_trans h1 h2)
      _ = 7 * K3 * ((M * r + 1) * p ^ 2) + 33 * K3 := by ring
  have hK4low : K4 * (2 * p + 5) ≤ 7 * K4 * ((M * r + 1) * p ^ 2) + 20 * K4 := by
    have h1 : 2 * p + 5 ≤ 7 * p ^ 2 + 20 := by nlinarith
    have h2 : 7 * p ^ 2 + 20 ≤ 7 * ((M * r + 1) * p ^ 2) + 20 := by
      have h := hsqK 7; omega
    calc K4 * (2 * p + 5) ≤ K4 * (7 * ((M * r + 1) * p ^ 2) + 20) :=
          Nat.mul_le_mul_left K4 (le_trans h1 h2)
      _ = 7 * K4 * ((M * r + 1) * p ^ 2) + 20 * K4 := by ring
  -- The bare `kK` term is absorbed by the `kK * (M*r+1)*p^2` term.
  have hTpos : 0 < (M * r + 1) * p ^ 2 :=
    Nat.mul_pos (Nat.succ_pos _) (pow_pos (lt_of_lt_of_le Nat.zero_lt_one hp) 2)
  have hkT : kK ≤ kK * ((M * r + 1) * p ^ 2) := Nat.le_mul_of_pos_right kK hTpos
  -- Assembly: sum the seven estimates.
  linarith [h3, h4, hKq, hkK, hK3low, hK4low, hkT]

end Work.ConvR
