import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

/-!
# The scalar identity `e = z · b / N` for the Suzuki model

In `K = GF(2 ^ (2n+1))`, with `A = a ^ 2 ^ (n+1)`, `B = b ^ 2 ^ (n+1)`,
`t = z ^ 2 ^ n` and the two atoms

`P = a ^ 2 * A + a * b + B`,
`Q = A ^ 2 * a ^ 2 + A * B + b ^ 2`,

the hypotheses of the Suzuki root-element computation give `z * t = P`, `P ^ 2 ^ (n+1) = Q`
(Frobenius), and hence `z = P ^ 2 / Q`.  From

`c = (a * A + b) / P`, `d = a / P + c ^ (1 + 2 ^ (n+1))`, `e = z ^ (1 + 2 ^ n) * d`

one computes `e = a + (a * A + b) * (A * a ^ 2 + B) / Q`, and the characteristic-two
polynomial identity `a * Q + (a * A + b) * (A * a ^ 2 + B) = b * P` finishes the proof:

`e = b * P / Q = z * b / P`.

The point of the lemma is the reduction of the division-heavy identity to the single
polynomial identity `a * Q + (a * A + b) * (A * a ^ 2 + B) = b * P`, which is closed by
`ring_nf` and `reduce_mod_char!`.
-/

namespace Work.ZassenhausSuzuki.SzAux

/-- Frobenius-type identity: every element of `GaloisField p n` (`n ≠ 0`) is fixed by the
`n`-fold Frobenius `x ↦ x ^ (p ^ n)` (the cardinality of the field is `p ^ n`). -/
theorem sz_pow_card_self (n : ℕ) (x : GaloisField 2 (2 * n + 1)) :
    x ^ (2 ^ (2 * n + 1)) = x := by
  haveI : Fintype (GaloisField 2 (2 * n + 1)) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * n + 1) (by omega)]
  rw [← hcard]
  exact FiniteField.pow_card x

/-- In `GF(2 ^ (2n+1))` the Tits endomorphism `x ↦ x ^ 2 ^ (n+1)` squares to the Frobenius. -/
theorem sz_pow_theta_sq (n : ℕ) (x : GaloisField 2 (2 * n + 1)) :
    (x ^ 2 ^ (n + 1)) ^ 2 ^ (n + 1) = x ^ 2 := by
  have hpow : 2 ^ (n + 1) * 2 ^ (n + 1) = 2 ^ (2 * n + 1) * 2 := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  rw [← pow_mul, hpow, pow_mul, sz_pow_card_self n x]

/-- In `GF(2 ^ (2n+1))`, `x ↦ x ^ 2 ^ n` and `x ↦ x ^ 2 ^ (n+1)` are mutually inverse. -/
theorem sz_pow_n_theta (n : ℕ) (x : GaloisField 2 (2 * n + 1)) :
    (x ^ 2 ^ n) ^ 2 ^ (n + 1) = x := by
  rw [← pow_mul]
  rw [show 2 ^ n * 2 ^ (n + 1) = 2 ^ (2 * n + 1) by rw [← pow_add]; congr 1; omega]
  exact sz_pow_card_self n x

theorem sz_e_eq (n : ℕ) (a b z : GaloisField 2 (2 * n + 1)) (hz0 : z ≠ 0)
    (hz : z ^ (1 + 2 ^ n) = a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)))
    (c d e : GaloisField 2 (2 * n + 1))
    (hc : c = (a ^ (1 + 2 ^ (n + 1)) + b) / z ^ (1 + 2 ^ n))
    (hd : d = a / z ^ (1 + 2 ^ n) + c ^ (1 + 2 ^ (n + 1)))
    (he : e = z ^ (1 + 2 ^ n) * d) :
    e = z * (b / (a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)))) := by
  have hchar : CharP (GaloisField 2 (2 * n + 1)) 2 := inferInstance
  set A : GaloisField 2 (2 * n + 1) := a ^ (2 ^ (n + 1)) with hA
  set B : GaloisField 2 (2 * n + 1) := b ^ (2 ^ (n + 1)) with hB
  set t : GaloisField 2 (2 * n + 1) := z ^ (2 ^ n) with ht
  have ht0 : t ≠ 0 := by rw [ht]; exact pow_ne_zero _ hz0
  have hz1 : z ^ (1 + 2 ^ n) = z * t := by
    rw [ht, show 1 + 2 ^ n = 2 ^ n + 1 by omega, pow_add, pow_one]; ring
  have hA1 : a ^ (1 + 2 ^ (n + 1)) = a * A := by
    rw [show 1 + 2 ^ (n + 1) = 2 ^ (n + 1) + 1 by omega, pow_add, pow_one, ← hA]; ring
  have hA2 : a ^ (2 + 2 ^ (n + 1)) = a ^ 2 * A := by rw [pow_add, ← hA]
  have hB1 : b ^ (2 ^ (n + 1)) = B := hB.symm
  have hzt2 : z ^ (2 ^ (n + 1)) = t ^ 2 := by
    rw [show 2 ^ (n + 1) = 2 ^ n * 2 by rw [mul_comm, ← pow_succ'], pow_mul, ht]
  have htth : t ^ (2 ^ (n + 1)) = z := by rw [ht]; exact sz_pow_n_theta n z
  have hAth : A ^ (2 ^ (n + 1)) = a ^ 2 := by rw [hA]; exact sz_pow_theta_sq n a
  have hBth : B ^ (2 ^ (n + 1)) = b ^ 2 := by rw [hB]; exact sz_pow_theta_sq n b
  have hAthmul : (a ^ 2) ^ (2 ^ (n + 1)) = A ^ 2 := by
    rw [← pow_mul, show 2 * 2 ^ (n + 1) = 2 ^ (n + 1) * 2 by rw [mul_comm], pow_mul, hA]
  set P : GaloisField 2 (2 * n + 1) := a ^ 2 * A + a * b + B with hPdef
  set Q : GaloisField 2 (2 * n + 1) := A ^ 2 * a ^ 2 + A * B + b ^ 2 with hQdef
  have hzP : z * t = P := by rw [hPdef, ← hz1, hz, hA2]
  have hPowP : P ^ (2 ^ (n + 1)) = Q := by
    rw [hPdef, add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, hAthmul, hAth, hBth,
      ← hA, ← hB, hQdef]
  have hzQ : z * t ^ 2 = Q := by
    have h := congrArg (fun x : GaloisField 2 (2 * n + 1) => x ^ (2 ^ (n + 1))) hz
    rw [hz1, mul_pow, hzt2, htth, hA2, ← hPdef, hPowP] at h
    rw [← h]; ring
  have hP0 : P ≠ 0 := by rw [← hzP]; exact mul_ne_zero hz0 ht0
  have hQ0 : Q ≠ 0 := by rw [← hzQ]; exact mul_ne_zero hz0 (pow_ne_zero _ ht0)
  have hz_eq : z = P ^ 2 / Q := by rw [eq_div_iff hQ0, ← hzQ, ← hzP]; ring
  have hc0 : c = (a * A + b) / P := by rw [hc, hA1, hz1, ← hzP]
  have hZc : (a * A + b) ^ (2 ^ (n + 1)) = A * a ^ 2 + B := by
    rw [add_pow_char_pow, mul_pow, ← hA, hAth, hB1]
  have hcθ : c ^ (2 ^ (n + 1)) = (A * a ^ 2 + B) / Q := by rw [hc0, div_pow, hZc, hPowP]
  have hc1 : c ^ (1 + 2 ^ (n + 1)) = (a * A + b) * (A * a ^ 2 + B) / (P * Q) := by
    rw [show 1 + 2 ^ (n + 1) = 2 ^ (n + 1) + 1 by omega, pow_add, pow_one, hcθ, hc0]
    ring_nf
  have hd0 : d = a / P + (a * A + b) * (A * a ^ 2 + B) / (P * Q) := by
    rw [hd, hz1, hzP, hc1]
  have he0 : e = a + (a * A + b) * (A * a ^ 2 + B) / Q := by
    rw [he, hz1, hzP, hd0]; field_simp
  have hPexpr : a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)) = P := by
    rw [hPdef, hA2, hB1]
  have hpoly : a * Q + (a * A + b) * (A * a ^ 2 + B) = b * P := by
    rw [hPdef, hQdef]; ring_nf; reduce_mod_char!
  have heq : e = b * P / Q := by
    rw [he0, eq_div_iff hQ0]
    rw [add_mul, div_mul_cancel₀]
    · rw [hpoly]
    · exact hQ0
  have hzb : z * (b / P) = b * P / Q := by
    rw [hz_eq]
    field_simp
  rw [hPexpr]
  exact heq.trans hzb.symm

end Work.ZassenhausSuzuki.SzAux
