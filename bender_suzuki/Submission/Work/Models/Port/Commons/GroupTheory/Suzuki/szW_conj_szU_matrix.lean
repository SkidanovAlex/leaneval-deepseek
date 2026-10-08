import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ReduceModChar
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.galoisField_pow_two_pow_succ_succ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Weyl conjugation of a Suzuki root element, in matrix form

For `F = GF(2 ^ (2n+1))` let `θ` be the map `x ↦ x ^ 2 ^ (n+1)` (`θ ^ 2` is the ordinary
squaring map `σ`, and `σ ^ (2n+1) = id`).  Writing `u(a,b)` for the root element

`u(a,b) = !![1, a, b, a ^ (2+2^(n+1)) + a*b + b ^ (2^(n+1)); 0, 1, a^(2^(n+1)), a^(1+2^(n+1)) + b; 0, 0, 1, a; 0, 0, 0, 1]`

and `w` for the antidiagonal matrix `!![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]`, this file
proves the Bruhat-type identity

`w * u(a,b) * w = u(c,d) * w * u(e,f) * t(z)`

where `t(z) = diag(z^(1+2^n), z^(2^n), (z^(2^n))⁻¹, (z^(1+2^n))⁻¹)` and `c, d, e, f` are the
explicit functions of `a, b, z` from the statement.

The proof proceeds by an explicit computation.  Abbreviating `A = a^θ`, `B = b^θ`,
`t = z^(2^n)`, one has `z t = P := a^2 A + a b + B` (the hypothesis `hz`) and, applying `θ`
to `hz`, also `z t^2 = Q := A^2 a^2 + A B + b^2`; hence `z = P^2/Q` and `t = Q/P`.  All the
powers of `c, d, e, f` are then rewritten in terms of the atoms `a, b, A, B`, and the sixteen
matrix entries are polynomial (characteristic two) identities, closed by `ring_nf` followed by
`reduce_mod_char!`.
-/

namespace Commons.GroupTheory.Suzuki

open Matrix

/-! ## Auxiliary power identities in `GF(2 ^ (2n+1))` -/

theorem sz_pow_sq_of_pow_theta {n : ℕ} (x : GaloisField 2 (2 * n + 1)) :
    x ^ (2 ^ (2 * n + 2)) = x ^ 2 := by
  rw [show 2 ^ (2 * n + 2) = 2 ^ (2 * n + 1) * 2 by
    rw [show 2 * n + 2 = 2 * n + 1 + 1 by omega, pow_succ]]
  rw [pow_mul,
    Commons.FieldTheory.FiniteField.galoisField_pow_card_pow_self (p := 2) (2 * n + 1)
      (by omega) x]

theorem sz_pow_of_pow_theta {n : ℕ} (x : GaloisField 2 (2 * n + 1)) :
    (x ^ 2 ^ n) ^ 2 ^ (n + 1) = x := by
  conv_lhs => rw [← pow_mul]
  rw [show 2 ^ n * 2 ^ (n + 1) = 2 ^ (2 * n + 1) by rw [← pow_add]; congr 1; omega]
  exact Commons.FieldTheory.FiniteField.galoisField_pow_card_pow_self (p := 2) (2 * n + 1)
    (by omega) x

theorem sz_pow_theta_theta {n : ℕ} (x : GaloisField 2 (2 * n + 1)) :
    (x ^ 2 ^ (n + 1)) ^ 2 ^ (n + 1) = x ^ 2 :=
  Commons.FieldTheory.FiniteField.galoisField_pow_two_pow_succ_succ n x

set_option maxHeartbeats 1000000 in
theorem szW_conj_szU_matrix (n : ℕ) (a b z c d e f : GaloisField 2 (2 * n + 1))
    (hz0 : z ≠ 0)
    (hz : z ^ (1 + 2 ^ n) = a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)))
    (hc : c = (a ^ (1 + 2 ^ (n + 1)) + b) / z ^ (1 + 2 ^ n))
    (hd : d = a / z ^ (1 + 2 ^ n) + c ^ (1 + 2 ^ (n + 1)))
    (he : e = z ^ (1 + 2 ^ n) * d)
    (hf : f = a * z ^ (2 ^ n)) :
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] *
      !![1, a, b, a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1));
         0, 1, a ^ (2 ^ (n + 1)), a ^ (1 + 2 ^ (n + 1)) + b;
         0, 0, 1, a; 0, 0, 0, 1] *
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] =
      !![1, c, d, c ^ (2 + 2 ^ (n + 1)) + c * d + d ^ (2 ^ (n + 1));
         0, 1, c ^ (2 ^ (n + 1)), c ^ (1 + 2 ^ (n + 1)) + d;
         0, 0, 1, c; 0, 0, 0, 1] *
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] *
      !![1, e, f, e ^ (2 + 2 ^ (n + 1)) + e * f + f ^ (2 ^ (n + 1));
         0, 1, e ^ (2 ^ (n + 1)), e ^ (1 + 2 ^ (n + 1)) + f;
         0, 0, 1, e; 0, 0, 0, 1] *
      !![z ^ (1 + 2 ^ n), 0, 0, 0; 0, z ^ (2 ^ n), 0, 0;
         0, 0, (z ^ (2 ^ n))⁻¹, 0; 0, 0, 0, (z ^ (1 + 2 ^ n))⁻¹] := by
  have hchar : CharP (GaloisField 2 (2 * n + 1)) 2 := inferInstance
  set A : GaloisField 2 (2 * n + 1) := a ^ (2 ^ (n + 1)) with hA
  set B : GaloisField 2 (2 * n + 1) := b ^ (2 ^ (n + 1)) with hB
  set t : GaloisField 2 (2 * n + 1) := z ^ (2 ^ n) with ht
  have ht0 : t ≠ 0 := by rw [ht]; exact pow_ne_zero _ hz0
  have hz1 : z ^ (1 + 2 ^ n) = z * t := by
    rw [ht, show 1 + 2 ^ n = 2 ^ n + 1 by omega, pow_add, pow_one]; ring
  have hA1 : a ^ (1 + 2 ^ (n + 1)) = a * A := by
    rw [show 1 + 2 ^ (n + 1) = 2 ^ (n + 1) + 1 by omega, pow_add, pow_one, ← hA] <;> ring
  have hA2 : a ^ (2 + 2 ^ (n + 1)) = a ^ 2 * A := by rw [pow_add]
  have hB1 : b ^ (2 ^ (n + 1)) = B := hB.symm
  have hzt2 : z ^ (2 ^ (n + 1)) = t ^ 2 := by
    conv_lhs => rw [show 2 ^ (n + 1) = 2 ^ n * 2 by rw [mul_comm, ← pow_succ']]
    rw [pow_mul, ht]
  have htth : t ^ (2 ^ (n + 1)) = z := by rw [ht]; exact sz_pow_of_pow_theta z
  have hAth : A ^ (2 ^ (n + 1)) = a ^ 2 := by rw [hA]; exact sz_pow_theta_theta a
  have hBth : B ^ (2 ^ (n + 1)) = b ^ 2 := by rw [hB]; exact sz_pow_theta_theta b
  have hAthmul : (a ^ 2) ^ (2 ^ (n + 1)) = A ^ 2 := by
    rw [← pow_mul, show 2 * 2 ^ (n + 1) = 2 ^ (n + 1) * 2 by rw [mul_comm], pow_mul, hA]
  set P : GaloisField 2 (2 * n + 1) := a ^ 2 * A + a * b + B with hPdef
  set Q : GaloisField 2 (2 * n + 1) := A ^ 2 * a ^ 2 + A * B + b ^ 2 with hQdef
  have hzP : z * t = P := by rw [hPdef, ← hz1, hz, hA2]
  have hPowP : P ^ (2 ^ (n + 1)) = Q := by
    rw [hPdef, add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, hAthmul, hAth, hBth, ← hA, ← hB, hQdef]
  have hzQ : z * t ^ 2 = Q := by
    have h := congrArg (fun x : GaloisField 2 (2 * n + 1) => x ^ (2 ^ (n + 1))) hz
    rw [hz1, mul_pow, hzt2, htth, hA2, ← hPdef, hPowP] at h
    rw [← h]; ring
  have hPowQ : Q ^ (2 ^ (n + 1)) = P ^ 2 := by
    have h1 : Q ^ (2 ^ (n + 1)) = (z * t) ^ 2 := by
      rw [← hzQ, mul_pow, pow_two, mul_pow, htth, hzt2]
      ring
    rw [h1, hzP]
  have hP0 : P ≠ 0 := by rw [← hzP]; exact mul_ne_zero hz0 ht0
  have hQ0 : Q ≠ 0 := by rw [← hzQ]; exact mul_ne_zero hz0 (pow_ne_zero _ ht0)
  have hz_eq : z = P ^ 2 / Q := by rw [eq_div_iff hQ0, ← hzQ, ← hzP]; ring
  have ht_eq : t = Q / P := by rw [eq_div_iff hP0, ← hzP, ← hzQ]; ring
  -- atom formulas for c, d, e, f
  have hc0 : c = (a * A + b) / P := by rw [hc, hA1, hz1, ← hzP]
  have hZc : (a * A + b) ^ (2 ^ (n + 1)) = A * a ^ 2 + B := by
    rw [add_pow_char_pow, mul_pow, ← hA, hAth, hB1]
  have hcθ : c ^ (2 ^ (n + 1)) = (A * a ^ 2 + B) / Q := by rw [hc0, div_pow, hZc, hPowP]
  have hc1 : c ^ (1 + 2 ^ (n + 1)) = (a * A + b) * (A * a ^ 2 + B) / (P * Q) := by
    rw [show 1 + 2 ^ (n + 1) = 2 ^ (n + 1) + 1 by omega, pow_add, pow_one, hcθ, hc0] <;> ring
  have hc2 : c ^ (2 + 2 ^ (n + 1)) = (a * A + b) ^ 2 * (A * a ^ 2 + B) / (P ^ 2 * Q) := by
    rw [pow_add, hcθ, hc0, pow_two] <;> ring
  have hd0 : d = a / P + (a * A + b) * (A * a ^ 2 + B) / (P * Q) := by
    rw [hd, hz1, hzP, hc1]
  have hdθ : d ^ (2 ^ (n + 1)) = A / Q + (A * a ^ 2 + B) * (a * A + b) ^ 2 / (Q * P ^ 2) := by
    rw [hd, hz1, hzP, add_pow_char_pow]
    congr 1
    · rw [div_pow, ← hA, hPowP]
    · rw [← pow_mul, show (1 + 2 ^ (n + 1)) * 2 ^ (n + 1) = 2 ^ (n + 1) + 2 ^ (2 * n + 2) by
        rw [show (1 + 2 ^ (n + 1)) * 2 ^ (n + 1)
            = 2 ^ (n + 1) + 2 ^ (n + 1) * 2 ^ (n + 1) by ring]
        rw [show 2 ^ (n + 1) * 2 ^ (n + 1) = 2 ^ (2 * n + 2) by rw [← pow_add]; congr 1; omega]]
      rw [pow_add, sz_pow_sq_of_pow_theta, hcθ, hc0, pow_two] <;> ring
  have he0 : e = a + (a * A + b) * (A * a ^ 2 + B) / Q := by
    rw [he, hz1, hzP, hd0] <;> field_simp
  have heθ : e ^ (2 ^ (n + 1)) = A + (A * a ^ 2 + B) * (a * A + b) ^ 2 / P ^ 2 := by
    rw [he, hz1, hzP, mul_pow, hPowP, hdθ] <;> field_simp
  have hf0 : f = a * Q / P := by rw [hf, ht_eq]; ring
  have hfθ : f ^ (2 ^ (n + 1)) = A * P ^ 2 / Q := by
    rw [hf0, div_pow, mul_pow, ← hA, hPowQ, hPowP]
  have he1 : e ^ (1 + 2 ^ (n + 1)) =
      (a + (a * A + b) * (A * a ^ 2 + B) / Q) * (A + (A * a ^ 2 + B) * (a * A + b) ^ 2 / P ^ 2) := by
    rw [show 1 + 2 ^ (n + 1) = 2 ^ (n + 1) + 1 by omega, pow_add, pow_one, heθ, he0] <;> ring
  have he2 : e ^ (2 + 2 ^ (n + 1)) =
      (a + (a * A + b) * (A * a ^ 2 + B) / Q) ^ 2
        * (A + (A * a ^ 2 + B) * (a * A + b) ^ 2 / P ^ 2) := by
    rw [pow_add, heθ, he0, pow_two]
  -- atom formulas for c, d, e, f
  have hc0 : c = (a * A + b) / P := by rw [hc, hA1, hz1, ← hzP]
  have hZc : (a * A + b) ^ (2 ^ (n + 1)) = A * a ^ 2 + B := by
    rw [add_pow_char_pow, mul_pow, ← hA, hAth, hB1]
  have hcθ : c ^ (2 ^ (n + 1)) = (A * a ^ 2 + B) / Q := by rw [hc0, div_pow, hZc, hPowP]
  have hc1 : c ^ (1 + 2 ^ (n + 1)) = (a * A + b) * (A * a ^ 2 + B) / (P * Q) := by
    rw [show 1 + 2 ^ (n + 1) = 2 ^ (n + 1) + 1 by omega, pow_add, pow_one, hcθ, hc0] <;> ring
  have hc2 : c ^ (2 + 2 ^ (n + 1)) = (a * A + b) ^ 2 * (A * a ^ 2 + B) / (P ^ 2 * Q) := by
    rw [pow_add, hcθ, hc0, pow_two] <;> ring
  have hd0 : d = a / P + (a * A + b) * (A * a ^ 2 + B) / (P * Q) := by
    rw [hd, hz1, hzP, hc1]
  have hdθ : d ^ (2 ^ (n + 1)) = A / Q + (A * a ^ 2 + B) * (a * A + b) ^ 2 / (Q * P ^ 2) := by
    rw [hd, hz1, hzP, add_pow_char_pow]
    congr 1
    · rw [div_pow, ← hA, hPowP]
    · rw [← pow_mul, show (1 + 2 ^ (n + 1)) * 2 ^ (n + 1) = 2 ^ (n + 1) + 2 ^ (2 * n + 2) by
        rw [show (1 + 2 ^ (n + 1)) * 2 ^ (n + 1)
            = 2 ^ (n + 1) + 2 ^ (n + 1) * 2 ^ (n + 1) by ring]
        rw [show 2 ^ (n + 1) * 2 ^ (n + 1) = 2 ^ (2 * n + 2) by rw [← pow_add]; congr 1; omega]]
      rw [pow_add, sz_pow_sq_of_pow_theta, hcθ, hc0, pow_two] <;> ring
  have he0 : e = a + (a * A + b) * (A * a ^ 2 + B) / Q := by
    rw [he, hz1, hzP, hd0] <;> field_simp
  have heθ : e ^ (2 ^ (n + 1)) = A + (A * a ^ 2 + B) * (a * A + b) ^ 2 / P ^ 2 := by
    rw [he, hz1, hzP, mul_pow, hPowP, hdθ] <;> field_simp
  have hf0 : f = a * Q / P := by rw [hf, ht_eq]; ring
  have hfθ : f ^ (2 ^ (n + 1)) = A * P ^ 2 / Q := by
    rw [hf0, div_pow, mul_pow, ← hA, hPowQ, hPowP]
  have he1 : e ^ (1 + 2 ^ (n + 1)) =
      (a + (a * A + b) * (A * a ^ 2 + B) / Q) * (A + (A * a ^ 2 + B) * (a * A + b) ^ 2 / P ^ 2) := by
    rw [show 1 + 2 ^ (n + 1) = 2 ^ (n + 1) + 1 by omega, pow_add, pow_one, heθ, he0] <;> ring
  have he2 : e ^ (2 + 2 ^ (n + 1)) =
      (a + (a * A + b) * (A * a ^ 2 + B) / Q) ^ 2
        * (A + (A * a ^ 2 + B) * (a * A + b) ^ 2 / P ^ 2) := by
    rw [pow_add, heθ, he0, pow_two]
  -- matrix abbreviations
  set Wm : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1)) :=
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] with hWm
  set Uab : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1)) :=
    !![1, a, b, a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1));
       0, 1, a ^ (2 ^ (n + 1)), a ^ (1 + 2 ^ (n + 1)) + b; 0, 0, 1, a; 0, 0, 0, 1] with hUab
  set Ucd : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1)) :=
    !![1, c, d, c ^ (2 + 2 ^ (n + 1)) + c * d + d ^ (2 ^ (n + 1));
       0, 1, c ^ (2 ^ (n + 1)), c ^ (1 + 2 ^ (n + 1)) + d; 0, 0, 1, c; 0, 0, 0, 1] with hUcd
  set Uef : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1)) :=
    !![1, e, f, e ^ (2 + 2 ^ (n + 1)) + e * f + f ^ (2 ^ (n + 1));
       0, 1, e ^ (2 ^ (n + 1)), e ^ (1 + 2 ^ (n + 1)) + f; 0, 0, 1, e; 0, 0, 0, 1] with hUef
  set Tm : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1)) :=
    !![z ^ (1 + 2 ^ n), 0, 0, 0; 0, z ^ (2 ^ n), 0, 0;
       0, 0, (z ^ (2 ^ n))⁻¹, 0; 0, 0, 0, (z ^ (1 + 2 ^ n))⁻¹] with hTm
  set Mmat : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1)) :=
    !![1, 0, 0, 0; a, 1, 0, 0; a * A + b, A, 1, 0; P, b, a, 1] with hMmat
  have hX : a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)) = P := by
    rw [hB1, ← hzP, ← hz1, hz]
  have hL : Wm * Uab * Wm = Mmat := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_four, hWm, hUab, hMmat, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.of_apply, Matrix.cons_val_two, Matrix.cons_val_three,
        Fin.reduceFinMk, Fin.isValue, Matrix.head_fin_const]
    all_goals try simp [hA1, hA, hzP, hX]
  have hR : Ucd * Wm * Uef * Tm = Mmat := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_four, hUcd, hWm, hUef, hTm, hMmat,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Matrix.cons_val_two,
        Matrix.cons_val_three, Fin.reduceFinMk, Fin.isValue, Matrix.head_fin_const,
        zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]
    all_goals
      try rw [hX]
      try rw [hc2]
      try rw [hc1]
      try rw [hcθ]
      try rw [hdθ]
      try rw [he2]
      try rw [he1]
      try rw [heθ]
      try rw [hfθ]
      try rw [hc0]
      try rw [hd0]
      try rw [he0]
      try rw [hf0]
      try rw [hz1]
      try rw [hzP]
      try rw [← ht]
      try rw [ht_eq]
      try field_simp [hP0, hQ0]
      try simp only [hPdef, hQdef]
      try ring_nf
      try reduce_mod_char!
  rw [hL, hR]

end Commons.GroupTheory.Suzuki