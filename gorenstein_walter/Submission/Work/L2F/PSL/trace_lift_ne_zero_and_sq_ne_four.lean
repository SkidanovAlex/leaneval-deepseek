import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.PSL2.Basic
import Submission.Work.L2F.Mat2.trace_mul_self
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-! ## Two computations for `2 × 2` matrices

Both facts below are immediate consequences of Cayley–Hamilton for `2 × 2` matrices,
`M * M = tr M • M - det M • 1` (`Work.L2F.Mat2.sq_eq_trace_smul_sub_det`), together with
`det M = 1`.

* If `tr M = 0`, then `M ^ 2 = -1`, hence `M ^ 4 = 1`.
* If `tr M = ±2`, then `M = ±1 + N` with `N ^ 2 = 0`; since `N ^ 2 = 0` the binomial expansion of
  the unipotent element `1 + N` has only the first two terms, and in characteristic `p` the
  linear term `(2p) • N` vanishes, so `M ^ (2 * p) = 1`.
-/

/-- **Binomial expansion of a unipotent element.**  In any ring, if `t ^ 2 = 0`, then
`(1 + t) ^ n = 1 + n * t` for every `n : ℕ`.  (This is just the binomial theorem truncated at the
linear term: formally, induction on `n`, the step being
`(1 + n t)(1 + t) = 1 + (n + 1) t + n t ^ 2 = 1 + (n + 1) t`.) -/
theorem one_add_pow_of_sq_eq_zero {R : Type*} [Ring R] (t : R) (ht : t ^ 2 = 0) (n : ℕ) :
    (1 + t) ^ n = 1 + (n : R) * t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    conv_rhs => rw [Nat.cast_succ, add_mul, one_mul]
    rw [add_mul, one_mul, mul_add, mul_one]
    rw [show (↑n : R) * t * t = 0 by rw [mul_assoc, ← pow_two, ht, mul_zero], add_zero]
    abel

/-- Cayley–Hamilton with `det M = 1` and `tr M = 0` gives `M ^ 2 = -1`, hence `M ^ 4 = 1`.
(Used to rule out `tr x = 0` for a lift of an element of odd order: then `orderOf x ∣ 4`.) -/
theorem pow_four_eq_one_of_trace_eq_zero {F : Type*} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1) (htr : M.trace = 0) :
    M ^ 4 = 1 := by
  have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F M
  have hsq : M ^ 2 = -1 := by
    rw [pow_two, hCH, htr, hdet]
    simp
  rw [show (4:ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
  norm_num

/-- Cayley–Hamilton with `det M = 1` and `tr M = ±2` gives `M = ±1 + N` with `N ^ 2 = 0`
(`N = M ∓ 1`), and then `M ^ (2 * p) = ((±1 + N) ^ 2) ^ p = (1 + 2 N') ^ p = 1` because the base
ring has characteristic `p`, so the linear term `p • (2 N')` of the binomial expansion vanishes.

In particular an element of `SL(2, F)` of trace `±2` has order dividing `2 * p`, which is what
rules out `(tr x) ^ 2 = 4` for a lift of an element of odd order prime to `p`. -/
theorem pow_two_mul_prime_eq_one_of_trace_eq_two_or_neg_two {p : ℕ} {F : Type*} [Field F]
    [CharP F p] (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1)
    (htr : M.trace = 2 ∨ M.trace = -2) : M ^ (2 * p) = 1 := by
  have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F M
  -- General shape: whenever `M ^ 2 = 1 + t` with `t ^ 2 = 0`, we have `M ^ (2 * p) = 1`.
  have hgen : ∀ t : Matrix (Fin 2) (Fin 2) F, M ^ 2 = 1 + t → t ^ 2 = 0 → M ^ (2 * p) = 1 := by
    intro t hM2 ht2
    have hp0 : (p : Matrix (Fin 2) (Fin 2) F) = 0 := CharP.cast_eq_zero _ p
    rw [pow_mul, hM2, one_add_pow_of_sq_eq_zero t ht2 p, hp0, zero_mul, add_zero]
  rcases htr with htr | htr
  · -- `tr M = 2` : `M ^ 2 = 2 * M - 1 = 1 + 2 * (M - 1)`, and `(M - 1) ^ 2 = 0`.
    have hMM : M * M = 2 * M - 1 := by
      have h := hCH
      rw [htr, hdet] at h
      rw [h, one_smul, Algebra.smul_def, map_ofNat]
    refine hgen (2 * (M - 1)) ?_ ?_
    · rw [pow_two, hMM]; noncomm_ring
    · have hN : (M - 1) * (M - 1) = 0 := by
        rw [sub_mul, mul_sub, mul_one, one_mul, hMM]; noncomm_ring
      rw [pow_two,
        show (2 * (M - 1)) * (2 * (M - 1)) = 4 * ((M - 1) * (M - 1)) by noncomm_ring,
        hN, mul_zero]
  · -- `tr M = -2` : `M ^ 2 = -(2 * M) - 1 = 1 - 2 * (M + 1)`, and `(M + 1) ^ 2 = 0`.
    have hMM : M * M = -(2 * M) - 1 := by
      have h := hCH
      rw [htr, hdet] at h
      rw [h, one_smul, neg_smul, Algebra.smul_def, map_ofNat]
    refine hgen (-(2 * (M + 1))) ?_ ?_
    · rw [pow_two, hMM]; noncomm_ring
    · have hN : (M + 1) * (M + 1) = 0 := by
        rw [add_mul, mul_add, mul_one, one_mul, hMM]; noncomm_ring
      rw [pow_two, neg_mul_neg,
        show (2 * (M + 1)) * (2 * (M + 1)) = 4 * ((M + 1) * (M + 1)) by noncomm_ring,
        hN, mul_zero]

/-! ## The main statement

The argument is carried out for an arbitrary field `F` of characteristic `p` (the assumption
`Odd p` is not needed: the statement also holds in characteristic `2`, where the centre of
`SL(2, F)` is trivial).  The only use of `pslMap x = y` is `orderOf y ∣ orderOf x`. -/

/-- General form of `trace_lift_ne_zero_and_sq_ne_four` over an arbitrary field of
characteristic `p`. -/
theorem trace_lift_ne_zero_and_sq_ne_four_aux {p : ℕ} [Fact p.Prime] (F : Type*) [Field F]
    [CharP F p] (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (hy1 : y ≠ 1)
    (hodd : Odd (orderOf y)) (hcop : ¬ p ∣ orderOf y)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) (hx : Work.PSL2.pslMap F x = y) :
    ((x : Matrix (Fin 2) (Fin 2) F)).trace ≠ 0 ∧
      ((x : Matrix (Fin 2) (Fin 2) F)).trace ^ 2 ≠ 4 := by
  -- Work with the underlying matrix `M` of `x`.
  set M : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : M.det = 1 := by rw [hM]; exact Matrix.SpecialLinearGroup.det_coe x
  -- `pslMap x = y` gives `orderOf y ∣ orderOf x`.
  have hn : orderOf y ∣ orderOf x := by
    have h := orderOf_map_dvd (Work.PSL2.pslMap F) x
    rwa [hx] at h
  -- `orderOf y` is odd, so it is coprime to `2`.
  have hcop2 : (orderOf y).Coprime 2 := Nat.coprime_two_right.mpr hodd
  constructor
  · -- Suppose `tr x = 0`.  Then `x ^ 4 = 1`, so `orderOf y ∣ 4`; as `orderOf y` is odd, it is `1`,
    -- whence `y = 1`, contradicting `hy1`.
    intro htr0
    have h4 : M ^ 4 = 1 := pow_four_eq_one_of_trace_eq_zero M hdet htr0
    have hx4 : x ^ 4 = 1 := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      rw [hM] at h4
      exact h4
    have hord : orderOf x ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hx4
    have hn4 : orderOf y ∣ 4 := dvd_trans hn hord
    rw [show (4:ℕ) = 2 * 2 by norm_num] at hn4
    have h2 : orderOf y ∣ 2 := hcop2.dvd_of_dvd_mul_left hn4
    have h1 : orderOf y ∣ 1 := hcop2.dvd_of_dvd_mul_left (by rw [mul_one]; exact h2)
    exact hy1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
  · -- Suppose `(tr x) ^ 2 = 4`.  Then `tr x = ±2`, so `x ^ (2 * p) = 1` and `orderOf y ∣ 2 * p`;
    -- as `orderOf y` is odd and `p` is prime, `orderOf y ∈ {1, p}`, contradicting `y ≠ 1`
    -- and `¬ p ∣ orderOf y`.
    intro htr4
    have htr2 : M.trace = 2 ∨ M.trace = -2 := by
      have hfac : (M.trace - 2) * (M.trace + 2) = 0 := by
        have : (M.trace - 2) * (M.trace + 2) = M.trace ^ 2 - 4 := by ring
        rw [this, htr4, sub_self]
      rcases mul_eq_zero.mp hfac with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)
    have h2p : M ^ (2 * p) = 1 :=
      pow_two_mul_prime_eq_one_of_trace_eq_two_or_neg_two M hdet htr2
    have hx2p : x ^ (2 * p) = 1 := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      rw [hM] at h2p
      exact h2p
    have hord : orderOf x ∣ 2 * p := orderOf_dvd_iff_pow_eq_one.mpr hx2p
    have hn2p : orderOf y ∣ 2 * p := dvd_trans hn hord
    have hnp : orderOf y ∣ p := hcop2.dvd_of_dvd_mul_left hn2p
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf y) hnp with h1 | hp'
    · exact hy1 (orderOf_eq_one_iff.mp h1)
    · exact hcop (hp'.symm ▸ dvd_refl p)

/-- **Trace of a lift.**  Let `p` be an odd prime, `y ∈ PSL(2,GF(p,k))` a non-identity element of
odd order not divisible by `p`, and `x ∈ SL(2,GF(p,k))` any lift of `y`.  Then
`tr x ≠ 0` and `(tr x)^2 ≠ 4`; equivalently `x` is not unipotent up to sign, and `x` is not
conjugate to `-x` (this is used to identify `C_{PSL}(y)` with the image of `C_{SL}(x)`).

Intended proof.  Since `pslMap x = y`, the order `n := orderOf y` divides the order of `x`, and
`x ^ n ∈ {±1}` is central, so `orderOf x` is `n` or `2n`.  If `tr x = 0` then Cayley–Hamilton
(`x^2 - (tr x) x + det x • 1 = 0`, `det x = 1`) gives `x^2 = -1`, so `x^4 = 1` and `orderOf x ∣ 4`;
as `orderOf x ∈ {n, 2n}` with `n` odd this forces `n = 1`, i.e. `y = 1`, a contradiction.  If
`(tr x)^2 = 4` then `tr x = ±2` and the characteristic polynomial is `(X ∓ 1)^2`, so
`(x ∓ 1)^2 = 0`; writing `x = ±1 + N` with `N^2 = 0` and expanding `(±1 + N)^p` in
characteristic `p` gives `x ^ p = ±1`, hence `orderOf x ∣ 2p`; with `n` odd, `n ∣ 2p` forces
`n = 1` or `n = p`, both impossible (`n ≠ 1` since `y ≠ 1`, and `p ∤ n`), a contradiction. -/
theorem trace_lift_ne_zero_and_sq_ne_four {p k : ℕ} [Fact p.Prime] (hp : Odd p)
    (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) (hy1 : y ≠ 1)
    (hodd : Odd (orderOf y)) (hcop : ¬ p ∣ orderOf y)
    (x : Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k))
    (hx : Work.PSL2.pslMap (GaloisField p k) x = y) :
    ((x : Matrix (Fin 2) (Fin 2) (GaloisField p k))).trace ≠ 0 ∧
      ((x : Matrix (Fin 2) (Fin 2) (GaloisField p k))).trace ^ 2 ≠ 4 :=
  trace_lift_ne_zero_and_sq_ne_four_aux (GaloisField p k) y hy1 hodd hcop x hx

end Work.L2F.PSL
