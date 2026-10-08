import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Torus

/-! ## Preliminaries: unipotent elements of `SL(2,F)`

If `x ∈ SL(2,F)` (`F` of characteristic `p`) has `disc F x = 0`, its trace is `±2`, so `x`
(or `-x`) is unipotent: `x = 1 + N` (or `x = -(1 + N)`) with `N² = 0`.  Expanding
`(1 + N)^p = 1 + p N = 1` in characteristic `p` shows that the image of `x` in `PSL(2,F)` has
order dividing `p`. -/

/-- **Binomial expansion of a unipotent element.**  In any ring, if `t ^ 2 = 0`, then
`(1 + t) ^ n = 1 + n * t` for every `n : ℕ`. -/
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

/-- A `2 × 2` matrix over a field of characteristic `p` with `det = 1` and trace `2` is
unipotent, so `M ^ p = 1`. -/
theorem mat_pow_prime_eq_one_of_det_one_trace_two (F : Type*) [Field F] (p : ℕ) [CharP F p]
    (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1) (htr : M.trace = 2) : M ^ p = 1 := by
  have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F M
  have hMM : M * M = 2 * M - 1 := by
    rw [hCH, htr, hdet, one_smul, Algebra.smul_def, map_ofNat]
  have hN : (M - 1) * (M - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_one, one_mul, hMM]; noncomm_ring
  have hp0 : (p : Matrix (Fin 2) (Fin 2) F) = 0 := CharP.cast_eq_zero _ p
  calc M ^ p = (1 + (M - 1)) ^ p := by rw [add_sub_cancel]
    _ = 1 + (p : Matrix (Fin 2) (Fin 2) F) * (M - 1) :=
          one_add_pow_of_sq_eq_zero (M - 1) (by rw [pow_two]; exact hN) p
    _ = 1 := by rw [hp0, zero_mul, add_zero]

/-- If `x ∈ SL(2, F)` (`F` of characteristic `p`) has trace `2`, then `x ^ p = 1`. -/
theorem sl_pow_prime_eq_one_of_trace_eq_two (F : Type*) [Field F] (p : ℕ) [CharP F p]
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (htr : (((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F).trace = 2) : x ^ p = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact mat_pow_prime_eq_one_of_det_one_trace_two F p _
    (Matrix.SpecialLinearGroup.det_coe x) htr

/-- The image of `-1` in `PSL(2,F)` is trivial (in odd characteristic, where `-1` is the
nontrivial central element). -/
theorem pslMap_negOne_eq_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Work.PSL2.pslMap F (Work.L2F.negOne F) = 1 :=
  (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)

/-- If `x ∈ SL(2,F)` has trace `-2`, then the image of `x` in `PSL(2,F)` has order dividing `p`:
`-x` has trace `2`, so `(-x) ^ p = 1`, and `-x` has the same image as `x` in `PSL(2,F)`. -/
theorem orderOf_pslMap_dvd_prime_of_trace_eq_neg_two (F : Type*) [Field F] (p : ℕ) [CharP F p]
    (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (htr : (((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F).trace = -2) :
    orderOf (Work.PSL2.pslMap F x) ∣ p := by
  have htr' : (((Work.L2F.negOne F * x : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 2 := by
    rw [Matrix.SpecialLinearGroup.coe_mul,
      show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = -1 from rfl,
      Matrix.neg_mul, Matrix.one_mul, Matrix.trace_neg, htr]
    norm_num
  have hyp : (Work.L2F.negOne F * x) ^ p = 1 := sl_pow_prime_eq_one_of_trace_eq_two F p _ htr'
  have hyord : orderOf (Work.L2F.negOne F * x) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hyp
  have hmap : Work.PSL2.pslMap F (Work.L2F.negOne F * x) = Work.PSL2.pslMap F x := by
    rw [map_mul, pslMap_negOne_eq_one F h2, one_mul]
  have h1 : orderOf (Work.PSL2.pslMap F (Work.L2F.negOne F * x)) ∣ p :=
    (orderOf_map_dvd (Work.PSL2.pslMap F) (Work.L2F.negOne F * x)).trans hyord
  rwa [hmap] at h1

/-- If `x ∈ SL(2,F)` has `disc F x = 0` (so its trace is `±2`), then the order of the image of
`x` in `PSL(2,F)` divides the characteristic `p`. -/
theorem orderOf_pslMap_dvd_prime_of_disc_eq_zero (F : Type*) [Field F] (p : ℕ) [CharP F p]
    (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F) (hD : disc F x = 0) :
    orderOf (Work.PSL2.pslMap F x) ∣ p := by
  have htrsq : (((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F).trace ^ 2 = 4 := by
    rw [disc_apply] at hD
    exact sub_eq_zero.mp hD
  have htr : (((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F).trace = 2 ∨
      (((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F).trace = -2 := by
    have hfac : ((((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
          Matrix (Fin 2) (Fin 2) F).trace - 2) *
        ((((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
          Matrix (Fin 2) (Fin 2) F).trace + 2) = 0 := by
      have h : ((((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
            Matrix (Fin 2) (Fin 2) F).trace - 2) *
          ((((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
            Matrix (Fin 2) (Fin 2) F).trace + 2) =
          (((x : Matrix.SpecialLinearGroup (Fin 2) F)) :
            Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 := by ring
      rw [h, htrsq]; ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)
  rcases htr with htr | htr
  · exact (orderOf_map_dvd (Work.PSL2.pslMap F) x).trans
      (orderOf_dvd_iff_pow_eq_one.mpr
        (sl_pow_prime_eq_one_of_trace_eq_two F p x htr))
  · exact orderOf_pslMap_dvd_prime_of_trace_eq_neg_two F p h2 x htr

/-- If `x ∈ SL(2,F)` has image of prime order `r ≠ p` in `PSL(2,F)` (`F` of odd characteristic
`p`), then `x` is not unipotent: `disc F x ≠ 0`. -/
theorem disc_ne_zero (F : Type*) [Field F] (p r : ℕ) [Fact p.Prime] [CharP F p] (hp : Odd p)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r.Prime) (hrp : r ≠ p)
    (hx : orderOf (Work.PSL2.pslMap F x) = r) : disc F x ≠ 0 := by
  intro hD
  -- `-1 ≠ 1` in `F` since `p` is odd.
  have h2 : (2 : F) ≠ 0 := by
    intro hzero
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp hzero
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · rw [h] at hp
      obtain ⟨k, hk⟩ := hp
      omega
  -- The image of `x` has order dividing `p`; as `r` is prime this forces `r = p`.
  have hdvd : orderOf (Work.PSL2.pslMap F x) ∣ p :=
    orderOf_pslMap_dvd_prime_of_disc_eq_zero F p h2 x hD
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h | h
  · exact hr.ne_one (hx ▸ h)
  · exact hrp (hx ▸ h)

end Work.L2F.Torus
