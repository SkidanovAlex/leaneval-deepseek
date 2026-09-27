import Mathlib
import Submission.Work.KT.isUnit_one_sub_of_matNorm_lt_one
import Submission.Work.KT.idem_close_conj_of_isUnit

namespace Work.KT

/-- Auxiliary computation: for idempotent `p`, `q` in a ring, the element
`1 + (2p - 1)(q - p)` intertwines `q` with `p`.  (This is the purely algebraic half of
`Work.KT.idem_close_conj_of_isUnit`, kept for the specific element rather than an abstract unit.) -/
private lemma one_add_two_mul_sub_one_intertwine {A : Type*} [Ring A] {p q : A} (hp : p * p = p)
    (hq : q * q = q) :
    (1 + (2 * p - 1) * (q - p)) * q = p * (1 + (2 * p - 1) * (q - p)) := by
  set a : A := 2 * p - 1 with ha
  have h1 : a * p = p := by
    rw [ha, sub_mul, one_mul, mul_assoc, hp, two_mul, add_sub_cancel_left]
  have h2 : p * a = p := by
    rw [ha, mul_sub, mul_one, two_mul, mul_add, hp, add_sub_cancel_left]
  have h3 : 1 + a = 2 * p := by rw [ha]; abel
  have hu_eq : 1 + a * (q - p) = 1 + a * q - p := by rw [mul_sub, h1]; abel
  have hadd : q + a * q = (1 + a) * q := by rw [add_mul, one_mul]
  have hL : (1 + a * q - p) * q = p * q := by
    rw [sub_mul, add_mul, one_mul, mul_assoc, hq, hadd, h3, mul_assoc, two_mul,
      add_sub_cancel_left]
  have hR : p * (1 + a * q - p) = p * q := by
    rw [mul_sub, mul_add, mul_one, ← mul_assoc, h2, hp]; abel
  rw [hu_eq, hL, hR]

/-- If `p`, `q` are idempotent complex matrices and the row-sum norm of `(2p-1)(q-p)` is `< 1`,
then `1 + (2p-1)(q-p)` is a unit and intertwines `q` with `p`. -/
theorem chain_idem_isUnit_and_conj {n : ℕ} (p q : Matrix (Fin n) (Fin n) ℂ) (hp : p * p = p)
    (hq : q * q = q)
    (h : (Finset.univ.sup fun i => ∑ j,
        ‖(((2 * p - 1) * (q - p) : Matrix (Fin n) (Fin n) ℂ)) i j‖₊ : NNReal) < 1) :
    IsUnit (1 + (2 * p - 1) * (q - p)) ∧
      (1 + (2 * p - 1) * (q - p)) * q = p * (1 + (2 * p - 1) * (q - p)) := by
  refine ⟨?_, one_add_two_mul_sub_one_intertwine hp hq⟩
  -- The row-sum norm of `-((2p-1)(q-p))` is the same as that of `(2p-1)(q-p)`, so it is `< 1`.
  have hrow : (Finset.univ.sup fun i => ∑ j,
      ‖(-((2 * p - 1) * (q - p) : Matrix (Fin n) (Fin n) ℂ)) i j‖₊ : NNReal) < 1 := by
    simpa only [Matrix.neg_apply, nnnorm_neg] using h
  -- Hence `1 - (-((2p-1)(q-p))) = 1 + (2p-1)(q-p)` is a unit.
  have h' := Work.KT.isUnit_one_sub_of_matNorm_lt_one
    (-((2 * p - 1) * (q - p) : Matrix (Fin n) (Fin n) ℂ)) hrow
  simpa only [sub_neg_eq_add] using h'

end Work.KT
