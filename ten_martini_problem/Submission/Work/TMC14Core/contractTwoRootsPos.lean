import Mathlib

namespace Work.TMC14Core

/-- If `p = q(X ^ 2)` has only real roots and `q 0 ≠ 0`, then every root of `q` is a
strictly positive real number. -/
theorem contractTwoRootsPos (p q : Polynomial ℂ) (hqe : p = Polynomial.expand ℂ 2 q)
    (h0 : q.eval 0 ≠ 0) (hreal : ∀ z : ℂ, p.eval z = 0 → z.im = 0) :
    ∀ z ∈ q.roots, z.im = 0 ∧ 0 < z.re := by
  intro z hz
  -- `z` is a root of `q`
  have hqz : q.eval z = 0 :=
    Polynomial.IsRoot.def.mp (Polynomial.isRoot_of_mem_roots hz)
  -- take a square root `w` of `z`, then `w` is a root of `p`, hence real
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_eq_mul_self (k := ℂ) z
  have hpow : w ^ 2 = z := by rw [hw]; ring
  have hpw : p.eval w = 0 := by
    rw [hqe, Polynomial.expand_eval, hpow]
    exact hqz
  have hwim : w.im = 0 := hreal w hpw
  -- consequently `z = w ^ 2` is a nonnegative real
  have hzre : z.re = w.re ^ 2 := by
    rw [hw, Complex.mul_re]
    simp only [hwim, mul_zero, sub_zero]
    ring
  have hzim : z.im = 0 := by
    rw [hw, Complex.mul_im]
    simp [hwim]
  -- and it is nonzero, since `q.eval 0 ≠ 0`
  have hwre : w.re ≠ 0 := by
    intro h
    have hz0 : z = 0 := by
      apply Complex.ext
      · rw [hzre, h]; simp
      · simp [hzim]
    rw [hz0] at hqz
    exact h0 hqz
  exact ⟨hzim, by rw [hzre]; exact sq_pos_of_ne_zero hwre⟩

end Work.TMC14Core
