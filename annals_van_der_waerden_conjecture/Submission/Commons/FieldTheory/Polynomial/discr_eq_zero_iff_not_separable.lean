import Mathlib.FieldTheory.Separable
import Submission.Commons.FieldTheory.Polynomial.discr_mul

open Polynomial

namespace Commons.FieldTheory.Polynomial

noncomputable section

variable {F : Type*} [Field F]

/-- For a monic polynomial `p` over a field, the discriminant, which is by definition
computed from the Sylvester matrix of `p` and `p.derivative` where the derivative is
treated as having degree `natDegree p - 1`, agrees with the ordinary resultant
`p.resultant p.derivative` (whose second degree argument is the actual degree of the
derivative). For monic `p` the missing power of the leading coefficient is `1`. -/
lemma discr_eq_resultant (p : F[X]) (hp : p.Monic) (hn : 0 < p.natDegree) :
    p.discr = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) *
      Polynomial.resultant p p.derivative := by
  classical
  have hdeg_le : p.derivative.natDegree ≤ p.natDegree - 1 := natDegree_derivative_le p
  have hcoeff : p.coeff p.natDegree = 1 := by
    exact hp.leadingCoeff
  have hmain := resultant_add_right_deg (f := p) (g := p.derivative)
    (m := p.natDegree) (n := p.derivative.natDegree)
    ((p.natDegree - 1) - p.derivative.natDegree)
    (le_rfl : p.derivative.natDegree ≤ p.derivative.natDegree)
  have hres : Polynomial.resultant p p.derivative p.natDegree (p.natDegree - 1) =
      Polynomial.resultant p p.derivative := by
    calc
      Polynomial.resultant p p.derivative p.natDegree (p.natDegree - 1)
          = p.coeff p.natDegree ^ ((p.natDegree - 1) - p.derivative.natDegree) *
              Polynomial.resultant p p.derivative p.natDegree p.derivative.natDegree := by
            simpa [Nat.add_sub_of_le hdeg_le] using hmain
      _ = Polynomial.resultant p p.derivative := by
            rw [hcoeff, one_pow, one_mul]
  calc
    p.discr = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) *
        Polynomial.resultant p p.derivative p.natDegree (p.natDegree - 1) :=
          discr_eq_signed_resultant p hp hn
    _ = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) *
        Polynomial.resultant p p.derivative := by
          rw [hres]

theorem discr_eq_zero_iff_not_separable {F : Type*} [Field F] {p : F[X]}
    (hp : p.Monic) (hn : 0 < p.natDegree) : Polynomial.discr p = 0 ↔ ¬ p.Separable := by
  classical
  have hdisc : Polynomial.discr p = 0 ↔
      Polynomial.resultant p p.derivative = 0 := by
    rw [discr_eq_resultant p hp hn]
    have ha : (-1 : F) ^ (p.natDegree * (p.natDegree - 1) / 2) ≠ 0 := by
      exact pow_ne_zero _ (by exact neg_ne_zero.mpr one_ne_zero)
    constructor
    · intro hx
      exact (mul_eq_zero.mp hx).resolve_left ha
    · intro hx
      rw [hx]
      exact mul_zero _
  have hpne : p ≠ 0 := hp.ne_zero
  have hsep : ¬ p.Separable ↔ ¬ IsCoprime p p.derivative :=
    not_congr (separable_def p)
  have hz : Polynomial.resultant p p.derivative = 0 ↔ ¬ p.Separable := by
    calc
      Polynomial.resultant p p.derivative = 0
          ↔ (p ≠ 0 ∨ p.derivative ≠ 0) ∧ ¬ IsCoprime p p.derivative :=
            resultant_eq_zero_iff (K := F) (f := p) (g := p.derivative)
      _ ↔ ¬ IsCoprime p p.derivative := by
            constructor
            · intro h; exact h.2
            · intro h; exact ⟨Or.inl hpne, h⟩
      _ ↔ ¬ p.Separable := hsep.symm
  exact hdisc.trans hz

end

end Commons.FieldTheory.Polynomial