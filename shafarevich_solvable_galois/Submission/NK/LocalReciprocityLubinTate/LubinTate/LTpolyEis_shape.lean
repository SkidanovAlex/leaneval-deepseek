import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.EisFactor
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shape of the Eisenstein factor `f^{[n]}(T) = f^{(n-1)}(T)^{q-1} + π`

The `n`-th Eisenstein factor `LTpolyEis π q n = (f^{(n)})^{q-1} + π` of the standard
Lubin–Tate polynomial `f(T) = πT + T^q` is monic of degree `(q-1)q^n`, has constant
coefficient `π` and leading coefficient `1`:

`f^{[n]}(T) = T^{(q-1)q^n} + ⋯ + π`,

(Milne, *CFT*, §I.3, Remark 3.1).

Everything is read off from the shape of the iterate `f^{(n)}` proved in
`NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree`
(`f^{(n)}` is monic of degree `q^n`, has linear coefficient `π^n` and vanishing
constant coefficient): raising to the `(q-1)`-st power is compatible with monicity and
multiplies the degree by `q-1`, adding the constant `π` only affects the constant
coefficient, and the top coefficient of `(f^{(n)})^{q-1}` survives because the degree of
the constant polynomial is strictly smaller.
-/

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

open Polynomial

theorem LTpolyEis_shape {A : Type u} [CommRing A] [Nontrivial A] (π : A) (q n : ℕ) (hq : 2 ≤ q) :
    (NK.LocalReciprocityLubinTate.LTpolyEis π q n).Monic
      ∧ (NK.LocalReciprocityLubinTate.LTpolyEis π q n).natDegree = (q - 1) * q ^ n
      ∧ (NK.LocalReciprocityLubinTate.LTpolyEis π q n).coeff 0 = π
      ∧ (NK.LocalReciprocityLubinTate.LTpolyEis π q n).coeff ((q - 1) * q ^ n) = 1 := by
  obtain ⟨hp, hpd, -, hpc0⟩ := LTpolyIter_monic_degree π q n hq
  have hpowmonic : ((LTpolyIter π q n) ^ (q - 1)).Monic := hp.pow _
  have hpowdeg : ((LTpolyIter π q n) ^ (q - 1)).natDegree = (q - 1) * q ^ n := by
    rw [hp.natDegree_pow, hpd]
  have hdegpos : 0 < (q - 1) * q ^ n := Nat.mul_pos (by omega) (pow_pos (by omega) n)
  have hlt : (C π).degree < ((LTpolyIter π q n) ^ (q - 1)).degree := by
    refine lt_of_le_of_lt degree_C_le ?_
    rw [degree_eq_natDegree hpowmonic.ne_zero, hpowdeg]
    exact_mod_cast hdegpos
  refine ⟨hpowmonic.add_of_left hlt, ?_, ?_, ?_⟩
  · rw [NK.LocalReciprocityLubinTate.LTpolyEis, natDegree_add_eq_left_of_degree_lt hlt, hpowdeg]
  · have hz : ((LTpolyIter π q n) ^ (q - 1)).coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, hpc0,
        zero_pow (by omega : q - 1 ≠ 0)]
    rw [NK.LocalReciprocityLubinTate.LTpolyEis, coeff_add, hz, coeff_C_zero, zero_add]
  · have hlead : ((LTpolyIter π q n) ^ (q - 1)).coeff ((q - 1) * q ^ n) = 1 := by
      rw [← hpowdeg]
      exact hpowmonic
    rw [NK.LocalReciprocityLubinTate.LTpolyEis, coeff_add, hlead,
      coeff_C_of_ne_zero (by omega : (q - 1) * q ^ n ≠ 0), add_zero]

end NK.LocalReciprocityLubinTate.LubinTate
