import Mathlib
import Submission.Work.HP.Defs

/-!
# The "monomial times a linear form" map on degree-`d` forms

For `m : Mon (d-1) n` (an exponent vector of a degree-`(d-1)` monomial in `n+1` variables) and
`c : Fin (n+1) → ℤ`, `prodVec d n m c : Mon d n → ℤ` is the coefficient vector of the degree-`d`
form `X^m · ⟨c, X⟩`: its value at `m'` is `c j` when `m' = m + e_j` for the (unique) `j`, and `0`
otherwise.

The two properties used in the proof of `Work.HP.lam_latOrth_veronese_le` are

* `formEval d n (prodVec d n m c) x = veronese (d-1) n x m * (∑ j, c j * x j)`, so that
  `prodVec d n m c ∈ latOrth (veronese d n x)` whenever `∑ j, c j * x j = 0`; and
* `eNorm (prodVec d n m c) = eNorm c`.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP

/-- The coefficient vector of `X^m · ⟨c, X⟩` in the degree-`d` monomial basis.  For `d ≥ 1` and
`m : Mon (d-1) n`, the `m'`-coordinate is `c j` if `m' = m + e_j`, and `0` if `m'` is not of that
form. -/
def prodVec (d n : ℕ) (m : Mon (d - 1) n) (c : Fin (n + 1) → ℤ) : Mon d n → ℤ :=
  fun m' => ∑ j : Fin (n + 1),
    if (∀ i, ((m'.1 i : ℕ) = (m.1 i : ℕ) + (if i = j then 1 else 0))) then c j else 0

/-- The coefficient vector of `X^m · ⟨c, X⟩` as a real vector. -/
def prodVecR (d n : ℕ) (m : Mon (d - 1) n) (c : Fin (n + 1) → ℤ) : Mon d n → ℝ :=
  fun m' => (prodVec d n m c m' : ℝ)

/-- The linear functional `F ↦ ∑ m, F m · ν_{d,n}(x) m`, i.e. evaluation of the degree-`d` form
with coefficient vector `F` at the point `x`.  Its kernel is the space of forms vanishing at `x`,
the hyperplane `(ℝ ν_{d,n}(x))^⊥` of `Mon d n → ℝ`. -/
def evalLin (d n : ℕ) (x : Fin (n + 1) → ℤ) : (Mon d n → ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ m : Mon d n, F m * ((veronese d n x m : ℤ) : ℝ)
  map_add' F G := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a F := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring

end Work.HP
