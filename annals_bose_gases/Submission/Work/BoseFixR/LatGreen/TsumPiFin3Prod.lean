import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Factoring a sum over `Fin 3 → ℤ` into a product of one-dimensional sums

`∑' n : Fin 3 → ℤ, ∏ i, F i (n i) = ∏ i, ∑' m : ℤ, F i m`

for a family of absolutely summable real series `F i`.  The proof reindexes `Fin 3 → ℤ`
along the bijection `(Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ`, `n ↦ (n 0, n 1, n 2)`, and then applies the
product formula for absolutely summable series (`tsum_mul_tsum_of_summable_norm`) twice.
Nonnegativity of `F` is not needed for the identity, but the hypothesis is retained because
the statement is fixed.
-/

namespace Work.BoseFixR.LatGreen

open scoped BigOperators

/-- The bijection `(Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ` sending `n` to `(n 0, n 1, n 2)`. -/
def fin3IntEquivProd : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun k := (k 0, k 1, k 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv := by
    intro k
    funext i
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨a, b, c⟩
    simp

-- The nonnegativity hypothesis `hF` of the statement below is redundant (the identity holds for
-- any absolutely summable family of real series), but it is part of the fixed statement, so it
-- cannot be dropped.
set_option linter.unusedVariables false in
theorem TsumPiFin3Prod {F : Fin 3 → ℤ → ℝ} (hF : ∀ i m, 0 ≤ F i m)
    (hS : ∀ i, Summable fun m : ℤ => F i m) :
    ∑' n : Fin 3 → ℤ, ∏ i, F i (n i) = ∏ i, ∑' m : ℤ, F i m := by
  have hnorm : ∀ i, Summable fun m : ℤ => ‖F i m‖ := fun i => (hS i).norm
  have h01 : Summable fun q : ℤ × ℤ => ‖F 1 q.1 * F 2 q.2‖ :=
    Summable.mul_norm (hnorm 1) (hnorm 2)
  have hinner : (∑' m : ℤ, F 1 m) * (∑' m : ℤ, F 2 m)
      = ∑' q : ℤ × ℤ, F 1 q.1 * F 2 q.2 :=
    tsum_mul_tsum_of_summable_norm (hnorm 1) (hnorm 2)
  have hmain : (∑' m : ℤ, F 0 m) * (∑' q : ℤ × ℤ, F 1 q.1 * F 2 q.2)
      = ∑' p : ℤ × ℤ × ℤ, F 0 p.1 * (F 1 p.2.1 * F 2 p.2.2) :=
    tsum_mul_tsum_of_summable_norm (hnorm 0) h01
  rw [show (∏ i : Fin 3, ∑' m : ℤ, F i m)
      = (∑' m : ℤ, F 0 m) * (∑' m : ℤ, F 1 m) * (∑' m : ℤ, F 2 m) by
    rw [Fin.prod_univ_three]]
  rw [← Equiv.tsum_eq fin3IntEquivProd.symm (fun n : Fin 3 → ℤ => ∏ i : Fin 3, F i (n i))]
  rw [show (∑' p : ℤ × ℤ × ℤ, ∏ i : Fin 3, F i ((fin3IntEquivProd.symm p) i))
      = ∑' p : ℤ × ℤ × ℤ, F 0 p.1 * (F 1 p.2.1 * F 2 p.2.2) by
    apply tsum_congr
    intro p
    obtain ⟨a, b, c⟩ := p
    simp only [fin3IntEquivProd, Equiv.coe_fn_symm_mk]
    rw [Fin.prod_univ_three]
    simp [mul_assoc]]
  rw [← hmain, ← hinner]
  ring

end Work.BoseFixR.LatGreen
