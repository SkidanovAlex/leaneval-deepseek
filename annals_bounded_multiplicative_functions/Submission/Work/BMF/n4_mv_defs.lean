import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.tuple_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N4 mean-value bound: the grouped coefficient sequence

To bound `∫_{-T}^{T} ‖Σ_{p ∈ admP P q} χ(p) p^{it}‖^{2ℓ-2}` one writes the `m = ℓ-1`-th power
of the prime–character sum as a Dirichlet polynomial
`(Σ_p χ(p) p^{it})^m = Σ_n a_n n^{it}` and applies the mean value theorem
`Commons.NumberTheory.DirichletPolynomial.dirichlet_mean_value`.  The coefficients `a_n` are
obtained by grouping the `m`-tuples `v` of admissible primes giving `∏_i v_i = n`.

This file fixes that notation: `mvCoeff P q χ m n = Σ_{v ∈ tup P q m, ∏ v_i = n} ∏_i χ(v_i)`.
No `sorry`.
-/

namespace Work.BMF

open Finset

/-- The coefficient of `n^{it}` in the expansion of `(Σ_{p ∈ admP P q} χ(p) p^{it})^m`:
the sum of `∏ i, χ (v i)` over the `m`-tuples `v` of admissible primes with `∏ i, v i = n`. -/
noncomputable def mvCoeff (P : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) (m : ℕ) : ℕ → ℂ :=
  fun n => ∑ v ∈ (tup P q m).filter (fun v => tprod v = n), ∏ i, χ ((v i : ℕ) : ZMod q)

@[simp] lemma mvCoeff_apply (P : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) (m n : ℕ) :
    mvCoeff P q χ m n =
      ∑ v ∈ (tup P q m).filter (fun v => tprod v = n), ∏ i, χ ((v i : ℕ) : ZMod q) := rfl

end Work.BMF
