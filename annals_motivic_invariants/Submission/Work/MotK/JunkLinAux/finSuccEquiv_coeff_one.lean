import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.JunkLinAux

/-- The coefficient of the split-off variable `X₀` in `f` (degree `≤ 1`) equals the constant
polynomial given by the coefficient of `X 0` in `f`.

Route: `MvPolynomial.ext` on the coefficient index `m : Fin n →₀ ℕ`, then
`MvPolynomial.finSuccEquiv_coeff_coeff` and `MvPolynomial.coeff_C`:
`((finSuccEquiv K n f).coeff 1).coeff m = f.coeff (Finsupp.cons 1 m)`, and
`(MvPolynomial.C c).coeff m = if 0 = m then c else 0`.  If `m = 0`, identify `Finsupp.cons 1 0`
with `Finsupp.single 0 1` (Mathlib has `Finsupp.cons_zero_eq_single_zero`).  If `m ≠ 0`, then
`0 < m.sum (fun _ e => e)`, so `∑ i ∈ (Finsupp.cons 1 m).support, (Finsupp.cons 1 m) i = 1 + m.sum
≥ 2 > 1 ≥ f.totalDegree` (`Finsupp.sum_cons`), and
`MvPolynomial.coeff_eq_zero_of_totalDegree_lt` gives the vanishing. -/
lemma finSuccEquiv_coeff_one {K : Type} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.totalDegree ≤ 1) :
    (MvPolynomial.finSuccEquiv K n f).coeff 1
      = MvPolynomial.C (f.coeff (Finsupp.single 0 1)) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_C]
  split_ifs with h0
  · -- `m = 0`: then `Finsupp.cons 1 m = Finsupp.single 0 1`.
    rw [← h0, Finsupp.cons_zero_eq_single_zero]
  · -- `m ≠ 0`: the monomial `Finsupp.cons 1 m` has degree `≥ 2 > totalDegree f`, so the
    -- coefficient of `f` at it vanishes, as does the right-hand side.
    have hm : m ≠ 0 := fun h => h0 h.symm
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    have hsum : (1 : ℕ) < ∑ i ∈ (Finsupp.cons 1 m).support, (Finsupp.cons 1 m) i := by
      have h1 : (∑ i ∈ (Finsupp.cons 1 m).support, (Finsupp.cons 1 m) i)
          = (Finsupp.cons 1 m).sum (fun _ e => e) := rfl
      rw [h1, Finsupp.sum_cons]
      have hpos : 0 < m.sum (fun _ e => e) := by
        rw [Finsupp.sum]
        exact Finset.sum_pos (fun i hi => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
          (Finsupp.support_nonempty_iff.mpr hm)
      omega
    exact lt_of_le_of_lt hf hsum

end Work.MotK.JunkLinAux
