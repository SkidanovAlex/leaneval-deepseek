import Mathlib

namespace Work.Mostow

/-- A real polynomial whose value is the constant `c` on the interval `(0, ε)` is constant. -/
theorem polyEqConstOfEventuallyEq (P : Polynomial ℝ) (c ε : ℝ) (hε : 0 < ε)
    (h : ∀ t ∈ Set.Ioo 0 ε, P.eval t = c) : P = Polynomial.C c := by
  have hinf : (Set.Ioo (0 : ℝ) ε).Infinite := Set.Ioo_infinite hε
  have hsub : Set.Ioo (0 : ℝ) ε ⊆ {x : ℝ | (P - Polynomial.C c).IsRoot x} := by
    intro t ht
    show (P - Polynomial.C c).eval t = 0
    rw [Polynomial.eval_sub, Polynomial.eval_C, h t ht, sub_self]
  have hzero : P - Polynomial.C c = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (hinf.mono hsub)
  exact sub_eq_zero.mp hzero

end Work.Mostow
