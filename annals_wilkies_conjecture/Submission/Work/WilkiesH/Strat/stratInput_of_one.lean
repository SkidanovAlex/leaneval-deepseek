import Mathlib
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Mfd.Defs
import Submission.Work.WilG5.Basic

/-!
# Area H — the two forms of the stratification input, and the bridge between them

`Work.WilkiesH.StratInput` (`Strat/Defs.lean`) asks for a *family* `(W j)_{j : Fin m}` of
`Ω`-sets covering `(X ∩ V) \ X.alg`, with `m` bounded by a polynomial in `(D + D_v, n + 1)`
and the degree index given by a *univariate* polynomial `c.eval (D + D_v)`.

The single-piece form (`Work.WilkiesH.Strat.strat_input_one`,
`Strat/strat_input_one.lean`) asks instead for a single `Ω`-set `W`, whose format and degree
index are controlled by a two-variable polynomial `pm.eval ![D + D_v, n + 1]`.

The two are equivalent, and this file records the direction used at the top level: a single
`W` gives `StratInput` by taking `m = 1`.  The only bookkeeping is the conversion of the
two-variable degree index into a univariate one, which is
`Work.WilkiesH.Strat.exists_poly_eval_le`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture

/-- A two-variable natural polynomial evaluated at `![D, n]` is bounded by a univariate
natural polynomial in `D` (whose coefficients absorb the value of `n`).  This is the
conversion used to turn the degree index `pm.eval ![D + D_v, n + 1]` of
`Work.WilkiesH.Strat.strat_input_one` into the univariate index `c.eval (D + D_v)` of
`Work.WilkiesH.StratInput`. -/
theorem exists_poly_eval_le (pm : MvPolynomial (Fin 2) ℕ) (n : ℕ) :
    ∃ c : Polynomial ℕ, ∀ D : ℕ, MvPolynomial.eval ![D, n] pm ≤ c.eval D := by
  classical
  refine ⟨∑ m ∈ pm.support,
    Polynomial.C (pm.coeff m * n ^ (m 1)) * Polynomial.X ^ (m 0), fun D => ?_⟩
  have hpoly : (∑ m ∈ pm.support,
      Polynomial.C (pm.coeff m * n ^ (m 1)) * Polynomial.X ^ (m 0)).eval D
      = ∑ m ∈ pm.support, (pm.coeff m * n ^ (m 1)) * D ^ (m 0) := by
    rw [Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun m _ => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hmv : MvPolynomial.eval ![D, n] pm
      = ∑ m ∈ pm.support, pm.coeff m * D ^ (m 0) * n ^ (m 1) := by
    rw [MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hpoly, hmv]
  exact Finset.sum_le_sum fun m _ => le_of_eq (by ring)

/-- **The bridge**: the single-piece stratification input implies the family form
`Work.WilkiesH.StratInput`. -/
theorem stratInput_of_one {S : SOMin}
    (h : ∀ F n : ℕ, ∃ (a : ℕ) (pm : MvPolynomial (Fin 2) ℕ),
      ∀ (μ D Dv : ℕ) (X V : Set (Fin n → ℝ)),
        X ∈ S.Ω F D n → V ∈ S.Ω F Dv n → IsSemialgebraic V → DimLE V μ →
        ∃ W : Set (Fin n → ℝ),
          W ∈ S.Ω a (MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm) n ∧ W ⊆ X ∧
          DimLE W (μ - 1) ∧ ((X ∩ V) \ X.alg) ⊆ W) : StratInput S := by
  intro F n
  obtain ⟨a, pm, h'⟩ := h F n
  obtain ⟨c, hc⟩ := exists_poly_eval_le pm (n + 1)
  refine ⟨a, pm + 1, c, ?_⟩
  intro μ D Dv X V hX hV hVsem hVdim
  obtain ⟨W, hWΩ, hWX, hWdim, hWcov⟩ := h' μ D Dv X V hX hV hVsem hVdim
  have hcount : (1 : ℕ) ≤ MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] (pm + 1) := by
    have : MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] (pm + 1)
        = MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm + 1 := by
      rw [map_add, map_one]
    rw [this]; omega
  refine ⟨1, fun _ => W, hcount, ?_, ?_, ?_, ?_⟩
  · intro j
    exact Work.WilG5.mem_mono hWΩ a (c.eval (D + Dv)) (le_refl a) (hc (D + Dv))
  · intro j; exact hWdim
  · intro j; exact hWX
  · have hU : (⋃ _j : Fin 1, W) = W := Set.iUnion_const W
    rw [hU]; exact hWcov

end Work.WilkiesH.Strat
