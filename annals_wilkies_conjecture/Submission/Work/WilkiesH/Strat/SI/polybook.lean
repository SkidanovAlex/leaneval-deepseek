import Mathlib
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Strat.omega_closure_defs
import Submission.Work.WilkiesH.Strat.omega_closure_v2

/-!
# Polynomial bookkeeping for the stratification input

Small, self-contained comparison lemmas used to convert a degree index computed as a sum of
polynomial expressions into a single two-variable polynomial evaluated at `![D + Dv, n + 1]`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat.SI.Book

open WilkiesDesign WilkiesConjecture

/-- Monotonicity of a natural `MvPolynomial` in its variables. -/
theorem mv_nat_eval_mono {b : MvPolynomial (Fin 2) ℕ} {x y : Fin 2 → ℕ}
    (h : ∀ i, x i ≤ y i) : b.eval x ≤ b.eval y := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
  refine Finset.sum_le_sum fun d _ => Nat.mul_le_mul_left _ ?_
  exact Finset.prod_le_prod fun i _ => Nat.pow_le_pow_left (h i) (d i)

/-- Monotonicity of a natural univariate polynomial on `ℕ`. -/
theorem poly_nat_eval_mono {p : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- A univariate natural polynomial, as a two-variable one in the first variable. -/
def univToTwo (q : Polynomial ℕ) : MvPolynomial (Fin 2) ℕ :=
  ∑ i ∈ Finset.range (q.natDegree + 1), MvPolynomial.C (q.coeff i) * MvPolynomial.X 0 ^ i

theorem eval_univToTwo (q : Polynomial ℕ) (m k : ℕ) :
    MvPolynomial.eval ![m, k] (univToTwo q) = q.eval m := by
  rw [Polynomial.eval_eq_sum_range, univToTwo, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow, MvPolynomial.eval_X]
  simp

/-- **Dominating a sum.**  Given a two-variable polynomial `pmr` and a univariate polynomial
`q`, there is a two-variable polynomial `pm` with
`(D + Dv) + pmr(D + Dv, K) + q(D + Dv) ≤ pm(D + Dv, K)` for all `D, Dv, K`. -/
theorem exists_pm_dominate_sum (pmr : MvPolynomial (Fin 2) ℕ) (q : Polynomial ℕ) :
    ∃ pm : MvPolynomial (Fin 2) ℕ, ∀ D Dv K : ℕ,
      (D + Dv) + MvPolynomial.eval ![(D + Dv : ℕ), K] pmr + q.eval (D + Dv)
        ≤ MvPolynomial.eval ![(D + Dv : ℕ), K] pm := by
  refine ⟨MvPolynomial.X 0 + pmr + univToTwo q, fun D Dv K => ?_⟩
  have hX : MvPolynomial.eval ![(D + Dv : ℕ), K] (MvPolynomial.X (0 : Fin 2)) = D + Dv := by
    simp
  rw [MvPolynomial.eval_add, MvPolynomial.eval_add, eval_univToTwo, hX]

/-- **Dominating a doubled sum.**  Variant of `exists_pm_dominate_sum` with two copies of
`D + Dv`, as produced by an intersection of two `Ω`-sets. -/
theorem exists_pm_dominate_sum_two (pmr : MvPolynomial (Fin 2) ℕ) (q : Polynomial ℕ) :
    ∃ pm : MvPolynomial (Fin 2) ℕ, ∀ D Dv K : ℕ,
      2 * (D + Dv) + MvPolynomial.eval ![(D + Dv : ℕ), K] pmr + q.eval (D + Dv)
        ≤ MvPolynomial.eval ![(D + Dv : ℕ), K] pm := by
  obtain ⟨pm, hpm⟩ := exists_pm_dominate_sum pmr q
  refine ⟨MvPolynomial.X 0 + pm, fun D Dv K => ?_⟩
  rw [MvPolynomial.eval_add]
  have hX : MvPolynomial.eval ![(D + Dv : ℕ), K] (MvPolynomial.X (0 : Fin 2)) = D + Dv := by
    simp
  rw [hX]
  have := hpm D Dv K
  omega

/-- The `Ω`-closure of a set is its topological closure (the set produced by
`Work.WilkiesH.Strat.omega_closure_v2`). -/
theorem closureSet_eq_closure {n : ℕ} (W : Set (Fin n → ℝ)) :
    closureSet W = closure W := by
  ext x
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨y, hyW, hy⟩ := h (ε / 2) (by linarith)
    refine ⟨y, hyW, ?_⟩
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq]
    have h1 := hy i
    rw [abs_sub_comm] at h1
    linarith
  · intro h ε hε
    obtain ⟨y, hyW, hy⟩ := h ε hε
    refine ⟨y, hyW, fun i => ?_⟩
    have h1 := (dist_pi_lt_iff hε).mp hy i
    rw [Real.dist_eq] at h1
    rw [abs_sub_comm]
    exact h1

end Work.WilkiesH.Strat.SI.Book
