import Mathlib.Analysis.Polynomial.MahlerMeasure

namespace Commons.Analysis.Polynomial

/-- The Mahler measure is multiplicative over finite products of complex polynomials. -/
lemma mahlerMeasure_finset_prod {α : Type*} (s : Finset α) (f : α → Polynomial ℂ) :
    (s.prod f).mahlerMeasure = s.prod (fun i => (f i).mahlerMeasure) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.mahlerMeasure_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.mahlerMeasure_mul, ih]

theorem mahlerMeasure_prod {ι : Type*} [Fintype ι] (P : ι → Polynomial ℂ) :
    (∏ i, P i).mahlerMeasure = ∏ i, (P i).mahlerMeasure := by
  exact mahlerMeasure_finset_prod Finset.univ P

end Commons.Analysis.Polynomial