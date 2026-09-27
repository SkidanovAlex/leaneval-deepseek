import Mathlib
import Submission.Work.PL.Defs

namespace Work.PL.Subdiv.Simplex

theorem sum_smul_unique {N : ℕ} {ι : Type*} [Fintype ι] {v : ι → PL.E N} (hv : AffineIndependent ℝ v)
    {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1)
    (h : ∑ i, a i • v i = ∑ i, b i • v i) : a = b := by
  have key :=
    (affineIndependent_iff_eq_of_fintype_affineCombination_eq (k := ℝ) v).1 hv a b ha hb
  apply key
  rw [Finset.affineCombination_eq_linear_combination _ _ _ ha,
    Finset.affineCombination_eq_linear_combination _ _ _ hb]
  exact h

end Work.PL.Subdiv.Simplex
