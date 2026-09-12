import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Submission.Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq

namespace Commons.Algebra.MvPolynomial

theorem finrank_homogeneousSubmodule (n k : ℕ) :
    Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) = (n + k - 1).choose k := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have hfin : Finite {d : Fin n →₀ ℕ | d.degree = k} :=
    (Finsupp.finite_of_degree_eq (σ := Fin n) k).to_subtype
  have hft : Fintype {d : Fin n →₀ ℕ | d.degree = k} := Fintype.ofFinite _
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := ℝ) (S := ℝ)
    ({d : Fin n →₀ ℕ | d.degree = k})).finrank_eq]
  rw [Module.finrank_finsupp_self]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {d : Fin n →₀ ℕ // d.degree = k} = (n + k - 1).choose k
  rw [Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq]
  simp only [Fintype.card_fin]

end Commons.Algebra.MvPolynomial