import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq

namespace Commons.Algebra.MvPolynomial

theorem finrank_homogeneousSubmodule_eq_choose {k : Type} [Field k] (n d : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin n) k d) = (n + d - 1).choose d := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have hfin : Finite {e : Fin n →₀ ℕ | e.degree = d} :=
    (Finsupp.finite_of_degree_eq (σ := Fin n) d).to_subtype
  have hft : Fintype {e : Fin n →₀ ℕ | e.degree = d} := Fintype.ofFinite _
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
    ({e : Fin n →₀ ℕ | e.degree = d})).finrank_eq]
  rw [Module.finrank_finsupp_self]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {e : Fin n →₀ ℕ // e.degree = d} = (n + d - 1).choose d
  rw [Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq]
  simp only [Fintype.card_fin]

end Commons.Algebra.MvPolynomial