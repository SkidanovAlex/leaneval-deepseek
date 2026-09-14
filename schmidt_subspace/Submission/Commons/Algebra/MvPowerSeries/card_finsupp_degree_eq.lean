import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Sym.NatCard

/-!
# The number of monomials of a given total degree

The monomials of total degree `m` in `n = Fintype.card σ` variables correspond to the
multisets of size `m` drawn from `σ` (a monomial `∏ xᵢ ^ dᵢ` is determined by the multiset
in which `xᵢ` occurs `dᵢ` times).  This file makes that bijection explicit, giving the
stars-and-bars count `(n + m - 1).choose m`.
-/

namespace Commons.Algebra.MvPowerSeries

/-- A finitely supported function `d : σ →₀ ℕ` has finsupp-sum with `id` equal to its
`Finsupp.degree` (both are the sum of the values over the support). -/
lemma finsupp_sum_id_eq_degree {σ : Type*} (d : σ →₀ ℕ) : d.sum (fun _ ↦ id) = d.degree := rfl

/-- The number of monomials of total degree exactly `m` in `Fintype.card σ` variables is
`(Fintype.card σ + m - 1).choose m`. -/
theorem card_finsupp_degree_eq (σ : Type*) [Fintype σ] [DecidableEq σ] (m : ℕ) :
    Nat.card {d : σ →₀ ℕ // d.degree = m} = (Fintype.card σ + m - 1).choose m := by
  -- `Sym σ m` is the type of multisets of size `m` over `σ`; `Sym.equivNatSum` identifies
  -- it with finitely supported maps `σ →₀ ℕ` of total mass `m`, and for `ℕ`-valued maps
  -- the total mass is the degree.
  have hdeg : ∀ d : σ →₀ ℕ, d.sum (fun _ ↦ id) = d.degree := fun d => rfl
  rw [← Nat.card_eq_fintype_card, ← Sym.natCard_sym_eq_choose σ m]
  refine Nat.card_congr (Equiv.symm ?_)
  exact (Sym.equivNatSum σ m).trans
    (Equiv.subtypeEquivRight (fun d => by rw [hdeg d]))

end Commons.Algebra.MvPowerSeries