import Mathlib
import Submission.Work.Holonomy3.comp_defs

/-!
# The coefficients of a product of one-variable lifts

If `g s : ℂ⟦X⟧` for `s : Fin d` and each `g s` is lifted to the `s`-th
variable of `MvPowerSeries (Fin d) ℂ` by `embedVarC s`, then the product over `s` is the
"separated" series whose `m`-th coefficient is the product of the univariate coefficients
`PowerSeries.coeff (m s) (g s)`.

This is the coefficient computation behind every product of lifts that occurs in the
(pole-)cleared pullback `uPoly P * diagComp Φ (auxSeriesC f Q)` of STEP 3: the factors
`embedVarC s (∏ i, P i s)` are separated, so their product has the coefficientwise product as its
coefficients.

The proof uses `MvPowerSeries.coeff_prod`: the `m`-th coefficient of the product is a sum over
`l ∈ Finset.finsuppAntidiag univ m` of `∏ i, coeff (l i) (embedVarC i (g i))`.  Since `embedVarC i`
only sees the `i`-th coordinate, every summand vanishes unless `l i = single i (l i i)` for all
`i`, and then `m = ∑ i, l i` forces `l i = single i (m i)`; so exactly one summand survives, and
it is `∏ i, PowerSeries.coeff (m i) (g i)`.
-/

namespace Work.Holonomy3

open scoped BigOperators

/-- The lift `embedVarC s f` evaluated at the monomial `single s k` is the univariate coefficient
`PowerSeries.coeff k f`. -/
lemma embedVarC_apply_single {d : ℕ} (s : Fin d) (f : PowerSeries ℂ) (k : ℕ) :
    embedVarC s f (Finsupp.single s k) = PowerSeries.coeff k f := by
  rw [embedVarC, if_pos (by rw [Finsupp.single_eq_same]), Finsupp.single_eq_same]

theorem embedVarC_prod_coeff {d : ℕ} (g : Fin d → PowerSeries ℂ) (m : Fin d →₀ ℕ) :
    MvPowerSeries.coeff m (∏ s : Fin d, embedVarC s (g s)) =
      ∏ s : Fin d, PowerSeries.coeff (m s) (g s) := by
  classical
  -- the unique multi-index whose lifted coefficients can contribute
  set l₀ : Fin d →₀ (Fin d →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm (fun i => Finsupp.single i (m i)) with hl₀def
  have hl₀ : ∀ i, l₀ i = Finsupp.single i (m i) := by
    intro i
    rw [hl₀def]
    exact Finsupp.equivFunOnFinite_symm_apply_apply _ i
  have hsum₀ : (Finset.univ.sum fun i => l₀ i) = m := by
    ext j
    rw [Finset.sum_apply']
    rw [Finset.sum_eq_single j]
    · rw [hl₀ j, Finsupp.single_eq_same]
    · intro i _ hij
      rw [hl₀ i]
      exact Finsupp.single_eq_of_ne hij.symm
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hmem : l₀ ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin d)) m := by
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨hsum₀, Finset.subset_univ _⟩
  rw [MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single l₀]
  · -- the surviving summand
    apply Finset.prod_congr rfl
    intro i _
    rw [hl₀ i]
    exact embedVarC_apply_single i (g i) (m i)
  · -- every other summand vanishes: a nonzero summand forces `l = l₀`
    intro l hl hne
    by_contra hz
    have hsingle : ∀ i, l i = Finsupp.single i ((l i) i) := by
      intro i
      by_contra hc
      exact hz (Finset.prod_eq_zero (Finset.mem_univ i)
        (embedVarC_apply_of_ne (s := i) (f := g i) (n := l i) hc))
    have hsum : (Finset.univ.sum fun i => l i) = m := (Finset.mem_finsuppAntidiag.mp hl).1
    apply hne
    ext j
    rw [hl₀ j]
    have h1 : m j = ∑ i, (l i) j := by
      have h1' : m j = (Finset.univ.sum fun i => l i) j := by rw [hsum]
      rw [h1', Finset.sum_apply']
    have h2 : (∑ i, (l i) j) = (l j) j := by
      conv_lhs =>
        enter [2, i]
        rw [hsingle i]
      rw [Finset.sum_eq_single j]
      · exact Finsupp.single_eq_same
      · intro i _ hij
        exact Finsupp.single_eq_of_ne hij.symm
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hsingle j, h1, h2]
  · intro h
    exact absurd hmem h

end Work.Holonomy3
