import Mathlib
import Submission.Work.ZeroEst.defs

/-!
# Coefficient of a product of one-variable embeddings

For `g : Fin d → PowerSeries ℚ` the series `∏ s, embedVar s (g s)` is the product of the
`d` series `g s(x_s)`, each of which depends on the single variable `x_s`.  Its `m`-th
coefficient is therefore the product of the one-variable coefficients
`∏ s, coeff (m s) (g s)`: the antidiagonal sum over `MvPowerSeries.coeff_prod` has exactly
one non-vanishing term, because a monomial of `embedVar s (g s)` is supported only at `s`.
-/

namespace Work.ZeroEst

open scoped BigOperators

/-- The `n`-th coefficient of `embedVar s f`: it vanishes unless `n` is a monomial in the
single variable `s`, in which case it is the corresponding coefficient of `f`. -/
theorem coeff_embedVar {d : ℕ} (s : Fin d) (f : PowerSeries ℚ) (n : Fin d →₀ ℕ) :
    MvPowerSeries.coeff n (Submission.CDTPlan.embedVar s f) =
      if n = Finsupp.single s (n s) then PowerSeries.coeff (n s) f else 0 := rfl

theorem coeff_prod_embedVar {d : ℕ} (g : Fin d → PowerSeries ℚ) (m : Fin d →₀ ℕ) :
    MvPowerSeries.coeff m (∏ s, Submission.CDTPlan.embedVar s (g s)) =
      ∏ s, PowerSeries.coeff (m s) (g s) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  -- the only finitely supported family `l` with `∑ l = m` all of whose values `l i` are
  -- supported at `i` is `l i = single i (m i)`
  let l₀ : Fin d →₀ (Fin d →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm (fun i => Finsupp.single i (m i))
  have hl₀ : ∀ i, l₀ i = Finsupp.single i (m i) := by intro i; rfl
  trans ∏ i, (MvPowerSeries.coeff (l₀ i)) (Submission.CDTPlan.embedVar i (g i))
  · refine Finset.sum_eq_single_of_mem (s := Finset.univ.finsuppAntidiag m)
      (f := fun l => ∏ i, (MvPowerSeries.coeff (l i)) (Submission.CDTPlan.embedVar i (g i)))
      l₀ ?_ ?_
    · -- `l₀` does lie in the antidiagonal: `∑ i, single i (m i) = m`
      rw [Finset.mem_finsuppAntidiag]
      exact ⟨by ext j; simp [hl₀], Finset.subset_univ _⟩
    · -- every other summand vanishes
      intro b hb hbne
      obtain ⟨hb1, -⟩ := Finset.mem_finsuppAntidiag.mp hb
      by_cases hall : ∀ i, b i = Finsupp.single i ((b i) i)
      · -- if all the values `b i` are supported at `i`, then `∑ i, b i = m` forces `b = l₀`
        exfalso
        apply hbne
        apply Finsupp.ext
        intro i
        have hzero : ∀ j ∈ (Finset.univ : Finset (Fin d)), j ≠ i → (b j) i = 0 := by
          intro j _ hji
          rw [hall j, Finsupp.single_eq_of_ne (Ne.symm hji)]
        have h1 : (∑ j, b j) i = m i := by rw [hb1]
        rw [Finsupp.finsetSum_apply] at h1
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hzero] at h1
        rw [hl₀ i, hall i, h1]
      · -- otherwise some value `b i` is not supported at `i`, so that factor vanishes
        push Not at hall
        obtain ⟨i, hi⟩ := hall
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [coeff_embedVar]
        simp [hi]
  · -- the surviving summand is `∏ i, coeff (single i (m i)) (embedVar i (g i))`
    apply Finset.prod_congr rfl
    intro i _
    rw [hl₀ i, coeff_embedVar]
    simp

end Work.ZeroEst
