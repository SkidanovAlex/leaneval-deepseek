import Mathlib
import Submission.Work.DSG4c.ChartPushout.DefsT

universe u

/-- In a localization, a product of fractions is the fraction of the products. -/
private lemma localization_mk_prod {R : Type*} [CommMonoid R] {S : Submonoid R}
    {ι : Type*} (s : Finset ι) (a : ι → R) (b : ι → S) :
    ∏ i ∈ s, Localization.mk (a i) (b i) =
      Localization.mk (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Finset.prod_empty, Localization.mk_one]
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx, ih,
      Localization.mk_mul]

namespace Work.DSG4c.ChartPushout

theorem prod_chartElemAllT (A A' : Type u) [CommRing A] [CommRing A'] (ψ : A →+* A')
    (N : ℕ) (i : Fin (N+1)) (m : Fin (N+1) → ℕ)
    (hp : (∏ k, MvPolynomial.X k ^ m k) ∈ DSMap.PGr A' N ((∑ k, m k) • 1)) :
    ∏ k, (Work.DSG4c.ChartPushout.chartElemAllT A A' ψ N i k) ^ (m k) =
      HomogeneousLocalization.Away.mk (DSMap.PGr A' N)
        ((Work.DSG4c.coeffExt A A' ψ N).2 (Work.DSG4c.X_mem A N i)) (∑ k, m k)
        (∏ k, MvPolynomial.X k ^ m k) hp := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  simp only [← HomogeneousLocalization.algebraMap_apply, map_prod, map_pow]
  simp only [Work.DSG4c.ChartPushout.chartElemAllT, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow]
  rw [localization_mk_prod]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum, Subtype.ext_iff, SubmonoidClass.coe_pow]
  simp

end Work.DSG4c.ChartPushout
