import Mathlib
import Submission.Work.DSG4c.ChartPushout.Defs

/-!
# `∏ (X k / X i)^{m k} = (∏ X k^{m k}) / (X i)^{∑ m k}` in the chart `D₊(X i)` of `ℙᴺ_A`

The elements `chartElemAll A N i k = X k / X i` of the `i`-th standard chart of `ℙᴺ_A`
satisfy the expected multiplicative relation: the product of their `m k`-th powers is the
homogeneous fraction `(∏ k, X k^{m k}) / (X i)^{∑ k, m k}`.
-/

namespace Work.DSG4c.ChartPushout

universe u

open HomogeneousLocalization MvPolynomial

/-- The type of homogeneous fractions with equal numerator/denominator degree in the chart
`Away (PGr A N) (X i)`. -/
abbrev ChartND (A : Type u) [CommRing A] (N : ℕ) (i : Fin (N+1)) :=
  HomogeneousLocalization.NumDenSameDeg (DSMap.PGr A N) (Submonoid.powers (MvPolynomial.X i))

section Helpers

variable {A : Type u} [CommRing A] {N : ℕ} {i : Fin (N+1)}

lemma chartND_deg_prod {β : Type*} (s : Finset β) (f : β → ChartND A N i) :
    (∏ b ∈ s, f b).deg = ∑ b ∈ s, (f b).deg := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, HomogeneousLocalization.NumDenSameDeg.deg_mul, ih,
      Finset.sum_insert ha]

lemma chartND_num_prod {β : Type*} (s : Finset β) (f : β → ChartND A N i) :
    ((∏ b ∈ s, f b).num : MvPolynomial (Fin (N+1)) A)
      = ∏ b ∈ s, ((f b).num : MvPolynomial (Fin (N+1)) A) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, HomogeneousLocalization.NumDenSameDeg.num_mul, ih,
      Finset.prod_insert ha]

lemma chartND_den_prod {β : Type*} (s : Finset β) (f : β → ChartND A N i) :
    ((∏ b ∈ s, f b).den : MvPolynomial (Fin (N+1)) A)
      = ∏ b ∈ s, ((f b).den : MvPolynomial (Fin (N+1)) A) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, HomogeneousLocalization.NumDenSameDeg.den_mul, ih,
      Finset.prod_insert ha]

lemma chartND_mk_prod {β : Type*} (s : Finset β) (f : β → ChartND A N i) :
    HomogeneousLocalization.mk (∏ b ∈ s, f b)
      = ∏ b ∈ s, HomogeneousLocalization.mk (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, HomogeneousLocalization.mk_mul, ih, Finset.prod_insert ha]

end Helpers

theorem prod_chartElemAll (A : Type u) [CommRing A] (N : ℕ) (i : Fin (N+1))
    (m : Fin (N+1) → ℕ)
    (hp : (∏ k, MvPolynomial.X k ^ m k) ∈ DSMap.PGr A N ((∑ k, m k) • 1)) :
    ∏ k, (Work.DSG4c.ChartPushout.chartElemAll A N i k) ^ (m k) =
      HomogeneousLocalization.Away.mk (DSMap.PGr A N) (Work.DSG4c.X_mem A N i) (∑ k, m k)
        (∏ k, MvPolynomial.X k ^ m k) hp := by
  let C : Fin (N+1) → ChartND A N i := fun k =>
    ⟨1 • 1, ⟨MvPolynomial.X k, Work.DSG4c.X_mem A N k⟩,
      ⟨MvPolynomial.X i ^ 1, SetLike.pow_mem_graded 1 (Work.DSG4c.X_mem A N i)⟩, ⟨1, rfl⟩⟩
  have hC : ∀ k, chartElemAll A N i k = HomogeneousLocalization.mk (C k) := fun k => rfl
  have hQ : (∏ k, C k ^ m k) =
      (⟨(∑ k, m k) • 1, ⟨∏ k, MvPolynomial.X k ^ m k, hp⟩,
        ⟨MvPolynomial.X i ^ (∑ k, m k),
          SetLike.pow_mem_graded (∑ k, m k) (Work.DSG4c.X_mem A N i)⟩,
        ⟨∑ k, m k, rfl⟩⟩ : ChartND A N i) := by
    refine HomogeneousLocalization.NumDenSameDeg.ext _ ?_ ?_ ?_
    · rw [chartND_deg_prod]
      simp [HomogeneousLocalization.NumDenSameDeg.deg_pow, C]
    · rw [chartND_num_prod]
      simp [HomogeneousLocalization.NumDenSameDeg.num_pow, C]
    · rw [chartND_den_prod]
      simp [HomogeneousLocalization.NumDenSameDeg.den_pow, C, Finset.prod_pow_eq_pow_sum]
  calc ∏ k, (Work.DSG4c.ChartPushout.chartElemAll A N i k) ^ (m k)
      = ∏ k, HomogeneousLocalization.mk (C k ^ m k) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [hC k, ← HomogeneousLocalization.mk_pow]
    _ = HomogeneousLocalization.mk (∏ k, C k ^ m k) :=
        (chartND_mk_prod Finset.univ fun k => C k ^ m k).symm
    _ = HomogeneousLocalization.mk (⟨(∑ k, m k) • 1, ⟨∏ k, MvPolynomial.X k ^ m k, hp⟩,
        ⟨MvPolynomial.X i ^ (∑ k, m k),
          SetLike.pow_mem_graded (∑ k, m k) (Work.DSG4c.X_mem A N i)⟩,
        ⟨∑ k, m k, rfl⟩⟩ : ChartND A N i) := by rw [hQ]
    _ = HomogeneousLocalization.Away.mk (DSMap.PGr A N) (Work.DSG4c.X_mem A N i) (∑ k, m k)
        (∏ k, MvPolynomial.X k ^ m k) hp := rfl

end Work.DSG4c.ChartPushout
