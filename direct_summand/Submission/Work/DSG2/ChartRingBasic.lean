import Mathlib
import Submission.Work.DSG2.Defs
import Submission.Work.DSG2.ChartRingDefs

/-!
# DSG2: arithmetic of the chart ring `Away 𝒜 (X i)`

This file collects the elementary computations on `Away 𝒜 (X i)` (where `𝒜` is the degree
grading on `A[x₀,…,xₙ]`) that are used to show that the dehomogenization map
`Phi : A[Y₀,…,Y_{n-1}] →+* Away 𝒜 (X i)` is surjective.

The main point is that `Away.mk` behaves additively/multiplicatively on numerators of the
same (suitable) degree; each identity is proved by passing to the underlying localization
via `HomogeneousLocalization.val_injective`.
-/

open MvPolynomial HomogeneousLocalization

universe u

namespace Work.DSG2

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1))

/-- `Away.mk` is additive in the numerator, for a fixed degree. -/
theorem Away_mk_add (m : ℕ) (x y : MvPolynomial (Fin (n + 1)) A)
    (hx : x ∈ chartGrading A n (m • 1)) (hy : y ∈ chartGrading A n (m • 1))
    (hxy : x + y ∈ chartGrading A n (m • 1)) :
    HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m x hx
      + HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m y hy
      = HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m (x+y) hxy := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  rw [HomogeneousLocalization.val_add, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  exact Localization.add_mk_self x ⟨(MvPolynomial.X i)^m, by use m⟩ y

/-- `Away.mk` at degree `0` of a constant polynomial is the induced map `AtoAway`. -/
theorem Away_mk_C (c : A) (h : (MvPolynomial.C c) ∈ chartGrading A n (0 • 1)) :
    HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) 0 (MvPolynomial.C c) h
      = AtoAway A n i c := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  rw [HomogeneousLocalization.Away.val_mk, val_AtoAway]
  rw [Localization.mk_eq_mk']
  rw [show (⟨(MvPolynomial.X i)^0, by use 0⟩ : Submonoid.powers (MvPolynomial.X i)) = 1 from
    Subtype.ext (pow_zero _)]
  rw [IsLocalization.mk'_one]

/-- `Away.mk` depends on the numerator only. -/
theorem Away_mk_congr (m : ℕ) {x y : MvPolynomial (Fin (n + 1)) A} (hxy : x = y)
    (hx : x ∈ chartGrading A n (m • 1)) (hy : y ∈ chartGrading A n (m • 1)) :
    HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m x hx
      = HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m y hy := by
  subst hxy
  exact congrArg (fun h => HomogeneousLocalization.Away.mk (chartGrading A n)
    (chartGrading_X_mem A n i) m x h) (Subsingleton.elim _ _)

/-- The full product of the variables with exponents `w` equals the `Finsupp`-product. -/
theorem prod_eq_finsupp_prod (w : Fin (n + 1) →₀ ℕ) :
    (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
      = w.prod (fun j e => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ e) := by
  rw [Finsupp.prod]
  exact (Finset.prod_subset (Finset.subset_univ _) (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, pow_zero])).symm

/-- The monomial `∏ j, X_j ^ (w j)` is homogeneous of degree `w.degree`. -/
theorem prod_X_mem (w : Fin (n + 1) →₀ ℕ) :
    (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
      ∈ chartGrading A n (w.degree • 1) := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have h1 : (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)).IsHomogeneous
      (∑ j, w j) := by
    apply MvPolynomial.IsHomogeneous.prod
    intro j _
    simpa using (MvPolynomial.isHomogeneous_X A j).pow (w j)
  simpa [Finsupp.degree_eq_sum, MvPolynomial.mem_homogeneousSubmodule] using h1

/-- `IsLocalization.mk'` is additive in the numerator, for a fixed denominator. -/
theorem mk'_add_same (m : ℕ) (x y : MvPolynomial (Fin (n + 1)) A) :
    IsLocalization.mk' (M := Submonoid.powers (MvPolynomial.X i))
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A)) (x+y)
        ⟨(MvPolynomial.X i)^m, by use m⟩
      = IsLocalization.mk' (M := Submonoid.powers (MvPolynomial.X i))
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A)) x
          ⟨(MvPolynomial.X i)^m, by use m⟩
      + IsLocalization.mk' (M := Submonoid.powers (MvPolynomial.X i))
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A)) y
          ⟨(MvPolynomial.X i)^m, by use m⟩ := by
  rw [← Localization.mk_eq_mk']
  exact (Localization.add_mk_self x ⟨(MvPolynomial.X i)^m, by use m⟩ y).symm

/-- The `Finset` form of `mk'_add_same`. -/
theorem mk'_sum_same (m : ℕ) (s : Finset (Fin (n + 1) →₀ ℕ))
    (g : (Fin (n + 1) →₀ ℕ) → MvPolynomial (Fin (n + 1)) A) :
    IsLocalization.mk' (M := Submonoid.powers (MvPolynomial.X i))
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
        (∑ d ∈ s, g d) ⟨(MvPolynomial.X i)^m, by use m⟩
      = ∑ d ∈ s, IsLocalization.mk' (M := Submonoid.powers (MvPolynomial.X i))
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A)) (g d)
          ⟨(MvPolynomial.X i)^m, by use m⟩ := by
  induction s using Finset.induction_on with
  | empty => simp [Finset.sum_empty]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mk'_add_same, ih]

/-- `Away.mk` is additive over a finite sum of numerators of a fixed degree. -/
theorem Away_mk_sum (m : ℕ) (s : Finset (Fin (n + 1) →₀ ℕ))
    (g : (Fin (n + 1) →₀ ℕ) → MvPolynomial (Fin (n + 1)) A)
    (hg : ∀ d, g d ∈ chartGrading A n (m • 1))
    (hsum : (∑ d ∈ s, g d) ∈ chartGrading A n (m • 1)) :
    HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m
        (∑ d ∈ s, g d) hsum
      = ∑ d ∈ s, HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m
          (g d) (hg d) := by
  have h1 : (∑ d ∈ s, HomogeneousLocalization.Away.mk (chartGrading A n)
        (chartGrading_X_mem A n i) m (g d) (hg d)).val
      = ∑ d ∈ s, Localization.mk (g d) ⟨(MvPolynomial.X i)^m, by use m⟩ := by
    rw [← HomogeneousLocalization.algebraMap_apply (𝒜 := chartGrading A n)
      (x := Submonoid.powers (MvPolynomial.X i)), map_sum]
    simp only [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  rw [HomogeneousLocalization.Away.val_mk, h1]
  rw [Localization.mk_eq_mk']
  exact mk'_sum_same A n i m s g

/-- A constant multiple of a numerator: `Away.mk` interacts with `C c *` as `AtoAway c *`. -/
theorem Away_mk_C_mul (m : ℕ) (c : A) (p : MvPolynomial (Fin (n + 1)) A)
    (hp : p ∈ chartGrading A n (m • 1))
    (hx : (MvPolynomial.C c) ∈ chartGrading A n (0 • 1))
    (h : MvPolynomial.C c * p ∈ chartGrading A n (m • 1)) :
    HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m
        (MvPolynomial.C c * p) h
      = HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) 0
          (MvPolynomial.C c) hx
        * HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m p hp := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul]
  congr 1
  exact Subtype.ext (by simp)

end Work.DSG2
