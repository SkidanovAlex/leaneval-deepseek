import Mathlib
import Submission.Work.Q44Geom.homogeneousComponent_mul_of_minDeg_gen
import Submission.Work.Q44Geom.list_prod_isHomogeneous
import Submission.Work.Q44Geom.isHomogeneous_of_isUnit

/-!
# Graded structure of multivariate polynomial rings

Auxiliary material for `Work.Q44Geom.factorizationHomogeneous`: over a domain, a product of
nonzero polynomials is homogeneous only if both factors are homogeneous, with degrees adding up.
From this it follows that every irreducible factor of a homogeneous polynomial is homogeneous
(a graded unique factorization domain has homogeneous irreducible elements), and that the degrees
of the irreducible factors of a homogeneous polynomial of degree `d` sum to `d`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

namespace Work.Q44Geom.Fac

variable {σ : Type*} {R : Type*}

/-- The minimal degree of a monomial occurring in a nonzero polynomial: the witness and the
minimality statement. -/
lemma exists_min_deg [CommSemiring R] (P : MvPolynomial σ R) (hP : P ≠ 0) :
    ∃ r, (∃ t ∈ P.support, Finsupp.degree t = r) ∧
      (∀ t ∈ P.support, r ≤ Finsupp.degree t) := by
  have hne : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hP (MvPolynomial.support_eq_empty.mp h)
  refine ⟨(P.support.image fun t : σ →₀ ℕ => Finsupp.degree t).min' (hne.image _), ?_, ?_⟩
  · obtain ⟨t, ht, hts⟩ :=
      Finset.mem_image.mp (Finset.min'_mem (P.support.image fun t : σ →₀ ℕ => Finsupp.degree t)
        (hne.image _))
    exact ⟨t, ht, hts⟩
  · intro t ht
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

/-- The degree of a monomial of the support is at most the total degree. -/
lemma degree_le_totalDegree [CommSemiring R] {P : MvPolynomial σ R} {t : σ →₀ ℕ}
    (ht : t ∈ P.support) : Finsupp.degree t ≤ P.totalDegree :=
  MvPolynomial.le_totalDegree ht

/-- Over a domain, if a product `A * B` of nonzero polynomials is homogeneous of degree `n`,
then both factors are homogeneous, with degrees adding up to `n`. -/
theorem isHomogeneous_of_mul_eq [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {n : ℕ} {P A B : MvPolynomial σ R} (hP : P.IsHomogeneous n) (hAB : P = A * B)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ i j : ℕ, i + j = n ∧ A.IsHomogeneous i ∧ B.IsHomogeneous j := by
  classical
  obtain ⟨r, ⟨hr1, hr2⟩⟩ := exists_min_deg A hA
  obtain ⟨s, ⟨hs1, hs2⟩⟩ := exists_min_deg B hB
  have hPne : P ≠ 0 := by rw [hAB]; exact mul_ne_zero hA hB
  have hcompA : MvPolynomial.homogeneousComponent r A ≠ 0 := by
    obtain ⟨t, ht, htr⟩ := hr1
    intro h0
    have h1 : (MvPolynomial.homogeneousComponent r A).coeff t = 0 := by rw [h0]; simp
    rw [MvPolynomial.coeff_homogeneousComponent, ite_eq_left htr] at h1
    exact (MvPolynomial.mem_support_iff.mp ht) h1
  have hcompB : MvPolynomial.homogeneousComponent s B ≠ 0 := by
    obtain ⟨t, ht, hts⟩ := hs1
    intro h0
    have h1 : (MvPolynomial.homogeneousComponent s B).coeff t = 0 := by rw [h0]; simp
    rw [MvPolynomial.coeff_homogeneousComponent, ite_eq_left hts] at h1
    exact (MvPolynomial.mem_support_iff.mp ht) h1
  have hrs : r + s = n := by
    by_contra hne
    have h1 : MvPolynomial.homogeneousComponent (r + s) (A * B) ≠ 0 := by
      rw [Work.Q44Geom.homogeneousComponent_mul_of_minDeg_gen hr1 hr2 hs1 hs2]
      exact mul_ne_zero hcompA hcompB
    have h2 : MvPolynomial.homogeneousComponent (r + s) (A * B) = 0 := by
      rw [← hAB, MvPolynomial.homogeneousComponent_of_mem hP, if_neg hne]
    exact h1 h2
  have hβδ : A.totalDegree + B.totalDegree = n := by
    rw [← MvPolynomial.totalDegree_mul_of_isDomain hA hB, ← hAB]
    exact hP.totalDegree hPne
  have hrβ : r ≤ A.totalDegree := by
    obtain ⟨t, ht, htr⟩ := hr1
    rw [← htr]
    exact degree_le_totalDegree ht
  have hsδ : s ≤ B.totalDegree := by
    obtain ⟨t, ht, hts⟩ := hs1
    rw [← hts]
    exact degree_le_totalDegree ht
  have hr : r = A.totalDegree := by omega
  have hs : s = B.totalDegree := by omega
  have hAr : A.IsHomogeneous r := by
    have heq : A = MvPolynomial.homogeneousComponent r A := by
      ext t
      rw [MvPolynomial.coeff_homogeneousComponent]
      by_cases ht : A.coeff t = 0
      · simp [ht]
      · have htmem : t ∈ A.support := MvPolynomial.mem_support_iff.mpr ht
        have h1 : r ≤ Finsupp.degree t := hr2 t htmem
        have h2 : Finsupp.degree t ≤ A.totalDegree := degree_le_totalDegree htmem
        rw [ite_eq_left (by omega)]
    rw [heq]
    exact MvPolynomial.homogeneousComponent_isHomogeneous r A
  have hBs : B.IsHomogeneous s := by
    have heq : B = MvPolynomial.homogeneousComponent s B := by
      ext t
      rw [MvPolynomial.coeff_homogeneousComponent]
      by_cases ht : B.coeff t = 0
      · simp [ht]
      · have htmem : t ∈ B.support := MvPolynomial.mem_support_iff.mpr ht
        have h1 : s ≤ Finsupp.degree t := hs2 t htmem
        have h2 : Finsupp.degree t ≤ B.totalDegree := degree_le_totalDegree htmem
        rw [ite_eq_left (by omega)]
    rw [heq]
    exact MvPolynomial.homogeneousComponent_isHomogeneous s B
  exact ⟨r, s, hrs, hAr, hBs⟩

/-- A product of nonzero elements of a domain is nonzero. -/
lemma list_prod_ne_zero [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {l : List (MvPolynomial σ R)} (h : ∀ p ∈ l, p ≠ 0) : l.prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    exact mul_ne_zero (h a (by simp)) (ih (fun q hq => h q (by simp [hq])))

/-- Every element of a list whose product is homogeneous is itself homogeneous (of its own total
degree), provided the elements are nonzero. -/
theorem list_factor_isHomogeneous [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {l : List (MvPolynomial σ R)} (h0 : ∀ p ∈ l, p ≠ 0) :
    ∀ {n : ℕ}, l.prod.IsHomogeneous n → ∀ p ∈ l, p.IsHomogeneous p.totalDegree := by
  induction l with
  | nil => intro n _ p hp; simp at hp
  | cons a t ih =>
    intro n h p hp
    have ha : a ≠ 0 := h0 a (by simp)
    have ht0 : ∀ q ∈ t, q ≠ 0 := fun q hq => h0 q (by simp [hq])
    have htprod : t.prod ≠ 0 := list_prod_ne_zero ht0
    rw [List.prod_cons] at h
    obtain ⟨i, j, hij, hai, htj⟩ := isHomogeneous_of_mul_eq h rfl ha htprod
    rcases List.mem_cons.mp hp with heq | hp
    · have htd : a.totalDegree = i := MvPolynomial.IsHomogeneous.totalDegree hai ha
      rw [heq, htd]
      exact hai
    · exact ih ht0 htj p hp

/-- A nonzero homogeneous polynomial of degree `0` is a unit (it is a nonzero constant). -/
lemma isUnit_of_isHomogeneous_zero [Field R] {P : MvPolynomial σ R}
    (h : P.IsHomogeneous 0) (hP : P ≠ 0) : IsUnit P := by
  have hC : P = MvPolynomial.C (P.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous σ).mpr h)
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨P.coeff 0, ?_, hC⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  exact hP (by rw [hC, h0, MvPolynomial.C_0])

end Work.Q44Geom.Fac
