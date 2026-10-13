import Mathlib
import Submission.Work.DSG2.ChartRingMain

/-!
# Universe-polymorphic surjectivity of the dehomogenization `Phi`

`Work.DSG2.Phi_surjective` states that `Phi A n i : A[Y₀,…,Y_{n-1}] →+* Away 𝒜 (X i)` is
surjective, but it was proved with `A : Type` fixed to universe `0`.  The definition `Phi`
itself is universe-polymorphic, and we need the surjectivity statement at an arbitrary
universe `A : Type*`.  Here we reproduce the (short) argument of `ChartRingMain.lean`
generically: the only ingredients that were universe-monomorphic are the two computational
lemmas `Away_mk_prod_X` and `Away_mk_mon` (and the auxiliary `val_Phi_prod_X`), which we
re-prove here; everything else (`Away_mk_congr`, `Away_mk_sum`, `Away_mk_C_mul`,
`Away_mk_C`, `prod_X_mem`, `chartGrading_X_mem`) is already polymorphic.
-/

open MvPolynomial HomogeneousLocalization

namespace Work.DSCHART

attribute [local instance] MvPolynomial.gradedAlgebra

section Helpers

/-- `Phi` sends the monomial `∏ k, Yₖ ^ (a k)` to `∏ k, (X_{i.succAbove k}/Xᵢ) ^ (a k)`. -/
theorem Phi_prod_X (A : Type*) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (a : Fin n → ℕ) :
    Work.DSG2.Phi A n i (∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (a k))
      = ∏ k, (Work.DSG2.e A n i k) ^ (a k) := by
  rw [Work.DSG2.Phi]
  simp only [map_prod, map_pow, MvPolynomial.eval₂Hom_X']

/-- The class of `X_{i.succAbove k}/Xᵢ` multiplied by the class of `Xᵢ` is the class of
`X_{i.succAbove k}`. -/
theorem val_e_mul_algebraMap (A : Type*) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (k : Fin n) :
    (Work.DSG2.e A n i k).val *
        algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X i)
      = algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X (i.succAbove k)) := by
  rw [Work.DSG2.e, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply]
  simp only [pow_one]
  rw [IsLocalization.mk'_spec]

/-- The value in `Localization.Away (X i)` of `Phi` applied to the monomial
`∏ k, Yₖ ^ (w (i.succAbove k))`. -/
theorem val_Phi_prod_X (A : Type*) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (w : Fin (n + 1) →₀ ℕ) :
    (Work.DSG2.Phi A n i (∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k)))).val
      = IsLocalization.mk' (M := Submonoid.powers (MvPolynomial.X i))
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
          ⟨(MvPolynomial.X i) ^ (w.degree), by use w.degree⟩ := by
  rw [show (Work.DSG2.Phi A n i (∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k))))
      = ∏ k, (Work.DSG2.e A n i k) ^ (w (i.succAbove k)) from
        Phi_prod_X A n i (fun k => w (i.succAbove k))]
  rw [show (∏ k, (Work.DSG2.e A n i k) ^ (w (i.succAbove k))).val
      = ∏ k, ((Work.DSG2.e A n i k).val) ^ (w (i.succAbove k)) from by
        rw [← HomogeneousLocalization.algebraMap_apply (𝒜 := Work.DSG2.chartGrading A n)
              (x := Submonoid.powers (MvPolynomial.X i)), map_prod]
        simp only [HomogeneousLocalization.algebraMap_apply, map_pow]]
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have hdeg : w.degree = w i + ∑ k : Fin n, w (i.succAbove k) := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succAbove]
  have hA : algebraMap (MvPolynomial (Fin (n + 1)) A)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
        (MvPolynomial.X i ^ w.degree)
      = algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X i) ^ (w i) *
        ∏ k : Fin n, (algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X i)) ^ (w (i.succAbove k)) := by
    rw [map_pow, hdeg, pow_add, ← Finset.prod_pow_eq_pow_sum]
  rw [hA]
  have hB : (∏ k : Fin n, ((Work.DSG2.e A n i k).val) ^ (w (i.succAbove k))) *
        ((algebraMap (MvPolynomial (Fin (n + 1)) A)
            (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
            (MvPolynomial.X i) ^ (w i)) *
          ∏ k : Fin n, (algebraMap (MvPolynomial (Fin (n + 1)) A)
            (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
            (MvPolynomial.X i)) ^ (w (i.succAbove k)))
      = (∏ k : Fin n, (((Work.DSG2.e A n i k).val) *
            (algebraMap (MvPolynomial (Fin (n + 1)) A)
              (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
              (MvPolynomial.X i))) ^ (w (i.succAbove k))) *
        (algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X i) ^ (w i)) := by
    rw [show (∏ k : Fin n, (((Work.DSG2.e A n i k).val) *
            (algebraMap (MvPolynomial (Fin (n + 1)) A)
              (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
              (MvPolynomial.X i))) ^ (w (i.succAbove k)))
        = (∏ k : Fin n, ((Work.DSG2.e A n i k).val) ^ (w (i.succAbove k))) *
          (∏ k : Fin n, (algebraMap (MvPolynomial (Fin (n + 1)) A)
            (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
            (MvPolynomial.X i)) ^ (w (i.succAbove k))) from by
      simp only [mul_pow]
      rw [Finset.prod_mul_distrib]]
    ring
  rw [hB]
  have hC : (∏ k : Fin n, (((Work.DSG2.e A n i k).val) *
            (algebraMap (MvPolynomial (Fin (n + 1)) A)
              (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
              (MvPolynomial.X i))) ^ (w (i.succAbove k)))
      = ∏ k : Fin n, (algebraMap (MvPolynomial (Fin (n + 1)) A)
            (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
            (MvPolynomial.X (i.succAbove k))) ^ (w (i.succAbove k)) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [val_e_mul_algebraMap A n i k]
  rw [hC]
  have hP : (∏ k : Fin n,
          (MvPolynomial.X (i.succAbove k) : MvPolynomial (Fin (n + 1)) A) ^ (w (i.succAbove k))) *
        (MvPolynomial.X i) ^ (w i)
      = (∏ j : Fin (n + 1),
          (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) := by
    rw [mul_comm, ← Fin.prod_univ_succAbove
      (fun j : Fin (n + 1) => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) i]
  simp_rw [← map_pow]
  rw [← map_prod, ← map_mul, hP]

/-- The image in `Away 𝒜 (X i)` of the monomial `∏ k, Yₖ ^ (w (i.succAbove k))` under `Phi`. -/
theorem Away_mk_prod_X (A : Type*) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (m : ℕ) (w : Fin (n + 1) →₀ ℕ) (hm : w.degree = m)
    (h : (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
      ∈ Work.DSG2.chartGrading A n (m • 1)) :
    HomogeneousLocalization.Away.mk (Work.DSG2.chartGrading A n)
        (Work.DSG2.chartGrading_X_mem A n i) m
      (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) h
      = Work.DSG2.Phi A n i
          (∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k))) := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', val_Phi_prod_X A n i w]
  congr 1
  exact Subtype.ext (by rw [hm])

/-- `Away.mk` of a monomial `C c * ∏ j, X j ^ w j` at degree `m = w.degree` is `Phi` of the
corresponding monomial of `A[Y₀,…,Y_{n-1}]`. -/
theorem Away_mk_mon (A : Type*) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (m : ℕ) (w : Fin (n + 1) →₀ ℕ) (c : A) (hm : w.degree = m)
    (hh' : (MvPolynomial.C c * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
      ∈ Work.DSG2.chartGrading A n (m • 1)) :
    HomogeneousLocalization.Away.mk (Work.DSG2.chartGrading A n)
        (Work.DSG2.chartGrading_X_mem A n i) m
        (MvPolynomial.C c * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) hh'
      = Work.DSG2.Phi A n i (MvPolynomial.C c *
          ∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k))) := by
  rw [Work.DSG2.Away_mk_C_mul A n i m c
      (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
      (by rw [← hm]; exact Work.DSG2.prod_X_mem A n w)
      (by simpa using MvPolynomial.isHomogeneous_C A c) hh']
  rw [Work.DSG2.Away_mk_C A n i c (by simpa using MvPolynomial.isHomogeneous_C A c)]
  rw [Away_mk_prod_X A n i m w hm (by rw [← hm]; exact Work.DSG2.prod_X_mem A n w)]
  rw [show Work.DSG2.AtoAway A n i c = Work.DSG2.Phi A n i (MvPolynomial.C c) from by
        rw [Work.DSG2.Phi, MvPolynomial.eval₂Hom_C]]
  rw [map_mul]

end Helpers

/-- The dehomogenization map `Phi A n i` is surjective, in the universe of `A`. -/
theorem Phi_surjective_univ {A : Type*} [CommRing A] (n : ℕ) (i : Fin (n + 1)) :
    Function.Surjective (Work.DSG2.Phi A n i) := by
  intro z
  obtain ⟨m, p, hp, hz⟩ := HomogeneousLocalization.Away.mk_surjective
    (𝒜 := Work.DSG2.chartGrading A n) (Work.DSG2.chartGrading_X_mem A n i) z
  have hp' : p.IsHomogeneous m := by
    have h := hp
    rw [MvPolynomial.mem_homogeneousSubmodule] at h
    simpa using h
  have hdeg : ∀ w ∈ p.support, w.degree = m := fun w hw => by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hw) (MvPolynomial.IsHomogeneous.coeff_eq_zero hp' h)
  have hG : ∀ d : Fin (n + 1) →₀ ℕ, MvPolynomial.C (p.coeff d) *
      ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (d j)
        ∈ Work.DSG2.chartGrading A n (m • 1) := by
    intro d
    by_cases hd : d ∈ p.support
    · rw [← hdeg d hd, Work.DSG2.prod_eq_finsupp_prod, ← MvPolynomial.monomial_eq,
        MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_monomial (p.coeff d) (by simp)
    · rw [show p.coeff d = 0 from by
        by_contra h
        exact hd (MvPolynomial.mem_support_iff.mpr h)]
      simp
  have hdecomp : p = ∑ w ∈ p.support, MvPolynomial.C (p.coeff w) *
      ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j) := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    apply Finset.sum_congr rfl
    intro w _
    rw [MvPolynomial.monomial_eq, ← Work.DSG2.prod_eq_finsupp_prod]
  refine ⟨∑ w ∈ p.support, MvPolynomial.C (p.coeff w) *
      ∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k)), ?_⟩
  rw [← hz]
  have key : HomogeneousLocalization.Away.mk (Work.DSG2.chartGrading A n)
        (Work.DSG2.chartGrading_X_mem A n i) m p hp
      = Work.DSG2.Phi A n i (∑ w ∈ p.support, MvPolynomial.C (p.coeff w) *
          ∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k))) := by
    rw [Work.DSG2.Away_mk_congr A n i m hdecomp hp (by rw [← hdecomp]; exact hp)]
    rw [Work.DSG2.Away_mk_sum A n i m p.support (fun w => MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) hG
        (by rw [← hdecomp]; exact hp)]
    rw [Finset.sum_congr rfl (fun w hw => Away_mk_mon A n i m w (p.coeff w) (hdeg w hw) (hG w))]
    rw [map_sum]
  exact key.symm

end Work.DSCHART
