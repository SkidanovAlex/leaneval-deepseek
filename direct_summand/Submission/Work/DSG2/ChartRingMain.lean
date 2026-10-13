import Mathlib
import Submission.Work.DSG2.Defs
import Submission.Work.DSG2.ChartRingDefs
import Submission.Work.DSG2.ChartRingBasic
import Submission.Work.DSG2.Psi_Phi
import Submission.Work.DSG2.val_Phi_prod_X

/-!
# DSG2: the `i`-th standard chart ring of `ℙⁿ` is a polynomial ring in `n` variables

The `i`-th standard affine chart of `ℙⁿ_A` has coordinate ring
`chartRing A n i = Away 𝒜 (X i)`, the degree-zero part of the localization of
`A[x₀,…,xₙ]` at the powers of `Xᵢ`.  The dehomogenization map
`Phi : A[Y₀,…,Y_{n-1}] →+* Away 𝒜 (X i)`, `Y_k ↦ X_{i.succAbove k}/Xᵢ`, is an isomorphism;
this file proves it by showing `Phi` is bijective (`Psi ∘ Phi = id` from `Psi_Phi.lean`
gives injectivity, and `Phi_surjective` below gives surjectivity) and deduces
`Work.DSG2.nonempty_chartRingEquiv`.
-/

open MvPolynomial HomogeneousLocalization

namespace Work.DSG2

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type) [CommRing A] (n : ℕ) (i : Fin (n + 1))

/-- The image in `Away 𝒜 (X i)` of the monomial `∏ k, Yₖ ^ (w (i.succAbove k))` under `Phi` is the
fraction `(∏ j, X j ^ w j) / (X i) ^ w.degree`, i.e. `Away.mk` of the monomial `∏ j, X j ^ w j`
at degree `w.degree`. -/
theorem Away_mk_prod_X (m : ℕ) (w : Fin (n + 1) →₀ ℕ) (hm : w.degree = m)
    (h : (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
      ∈ chartGrading A n (m • 1)) :
    HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m
      (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) h
      = Phi A n i (∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k))) := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', val_Phi_prod_X A n i w]
  congr 1
  exact Subtype.ext (by rw [hm])

/-- `Away.mk` of a monomial `C c * ∏ j, X j ^ w j` at degree `m = w.degree` is `Phi` of the
corresponding monomial of `A[Y₀,…,Y_{n-1}]`. -/
theorem Away_mk_mon (m : ℕ) (w : Fin (n + 1) →₀ ℕ) (c : A) (hm : w.degree = m)
    (hh' : (MvPolynomial.C c * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
      ∈ chartGrading A n (m • 1)) :
    HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m
        (MvPolynomial.C c * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) hh'
      = Phi A n i (MvPolynomial.C c *
          ∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k))) := by
  rw [Away_mk_C_mul A n i m c (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
      (by rw [← hm]; exact prod_X_mem A n w) (by simpa using MvPolynomial.isHomogeneous_C A c) hh']
  rw [Away_mk_C A n i c (by simpa using MvPolynomial.isHomogeneous_C A c)]
  rw [Away_mk_prod_X A n i m w hm (by rw [← hm]; exact prod_X_mem A n w)]
  rw [show AtoAway A n i c = Phi A n i (MvPolynomial.C c) from by rw [Phi, MvPolynomial.eval₂Hom_C]]
  rw [map_mul]

/-- The dehomogenization map `Phi : A[Y₀,…,Y_{n-1}] →+* Away 𝒜 (X i)` is surjective: every element
of the chart ring is a polynomial in the fractions `X_{i.succAbove k}/Xᵢ`. -/
theorem Phi_surjective : Function.Surjective (Phi A n i) := by
  intro z
  obtain ⟨m, p, hp, hz⟩ := HomogeneousLocalization.Away.mk_surjective (𝒜 := chartGrading A n)
    (chartGrading_X_mem A n i) z
  have hp' : p.IsHomogeneous m := by
    have h := hp
    rw [MvPolynomial.mem_homogeneousSubmodule] at h
    simpa using h
  have hdeg : ∀ w ∈ p.support, w.degree = m := fun w hw => by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hw) (MvPolynomial.IsHomogeneous.coeff_eq_zero hp' h)
  have hG : ∀ d : Fin (n + 1) →₀ ℕ, MvPolynomial.C (p.coeff d) *
      ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (d j)
        ∈ chartGrading A n (m • 1) := by
    intro d
    by_cases hd : d ∈ p.support
    · rw [← hdeg d hd, prod_eq_finsupp_prod, ← MvPolynomial.monomial_eq,
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
    rw [MvPolynomial.monomial_eq, ← prod_eq_finsupp_prod]
  refine ⟨∑ w ∈ p.support, MvPolynomial.C (p.coeff w) *
      ∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k)), ?_⟩
  rw [← hz]
  have key : HomogeneousLocalization.Away.mk (chartGrading A n) (chartGrading_X_mem A n i) m p hp
      = Phi A n i (∑ w ∈ p.support, MvPolynomial.C (p.coeff w) *
          ∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k))) := by
    rw [Away_mk_congr A n i m hdecomp hp (by rw [← hdecomp]; exact hp)]
    rw [Away_mk_sum A n i m p.support (fun w => MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) hG (by rw [← hdecomp]; exact hp)]
    rw [Finset.sum_congr rfl (fun w hw => Away_mk_mon A n i m w (p.coeff w) (hdeg w hw) (hG w))]
    rw [map_sum]
  exact key.symm

end Work.DSG2
