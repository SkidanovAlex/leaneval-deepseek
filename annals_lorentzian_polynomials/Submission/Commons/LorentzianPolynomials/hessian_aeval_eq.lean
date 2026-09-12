import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

open Finsupp Matrix MvPolynomial

set_option autoImplicit false

namespace Commons.LorentzianPolynomials

/-- The set of degree `d` homogeneous polynomials in `n` variables, mirrored here so that
this lemma lives in the commons rather than depending on the challenge definitions. -/
def H (n d : ℕ) : Type := homogeneousSubmodule (Fin n) ℝ d

/-- The Hessian matrix of a degree 2 homogeneous polynomial in `n` variables. -/
noncomputable def H.hessian {n : ℕ} (f : H n 2) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    if i = j then
      2 * f.1.coeff (single i 2)
    else
      f.1.coeff (single i 1 + single j 1)

lemma hessian_aeval_eq_coeff_eq_zero_of_not_weight_two (n : ℕ) (f : H n 2)
    (d : Fin n →₀ ℕ) (hd : Finsupp.weight (1 : Fin n → ℕ) d ≠ 2) :
    f.1.coeff d = 0 := by
  have hh : f.1.IsWeightedHomogeneous (1 : Fin n → ℕ) 2 := by
    simpa [MvPolynomial.IsHomogeneous] using f.2
  exact MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hh d hd

lemma hessian_aeval_eq_pderiv_eq_sum_hessian (n : ℕ) (f : H n 2) (i : Fin n) :
    MvPolynomial.pderiv i f.1 =
      ∑ j : Fin n, MvPolynomial.C (f.hessian i j) * MvPolynomial.X j := by
  classical
  ext m
  rw [MvPolynomial.coeff_pderiv]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  by_cases hm : ∃ j : Fin n, m = Finsupp.single j 1
  · obtain ⟨j, rfl⟩ := hm
    have hsum : (∑ x : Fin n, f.hessian i x *
        if (Finsupp.single x 1) = Finsupp.single j 1 then 1 else 0) = f.hessian i j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb, Finsupp.single_left_inj one_ne_zero]
      · intro hj
        simp at hj
    rw [hsum]
    by_cases hij : i = j
    · subst j
      have hs : (Finsupp.single i (1 : ℕ)) + Finsupp.single i 1 = Finsupp.single i 2 := by
        ext k
        by_cases hik : i = k
        · simp [hik]
        · simp [hik]
      rw [hs]
      simp [H.hessian]
      ring
    · rw [add_comm (Finsupp.single j 1) (Finsupp.single i 1)]
      simp [H.hessian, hij]
  · have hm1 : Finsupp.weight (1 : Fin n → ℕ) m ≠ 1 := by
      intro hw
      apply hm
      rw [Finsupp.weight_apply] at hw
      simp only [Pi.one_apply, smul_eq_mul, mul_one] at hw
      exact (Finsupp.sum_eq_one_iff m).mp hw
    have hsum0 : (∑ x : Fin n, f.hessian i x *
        if (Finsupp.single x 1) = m then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hjm : Finsupp.single j 1 = m
      · exfalso
        apply hm
        exact ⟨j, hjm.symm⟩
      · simp [hjm]
    rw [hsum0]
    have hwadd : Finsupp.weight (1 : Fin n → ℕ) (m + Finsupp.single i 1) =
        Finsupp.weight (1 : Fin n → ℕ) m + 1 := by
      rw [map_add]
      rw [Finsupp.weight_single]
      simp
    have hd : Finsupp.weight (1 : Fin n → ℕ) (m + Finsupp.single i 1) ≠ 2 := by
      intro h
      have hm_eq : Finsupp.weight (1 : Fin n → ℕ) m = 1 := by
        rw [hwadd] at h
        omega
      exact hm1 hm_eq
    have hcoeff := hessian_aeval_eq_coeff_eq_zero_of_not_weight_two n f
      (m + Finsupp.single i 1) hd
    rw [hcoeff]
    simp

theorem hessian_aeval_eq (n : ℕ) (f : H n 2) (z : Fin n → ℂ) :
    2 * MvPolynomial.aeval z f.1 =
      ∑ i : Fin n, ∑ j : Fin n, f.hessian i j * z i * z j := by
  have heuler : (∑ i : Fin n, MvPolynomial.X i * MvPolynomial.pderiv i f.1) =
      (2 : ℕ) • f.1 := by
    have hh : f.1.IsHomogeneous 2 := by exact f.2
    simpa using MvPolynomial.IsHomogeneous.sum_X_mul_pderiv (φ := f.1) hh
  have hae := congrArg (MvPolynomial.aeval z) heuler
  rw [map_sum] at hae
  simp only [map_mul, MvPolynomial.aeval_X] at hae
  have hae_nsmul : MvPolynomial.aeval z ((2 : ℕ) • f.1) =
      (2 : ℕ) • MvPolynomial.aeval z f.1 := by
    exact map_nsmul (MvPolynomial.aeval z) 2 f.1
  rw [hae_nsmul] at hae
  have hrow : ∀ i : Fin n, MvPolynomial.aeval z (MvPolynomial.pderiv i f.1) =
      ∑ j : Fin n, f.hessian i j * z j := by
    intro i
    rw [hessian_aeval_eq_pderiv_eq_sum_hessian n f i]
    simp [map_sum, map_mul, MvPolynomial.aeval_X]
  simp_rw [hrow] at hae
  have hsmul : (2 : ℕ) • MvPolynomial.aeval z f.1 = 2 * MvPolynomial.aeval z f.1 := by
    norm_num [nsmul_eq_mul]
  have hdist : (∑ i : Fin n, z i * ∑ j : Fin n, f.hessian i j * z j) =
      ∑ i : Fin n, ∑ j : Fin n, f.hessian i j * z i * z j := by
    calc
      (∑ i : Fin n, z i * ∑ j : Fin n, f.hessian i j * z j)
          = ∑ i : Fin n, ∑ j : Fin n, z i * (f.hessian i j * z j) := by
            simp [Finset.mul_sum]
      _ = ∑ i : Fin n, ∑ j : Fin n, f.hessian i j * z i * z j := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
  calc
    2 * MvPolynomial.aeval z f.1 = (2 : ℕ) • MvPolynomial.aeval z f.1 := by
      rw [hsmul]
    _ = ∑ i : Fin n, z i * ∑ j : Fin n, f.hessian i j * z j := hae.symm
    _ = ∑ i : Fin n, ∑ j : Fin n, f.hessian i j * z i * z j := hdist

end Commons.LorentzianPolynomials