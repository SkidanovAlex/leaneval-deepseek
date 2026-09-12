import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq

open Finsupp Matrix MvPolynomial UpperHalfPlane

set_option autoImplicit false

namespace Commons.LorentzianPolynomials

/-- The set of degree `d` homogeneous polynomials in `ℝ[w₁,...,wₙ]` whose coefficients
are positive. -/
abbrev P (n d : ℕ) : Set (H n d) :=
  { f | ∀ m : Fin n →₀ ℕ, weight 1 m = d → 0 < f.1.coeff m }

/-- The set of degree `d` strictly Lorentzian polynomials in `ℝ[w₁,...,wₙ]`. -/
noncomputable def Ŀ (n d : ℕ) : Set (H n d) := match d with
  | 0 => P n 0
  | 1 => P n 1
  | 2 => { f ∈ P n 2 | IsUnit f.hessian ∧ (f.hessian.charpoly.roots.filter (0 < ·)).card = 1 }
  | d + 3 => { f ∈ P n (d + 3) | ∀ i, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ Ŀ n (d + 2) }

/-- A polynomial `f` in `ℝ[w₁,...,wₙ]` is stable if it is nonvanishing on
`ℍⁿ` or identically zero, where `ℍ` is the open upper half plane in `ℂ`. -/
def IsStable {n : ℕ} (f : MvPolynomial (Fin n) ℝ) : Prop :=
  f = 0 ∨ ∀ z : Fin n → ℍ, aeval (((↑) : ℍ → ℂ) ∘ z) f ≠ 0

private lemma hessian_isSymm (n : ℕ) (f : H n 2) : f.hessian.IsSymm := by
  classical
  refine Matrix.IsSymm.ext ?_
  intro i j
  unfold H.hessian
  by_cases h : i = j
  · subst h
    simp
  · have hji : j ≠ i := by exact Ne.symm h
    simp [h, hji, add_comm]

private lemma hessian_pos (n : ℕ) (f : H n 2) (hf : f ∈ P n 2) :
    ∀ i j : Fin n, 0 < f.hessian i j := by
  classical
  intro i j
  unfold H.hessian
  by_cases h : i = j
  · subst h
    simp
    have hc : 0 < f.1.coeff (Finsupp.single i 2) := by
      exact hf (Finsupp.single i 2) (by simp [Finsupp.weight_single])
    positivity
  · simp [h]
    have hc : 0 < f.1.coeff (Finsupp.single i 1 + Finsupp.single j 1) := by
      exact hf (Finsupp.single i 1 + Finsupp.single j 1) (by simp [Finsupp.weight_single])
    exact hc

theorem strict_lorentzian_quadratic_stable (n : ℕ) (f : H n 2)
    (hf : f ∈ Ŀ n 2) : IsStable f.1 := by
  classical
  simp [Ŀ] at hf
  rcases hf with ⟨hP, _hUnit, hcard⟩
  have hsymm : f.hessian.IsSymm := hessian_isSymm n f
  have hnonneg : ∀ i j : Fin n, 0 ≤ f.hessian i j := by
    intro i j
    exact le_of_lt (hessian_pos n f hP i j)
  have hroots : (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1 := by
    rw [hcard]
  have hmat := (Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
    f.hessian hsymm hnonneg).mpr hroots
  rw [IsStable]
  right
  intro z
  have hsum_ne : (∑ i : Fin n, ∑ j : Fin n, f.hessian i j * (z i : ℂ) * (z j : ℂ)) ≠ 0 := by
    rcases hmat with hA0 | hsum
    · exfalso
      have hzero : ((0 : Matrix (Fin n) (Fin n) ℝ).charpoly.roots.filter
          (fun r : ℝ => 0 < r)).card = 0 := by
        simp [Matrix.charpoly_zero]
      rw [hA0] at hcard
      rw [hzero] at hcard
      omega
    · exact hsum z
  have hae := hessian_aeval_eq n f (fun i : Fin n => (z i : ℂ))
  have hae_ne : MvPolynomial.aeval (fun i : Fin n => (z i : ℂ)) f.1 ≠ 0 := by
    intro hz
    have hsum0 : (∑ i : Fin n, ∑ j : Fin n, f.hessian i j * (z i : ℂ) * (z j : ℂ)) = 0 := by
      rw [← hae]
      rw [hz]
      simp
    exact hsum_ne hsum0
  simpa [Function.comp_def] using hae_ne

end Commons.LorentzianPolynomials
