import Mathlib
import Submission.Commons.Analysis.MvPolynomial.isStable_of_degree_le_one
import Submission.Commons.LorentzianPolynomials.P_subset_M
import Submission.Commons.LorentzianPolynomials.S_closed

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.LorentzianPolynomials

/-- A subset `J ⊆ ℕⁿ` is said to be M-convex, if for any `α, β ∈ J` and any index `i`
satisfying `αᵢ > βᵢ`, there is an index `j` satisfying `αⱼ < βⱼ` and `α - eᵢ + eⱼ ∈ J`. -/
def IsMConvex {n : ℕ} (J : Set (Fin n →₀ ℕ)) : Prop :=
  ∀ α ∈ J, ∀ β ∈ J, ∀ i, α i > β i → ∃ j, α j < β j ∧ α - single i 1 + single j 1 ∈ J

/-- The set of degree `d` homogeneous polynomials with nonnegative coefficients whose
supports are M-convex. -/
abbrev M (n d : ℕ) : Set (H n d) :=
  { f | IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) ∧ ∀ m, 0 ≤ f.1.coeff m }

/-- The set `L n d`, defined recursively as in the paper: `S` in degrees `0,1,2`, and
for larger degrees the M-convex polynomials whose partial derivatives lie in the previous
`L`. -/
def L (n d : ℕ) : Set (H n d) := match d with
  | 0 => S n 0
  | 1 => S n 1
  | 2 => S n 2
  | d + 3 => { f ∈ M n (d + 3) | ∀ i, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n (d + 2) }

lemma P_subset_S_of_degree_le_one (n d : ℕ) (hd : d ≤ 1) : P n d ⊆ S n d := by
  intro f hf
  have hnonneg : ∀ m, 0 ≤ f.1.coeff m := (P_subset_M n d hf).2
  constructor
  · exact Commons.Analysis.MvPolynomial.isStable_of_degree_le_one n d hd f hnonneg
  · exact hnonneg

lemma strict_lorentzian_quadratic_subset_S (n : ℕ) : Ŀ n 2 ⊆ S n 2 := by
  intro f hf
  have hP : f ∈ P n 2 := by
    simp [Ŀ] at hf ⊢
    exact hf.1
  constructor
  · exact strict_lorentzian_quadratic_stable n f hf
  · intro m
    exact (P_subset_M n 2 hP).2 m

theorem strict_subset_L (n d : ℕ) (hn : 0 < n) : Ŀ n d ⊆ L n d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro f hf
      cases d with
      | zero =>
          have hP : f ∈ P n 0 := by simpa [Ŀ] using hf
          have hS : f ∈ S n 0 := P_subset_S_of_degree_le_one n 0 (by norm_num) hP
          simpa [L] using hS
      | succ d =>
          cases d with
          | zero =>
              have hP : f ∈ P n 1 := by simpa [Ŀ] using hf
              have hS : f ∈ S n 1 := P_subset_S_of_degree_le_one n 1 (by norm_num) hP
              simpa [L] using hS
          | succ d =>
              cases d with
              | zero =>
                  have hS : f ∈ S n 2 := strict_lorentzian_quadratic_subset_S n (by simpa [Ŀ] using hf)
                  simpa [L] using hS
              | succ k =>
                  have ihk : Ŀ n (k + 2) ⊆ L n (k + 2) := ih (k + 2) (by omega)
                  have hf' : f ∈ P n (k + 3) ∧
                      ∀ i : Fin n, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ Ŀ n (k + 2) := by
                    simpa [Ŀ] using hf
                  rcases hf' with ⟨hP, hderiv⟩
                  constructor
                  · exact P_subset_M n (k + 3) hP
                  · intro i
                    exact ihk (hderiv i)

end Commons.LorentzianPolynomials
