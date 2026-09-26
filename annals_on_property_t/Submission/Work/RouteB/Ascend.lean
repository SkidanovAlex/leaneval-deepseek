import Submission.Work.RouteB.StarStructure
import Submission.Work.PropertyTCert
import Submission.Work.RouteB.FreeGroupAutDecEq

open OnPropertyT Submission.Helpers Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

namespace Submission.RouteB

noncomputable section

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]

/-- `star` on `ℝ` is the identity, so `star (c • z) = c • star z`. -/
lemma star_real_smul (c : ℝ) (z : A) : star (c • z) = c • star z := by
  rw [StarModule.star_smul]
  simp

/-- **Two-square normal form.**  With `u = (√2)⁻¹•(x+y)`, `v = (√2)⁻¹•(x-y)`
one has `star u * u + star v * v = star x * x + star y * y`. -/
lemma two_sq_normal_form (x y : A) :
    star ((Real.sqrt 2)⁻¹ • (x + y)) * ((Real.sqrt 2)⁻¹ • (x + y))
      + star ((Real.sqrt 2)⁻¹ • (x - y)) * ((Real.sqrt 2)⁻¹ • (x - y))
    = star x * x + star y * y := by
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [star_real_smul, star_real_smul, StarAddMonoid.star_add, _root_.star_sub]
  rw [smul_mul_smul, smul_mul_smul]
  rw [show (star x + star y) * (x + y)
        = star x * x + star x * y + star y * x + star y * y by noncomm_ring,
      show (star x - star y) * (x - y)
        = star x * x - star x * y - star y * x + star y * y by noncomm_ring]
  rw [← smul_add]
  rw [show (star x * x + star x * y + star y * x + star y * y)
        + (star x * x - star x * y - star y * x + star y * y)
      = (2 : ℝ) • (star x * x + star y * y) by
        rw [two_smul ℝ (star x * x + star y * y)]
        abel]
  rw [h2, ← smul_assoc, smul_eq_mul, show (2:ℝ)⁻¹ * (2:ℝ) = 1 by norm_num, one_smul]

/-- The hermitian square of a scaled element: `star (c • z) * (c • z) = (c*c) • (star z * z)`. -/
lemma smul_star_mul_smul (c : ℝ) (z : A) :
    star (c • z) * (c • z) = (c * c) • (star z * z) := by
  rw [star_real_smul, smul_mul_smul]

/-- Scaling a finite sum of hermitian squares by a nonnegative real: for any
`c : ℝ`, `∑_{i ∈ s} star (c • z i) * (c • z i) = (c*c) • ∑_{i ∈ s} star (z i) * z i`. -/
lemma sum_smul_star_mul (c : ℝ) {ι : Type*} (s : Finset ι) (z : ι → A) :
    (∑ i ∈ s, star (c • z i) * (c • z i)) = (c * c) • (∑ i ∈ s, star (z i) * z i) := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => smul_star_mul_smul c (z i))

variable [DecidableEq A]

/-- **Merging a single hermitian square into a finite sum of hermitian squares.**
For any `x : A` and any finite `ξ`, the element `star x * x + ∑_{z ∈ ξ} star z * z`
is again a Finset sum of hermitian squares.  (If `x ∈ ξ` one uses
`star x * x + star x * x = star ((√2)•x) * ((√2)•x)` and recurses on `ξ.erase x`.) -/
lemma merge_sq_finset (ξ : Finset A) :
    ∀ x : A, ∃ ζ : Finset A, star x * x + ∑ z ∈ ξ, star z * z = ∑ z ∈ ζ, star z * z := by
  classical
  induction ξ using Finset.strongInductionOn with
  | _ ξ ih =>
      intro x
      by_cases hx : x ∈ ξ
      · have hsq2 : star ((Real.sqrt 2) • x) * ((Real.sqrt 2) • x) = (2 : ℝ) • (star x * x) := by
          rw [star_real_smul, smul_mul_smul,
            Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        have h2 : star x * x + ∑ z ∈ ξ, star z * z
            = star ((Real.sqrt 2) • x) * ((Real.sqrt 2) • x)
              + ∑ z ∈ ξ.erase x, star z * z := by
          rw [← Finset.sum_erase_add _ _ hx]
          rw [show star x * x + (∑ z ∈ ξ.erase x, star z * z + star x * x)
                = (star x * x + star x * x) + ∑ z ∈ ξ.erase x, star z * z by abel]
          rw [← two_smul ℝ (star x * x), ← hsq2]
        obtain ⟨ζ, hζ⟩ := ih (ξ.erase x) (Finset.erase_ssubset hx) ((Real.sqrt 2) • x)
        exact ⟨ζ, by rw [h2, hζ]⟩
      · exact ⟨insert x ξ, by rw [Finset.sum_insert hx]⟩

/-- **Every finite sum of hermitian squares is a Finset sum of hermitian
squares.**  In particular a certificate `∑_{i∈ι} star (y i) * y i` over any finite
index type can be rewritten as `∑_{x ∈ ξ} star x * x` for a Finset `ξ` (so the
sum may be taken over *distinct* elements, as required by the definition of
`PropertyT`). -/
theorem merge_sq_fintype {ι : Type*} [Fintype ι] (y : ι → A) :
    ∃ ξ : Finset A, (∑ i, star (y i) * y i) = ∑ x ∈ ξ, star x * x := by
  classical
  have h : ∀ s : Finset ι, ∃ ζ : Finset A,
      (∑ i ∈ s, star (y i) * y i) = ∑ x ∈ ζ, star x * x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨∅, by simp⟩
    | insert a t ha ih =>
        obtain ⟨ζ₁, hζ₁⟩ := ih
        obtain ⟨ζ, hζ⟩ := merge_sq_finset ζ₁ (y a)
        exact ⟨ζ, by rw [Finset.sum_insert ha, hζ₁, hζ]⟩
  obtain ⟨ζ, hζ⟩ := h Finset.univ
  exact ⟨ζ, by simpa using hζ⟩

end

end Submission.RouteB
