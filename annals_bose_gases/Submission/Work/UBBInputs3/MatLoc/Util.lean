import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.Util` — elementary algebra of `normSq` and `qform`

Scaling and positivity of the two quadratic quantities appearing in the localisation:
`normSq R φ = Σ_{j∈R} ‖φ j‖²` and `qform A R φ ψ = (Σ_{i,j∈R} conj(φ i) A i j ψ j).re`.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3

/-- `normSq` depends only on the values of `φ` on `R`. -/
theorem normSq_congr {R : Finset ℤ} {φ χ : ℤ → ℂ} (h : ∀ j ∈ R, φ j = χ j) :
    normSq R φ = normSq R χ :=
  Finset.sum_congr rfl (fun j hj => by rw [h j hj])

/-- `qform` depends only on the values of `φ, χ` on `R`. -/
theorem qform_congr {A : ℤ → ℤ → ℂ} {R : Finset ℤ} {φ χ φ' χ' : ℤ → ℂ}
    (h1 : ∀ j ∈ R, φ j = φ' j) (h2 : ∀ j ∈ R, χ j = χ' j) :
    qform A R φ χ = qform A R φ' χ' := by
  unfold qform
  congr 1
  exact Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => by
    rw [h1 i hi, h2 j hj]))

/-- `normSq` of a real multiple. -/
theorem normSq_smul (R : Finset ℤ) (c : ℝ) (φ : ℤ → ℂ) :
    normSq R (fun j => (c : ℂ) * φ j) = c ^ 2 * normSq R φ := by
  unfold normSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- `qform` at a real multiple (both arguments). -/
theorem qform_smul (A : ℤ → ℤ → ℂ) (R : Finset ℤ) (c : ℝ) (φ : ℤ → ℂ) :
    qform A R (fun j => (c : ℂ) * φ j) (fun j => (c : ℂ) * φ j)
      = c ^ 2 * qform A R φ φ := by
  have hc : star ((c : ℂ)) = (c : ℂ) := by simp
  have key : ∀ i j, star ((c : ℂ) * φ i) * A i j * ((c : ℂ) * φ j)
      = ((c ^ 2 : ℝ) : ℂ) * (star (φ i) * A i j * φ j) := by
    intro i j
    rw [star_mul, hc]
    push_cast
    ring
  simp only [qform]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => key i j))]
  rw [show (∑ i ∈ R, ∑ j ∈ R, ((c ^ 2 : ℝ) : ℂ) * (star (φ i) * A i j * φ j))
        = ((c ^ 2 : ℝ) : ℂ) * (∑ i ∈ R, ∑ j ∈ R, star (φ i) * A i j * φ j) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]]
  rw [Complex.re_ofReal_mul]

/-- `normSq` is positive as soon as some value off the zero function is nonzero. -/
theorem normSq_pos_of_ne_zero {R : Finset ℤ} {φ : ℤ → ℂ} (h : ∃ j ∈ R, φ j ≠ 0) :
    0 < normSq R φ := by
  obtain ⟨j, hj, hj0⟩ := h
  unfold normSq
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨j, hj, by positivity⟩

/-- `normSq` vanishes exactly on the functions vanishing on `R`. -/
theorem normSq_eq_zero_iff {R : Finset ℤ} {φ : ℤ → ℂ} :
    normSq R φ = 0 ↔ ∀ j ∈ R, φ j = 0 := by
  constructor
  · intro h j hj
    by_contra hj0
    have := normSq_pos_of_ne_zero (R := R) ⟨j, hj, hj0⟩
    rw [h] at this
    exact lt_irrefl 0 this
  · intro h
    unfold normSq
    exact Finset.sum_eq_zero (fun j hj => by rw [h j hj]; simp)

/-- The zero vector has zero `qform`. -/
theorem qform_zero_right (A : ℤ → ℤ → ℂ) (R : Finset ℤ) (φ : ℤ → ℂ) :
    qform A R φ (fun _ => 0) = 0 := by
  simp [qform]

/-- The zero vector has zero `qform` (both arguments). -/
theorem qform_zero (A : ℤ → ℤ → ℂ) (R : Finset ℤ) :
    qform A R (fun _ => 0) (fun _ => 0) = 0 := by
  simp [qform]


end Work.UBBInputs3
