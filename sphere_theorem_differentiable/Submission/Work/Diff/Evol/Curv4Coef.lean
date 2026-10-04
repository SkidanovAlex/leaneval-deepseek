import Mathlib
import Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Coordinates of a continuous linear functional on curvature arrays

`Curv4 n = Fin n → Fin n → Fin n → Fin n → ℝ` is a finite-dimensional vector space; the coordinate
functionals `X ↦ X i j k l` (evaluated on the array which is `1` at `(i,j,k,l)` and `0` elsewhere)
form a basis of its dual.  `coef ℓ i j k l` is the value of `ℓ` on that basis array, so that

`ℓ X = ∑ i, ∑ j, ∑ k, ∑ l, coef ℓ i j k l * X i j k l`

(`ell_eq_sum_coef`).  This is the tool that turns a statement about an arbitrary linear functional
`ℓ` on curvature components into a finite sum of statements about the components.
-/

namespace Work.Diff.Evol

open Submission.Diff.Alg

/-- The basis array with a `1` in position `(i,j,k,l)` and `0` elsewhere. -/
noncomputable def basisArr {n : ℕ} (i j k l : Fin n) : Curv4 n :=
  fun i' j' k' l' =>
    (if i' = i then (1 : ℝ) else 0) * (if j' = j then (1 : ℝ) else 0) *
      (if k' = k then (1 : ℝ) else 0) * (if l' = l then (1 : ℝ) else 0)

/-- Coordinates of a continuous linear functional on the curvature arrays: its values on the basis
arrays. -/
noncomputable def coef {n : ℕ} (ℓ : Curv4 n →L[ℝ] ℝ) : Fin n → Fin n → Fin n → Fin n → ℝ :=
  fun i j k l => ℓ (basisArr i j k l)

/-- Unfolding of `coef`. -/
theorem coef_apply {n : ℕ} (ℓ : Curv4 n →L[ℝ] ℝ) (i j k l : Fin n) :
    coef ℓ i j k l = ℓ (basisArr i j k l) := rfl

/-- **Decomposition in the basis arrays**: every curvature array is the sum of its coordinates times
the basis arrays. -/
theorem sum_smul_basisArr {n : ℕ} (X : Curv4 n) :
    (∑ i, ∑ j, ∑ k, ∑ l, X i j k l • basisArr i j k l : Curv4 n) = X := by
  funext i' j' k' l'
  simp only [Finset.sum_apply, Pi.smul_apply, basisArr, smul_eq_mul]
  rw [Finset.sum_eq_single i']
  · rw [Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single k']
      · rw [Finset.sum_eq_single l']
        · simp
        · intro l _ hl; simp [hl.symm]
        · intro h; exact absurd (Finset.mem_univ l') h
      · intro k _ hk; simp [hk.symm]
      · intro h; exact absurd (Finset.mem_univ k') h
    · intro j _ hj; simp [hj.symm]
    · intro h; exact absurd (Finset.mem_univ j') h
  · intro i _ hi; simp [hi.symm]
  · intro h; exact absurd (Finset.mem_univ i') h

/-- A continuous linear functional on the curvature arrays is the sum of its coordinate
functionals. -/
theorem ell_eq_sum_coef {n : ℕ} (ℓ : Curv4 n →L[ℝ] ℝ) (X : Curv4 n) :
    ℓ X = ∑ i, ∑ j, ∑ k, ∑ l, coef ℓ i j k l * X i j k l := by
  conv_lhs => rw [← sum_smul_basisArr X]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [coef_apply]
  ring

end Work.Diff.Evol
