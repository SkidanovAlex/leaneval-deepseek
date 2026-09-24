import Mathlib
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.winMass_le_fejer

/-!
# Basic bounds for the Fejér kernel `fejerK`

`fejerK M₃ x = 1 + 2 ∑_{k=1}^{N-1} (1 - k/N) cos (2π k x)`, `N = fejerN M₃`, is the Fejér
kernel of order `N`.  We record the two fundamental pointwise bounds
`0 ≤ fejerK M₃ x ≤ N`.

The non-negativity is `fejerK_nonneg` (from `winMass_le_fejer`).  For the upper bound we use
the identity (`fejerN_mul_fejerK` + `fejer_Icc_eq_range`)

`N * fejerK M₃ x = (∑_{j<N} cos (2π j x))² + (∑_{j<N} sin (2π j x))²`

together with Cauchy–Schwarz and `cos² + sin² = 1`:
`(∑ cos)² ≤ N ∑ cos²`, `(∑ sin)² ≤ N ∑ sin²`, and `∑ (cos² + sin²) = N`, whence
`N * fejerK M₃ x ≤ N²` and `fejerK M₃ x ≤ N`.
-/

namespace Work.GM.Affine

open Finset

theorem fejerK_basic (M₃ x : ℝ) : 0 ≤ fejerK M₃ x ∧ fejerK M₃ x ≤ (fejerN M₃ : ℝ) := by
  refine ⟨fejerK_nonneg M₃ x, ?_⟩
  have hN1 : 1 ≤ fejerN M₃ := fejerN_pos M₃
  have hNpos : (0 : ℝ) < (fejerN M₃ : ℝ) := by exact_mod_cast hN1
  have hkey : (fejerN M₃ : ℝ) * fejerK M₃ x
      = (∑ j ∈ Finset.range (fejerN M₃), Real.cos (2 * Real.pi * (j : ℝ) * x)) ^ 2
        + (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2 * Real.pi * (j : ℝ) * x)) ^ 2 := by
    rw [fejerN_mul_fejerK M₃ x, fejer_Icc_eq_range (fejerN M₃) hN1 x]
  have hcs : (∑ j ∈ Finset.range (fejerN M₃), Real.cos (2 * Real.pi * (j : ℝ) * x)) ^ 2
      ≤ (fejerN M₃ : ℝ)
        * ∑ j ∈ Finset.range (fejerN M₃), Real.cos (2 * Real.pi * (j : ℝ) * x) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (fejerN M₃))
      (f := fun j : ℕ => Real.cos (2 * Real.pi * (j : ℝ) * x))
    simpa using h
  have hss : (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2 * Real.pi * (j : ℝ) * x)) ^ 2
      ≤ (fejerN M₃ : ℝ)
        * ∑ j ∈ Finset.range (fejerN M₃), Real.sin (2 * Real.pi * (j : ℝ) * x) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (fejerN M₃))
      (f := fun j : ℕ => Real.sin (2 * Real.pi * (j : ℝ) * x))
    simpa using h
  have htrig : (∑ j ∈ Finset.range (fejerN M₃), Real.cos (2 * Real.pi * (j : ℝ) * x) ^ 2)
      + (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2 * Real.pi * (j : ℝ) * x) ^ 2)
      = (fejerN M₃ : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp [Real.cos_sq_add_sin_sq]
  have hbound : (fejerN M₃ : ℝ) * fejerK M₃ x
      ≤ (fejerN M₃ : ℝ) * (fejerN M₃ : ℝ) := by
    rw [hkey]
    nlinarith [hcs, hss, htrig, hNpos.le]
  nlinarith [hbound, hNpos]

end Work.GM.Affine
