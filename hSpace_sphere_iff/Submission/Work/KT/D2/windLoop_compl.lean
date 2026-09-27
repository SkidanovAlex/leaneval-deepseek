import Mathlib
import Submission.Work.KT.D2.mZero
import Submission.Work.KT.D2.windLoop_mul

/-!
# `Work.KT.D2.windLoop_compl` — additivity of the winding over an idempotent complement

For an idempotent matrix `e` and a loop `γ` of matrices commuting with `e` (pointwise), the loop
`γ` splits, at each point, into its "`e`-block" and its "`(1 - e)`-block":

  `γ x = (e * γ x * e + (1 - e)) * ((1 - e) * γ x * (1 - e) + e)`.

Consequently `det (γ x) = det (e * γ x * e + (1 - e)) * det ((1 - e) * γ x * (1 - e) + e)`, so
the winding of `det ∘ γ` is the sum of the windings measured through `im e` and through
`im (1 - e)`:

  `windLoop n e γ h + windLoop n (1 - e) γ h' = degNZ (detCM γ) hd`.

The key pointwise input is the pure ring identity `idem_corner_decomp`: for `e * e = e` and
`a * e = e * a`, `(e * a * e + (1 - e)) * ((1 - e) * a * (1 - e) + e) = a`.  Geometrically it
says that `a` preserves the decomposition `1 = e + (1 - e)` (the off-diagonal Peirce components
`e * a * (1 - e)` and `(1 - e) * a * e` vanish), so `a` is the product of "`a` on `im e`, extended
by the identity on `im (1 - e)`" with "`a` on `im (1 - e)`, extended by the identity on `im e`";
`Matrix.det_mul` then turns this into the multiplicative statement about determinants.
-/

namespace Work.KT.D2

open Matrix

noncomputable section

/-! ## 1. The pointwise Peirce decomposition -/

/-- **Peirce decomposition of an element commuting with an idempotent.**  If `e * e = e` and
`a * e = e * a`, then `a = (e * a * e + (1 - e)) * ((1 - e) * a * (1 - e) + (1 - (1 - e)))`:
`a` preserves the decomposition `1 = e + (1 - e)`, its two factors being `a` on `im e` extended
by the identity on `im (1 - e)`, and `a` on `im (1 - e)` extended by the identity on `im e`. -/
lemma idem_corner_decomp {R : Type*} [Ring R] (e a : R) (he : e * e = e)
    (ha : a * e = e * a) :
    (e * a * e + (1 - e)) * ((1 - e) * a * (1 - e) + (1 - (1 - e))) = a := by
  have hsub : 1 - (1 - e) = e := by rw [sub_sub_cancel]
  have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have hfe : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have hff : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, hef, sub_zero]
  have heae : e * a * e = e * a := by rw [mul_assoc, ha, ← mul_assoc, he]
  have hleft : (1 - e) * a = a - e * a := by rw [sub_mul, one_mul]
  have hfae : (1 - e) * a * e = 0 := by rw [hleft, sub_mul, ha, heae, sub_self]
  have hfaf : (1 - e) * a * (1 - e) = (1 - e) * a := by rw [mul_sub, mul_one, hfae, sub_zero]
  have heaf : e * a * (1 - e) = 0 := by rw [mul_sub, mul_one, heae, sub_self]
  have hsum : e + (1 - e) = 1 := by rw [add_sub_cancel]
  have hsum2 : e * a + (1 - e) * a = a := by rw [← add_mul, hsum, one_mul]
  rw [hsub]
  calc (e * a * e + (1 - e)) * ((1 - e) * a * (1 - e) + e)
      = (e * a + (1 - e)) * ((1 - e) * a + e) := by rw [heae, hfaf]
    _ = (e * a) * ((1 - e) * a) + (e * a) * e + (1 - e) * ((1 - e) * a) + (1 - e) * e := by
          noncomm_ring
    _ = 0 + e * a + (1 - e) * a + 0 := by
          rw [show (e * a) * ((1 - e) * a) = 0 from by rw [← mul_assoc, heaf, zero_mul],
              heae, show (1 - e) * ((1 - e) * a) = (1 - e) * a from by rw [← mul_assoc, hff],
              hfe]
    _ = a := by rw [zero_add, add_zero, hsum2]

/-- The determinant form of the Peirce decomposition: for an idempotent matrix `e` and a matrix
`a` commuting with `e`, `det a` factors as the product of the determinants of the two
"`e`-corner extended by the complementary identity" matrices. -/
lemma idem_corner_det (n : ℕ) (e a : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    (ha : a * e = e * a) :
    Matrix.det (e * a * e + (1 - e)) * Matrix.det ((1 - e) * a * (1 - e) + (1 - (1 - e)))
      = Matrix.det a := by
  rw [← Matrix.det_mul, idem_corner_decomp e a he ha]

/-! ## 2. The determinant loops multiply -/

/-- The determinant loop of the corner `e` times the determinant loop of the corner `1 - e`
is the determinant loop of `γ`, for `γ` pointwise commuting with the idempotent `e`. -/
lemma wlmDet_mul_compl (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    (γ : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ))
    (hγ : ∀ x, γ x * e = e * γ x) :
    wlmDet n e γ * wlmDet n (1 - e) γ = detCM γ := by
  apply ContinuousMap.ext
  intro x
  simp only [ContinuousMap.mul_apply, wlmDet_apply, detCM_apply]
  exact idem_corner_det n e (γ x) he (hγ x)

/-! ## 3. Additivity of the winding -/

/-- **The windings of the two corners add up to the winding of the determinant.**  For an
idempotent `e` and a nowhere-singular loop `γ` pointwise commuting with `e`, the winding of `γ`
restricted to `im e` plus its winding restricted to `im (1 - e)` is the winding of `det ∘ γ`. -/
theorem windLoop_compl (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    (γ : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ))
    (hγ : ∀ x, γ x * e = e * γ x)
    (h : ∀ x, Matrix.det (e * γ x * e + (1 - e)) ≠ 0)
    (h' : ∀ x, Matrix.det ((1 - e) * γ x * (1 - e) + (1 - (1 - e))) ≠ 0)
    (hd : ∀ x, Matrix.det (γ x) ≠ 0) :
    Work.KT.D2.windLoop n e γ h + Work.KT.D2.windLoop n (1 - e) γ h'
      = Work.KT.D2.degNZ (Work.KT.D2.detCM γ) hd := by
  have hfun := wlmDet_mul_compl n e he γ hγ
  have h2 : ∀ x, (wlmDet n e γ * wlmDet n (1 - e) γ) x ≠ 0 := by
    intro x
    rw [hfun]
    exact hd x
  rw [windLoop_eq_degNZ n e γ h, windLoop_eq_degNZ n (1 - e) γ h']
  rw [← degNZ_mul (wlmDet n e γ) (wlmDet n (1 - e) γ) h h' h2]
  exact wlmDegNZcongr hfun h2 hd

end

end Work.KT.D2
