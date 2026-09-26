import Mathlib
import Submission.Work.Modular.Lattice

/-!
# The imaginary axis and the Gaussian sum

This file provides the vocabulary connecting the theta series `Θ_L` of a lattice `L ⊆ ℝⁿ` with
the Gaussian sum `F t = ∑_{x ∈ L} exp (-π t ‖x‖²)`.

* `imagPoint t` is the point `i t` of the upper half plane (`UpperHalfPlane.ofComplex` applied to
  `t * I`; junk for `t ≤ 0`, but we only use it for `0 < t`).
* `gaussSum L t = ∑_{x ∈ L} exp (-π t ‖x‖²)`.

The bridge between the two is `Θ_L (i t) = F t`, while the modular `S`-action sends `i t` to
`i / t`, so the `S`-transformation law for `Θ_L` is on the imaginary axis exactly the functional
equation `F t = t^{-n/2} F (1/t)` of the Gaussian.
-/

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

/-- The point `i t` of the upper half plane, for a real number `t`.  For `t ≤ 0` this is junk
(the value of `UpperHalfPlane.ofComplex` off `ℍ`); we only ever use it with `0 < t`. -/
noncomputable def imagPoint (t : ℝ) : ℍ := ofComplex ((t : ℂ) * Complex.I)

lemma coe_imagPoint {t : ℝ} (ht : 0 < t) : (imagPoint t : ℂ) = (t : ℂ) * Complex.I := by
  rw [imagPoint, ofComplex_apply_of_im_pos (by simpa [Complex.mul_im] using ht)]

lemma imagPoint_im {t : ℝ} (ht : 0 < t) : (imagPoint t).im = t := by
  rw [← UpperHalfPlane.coe_im, coe_imagPoint ht, Complex.mul_im]
  simp

lemma imagPoint_injOn : Set.InjOn imagPoint {t : ℝ | 0 < t} := by
  intro t ht s hs h
  have h' := congrArg (fun z : ℍ => (z : ℂ)) h
  rw [coe_imagPoint ht, coe_imagPoint hs] at h'
  have := congrArg Complex.im h'
  simpa [Complex.mul_im] using this

lemma imagPoint_eq_iff {t : ℝ} (ht : 0 < t) : imagPoint t = imagPoint 1 ↔ t = 1 := by
  refine ⟨fun h => imagPoint_injOn ht (by norm_num) h, fun h => by rw [h]⟩

/-- The Gaussian sum `F t = ∑_{x ∈ L} exp (-π t ‖x‖²)` of a discrete lattice `L ⊆ ℝⁿ`. -/
noncomputable def gaussSum {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (t : ℝ) : ℂ :=
  ∑' x : L, Complex.exp (-(↑(Real.pi * t * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) : ℂ))

end Work.Modular
