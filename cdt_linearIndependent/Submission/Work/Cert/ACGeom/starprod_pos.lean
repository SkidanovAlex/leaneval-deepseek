import Mathlib
import Submission.Work.Cert.ACGeom.GeomAux

/-!
# Positivity of `star (cx x y) * cx u v`

For `cx x y = (x/S) + (y/S)·I` (module `Submission.Work.Cert.Spec`) the Hermitian product
`star (cx x y) * cx u v = ((x·u + y·v) + (x·v - y·u)·I)/S²` has both its real and its
imaginary part positive as soon as the two integer bilinear forms `x·u + y·v` and
`x·v - y·u` are positive.  This is the elementary algebraic step behind the geometric
soundness condition `geomOK` (see `geomOK_facts.lean`), where `(x,y)` and `(u,v)` are two
successive points of a short counter-clockwise arc of a circle.
-/
namespace Work.Cert.ACGeom

/-- Real part of `star (cx x y) * cx u v`. -/
lemma star_cx_mul_re (x y u v : ℤ) :
    (star (cx x y) * cx u v).re = ((x * u + y * v : ℤ) : ℝ) / (S : ℝ) ^ 2 := by
  simp [cx, Complex.mul_re, Complex.mul_im]
  field_simp

/-- Imaginary part of `star (cx x y) * cx u v`. -/
lemma star_cx_mul_im (x y u v : ℤ) :
    (star (cx x y) * cx u v).im = ((x * v - y * u : ℤ) : ℝ) / (S : ℝ) ^ 2 := by
  simp [cx, Complex.mul_re, Complex.mul_im, Int.cast_sub]
  field_simp
  ring

theorem starprod_pos (x y u v : ℤ) (hre : 0 < x * u + y * v) (him : 0 < x * v - y * u) :
    0 < (star (cx x y) * cx u v).im ∧ 0 < (star (cx x y) * cx u v).re := by
  have him' : (0 : ℝ) < ((x * v - y * u : ℤ) : ℝ) := by exact_mod_cast him
  have hre' : (0 : ℝ) < ((x * u + y * v : ℤ) : ℝ) := by exact_mod_cast hre
  constructor
  · rw [star_cx_mul_im]
    exact div_pos him' (pow_pos S_pos 2)
  · rw [star_cx_mul_re]
    exact div_pos hre' (pow_pos S_pos 2)

end Work.Cert.ACGeom
