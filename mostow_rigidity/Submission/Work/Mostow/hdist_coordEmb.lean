import Mathlib
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.fermi_inv

namespace Work.Mostow

set_option linter.unusedVariables false

open Submission.Mostow

/-! `Submission.Mostow.coordEmb k m : E k → E (k+m)` is the standard isometric embedding of the
stratum into `E (k+m)` (first `k` chart coordinates, last `m` zero); it is the Fermi point
`fermi k m v 0`.

Guidance: use `Work.Mostow.cosh_hdist_fermi` with `w = w' = 0` (plus `sinhc 0 = 1`, `inner _ 0 = 0`,
and `fermi k m v 0 = coordEmb k m v`, from `Work.Mostow.fermi_inv` and the definitions) to get
`Real.cosh (hdist (coordEmb k m a) (coordEmb k m b)) = Real.cosh (hdist a b)`; conclude with
`Real.cosh_injOn` on `Set.Ici 0`, using clause 1 of `HypIsometryProp (k+m)` (`0 ≤ hdist _ _`).
Alternatively the whole thing is a coordinate computation: `coordEmb` preserves the Euclidean norm
and inner product, so the two `arcosh` arguments coincide and `congrArg Real.arcosh` closes. -/

/-- `coordEmb k m v` is the Fermi point with foot `v` and zero normal coordinate. -/
private lemma fermi_zero_eq_coordEmb (k m : ℕ) (v : E k) :
    fermi k m v 0 = coordEmb k m v := by
  have hs : sinhc (0 : ℝ) = 1 := by rw [sinhc]; norm_num
  simp only [fermi, coordEmb, norm_zero, Real.cosh_zero, hs, one_mul]
  congr 1

/-- `coordEmb` preserves the time coordinate. -/
private lemma tpart_coordEmb (k m : ℕ) (v : E k) :
    tpart (coordEmb k m v) = tpart v := by
  rw [← fermi_zero_eq_coordEmb k m v, tpart_fermi]
  simp

/-- `coordEmb` preserves the Euclidean inner product. -/
private lemma inner_coordEmb (k m : ℕ) (a b : E k) :
    inner ℝ (coordEmb k m a) (coordEmb k m b) = inner ℝ a b := by
  rw [← fermi_zero_eq_coordEmb k m a, ← fermi_zero_eq_coordEmb k m b, inner_fermi]
  simp

theorem hdist_coordEmb (k m : ℕ) (hI : Submission.Mostow.HypIsometryProp (k + m))
    (a b : Submission.Mostow.E k) :
    Submission.Mostow.hdist (Submission.Mostow.coordEmb k m a) (Submission.Mostow.coordEmb k m b)
      = Submission.Mostow.hdist a b := by
  rw [hdist, hdist, tpart_coordEmb, tpart_coordEmb, inner_coordEmb]

end Work.Mostow
