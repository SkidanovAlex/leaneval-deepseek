import Mathlib
import Submission.Work.Drive.Generic.HeightDefs

/-!
# Smoothness of the Gauss parametrisation

`gaussParam Φ z = z 2 • normal Φ (z 0, z 1)` where `normal Φ p = d1 Φ p ⨯ d2 Φ p` is built from the
first derivative of `Φ`.  Hence if `Φ` is `C^3` then `z ↦ fderiv ℝ Φ (z 0, z 1)` is `C^2`, its two
partial evaluations `z ↦ fderiv ℝ Φ (z 0, z 1) (1,0)` and `z ↦ fderiv ℝ Φ (z 0, z 1) (0,1)` are
`C^2`, the cross product of two `C^2` maps is `C^2`, and multiplying by the (linear, hence `C^2`)
scalar function `z ↦ z 2` preserves `C^2`.
-/

namespace Work.Drive.Generic

/-- The cross product on `E3`, as a map on pairs, is `C^∞` (we only need `C^2`).  This is proved
coordinate by coordinate: each coordinate of `crossE u v` is a difference of products of two
coordinates of `u` and `v`. -/
lemma contDiff_crossE_pair : ContDiff ℝ 2 (fun w : E3 × E3 => crossE w.1 w.2) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [crossE, cross_apply] <;> fun_prop

/-- The parametrisation `z ↦ z 2 • N(z 0, z 1)` of the critical directions of the height functions
is `C^2` when `Φ` is `C^3`. -/
theorem contDiff_gaussParam {Φ : ℝ × ℝ → Work.Drive.Generic.E3} (hΦ : ContDiff ℝ 3 Φ) :
    ContDiff ℝ 2 (Work.Drive.Generic.gaussParam Φ) := by
  -- the uncurried first derivative `(p, v) ↦ fderiv ℝ Φ p v` is `C^2`
  have hderiv : ContDiff ℝ 2 (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ Φ p.1) p.2) :=
    hΦ.contDiff_fderiv_apply (m := 2) (by norm_num)
  -- the partial evaluations against the two coordinate directions, as functions of `z`
  have hL1 : ContDiff ℝ 2 (fun z : E3 => (((z 0, z 1) : ℝ × ℝ), ((1, 0) : ℝ × ℝ))) := by
    fun_prop
  have hL2 : ContDiff ℝ 2 (fun z : E3 => (((z 0, z 1) : ℝ × ℝ), ((0, 1) : ℝ × ℝ))) := by
    fun_prop
  have hd1 : ContDiff ℝ 2 (fun z : E3 => (fderiv ℝ Φ (z 0, z 1)) (1, 0)) := hderiv.comp hL1
  have hd2 : ContDiff ℝ 2 (fun z : E3 => (fderiv ℝ Φ (z 0, z 1)) (0, 1)) := hderiv.comp hL2
  -- the Gauss map `z ↦ normal Φ (z 0, z 1)` is `C^2`
  have hnorm : ContDiff ℝ 2 (fun z : E3 => normal Φ (z 0, z 1)) :=
    contDiff_crossE_pair.comp (hd1.prodMk hd2)
  -- multiplying by the linear scalar function `z ↦ z 2` preserves `C^2`
  have h2 : ContDiff ℝ 2 (fun z : E3 => z 2) := by fun_prop
  exact h2.smul hnorm

end Work.Drive.Generic
