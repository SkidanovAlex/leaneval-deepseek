import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- The dual-lattice momentum vector is additive in the lattice label:
`vec (a - b) = vec a - vec b`. -/
private lemma vec_sub (a b : Fin 3 → ℤ) :
    Work.BoseB4.vec (a - b) = Work.BoseB4.vec a - Work.BoseB4.vec b := by
  unfold Work.BoseB4.vec
  rw [show (fun i : Fin 3 => 2 * Real.pi * ↑((a - b) i))
      = (fun i : Fin 3 => 2 * Real.pi * ↑(a i)) - (fun i : Fin 3 => 2 * Real.pi * ↑(b i)) from by
    funext i; simp only [Pi.sub_apply]; push_cast; ring]
  exact WithLp.toLp_sub 2 _ _

/-- `vec (a + b) = vec a + vec b`. -/
private lemma vec_add (a b : Fin 3 → ℤ) :
    Work.BoseB4.vec (a + b) = Work.BoseB4.vec a + Work.BoseB4.vec b := by
  unfold Work.BoseB4.vec
  rw [show (fun i : Fin 3 => 2 * Real.pi * ↑((a + b) i))
      = (fun i : Fin 3 => 2 * Real.pi * ↑(a i)) + (fun i : Fin 3 => 2 * Real.pi * ↑(b i)) from by
    funext i; simp only [Pi.add_apply]; push_cast; ring]
  exact WithLp.toLp_add 2 _ _

/-- **Product-to-sum on the unit cell.**  Since `vec` is additive on lattice labels
(`vec_sub`, `vec_add`) and the inner product is linear in its first argument, the
product of the two cosines is the sum of the cosines at the sum and difference
frequencies:
`cos⟪vec a,x⟫ cos⟪vec b,x⟫ = ½(cos⟪vec (a−b),x⟫ + cos⟪vec (a+b),x⟫)`, which is the
prosthaphaeresis identity `Real.cos_sub`, `Real.cos_add`. -/
private lemma cos_mul_cos_vec (a b : Fin 3 → ℤ) (x : EuclideanSpace ℝ (Fin 3)) :
    Real.cos (inner ℝ (Work.BoseB4.vec a) x) * Real.cos (inner ℝ (Work.BoseB4.vec b) x)
      = (Real.cos (inner ℝ (Work.BoseB4.vec (a - b)) x)
          + Real.cos (inner ℝ (Work.BoseB4.vec (a + b)) x)) / 2 := by
  rw [vec_sub, vec_add, inner_sub_left, inner_add_left, Real.cos_sub, Real.cos_add]
  ring

/-- **The characters of the unit torus are orthogonal, jointly.**  For every pair of
lattice vectors `a b : ℤ³`,

`∫_{[-1/2,1/2]³} cos⟪vec a,x⟫ cos⟪vec b,x⟫ dx = ½(δ_{a,b} + δ_{a,−b})`.

Indeed, by `cos_mul_cos_vec` the integrand is `½` times the sum of the two single-cosine
integrands at the frequencies `a − b` and `a + b`, and each of those integrates to the
Kronecker delta of its frequency (`Work.BoseB4.integral_unitCell_cos_lattice`). -/
theorem integral_unitCell_cos_cos (a b : Fin 3 → ℤ) :
    ∫ x in Work.BoseB4.unitCell,
        Real.cos (inner ℝ (Work.BoseB4.vec a) x) * Real.cos (inner ℝ (Work.BoseB4.vec b) x)
      = ((if a = b then (1 : ℝ) else 0) + (if a = -b then (1 : ℝ) else 0)) / 2 := by
  rw [MeasureTheory.setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
    (fun x _ => cos_mul_cos_vec a b x)]
  rw [MeasureTheory.integral_div]
  rw [MeasureTheory.integral_add]
  · simp only [Work.BoseB4.vec]
    rw [Work.BoseB4.integral_unitCell_cos_lattice (a - b),
      Work.BoseB4.integral_unitCell_cos_lattice (a + b)]
    simp only [sub_eq_zero, add_eq_zero_iff_eq_neg]
  · exact ((by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Real.cos (inner ℝ (Work.BoseB4.vec (a - b)) x)))).continuousOn.integrableOn_compact
      Work.BoseB4.isCompact_unitCell
  · exact ((by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Real.cos (inner ℝ (Work.BoseB4.vec (a + b)) x)))).continuousOn.integrableOn_compact
      Work.BoseB4.isCompact_unitCell

end Work.BoseBoxFock
