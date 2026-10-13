import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RPFresh

/-- The derivative of the radial weight `w(z) = (1+z)²/z²`:
`w'(x) = -2(1+x)/x³` for `x ≠ 0`. -/
lemma hasDerivAt_w {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt Work.Spaces.w (-(2 * (1 + x) / x ^ 3)) x := by
  have ha : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + x)) x := by
    have h := ((hasDerivAt_const (x : ℝ) (1 : ℝ)).add (hasDerivAt_id x)).pow 2
    convert h using 1
    · ext z; simp
    · simp only [Pi.add_apply, id_eq]; ring
  have hb : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    have h := (hasDerivAt_id x).pow 2
    convert h using 1
    · ext z; simp
    · simp only [id_eq]; ring
  exact (ha.div hb (by positivity)).congr_deriv (by field_simp; ring)

/-- `w(x)² * x` as a function of `x` has derivative `w(x)² * (x-3)/(1+x)`. -/
lemma hasDerivAt_w2_mul_id {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z)
      ((Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hw : HasDerivAt Work.Spaces.w (-(2 * (1 + x) / x ^ 3)) x := hasDerivAt_w hxne
  have hw2 : HasDerivAt (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (2 * Work.Spaces.w x * (-(2 * (1 + x) / x ^ 3))) x := by
    have h := hw.pow 2
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    norm_num
  have hz : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
  have h := hw2.mul hz
  refine h.congr_deriv ?_
  unfold Work.Spaces.w
  field_simp
  ring

theorem hasDerivAt_w2z_mul {f : ℝ → ℝ} {x f' : ℝ} (hx : 0 < x) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z * f z)
      ((Work.Spaces.w x) ^ 2 * (x * f' + ((x - 3) / (1 + x)) * f x)) x := by
  have hmain := hasDerivAt_w2_mul_id hx
  refine (hmain.mul hf).congr_deriv ?_
  ring_nf

end Work.RPFresh
