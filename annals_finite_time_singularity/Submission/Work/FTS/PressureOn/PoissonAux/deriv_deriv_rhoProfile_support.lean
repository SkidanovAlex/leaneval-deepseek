import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux

open Filter
open scoped Topology

/-- If `f` is constant on an open neighbourhood `t` of `r`, then `deriv (deriv f) r = 0`.

Indeed `deriv f` is then eventually `0` at `r` (at every point of the open set `t` the function
`f` is constant on a neighbourhood, hence has derivative `0` there), so the second derivative
vanishes at `r`. -/
lemma deriv_deriv_eq_zero_of_isOpen_const {f : ℝ → ℝ} {c r : ℝ} {t : Set ℝ}
    (ht : IsOpen t) (hr : r ∈ t) (hf : ∀ s ∈ t, f s = c) :
    deriv (deriv f) r = 0 := by
  have hder : deriv f =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
    filter_upwards [ht.mem_nhds hr] with s hs
    have hfs : f =ᶠ[𝓝 s] fun _ => c := by
      filter_upwards [ht.mem_nhds hs] with x hx
      exact hf x hx
    rw [hfs.deriv_eq]
    exact deriv_const s c
  calc deriv (deriv f) r = deriv (fun _ => (0 : ℝ)) r := hder.deriv_eq
    _ = 0 := deriv_const r 0

theorem deriv_deriv_rhoProfile_support {ε r : ℝ} (hε : 0 < ε)
    (hr : |r| < ε ∨ Real.sqrt 2 * ε < |r|) :
    deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r = 0 := by
  rcases hr with hr | hr
  · -- inside the ball `|r| < ε`, where `rhoProfile ε = 0`
    have hrU : r ^ 2 < ε ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hε]
      exact hr
    refine deriv_deriv_eq_zero_of_isOpen_const
      (f := Work.FTS.PressureOn.rhoProfile ε) (c := 0)
      (isOpen_lt (continuous_pow 2) continuous_const) hrU ?_
    intro s hs
    exact Work.FTS.PressureOn.rhoProfile_eq_zero hε (le_of_lt hs)
  · -- outside the ball `√2 ε < |r|`, where `rhoProfile ε = 1`
    have hsq : (Real.sqrt 2 * ε) ^ 2 < r ^ 2 := by
      rw [sq_lt_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2 * ε)]
      exact hr
    have hrU : 2 * ε ^ 2 < r ^ 2 := by
      nlinarith [hsq, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    refine deriv_deriv_eq_zero_of_isOpen_const
      (f := Work.FTS.PressureOn.rhoProfile ε) (c := 1)
      (isOpen_lt continuous_const (continuous_pow 2)) hrU ?_
    intro s hs
    exact Work.FTS.PressureOn.rhoProfile_eq_one hε (le_of_lt hs)

end Work.FTS.PressureOn.PoissonAux
