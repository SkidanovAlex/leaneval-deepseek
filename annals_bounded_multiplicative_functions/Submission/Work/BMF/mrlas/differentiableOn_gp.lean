import Mathlib
import Submission.Work.BMF.halasz_series_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open scoped Classical

/-- The local Euler factor `g_p` of a bounded sequence `f` is holomorphic on the half-plane
`re s > 1`.  Indeed `g_p(s) = Σ_{e ≥ 0} f(p^e) (p^e)^{-s}` is a sub-series of the L-series of
`f`, which is absolutely convergent (hence differentiable) for `re s > abscissaOfAbsConv f ≤ 1`. -/
theorem differentiableOn_gp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime) :
    DifferentiableOn ℂ (fun z : ℂ => Work.BMF.gp f p z) {z : ℂ | 1 < z.re} := by
  -- `f` is bounded, hence its abscissa of absolute convergence is `≤ 1`.
  have habs : LSeries.abscissaOfAbsConv f ≤ (1 : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => hb n⟩
  have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp.two_le
  intro z hz
  -- rewrite `g_p` as the (sub-)series whose differentiability we establish
  rw [show (fun z : ℂ => Work.BMF.gp f p z)
        = fun z : ℂ => ∑' e : ℕ, LSeries.term f z (p ^ e) from by funext w; rfl]
  have hzre : (1 : ℝ) < z.re := hz
  -- a real point `y` with `1 < y < re z`
  set y : ℝ := (1 + z.re) / 2 with hy_def
  have hy1 : 1 < y := by rw [hy_def]; linarith
  have hyz : y < z.re := by rw [hy_def]; linarith
  have hU : IsOpen {w : ℂ | y < w.re} := isOpen_lt continuous_const Complex.continuous_re
  -- the L-series of `f` is summable at the real point `y > 1`
  have hylt : LSeries.abscissaOfAbsConv f < ((y : ℂ).re : EReal) := by
    rw [Complex.ofReal_re]
    exact lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hy1)
  have hsumm : LSeriesSummable f (y : ℂ) := LSeriesSummable_of_abscissaOfAbsConv_lt_re hylt
  have hsumm' : Summable (fun n : ℕ => ‖LSeries.term f (y : ℂ) n‖) :=
    summable_norm_iff.mpr hsumm
  -- hence also along the subsequence `e ↦ p ^ e`
  have hsumm'' : Summable (fun e : ℕ => ‖LSeries.term f (y : ℂ) (p ^ e)‖) :=
    hsumm'.comp_injective hinj
  -- term-by-term differentiation on the open half-plane `{w | y < w.re}`
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => ∑' e : ℕ, LSeries.term f w (p ^ e)) {w : ℂ | y < w.re} :=
    Complex.differentiableOn_tsum_of_summable_norm hsumm''
      (fun e => fun w _ =>
        (LSeries.hasDerivAt_term f (p ^ e) w).differentiableAt.differentiableWithinAt)
      hU
      (fun e w hw => LSeries.norm_term_le_of_re_le_re f
        (by rw [Complex.ofReal_re]; exact le_of_lt hw) (p ^ e))
  have hzw : z ∈ {w : ℂ | y < w.re} := hyz
  exact (hdiff.differentiableAt (hU.mem_nhds hzw)).differentiableWithinAt

end Work.BMF.mrlas
