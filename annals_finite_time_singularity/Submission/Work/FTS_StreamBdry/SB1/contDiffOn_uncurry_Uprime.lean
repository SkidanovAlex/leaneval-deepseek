import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB1.contDiffOn_uncurry_Uprime`

`U'(Ψ) = Uop αG Ψ / s2` with `Uop αG Ψ = -3Ψ - αG z ∂_zΨ` and `s2 θ = sin 2θ` is `C¹`
on the open quadrant `Qd = (0,∞) × (0,π/2)` as soon as `Ψ` is `C³` there.

Route: `Ψ` is `C¹` on `Qd` (`h3.of_le`), and `∂_zΨ` is `C¹` on `Qd` by
`Work.Spaces.uncurry_partial_c1` (the curried `z`-partial of a `C²` function on an open
set), so the numerator `-3Ψ - αG z ∂_zΨ` is `C¹`; the denominator `sin 2θ` is `C^∞` and
non-zero on `Qd` (`0 < 2θ < π`), so `ContDiffOn.div` applies.  The division is exactly the
definition of `Uprime`, so the last step is `rfl` after unfolding.
-/

namespace Work.FTS_StreamBdry.SB1

open Set

theorem contDiffOn_uncurry_Uprime {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.FTS.StreamBdryIface.Uprime αG Ψ))
      Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have h2 : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd :=
    h3.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ)) Work.Construction.Qd :=
    (Work.Spaces.uncurry_partial_c1 hQd h2).1
  have hnum : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      -3 * Function.uncurry Ψ p - αG * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Construction.Qd := by
    refine (contDiffOn_const.mul (h2.of_le (m := 1) (by norm_num))).sub ?_
    exact (contDiffOn_const.mul (contDiff_fst.contDiffOn)).mul hpz
  have hden : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Construction.Qd :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hne : ∀ p ∈ Work.Construction.Qd, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    have hθ1 : 0 < p.2 := hp.2.1
    have hθ2 : p.2 < Real.pi / 2 := hp.2.2
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [Real.pi_pos]))
  have hquot := hnum.div hden hne
  refine hquot.congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry, Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop,
    Work.Construction.s2, Work.Spaces.pz, Pi.div_apply]

end Work.FTS_StreamBdry.SB1
