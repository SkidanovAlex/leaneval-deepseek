import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS.ClassC.HkMem_seven_slots_of_plain_family
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-- **The `z²∂_z²` bound for the particular solution `psiP` at `z = 1`.**
`SlotBd α Ψ M` bounds `|D_z^j psiP| ≤ M·sin 2θ` for `j ≤ 2` (`SB3.psiP_DzLe`, which needs
`0 < α`, `ContDiffOn ℝ 3 (uncurry Ψ) Qd` and `SlotBd α Ψ M`), and on the open quadrant
`z²∂_z² h = D_z²h - D_zh` (`ClassC.seven_zsq_pzIter_two_eq`, from `SmoothOpen h`).
At `z = 1` (`1² = 1`) this gives `|∂_z² psiP| = |D_z² psiP − D_z psiP| ≤ M sin 2θ + M sin 2θ =
2 M sin 2θ` by the triangle inequality (no sign hypothesis on `M` is needed for that step).
Consumed by `Work.FTS.EllLimOK.ProducerH.kappa_eq_zero`. -/
theorem abs_pzIterTwo_psiP_le {α M : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd α Ψ M)
    (hP : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StreamBdryIface.psiP α Ψ))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
      ≤ 2 * M * Real.sin (2 * θ) := by
  -- SB3: `|D_z^j psiP| ≤ M·sin 2θ` on the open quadrant, for `j ≤ 2`.
  have hPsi : Work.FTS_StreamBdry.PsiPDzLe α M Ψ :=
    Work.FTS_StreamBdry.SB3.psiP_DzLe hα h3 hslot
  have hmem : ((1 : ℝ), θ) ∈ Work.Construction.Qd :=
    ⟨by norm_num, hθ.1, hθ.2⟩
  have h2 : |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
      ≤ M * Real.sin (2 * θ) := by
    simpa only [Work.Construction.s2_eq] using hPsi 1 θ hmem 2 (by norm_num)
  have h1 : |Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
      ≤ M * Real.sin (2 * θ) := by
    simpa only [Work.Construction.s2_eq] using hPsi 1 θ hmem 1 (by norm_num)
  -- The level-0 identity `z²∂_z²h = D_z²h − D_zh`, at `z = 1`.
  have heq := Work.FTS.ClassC.seven_zsq_pzIter_two_eq
    (Work.FTS.StreamBdryIface.psiP α Ψ) hP 1 θ (by norm_num) hθ.1 hθ.2
  have hkey : Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ
      = Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ
        - Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ := by
    simpa using heq
  rw [hkey]
  calc |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ
          - Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
      ≤ |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
        + |Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ| := abs_sub _ _
    _ ≤ M * Real.sin (2 * θ) + M * Real.sin (2 * θ) := add_le_add h2 h1
    _ = 2 * M * Real.sin (2 * θ) := by ring

end Work.FTS_EllLimOK.ProducerH
