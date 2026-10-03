import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.thetaHol_exp_decay
import Submission.Work.FIArea6Hecke.R.thetaHol_meas_li

namespace Work.FIArea6Hecke.R

open Work.FIArea5.S16Hecke

/-- Shifting the Gaussian decay to the origin: for the fixed cut `c`,
`e^{-π(u-c)} = e^{πc}·e^{-πu}`.  This is the only point where the decay statement of
`thetaHol_exp_decay` (relative to the cut `thetaC d`) is converted into the decay
`C·e^{-πu}` from the origin. -/
lemma thetaHol_zero_exp_shift (u c : ℝ) :
    Real.exp (-Real.pi * (u - c)) = Real.exp (Real.pi * c) * Real.exp (-Real.pi * u) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Basic analyticity facts for `thetaHol χ 0`.**  For a character `χ` modulo `4d` (strict,
i.e. vanishing off the units), the weight-`0` holomorphic theta series `Σ_{z primary} χ(z)e^{-πu|z|²}`
is continuous on `(0,∞)` and decays like `e^{-πu}` at infinity: there are `C` and `u₀ > 0` with
`‖thetaHol χ 0 u‖ ≤ C·e^{-πu}` for all `u ≥ u₀`.

Continuity is `Work.FIArea6Hecke.R.continuousOn_thetaHol_Ioi` (dominated convergence for the
`tsum`, the Gaussian weight at any fixed `a > 0` being summable).  Decay is
`Work.FIArea5.S16Hecke.thetaHol_exp_decay` at the cut `thetaC d = 1/(4d)`, whose conclusion
`≤ C₀·e^{-π(u-1/(4d))}` becomes `≤ C₀e^{π/(4d)}·e^{-πu}`. -/
theorem thetaHol_zero_basic {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    ContinuousOn (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol chi 0 u) (Set.Ioi 0) ∧
    ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖Work.FIArea5.S16Hecke.thetaHol chi 0 u‖ ≤ C * Real.exp (-Real.pi * u) := by
  -- a strict character modulo `4d` is bounded by `1`
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  refine ⟨continuousOn_thetaHol_Ioi (m := 0) hb, ?_⟩
  obtain ⟨C₀, _hC₀, hdec⟩ := thetaHol_exp_decay d hd chi 0 hb
  refine ⟨C₀ * Real.exp (Real.pi * thetaC d), thetaC d, thetaC_pos hd, fun u hu => ?_⟩
  refine (hdec u hu).trans_eq ?_
  rw [thetaHol_zero_exp_shift]
  ring

end Work.FIArea6Hecke.R
