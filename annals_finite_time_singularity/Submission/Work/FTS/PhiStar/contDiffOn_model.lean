import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Model
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.contDiffOn_model`

The joint `C^n`-regularity of the two-term model `Model α Gz ψ` on the open quadrant:
the model is `(z,θ) ↦ Gz z · sin 2θ + α φ(z) ψ(θ)`, so on `Q0 = (0,∞) × (0,π/2)` it is
`C^n` as soon as `Gz` is `C^n` on `(0,∞)` and `ψ` is `C^n` on `(0,π/2)` — the radial factor
`φ = 2z/(1+z)²` being a rational function with non-vanishing denominator for `z > 0`.

Note (`open scoped Real`): the statement below writes `π` for the angular endpoint; the
`Real` scope is opened so that `π` denotes `Real.pi` (as it does in the definition of
`Work.FTS.EllipticEst.Q0` and in the sibling statement `contDiffAt_model`).
-/

open scoped Real Topology

namespace Work.FTS.PhiStar

/-- **Joint regularity of the model part.**  If `Gz` is `C^n` on `(0,∞)` and `ψ` is `C^n` on
`(0,π/2)`, then the uncurried model `(z,θ) ↦ Gz z · sin 2θ + α φ(z) ψ(θ)` is `C^n` on the
open quadrant `Q0 = (0,∞) × (0,π/2)`.

Every factor is smooth on exactly the interval on which its coordinate ranges over `Q0`:
`sin (2·)` is smooth everywhere, `φ = 2z/(1+z)²` is smooth on `Ioi 0`, and the composition
of `hGz`, `hψ` with the two projections through `ContDiffOn.comp` plus closure of
`ContDiffOn` under products and sums gives the claim. -/
theorem contDiffOn_model {α : ℝ} {Gz ψ : ℝ → ℝ} (n : ℕ)
    (hGz : ContDiffOn ℝ n Gz (Set.Ioi 0)) (hψ : ContDiffOn ℝ n ψ (Set.Ioo 0 (π / 2))) :
    ContDiffOn ℝ n (Function.uncurry (Work.FTS.PhiStar.Model α Gz ψ))
      Work.FTS.EllipticEst.Q0 := by
  have hG : ContDiffOn ℝ n (fun p : ℝ × ℝ => Gz p.1) Work.FTS.EllipticEst.Q0 :=
    hGz.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have hPsi : ContDiffOn ℝ n (fun p : ℝ × ℝ => ψ p.2) Work.FTS.EllipticEst.Q0 :=
    hψ.comp contDiffOn_snd fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_snd).sin
  have hden : ∀ p ∈ Work.FTS.EllipticEst.Q0, (1 + p.1) ^ 2 ≠ 0 := by
    intro p hp
    have hz : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    positivity
  have hnum : ContDiffOn ℝ n (fun p : ℝ × ℝ => (2 : ℝ) * p.1) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_fst
  have hden2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_fst).pow 2
  have hphi : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => 2 * p.1 / (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 :=
    hnum.div hden2 hden
  have hall : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      Gz p.1 * Real.sin (2 * p.2) + α * (2 * p.1 / (1 + p.1) ^ 2) * ψ p.2)
      Work.FTS.EllipticEst.Q0 :=
    (hG.mul hsin).add (((contDiffOn_const (c := α)).mul hphi).mul hPsi)
  show ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      Gz p.1 * Real.sin (2 * p.2) + α * Work.FTS.VocabO.phiR p.1 * ψ p.2)
      Work.FTS.EllipticEst.Q0
  simpa only [Work.FTS.VocabO.phiR] using hall

end Work.FTS.PhiStar
