/-
# `Transfer/GamSmooth.lean` — smoothness of the angular factor `Γ` on the open quadrant

The transfer's `D_z`-defect `E2 α f = Ê₂ f + Γ(θ)·radS α f z` and the membership of the second
summand need the smoothness on the open quadrant of the *angular* factor

  `Gam α θ = (sin θ · cos²θ)^{α/3}`   (`Work.Spaces.Gam`),

which is a `C^∞` function of `θ` alone on `(0, π/2)`.  This is a local copy of
`Work.FTS.OpenPkg.contDiffOn_Gam_Q0`, provided here so that the coercivity cone does **not**
have to import the `OpenPkg` chapter (whose import closure contains other areas' work in
progress).  The statement is at the open quadrant `Work.Construction.Qd = (0,∞) × (0,π/2)`,
which is the form in which the transfer consumes it.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.Vocab
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

set_option autoImplicit false

/-- **`Γ α = (sin θ·cos²θ)^{α/3}` is `C^n` on the open quadrant**, for every `n` and every `α`:
the base `sin θ·cos²θ` is positive and smooth there. -/
theorem contDiffOn_Gam_Qd (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Work.Construction.Qd := by
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
      Work.Construction.Qd :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Work.Construction.Qd, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hp.2.1, Real.pi_pos])
      (by linarith [hp.2.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
    positivity
  simpa only [Work.Spaces.Gam] using
    hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

end Work.FTS.CoercivityFix.Transfer
